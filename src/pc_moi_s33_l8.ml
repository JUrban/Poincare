(* ========================================================================= *)
(* pc_moi_s33_l8: Moise Sec 33 Lemma 8, p.233.  Main theorem                *)
(* S33_L8 |- MOI_S33_L8 of pc_moi_s33_stmt.ml: a PL disk d in a piece c     *)
(* v, inside Int N', whose boundary is its trace on the pseudo-cell e[v,w]  *)
(* and bounds there a disk around the centre, and which misses the other    *)
(* pseudo-cells, meets K'.  Route (topological): d UNION dj is a 2-sphere   *)
(* (Part 2); dj lies in the open pseudo-cell (Part 1); Jordan-Brouwer; the  *)
(* frontier of N' (connected by TUBE_FACTS), the w-side piece and the       *)
(* second pseudo-cell e[v,w'] lie in one component; an arm along K' puts    *)
(* the v-side near the centre there too; at a triangle point of e[v,w] near *)
(* the centre (LOCAL_TRI) both local sides are then in one component, a     *)
(* contradiction.  MOISE_324 is an unused antecedent.  MOI_S3L8_MAIN proves *)
(* the body from MOI_S33_TUBE_FACTS; Part 7 discharges it by MP with        *)
(* TUBE_FACTS of pc_moi_s33_frame.                                          *)
(* ========================================================================= *)

needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_s26_local.ml";;
needs "src/pc_moi_s33_frame.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: the planar lemma.  A disk dj in a pseudo-cell e whose           *)
(* boundary J misses the rim lies in the open cell e minus its rim, and    *)
(* its interior is open in e.  In the planar chart of the open cell, J is  *)
(* a Jordan curve; the interior of dj is connected, so it lies inside J or *)
(* outside J.  Outside is impossible: by invariance of domain the interior  *)
(* would fill the annulus between J and the rim, so the rim would lie in   *)
(* the open disk dj DIFF J, and the rim (a circle) would disconnect it.    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L8_COMPACT_IN_BALL = prove
 (`!k:real^N->bool.
     compact k /\ k SUBSET ball(vec 0,&1)
     ==> ?r. &0 < r /\ r < &1 /\ k SUBSET ball(vec 0,r)`,
  GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `k:real^N->bool = {}` THENL
   [EXISTS_TAC `&1 / &2` THEN ASM_REWRITE_TAC[EMPTY_SUBSET] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (norm:real^N->real) k` COMPACT_ATTAINS_SUP) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_EQ_EMPTY; GSYM IMAGE_o] THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `norm(x0:real^N) < &1` ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^N->bool) SUBSET ball(vec 0,&1)` THEN
    UNDISCH_TAC `(x0:real^N) IN k` THEN REWRITE_TAC[SUBSET; IN_BALL_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(norm(x0:real^N) + &1) / &2` THEN
  REWRITE_TAC[SUBSET; IN_BALL_0] THEN CONJ_TAC THENL
   [MP_TAC(ISPEC `x0:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* The open unit disk minus a compact subset with connected complement is  *)
(* connected (radial retraction onto a smaller closed disk, plus an outer  *)
(* annulus).                                                                *)

let MOI_S3L8_BALL_MINUS_COMPACT = prove
 (`!k:real^2->bool.
     compact k /\ k SUBSET ball(vec 0,&1) /\ connected ((:real^2) DIFF k)
     ==> connected (ball(vec 0,&1) DIFF k)`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `k:real^2->bool` MOI_S3L8_COMPACT_IN_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?q. r < q /\ q < &1` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `(r + &1) / &2` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. x IN k ==> norm x < r` ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^2->bool) SUBSET ball(vec 0,r)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^2,&1) DIFF k =
                (cball(vec 0,q) DIFF k) UNION {x | r < norm(x - vec 0) /\ norm(x - vec 0) < &1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNION; IN_ELIM_THM; IN_BALL_0; IN_CBALL_0;
                VECTOR_SUB_RZERO] THEN
    X_GEN_TAC `x:real^2` THEN
    ASM_CASES_TAC `(x:real^2) IN k` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
   [(* the radial retraction onto cball(0,q) *)
    SUBGOAL_THEN
     `cball(vec 0:real^2,q) DIFF k =
      IMAGE (\x:real^2. if norm x <= q then x else (q / norm x) % x) ((:real^2) DIFF k)`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^2` THEN
      REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_UNIV; IN_CBALL_0] THEN EQ_TAC THENL
       [STRIP_TAC THEN EXISTS_TAC `y:real^2` THEN ASM_REWRITE_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
        FIRST_X_ASSUM SUBST1_TAC THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `norm((q / norm(x:real^2)) % x) = q` ASSUME_TAC THENL
         [REWRITE_TAC[NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
          SUBGOAL_THEN `&0 < norm(x:real^2) /\ &0 < q` STRIP_ASSUME_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ; REAL_ABS_REFL; REAL_LT_IMP_LE];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[REAL_LE_REFL] THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `(q / norm(x:real^2)) % x`) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[SUBSET_UNIV] THEN
    SUBGOAL_THEN `(:real^2) = {x | norm x <= q} UNION {x | q <= norm x}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_UNIV] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CASES THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM IN_CBALL_0; SET_RULE `{x:real^2 | x IN s} = s`; CLOSED_CBALL];
      REWRITE_TAC[REAL_ARITH `q <= x <=> ~(x < q)`; GSYM IN_BALL_0] THEN
      REWRITE_TAC[SET_RULE `{x:real^2 | ~(x IN s)} = (:real^2) DIFF s`] THEN
      REWRITE_TAC[GSYM OPEN_CLOSED; OPEN_BALL];
      REWRITE_TAC[CONTINUOUS_ON_ID];
      MATCH_MP_TAC CONTINUOUS_ON_MUL THEN REWRITE_TAC[CONTINUOUS_ON_ID] THEN
      SUBGOAL_THEN `(lift o (\x:real^2. q / norm x)) = (\x. q % (lift o inv o norm) x)`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; real_div; LIFT_CMUL] THEN
        REWRITE_TAC[REAL_MUL_SYM];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN REWRITE_TAC[ETA_AX] THEN
      MATCH_MP_TAC CONTINUOUS_ON_INV THEN
      REWRITE_TAC[CONTINUOUS_ON_LIFT_NORM; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `x:real^2` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `norm(x:real^2) = q` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `~(q = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_DIV_REFL; VECTOR_MUL_LID]];
    MP_TAC(ISPECL [`vec 0:real^2`; `r:real`; `&1`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
    REWRITE_TAC[DIMINDEX_2] THEN CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF; IN_CBALL_0; IN_ELIM_THM;
                VECTOR_SUB_RZERO] THEN
    EXISTS_TAC `q % basis 1:real^2` THEN
    SUBGOAL_THEN `norm(q % basis 1:real^2) = q` ASSUME_TAC THENL
     [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `q % basis 1:real^2`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Points far from the origin are outside a bounded planar set.              *)

let MOI_S3L8_OUTSIDE_FAR = prove
 (`!(s:real^2->bool) r z. s SUBSET ball(vec 0,r) /\ r <= norm z ==> z IN outside s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[outside; IN_ELIM_THM] THEN CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(s:real^2->bool) SUBSET ball(vec 0,r)` THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN DISCH_THEN(MP_TAC o SPEC `z:real^2`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  SUBGOAL_THEN `(:real^2) DIFF ball(vec 0,r) SUBSET
                connected_component ((:real^2) DIFF s) z` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; IN_BALL_0] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPLEMENT_BOUNDED_CONVEX THEN
      REWRITE_TAC[BOUNDED_BALL; CONVEX_BALL; DIMINDEX_2; LE_REFL];
      UNDISCH_TAC `(s:real^2->bool) SUBSET ball(vec 0,r)` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(INST_TYPE [`:2`,`:N`] NOT_BOUNDED_UNIV) THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(:real^2) = ((:real^2) DIFF ball(vec 0,r)) UNION ball(vec 0,r)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_UNION; BOUNDED_BALL] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `connected_component ((:real^2) DIFF s) z` THEN ASM_REWRITE_TAC[]);;

(* The planar lemma.                                                         *)

let MOI_S3L8_PLANAR = prove
 (`!(e:real^N->bool) rim p dj J.
     pseudo_cell e rim p /\ J SUBSET e DIFF rim /\
     dj SUBSET e /\ disk_with_boundary dj J
     ==> dj SUBSET e DIFF rim /\ open_in (subtopology euclidean e) (dj DIFF J)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC))) THEN
  REWRITE_TAC[disk_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `f':real^N->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  REWRITE_TAC[pseudo_cell] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^N->real^2` (X_CHOOSE_THEN `phi':real^2->real^N`
    ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    concl th = `homeomorphism (e DIFF rim,ball(vec 0:real^2,&1))
                  (phi:real^N->real^2,phi')`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    concl th = `homeomorphism (cball(vec 0:real^2,&1),dj) (f:real^2->real^N,f')`)) THEN
  (* basic facts *)
  SUBGOAL_THEN `compact (rim:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (dj:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^N) (cball(vec 0,&1)) = dj` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean e) (e DIFF rim:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) (ball(vec 0,&1)) = dj DIFF J` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^2->real^N) (sphere(vec 0,&1)) = J`)) THEN
    SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^2->real^N) (cball(vec 0,&1)) = dj`)) THEN
    REWRITE_TAC[GSYM CBALL_DIFF_SPHERE] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC(SET_RULE `(!x y. x IN s /\ y IN s /\ (f:real^2->real^N) x = f y ==> x = y) /\
                           t SUBSET s
                           ==> IMAGE f s DIFF IMAGE f t = IMAGE f (s DIFF t)`) THEN
    REWRITE_TAC[SPHERE_SUBSET_CBALL] THEN
    MESON_TAC[ASSUME `!x. x IN cball(vec 0:real^2,&1) ==> (f':real^N->real^2) (f x) = x`];
    ALL_TAC] THEN
  (* the Jordan curve J' = phi(J) in the chart *)
  SUBGOAL_THEN `IMAGE (phi:real^N->real^2) J SUBSET ball(vec 0,&1) /\
                IMAGE (phi':real^2->real^N) (IMAGE phi J) = J` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(J:real^N->bool) SUBSET e DIFF rim` THEN
      UNDISCH_TAC `IMAGE (phi:real^N->real^2) (e DIFF rim) = ball(vec 0,&1)` THEN SET_TAC[];
      REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (\x:real^N. x) J` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[o_THM] THEN
        UNDISCH_TAC `(J:real^N->bool) SUBSET e DIFF rim` THEN
        REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
        REWRITE_TAC[IMAGE_ID]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (phi:real^N->real^2) J homeomorphic sphere(vec 0:real^2,&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN EXISTS_TAC `J:real^N->bool` THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`phi:real^N->real^2`; `phi':real^2->real^N`] THEN
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`e DIFF rim:real^N->bool`; `ball(vec 0:real^2,&1)`] THEN
      ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`f:real^2->real^N`; `f':real^N->real^2`] THEN
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`cball(vec 0:real^2,&1)`; `dj:real^N->bool`] THEN
      ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL] THEN
      SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^2->real^N) (sphere(vec 0,&1)) = J`)) THEN
      SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^2->real^N) (cball(vec 0,&1)) = dj`)) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[SPHERE_SUBSET_CBALL]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (phi:real^N->real^2) J` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `inside(IMAGE (phi:real^N->real^2) J) SUBSET ball(vec 0,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN ASM_REWRITE_TAC[CONVEX_BALL]; ALL_TAC] THEN
  ABBREV_TAC `K0 = IMAGE (phi:real^N->real^2) J UNION inside(IMAGE phi J)` THEN
  SUBGOAL_THEN `compact (K0:real^2->bool) /\ K0 SUBSET ball(vec 0,&1) /\
                (:real^2) DIFF K0 = outside(IMAGE (phi:real^N->real^2) J)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K0" THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
       [REWRITE_TAC[BOUNDED_UNION] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
        ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE];
        SUBGOAL_THEN `IMAGE (phi:real^N->real^2) J UNION inside(IMAGE phi J) =
                      (:real^2) DIFF outside(IMAGE phi J)` SUBST1_TAC THENL
         [UNDISCH_TAC `inside(IMAGE (phi:real^N->real^2) J) INTER outside(IMAGE phi J) = {}` THEN
          UNDISCH_TAC `inside(IMAGE (phi:real^N->real^2) J) UNION outside(IMAGE phi J) =
                       (:real^2) DIFF IMAGE phi J` THEN
          SET_TAC[];
          REWRITE_TAC[GSYM OPEN_CLOSED] THEN ASM_REWRITE_TAC[]]];
      UNDISCH_TAC `inside(IMAGE (phi:real^N->real^2) J) SUBSET ball(vec 0,&1)` THEN
      UNDISCH_TAC `IMAGE (phi:real^N->real^2) J SUBSET ball(vec 0,&1)` THEN SET_TAC[];
      UNDISCH_TAC `inside(IMAGE (phi:real^N->real^2) J) INTER outside(IMAGE phi J) = {}` THEN
      UNDISCH_TAC `inside(IMAGE (phi:real^N->real^2) J) UNION outside(IMAGE phi J) =
                   (:real^2) DIFF IMAGE phi J` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (ball(vec 0:real^2,&1) DIFF K0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L8_BALL_MINUS_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the inside of J, pulled back to e *)
  ABBREV_TAC `Ins = IMAGE (phi':real^2->real^N) (inside(IMAGE phi (J:real^N->bool)))` THEN
  SUBGOAL_THEN `!y. y IN ball(vec 0:real^2,&1) ==> (phi':real^2->real^N) y IN e DIFF rim`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (phi':real^2->real^N) (ball(vec 0,&1)) = e DIFF rim` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(Ins:real^N->bool) SUBSET e DIFF rim /\ DISJOINT Ins (J:real^N->bool) /\
    IMAGE (phi':real^2->real^N) K0 = Ins UNION J /\ compact (Ins UNION J) /\
    open_in (subtopology euclidean e) Ins`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Ins" THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `inside(IMAGE (phi:real^N->real^2) J) SUBSET ball(vec 0,&1)` THEN
      UNDISCH_TAC `!y. y IN ball(vec 0:real^2,&1) ==> (phi':real^2->real^N) y IN e DIFF rim` THEN
      SET_TAC[];
      REWRITE_TAC[DISJOINT] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_INTER; IN_IMAGE; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^2) IN ball(vec 0,&1)` ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^2) IN inside(IMAGE (phi:real^N->real^2) J)` THEN
        UNDISCH_TAC `inside(IMAGE (phi:real^N->real^2) J) SUBSET ball(vec 0,&1)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(phi:real^N->real^2) x = y` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^2) IN inside(IMAGE (phi:real^N->real^2) J)` THEN
      UNDISCH_TAC `inside(IMAGE (phi:real^N->real^2) J) UNION outside(IMAGE phi J) =
                   (:real^2) DIFF IMAGE phi J` THEN
      UNDISCH_TAC `(phi:real^N->real^2) x = y` THEN
      UNDISCH_TAC `(x:real^N) IN J` THEN SET_TAC[];
      EXPAND_TAC "K0" THEN REWRITE_TAC[IMAGE_UNION] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `IMAGE (phi':real^2->real^N) (inside(IMAGE phi J)) UNION J =
                    IMAGE phi' K0` SUBST1_TAC THENL
       [EXPAND_TAC "K0" THEN REWRITE_TAC[IMAGE_UNION] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `e DIFF rim:real^N->bool` THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      SUBGOAL_THEN `IMAGE (phi':real^2->real^N) (inside(IMAGE phi J)) =
                    {x | x IN e DIFF rim /\ (phi:real^N->real^2) x IN inside(IMAGE phi J)}`
      SUBST1_TAC THENL
       [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
        REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
         [DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
          SUBGOAL_THEN `(y:real^2) IN ball(vec 0,&1)` ASSUME_TAC THENL
           [UNDISCH_TAC `(y:real^2) IN inside(IMAGE (phi:real^N->real^2) J)` THEN
            UNDISCH_TAC `inside(IMAGE (phi:real^N->real^2) J) SUBSET ball(vec 0,&1)` THEN
            SET_TAC[];
            ALL_TAC] THEN
          ASM_SIMP_TAC[];
          STRIP_TAC THEN EXISTS_TAC `(phi:real^N->real^2) x` THEN ASM_SIMP_TAC[]];
        MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the open disk G = dj DIFF J *)
  SUBGOAL_THEN `connected (dj DIFF J:real^N->bool) /\ dj DIFF J SUBSET e DIFF J`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^2->real^N) (ball(vec 0,&1)) = dj DIFF J`)) THEN
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_BALL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      UNDISCH_TAC `(dj:real^N->bool) SUBSET e` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (e DIFF J)) (Ins:real^N->bool) /\
                closed_in (subtopology euclidean (e DIFF J)) Ins` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `e:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(Ins:real^N->bool) SUBSET e DIFF rim` THEN
      UNDISCH_TAC `DISJOINT (Ins:real^N->bool) J` THEN SET_TAC[];
      SUBGOAL_THEN `(Ins:real^N->bool) = (e DIFF J) INTER (Ins UNION J)` SUBST1_TAC THENL
       [UNDISCH_TAC `(Ins:real^N->bool) SUBSET e DIFF rim` THEN
        UNDISCH_TAC `DISJOINT (Ins:real^N->bool) J` THEN SET_TAC[];
        MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN e DIFF rim /\ y IN e DIFF rim /\
                      (phi:real^N->real^2) x = phi y ==> x = y` ASSUME_TAC THENL
   [MESON_TAC[ASSUME `!x. x IN e DIFF rim ==> (phi':real^2->real^N) (phi x) = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y. x IN cball(vec 0,&1) /\ y IN cball(vec 0,&1) /\
                      (f:real^2->real^N) x = f y ==> x = y` ASSUME_TAC THENL
   [MESON_TAC[ASSUME `!x. x IN cball(vec 0:real^2,&1) ==> (f':real^N->real^2) (f x) = x`];
    ALL_TAC] THEN
  ASM_CASES_TAC `(dj DIFF J) INTER (Ins:real^N->bool) = {}` THENL
   [ALL_TAC;
    (* G lies inside J *)
    SUBGOAL_THEN `dj DIFF J SUBSET (Ins:real^N->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN EXISTS_TAC `e DIFF J:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `dj DIFF J SUBSET (Ins:real^N->bool)` THEN
      UNDISCH_TAC `(Ins:real^N->bool) SUBSET e DIFF rim` THEN
      UNDISCH_TAC `(J:real^N->bool) SUBSET e DIFF rim` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (f:real^2->real^N) (ball(vec 0,&1)) SUBSET e DIFF rim` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `dj DIFF J SUBSET (Ins:real^N->bool)` THEN
      UNDISCH_TAC `(Ins:real^N->bool) SUBSET e DIFF rim` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open (IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) (ball(vec 0,&1)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
          ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `e DIFF rim:real^N->bool` THEN
          ASM_REWRITE_TAC[]];
        REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!x y. x IN cball(vec 0:real^2,&1) /\ y IN cball(vec 0,&1) /\
                                    (f:real^2->real^N) x = f y ==> x = y`) (concl th))) THEN
        ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL] THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!x y. x IN e DIFF rim /\ y IN e DIFF rim /\
                                    (phi:real^N->real^2) x = phi y ==> x = y`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (f:real^2->real^N) (ball(vec 0,&1)) SUBSET e DIFF rim` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `dj DIFF J = {x | x IN e DIFF rim /\
                                   (phi:real^N->real^2) x IN
                                   IMAGE (phi o (f:real^2->real^N)) (ball(vec 0,&1))}`
    SUBST1_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^2->real^N) (ball(vec 0,&1)) = dj DIFF J`)) THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; o_THM] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `IMAGE (f:real^2->real^N) (ball(vec 0,&1)) SUBSET e DIFF rim` THEN
          ASM SET_TAC[];
          EXISTS_TAC `u:real^2` THEN ASM_REWRITE_TAC[]];
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC)) THEN
        EXISTS_TAC `u:real^2` THEN ASM_REWRITE_TAC[] THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!x y. x IN e DIFF rim /\ y IN e DIFF rim /\
                                    (phi:real^N->real^2) x = phi y ==> x = y`) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `IMAGE (f:real^2->real^N) (ball(vec 0,&1)) SUBSET e DIFF rim` THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `e DIFF rim:real^N->bool` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[]] THEN
  (* G outside J: impossible *)
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  ABBREV_TAC `U = {u | u IN ball(vec 0:real^2,&1) /\
                       (f:real^2->real^N) u IN (:real^N) DIFF rim}` THEN
  SUBGOAL_THEN `open (U:real^2->bool) /\ U SUBSET ball(vec 0,&1) /\
                IMAGE (f:real^2->real^N) U = (dj DIFF J) DIFF rim` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      REWRITE_TAC[OPEN_BALL; GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
      ASM_REWRITE_TAC[BALL_SUBSET_CBALL];
      SET_TAC[];
      UNDISCH_TAC `IMAGE (f:real^2->real^N) (ball(vec 0,&1)) = dj DIFF J` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(U:real^2->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `IMAGE (f:real^2->real^N) (closure(ball(vec 0,&1))) SUBSET rim` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
      SIMP_TAC[CLOSURE_BALL; REAL_LT_01; COMPACT_IMP_CLOSED;
               ASSUME `(f:real^2->real^N) continuous_on cball(vec 0,&1)`;
               ASSUME `compact (rim:real^N->bool)`] THEN
      UNDISCH_TAC `{u | u IN ball(vec 0:real^2,&1) /\
                        (f:real^2->real^N) u IN (:real^N) DIFF rim} = U` THEN
      SUBST1_TAC(ASSUME `U:real^2->bool = {}`) THEN SET_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[CLOSURE_BALL; REAL_LT_01] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^N) (sphere(vec 0,&1)) = J` THEN
    UNDISCH_TAC `(J:real^N->bool) SUBSET e DIFF rim` THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_SUBSET_CBALL) THEN
    SUBGOAL_THEN `~(sphere(vec 0:real^2,&1) = {})` MP_TAC THENL
     [REWRITE_TAC[SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. u IN U ==> u IN cball(vec 0:real^2,&1) /\
                               (f:real^2->real^N) u IN e DIFF rim /\
                               f u IN (dj DIFF J) DIFF rim` (LABEL_TAC "UF") THENL
   [X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^2->real^N) u IN (dj DIFF J) DIFF rim` ASSUME_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^2->real^N) U = (dj DIFF J) DIFF rim` THEN
      UNDISCH_TAC `(u:real^2) IN U` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(U:real^2->bool) SUBSET ball(vec 0,&1)` THEN
      UNDISCH_TAC `(u:real^2) IN U` THEN MP_TAC(ISPECL [`vec 0:real^2`; `&1`] BALL_SUBSET_CBALL) THEN
      SET_TAC[];
      UNDISCH_TAC `(f:real^2->real^N) u IN (dj DIFF J) DIFF rim` THEN
      UNDISCH_TAC `(dj:real^N->bool) SUBSET e` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the image of U in the chart is the annulus A = ball DIFF K0 *)
  SUBGOAL_THEN `IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) U SUBSET
                ball(vec 0,&1) DIFF K0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
    USE_THEN "UF" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(u:real^2) IN U`)) THEN
    REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (phi:real^N->real^2) (e DIFF rim) = ball(vec 0,&1)` THEN
      UNDISCH_TAC `(f:real^2->real^N) u IN e DIFF rim` THEN SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(f:real^2->real^N) u IN Ins UNION J` MP_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `IMAGE (phi':real^2->real^N) K0 = Ins UNION J`)) THEN
        REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `(phi:real^N->real^2) ((f:real^2->real^N) u)` THEN
        ASM_SIMP_TAC[];
        UNDISCH_TAC `(f:real^2->real^N) u IN (dj DIFF J) DIFF rim` THEN
        UNDISCH_TAC `(dj DIFF J) INTER (Ins:real^N->bool) = {}` THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) U)` ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "UF" (fun th -> REWRITE_TAC[SUBSET] THEN MESON_TAC[th]);
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `e DIFF rim:real^N->bool` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        USE_THEN "UF" (fun th -> MESON_TAC[th])];
      REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN STRIP_TAC THEN
      USE_THEN "UF" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(u:real^2) IN U`)) THEN
      USE_THEN "UF" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(v:real^2) IN U`)) THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x y. x IN cball(vec 0:real^2,&1) /\ y IN cball(vec 0,&1) /\
                                  (f:real^2->real^N) x = f y ==> x = y`) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x y. x IN e DIFF rim /\ y IN e DIFF rim /\
                                  (phi:real^N->real^2) x = phi y ==> x = y`) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) U =
                (ball(vec 0,&1) DIFF K0) INTER
                {y | y IN ball(vec 0,&1) /\ (phi':real^2->real^N) y IN dj}` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^2` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^2) IN ball(vec 0,&1) DIFF K0` ASSUME_TAC THENL
       [UNDISCH_TAC `IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) U SUBSET
                     ball(vec 0,&1) DIFF K0` THEN
        UNDISCH_TAC `(y:real^2) IN IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) U` THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(y:real^2) IN ball(vec 0,&1) DIFF K0` THEN SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^2) IN IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) U` THEN
      REWRITE_TAC[IN_IMAGE; o_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN
      USE_THEN "UF" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(u:real^2) IN U`)) THEN
      ASM_SIMP_TAC[] THEN
      UNDISCH_TAC `(f:real^2->real^N) u IN (dj DIFF J) DIFF rim` THEN SET_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `(phi':real^2->real^N) y IN (dj DIFF J) DIFF rim` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
         [DISCH_TAC THEN
          UNDISCH_TAC `(y:real^2) IN ball(vec 0,&1) DIFF K0` THEN REWRITE_TAC[IN_DIFF] THEN
          DISCH_THEN(MP_TAC o CONJUNCT2) THEN REWRITE_TAC[] THEN
          EXPAND_TAC "K0" THEN REWRITE_TAC[IN_UNION; IN_IMAGE] THEN DISJ1_TAC THEN
          EXISTS_TAC `(phi':real^2->real^N) y` THEN ASM_SIMP_TAC[];
          UNDISCH_TAC `!y. y IN ball(vec 0:real^2,&1) ==> (phi':real^2->real^N) y IN e DIFF rim` THEN
          DISCH_THEN(MP_TAC o SPEC `y:real^2`) THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
        SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^2->real^N) U = (dj DIFF J) DIFF rim`)) THEN
        REWRITE_TAC[IN_IMAGE; o_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `u:real^2` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `(phi':real^2->real^N) y = f (u:real^2)`)) THEN
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean (ball(vec 0:real^2,&1) DIFF K0))
                  (IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) U)` ASSUME_TAC THENL
   [SUBGOAL_THEN `closed_in (subtopology euclidean (ball(vec 0:real^2,&1)))
                    {y | y IN ball(vec 0,&1) /\ (phi':real^2->real^N) y IN dj}` MP_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_CLOSED_IN_PREIMAGE THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN
      DISCH_THEN(X_CHOOSE_THEN `c0:real^2->bool` STRIP_ASSUME_TAC)] THEN
    SUBST1_TAC(ASSUME `IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) U =
                       (ball(vec 0,&1) DIFF K0) INTER
                       {y | y IN ball(vec 0,&1) /\ (phi':real^2->real^N) y IN dj}`) THEN
    SUBST1_TAC(ASSUME `{y | y IN ball(vec 0:real^2,&1) /\ (phi':real^2->real^N) y IN dj} =
                       ball(vec 0,&1) INTER c0`) THEN
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `c0:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) U = ball(vec 0,&1) DIFF K0`
  ASSUME_TAC THENL
   [UNDISCH_TAC `connected (ball(vec 0:real^2,&1) DIFF K0)` THEN
    REWRITE_TAC[CONNECTED_CLOPEN] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) U`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_SUBSET THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC];
      REWRITE_TAC[IMAGE_EQ_EMPTY; ASSUME `~(U:real^2->bool = {})`]];
    ALL_TAC] THEN
  (* the rim lies in the open disk dj DIFF J *)
  SUBGOAL_THEN `IMAGE (phi':real^2->real^N) (ball(vec 0,&1) DIFF K0) = IMAGE (f:real^2->real^N) U`
  ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) U =
                          ball(vec 0,&1) DIFF K0`)) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
    X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    USE_THEN "UF" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(u:real^2) IN U`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(rim:real^N->bool) SUBSET dj DIFF J` ASSUME_TAC THENL
   [SUBGOAL_THEN `e DIFF rim = IMAGE (f:real^2->real^N) U UNION (Ins UNION J)` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `IMAGE (phi':real^2->real^N) (ball(vec 0,&1)) = e DIFF rim`)) THEN
      SUBST1_TAC(SYM(ASSUME `IMAGE (phi':real^2->real^N) (ball(vec 0,&1) DIFF K0) =
                             IMAGE (f:real^2->real^N) U`)) THEN
      SUBST1_TAC(SYM(ASSUME `IMAGE (phi':real^2->real^N) K0 = Ins UNION J`)) THEN
      REWRITE_TAC[GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
      UNDISCH_TAC `K0 SUBSET ball(vec 0:real^2,&1)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^N->bool) SUBSET dj UNION (Ins UNION J)` MP_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `closure(e DIFF rim:real^N->bool) = e`)) THEN
      SUBST1_TAC(ASSUME `e DIFF rim = IMAGE (f:real^2->real^N) U UNION (Ins UNION J)`) THEN
      ONCE_REWRITE_TAC[CLOSURE_UNION] THEN
      SUBGOAL_THEN `closure(Ins UNION J:real^N->bool) = Ins UNION J` SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> s UNION u SUBSET t UNION u`) THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      SUBST1_TAC(ASSUME `IMAGE (f:real^2->real^N) U = (dj DIFF J) DIFF rim`) THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(rim:real^N->bool) SUBSET e` THEN
    UNDISCH_TAC `(Ins:real^N->bool) SUBSET e DIFF rim` THEN
    UNDISCH_TAC `(J:real^N->bool) SUBSET e DIFF rim` THEN SET_TAC[];
    ALL_TAC] THEN
  (* Jordan in the open disk: the rim disconnects U *)
  SUBGOAL_THEN `IMAGE (f':real^N->real^2) rim SUBSET ball(vec 0,&1) /\
                U = ball(vec 0,&1) DIFF IMAGE (f':real^N->real^2) rim` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^N) IN IMAGE (f:real^2->real^N) (ball(vec 0,&1))` MP_TAC THENL
       [SUBST1_TAC(ASSUME `IMAGE (f:real^2->real^N) (ball(vec 0,&1)) = dj DIFF J`) THEN
        UNDISCH_TAC `(rim:real^N->bool) SUBSET dj DIFF J` THEN
        UNDISCH_TAC `(y:real^N) IN rim` THEN SET_TAC[];
        REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN
        ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL]];
      EXPAND_TAC "U" THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `u:real^2` THEN
      REWRITE_TAC[IN_ELIM_THM; IN_DIFF; IN_UNIV; IN_IMAGE] THEN
      ASM_CASES_TAC `(u:real^2) IN ball(vec 0,&1)` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[TAUT `(~p <=> ~q) <=> (p <=> q)`] THEN EQ_TAC THENL
       [DISCH_TAC THEN EXISTS_TAC `(f:real^2->real^N) u` THEN ASM_REWRITE_TAC[] THEN
        CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN
        ASM_SIMP_TAC[REWRITE_RULE[SUBSET] BALL_SUBSET_CBALL];
        DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(y:real^N) IN dj` (fun th -> ASM_SIMP_TAC[th]) THEN
        UNDISCH_TAC `(rim:real^N->bool) SUBSET dj DIFF J` THEN
        UNDISCH_TAC `(y:real^N) IN rim` THEN SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f':real^N->real^2) rim homeomorphic sphere(vec 0:real^2,&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN EXISTS_TAC `rim:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f':real^N->real^2`; `f:real^2->real^N`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`dj:real^N->bool`; `cball(vec 0:real^2,&1)`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(rim:real^N->bool) SUBSET dj DIFF J` THEN SET_TAC[];
      UNDISCH_TAC `IMAGE (f':real^N->real^2) rim SUBSET ball(vec 0,&1)` THEN
      MP_TAC(ISPECL [`vec 0:real^2`; `&1`] BALL_SUBSET_CBALL) THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (f':real^N->real^2) rim` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `IMAGE (f':real^N->real^2) rim` MOI_S3L8_COMPACT_IN_BALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `dj:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(rim:real^N->bool) SUBSET dj DIFF J` THEN SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `connected (U:real^2->bool)` MP_TAC THENL
   [SUBGOAL_THEN `U = IMAGE ((f':real^N->real^2) o (phi':real^2->real^N))
                            (ball(vec 0,&1) DIFF K0)` SUBST1_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `IMAGE ((phi:real^N->real^2) o (f:real^2->real^N)) U =
                            ball(vec 0,&1) DIFF K0`)) THEN
      REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (\u:real^2. u) U` THEN CONJ_TAC THENL
       [REWRITE_TAC[IMAGE_ID];
        MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
        REWRITE_TAC[o_THM] THEN
        USE_THEN "UF" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(u:real^2) IN U`)) THEN
        ASM_SIMP_TAC[]];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^2,&1)` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `dj:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        SUBST1_TAC(ASSUME `IMAGE (phi':real^2->real^N) (ball(vec 0,&1) DIFF K0) =
                           IMAGE (f:real^2->real^N) U`) THEN
        SUBST1_TAC(ASSUME `IMAGE (f:real^2->real^N) U = (dj DIFF J) DIFF rim`) THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBST1_TAC(ASSUME `U = ball(vec 0:real^2,&1) DIFF IMAGE (f':real^N->real^2) rim`) THEN
  REWRITE_TAC[connected] THEN
  MAP_EVERY EXISTS_TAC [`inside(IMAGE (f':real^N->real^2) rim)`;
                        `outside(IMAGE (f':real^N->real^2) rim)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `inside(IMAGE (f':real^N->real^2) rim) UNION outside(IMAGE f' rim) =
                 (:real^2) DIFF IMAGE f' rim` THEN SET_TAC[];
    UNDISCH_TAC `inside(IMAGE (f':real^N->real^2) rim) INTER outside(IMAGE f' rim) = {}` THEN
    SET_TAC[];
    MP_TAC(ISPECL [`IMAGE (f':real^N->real^2) rim`; `ball(vec 0:real^2,&1)`]
                  INSIDE_SUBSET_CONVEX) THEN
    ASM_REWRITE_TAC[CONVEX_BALL] THEN
    UNDISCH_TAC `~(inside(IMAGE (f':real^N->real^2) rim) = {})` THEN
    UNDISCH_TAC `inside(IMAGE (f':real^N->real^2) rim) UNION outside(IMAGE f' rim) =
                 (:real^2) DIFF IMAGE f' rim` THEN
    SET_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF] THEN
    EXISTS_TAC `((r1 + &1) / &2) % basis 1:real^2` THEN
    SUBGOAL_THEN `norm(((r1 + &1) / &2) % basis 1:real^2) = (r1 + &1) / &2` ASSUME_TAC THENL
     [SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_2; ARITH; REAL_MUL_RID] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3L8_OUTSIDE_FAR THEN EXISTS_TAC `r1:real` THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      DISCH_TAC THEN
      UNDISCH_TAC `IMAGE (f':real^N->real^2) rim SUBSET ball(vec 0,r1)` THEN
      REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `((r1 + &1) / &2) % basis 1:real^2`) THEN
      ASM_REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: two disks with a common boundary circle and disjoint             *)
(* interiors form a topological 2-sphere.  The boundary identification is  *)
(* extended over the disk by the Schoenflies theorem (JORDAN_SCHOENFLIES), *)
(* and the two disks are pasted on the closed hemispheres of the unit      *)
(* sphere, projected vertically onto the unit disk.                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L8_CIRCLE_EXTEND = prove
 (`!(f:real^2->real^2) f'.
     homeomorphism (sphere(vec 0,&1),sphere(vec 0,&1)) (f,f')
     ==> ?k k'. homeomorphism (cball(vec 0,&1),cball(vec 0,&1)) (k,k') /\
                !x. x IN sphere(vec 0,&1) ==> k x = f x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`circlepath(vec 0:real^2,&1)`; `circlepath(vec 0:real^2,&1)`;
                 `f:real^2->real^2`; `f':real^2->real^2`] JORDAN_SCHOENFLIES) THEN
  ASM_SIMP_TAC[SIMPLE_PATH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH; REAL_POS; REAL_OF_NUM_EQ;
               ARITH_EQ; INSIDE_SPHERE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->real^2` (X_CHOOSE_THEN `k':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:real^2->real^2`; `k':real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
  MAP_EVERY EXISTS_TAC [`(:real^2)`; `(:real^2)`] THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; GSYM BALL_UNION_SPHERE; IMAGE_UNION]);;

(* Vertical projection of the closed hemispheres onto the unit disk.        *)

let MOI_S3L8_HEMI_CBALL = prove
 (`!x:real^3. x IN sphere(vec 0,&1) ==> (vector[x$1; x$2]:real^2) IN cball(vec 0,&1)`,
  REWRITE_TAC[IN_SPHERE_0; IN_CBALL_0; NORM_EQ_1; NORM_LE_SQUARE; DOT_2; DOT_3;
              VECTOR_2] THEN
  GEN_TAC THEN MP_TAC(SPEC `(x:real^3)$3` REAL_LE_SQUARE) THEN REAL_ARITH_TAC);;

let MOI_S3L8_HEMI_RIM = prove
 (`!x:real^3. x IN sphere(vec 0,&1)
              ==> ((vector[x$1; x$2]:real^2) IN sphere(vec 0,&1) <=> x$3 = &0)`,
  REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_2; DOT_3; VECTOR_2] THEN
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3)$1 * x$1 + x$2 * x$2 = &1 <=> x$3 * x$3 = &0` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; REWRITE_TAC[REAL_ENTIRE]]);;

let MOI_S3L8_HEMI_INJ = prove
 (`!x y:real^3. x IN sphere(vec 0,&1) /\ y IN sphere(vec 0,&1) /\
                ((&0 <= x$3 /\ &0 <= y$3) \/ (x$3 <= &0 /\ y$3 <= &0)) /\
                (vector[x$1; x$2]:real^2) = vector[y$1; y$2]
                ==> x = y`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_3; CART_EQ; DIMINDEX_2; DIMINDEX_3;
              FORALL_2; FORALL_3; VECTOR_2] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `((x:real^3)$3 - (y:real^3)$3) * (x$3 + y$3) = &0` MP_TAC THENL
   [UNDISCH_TAC `(x:real^3)$1 * x$1 + x$2 * x$2 + x$3 * x$3 = &1` THEN
    UNDISCH_TAC `(y:real^3)$1 * y$1 + y$2 * y$2 + y$3 * y$3 = &1` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC]);;

let MOI_S3L8_HEMI_LIFT = prove
 (`!u:real^2. u IN cball(vec 0,&1)
              ==> (?x:real^3. x IN sphere(vec 0,&1) /\ &0 <= x$3 /\
                              vector[x$1; x$2] = u) /\
                  (?x:real^3. x IN sphere(vec 0,&1) /\ x$3 <= &0 /\
                              vector[x$1; x$2] = u)`,
  GEN_TAC THEN REWRITE_TAC[IN_CBALL_0; NORM_LE_SQUARE; DOT_2] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 <= &1 - ((u:real^2)$1 * u$1 + u$2 * u$2)` ASSUME_TAC THENL
   [UNDISCH_TAC `(u:real^2)$1 * u$1 + u$2 * u$2 <= &1 pow 2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `&1 - ((u:real^2)$1 * u$1 + u$2 * u$2)` SQRT_POW_2) THEN
  MP_TAC(SPEC `&1 - ((u:real^2)$1 * u$1 + u$2 * u$2)` SQRT_POS_LE) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN CONJ_TAC THENL
   [EXISTS_TAC `vector[(u:real^2)$1; u$2; sqrt(&1 - (u$1 * u$1 + u$2 * u$2))]:real^3`;
    EXISTS_TAC `vector[(u:real^2)$1; u$2; --sqrt(&1 - (u$1 * u$1 + u$2 * u$2))]:real^3`] THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_EQ_1; DOT_3; VECTOR_3; CART_EQ; DIMINDEX_2; FORALL_2;
              VECTOR_2] THEN
  UNDISCH_TAC `sqrt(&1 - ((u:real^2)$1 * u$1 + u$2 * u$2)) pow 2 =
               &1 - (u$1 * u$1 + u$2 * u$2)` THEN
  UNDISCH_TAC `&0 <= sqrt(&1 - ((u:real^2)$1 * u$1 + u$2 * u$2))` THEN
  REAL_ARITH_TAC);;

(* The gluing.                                                               *)

let MOI_S3L8_DISKS_SPHERE = prove
 (`!(d1:real^N->bool) d2 j.
     disk_with_boundary d1 j /\ disk_with_boundary d2 j /\ d1 INTER d2 = j
     ==> (d1 UNION d2) homeomorphic sphere(vec 0:real^3,&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[disk_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `a:real^2->real^N` (X_CHOOSE_THEN `a':real^N->real^2`
      STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `b:real^2->real^N` (X_CHOOSE_THEN `b':real^N->real^2`
        STRIP_ASSUME_TAC))
      ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (a:real^2->real^N) (sphere(vec 0,&1)) =
                IMAGE (b:real^2->real^N) (sphere(vec 0,&1))` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^2,&1) SUBSET cball(vec 0,&1)` ASSUME_TAC THENL
   [REWRITE_TAC[SPHERE_SUBSET_CBALL]; ALL_TAC] THEN
  (* the boundary identification b' o a on the circle *)
  SUBGOAL_THEN `homeomorphism (sphere(vec 0:real^2,&1),sphere(vec 0,&1))
                  ((b':real^N->real^2) o (a:real^2->real^N),
                   (a':real^N->real^2) o (b:real^2->real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (a:real^2->real^N) (sphere(vec 0,&1))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`cball(vec 0:real^2,&1)`; `d1:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `homeomorphism (cball(vec 0:real^2,&1),d1) (a:real^2->real^N,a')` THEN
      REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN ASM SET_TAC[];
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`cball(vec 0:real^2,&1)`; `d2:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `homeomorphism (cball(vec 0:real^2,&1),d2) (b:real^2->real^N,b')` THEN
      REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `k:real^2->real^2` (X_CHOOSE_THEN `k':real^2->real^2`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_S3L8_CIRCLE_EXTEND) THEN
  SUBGOAL_THEN `homeomorphism (cball(vec 0:real^2,&1),d2)
                  ((b:real^2->real^N) o (k:real^2->real^2),
                   (k':real^2->real^2) o (b':real^N->real^2))` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^2. u IN sphere(vec 0,&1) ==> ((b:real^2->real^N) o k) u = a u`
  (LABEL_TAC "agree") THENL
   [X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN ASM_SIMP_TAC[o_THM] THEN
    UNDISCH_TAC `homeomorphism (cball(vec 0:real^2,&1),d2) (b:real^2->real^N,b')` THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(u:real^2) IN sphere(vec 0,&1)` THEN
    UNDISCH_TAC `IMAGE (a:real^2->real^N) (sphere(vec 0,&1)) =
                 IMAGE (b:real^2->real^N) (sphere(vec 0,&1))` THEN
    UNDISCH_TAC `IMAGE (b:real^2->real^N) (cball(vec 0,&1)) = d2` THEN
    UNDISCH_TAC `sphere(vec 0:real^2,&1) SUBSET cball(vec 0,&1)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* inverse and boundary facts *)
  SUBGOAL_THEN
   `(!u. u IN cball(vec 0:real^2,&1) ==> (a':real^N->real^2) ((a:real^2->real^N) u) = u) /\
    (!u. u IN cball(vec 0:real^2,&1)
         ==> ((k':real^2->real^2) o (b':real^N->real^2))
             (((b:real^2->real^N) o (k:real^2->real^2)) u) = u) /\
    IMAGE (a:real^2->real^N) (cball(vec 0,&1)) = d1 /\
    IMAGE ((b:real^2->real^N) o (k:real^2->real^2)) (cball(vec 0,&1)) = d2 /\
    (a:real^2->real^N) continuous_on cball(vec 0,&1) /\
    ((b:real^2->real^N) o (k:real^2->real^2)) continuous_on cball(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (cball(vec 0:real^2,&1),d1) (a:real^2->real^N,a')` THEN
    UNDISCH_TAC `homeomorphism (cball(vec 0:real^2,&1),d2)
                   ((b:real^2->real^N) o (k:real^2->real^2),
                    (k':real^2->real^2) o (b':real^N->real^2))` THEN
    REWRITE_TAC[homeomorphism] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((b:real^2->real^N) o (k:real^2->real^2)) (sphere(vec 0,&1)) = j`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE (k:real^2->real^2) (sphere(vec 0,&1)) = sphere(vec 0,&1)`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE ((b':real^N->real^2) o (a:real^2->real^N)) (sphere(vec 0,&1))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[];
        UNDISCH_TAC `homeomorphism (sphere(vec 0:real^2,&1),sphere(vec 0,&1))
                       ((b':real^N->real^2) o (a:real^2->real^N),
                        (a':real^N->real^2) o (b:real^2->real^N))` THEN
        SIMP_TAC[homeomorphism]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!u. u IN cball(vec 0:real^2,&1) /\ (a:real^2->real^N) u IN j
         ==> u IN sphere(vec 0,&1)) /\
    (!u. u IN cball(vec 0:real^2,&1) /\ ((b:real^2->real^N) o (k:real^2->real^2)) u IN j
         ==> u IN sphere(vec 0,&1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `u:real^2` THEN STRIP_TAC THENL
     [UNDISCH_TAC `(a:real^2->real^N) u IN j` THEN
      SUBST1_TAC(ASSUME `j = IMAGE (a:real^2->real^N) (sphere(vec 0,&1))`) THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `u':real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `u:real^2 = u'` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[SUBSET];
      UNDISCH_TAC `((b:real^2->real^N) o (k:real^2->real^2)) u IN j` THEN
      SUBST1_TAC(SYM(ASSUME `IMAGE ((b:real^2->real^N) o (k:real^2->real^2))
                                (sphere(vec 0,&1)) = j`)) THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `u':real^2` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `u:real^2 = u'` (fun th -> ASM_REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^3. vector[x$1; x$2]:real^2) continuous_on (:real^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
    REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT];
    ALL_TAC] THEN
  ABBREV_TAC `ff = \x:real^3. if &0 <= x$3 then (a:real^2->real^N) (vector[x$1; x$2])
                             else ((b:real^2->real^N) o (k:real^2->real^2))
                                  (vector[x$1; x$2])` THEN
  SUBGOAL_THEN
   `(!x:real^3. x IN sphere(vec 0,&1) /\ &0 <= x$3
                ==> (ff:real^3->real^N) x = (a:real^2->real^N) (vector[x$1; x$2])) /\
    (!x:real^3. x IN sphere(vec 0,&1) /\ x$3 <= &0
                ==> (ff:real^3->real^N) x =
                    ((b:real^2->real^N) o (k:real^2->real^2)) (vector[x$1; x$2]))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN EXPAND_TAC "ff" THEN
    REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY ASM_REAL_ARITH_TAC THEN
    CONV_TAC SYM_CONV THEN USE_THEN "agree" MATCH_MP_TAC THEN
    MP_TAC(SPEC `x:real^3` MOI_S3L8_HEMI_RIM) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* continuity *)
  SUBGOAL_THEN `(ff:real^3->real^N) continuous_on sphere(vec 0,&1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `sphere(vec 0:real^3,&1) =
                  {x | x IN sphere(vec 0,&1) /\ &0 <= x$3} UNION
                  {x | x IN sphere(vec 0,&1) /\ x$3 <= &0}` SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
      ASM_CASES_TAC `(x:real^3) IN sphere(vec 0,&1)` THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    EXPAND_TAC "ff" THEN MATCH_MP_TAC CONTINUOUS_ON_CASES THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SET_RULE `{x:real^3 | x IN s /\ P x} = s INTER {x | P x}`] THEN
      MATCH_MP_TAC CLOSED_INTER THEN
      REWRITE_TAC[CLOSED_SPHERE; GSYM real_ge; CLOSED_HALFSPACE_COMPONENT_GE];
      REWRITE_TAC[SET_RULE `{x:real^3 | x IN s /\ P x} = s INTER {x | P x}`] THEN
      MATCH_MP_TAC CLOSED_INTER THEN
      REWRITE_TAC[CLOSED_SPHERE; CLOSED_HALFSPACE_COMPONENT_LE];
      SUBGOAL_THEN `(\x:real^3. (a:real^2->real^N) (vector[x$1; x$2])) =
                    a o (\x:real^3. vector[x$1; x$2]:real^2)` SUBST1_TAC THENL
       [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        MESON_TAC[MOI_S3L8_HEMI_CBALL]];
      SUBGOAL_THEN `(\x:real^3. ((b:real^2->real^N) o (k:real^2->real^2))
                                  (vector[x$1; x$2])) =
                    (b o k) o (\x:real^3. vector[x$1; x$2]:real^2)` SUBST1_TAC THENL
       [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        MESON_TAC[MOI_S3L8_HEMI_CBALL]];
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN USE_THEN "agree" MATCH_MP_TAC THEN
      MP_TAC(SPEC `x:real^3` MOI_S3L8_HEMI_RIM) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* image *)
  SUBGOAL_THEN `IMAGE (ff:real^3->real^N) (sphere(vec 0,&1)) = d1 UNION d2` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[IN_IMAGE; IN_UNION] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM SUBST1_TAC THEN
      MP_TAC(SPEC `x:real^3` MOI_S3L8_HEMI_CBALL) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_CASES_TAC `&0 <= (x:real^3)$3` THENL
       [DISJ1_TAC THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
        DISJ2_TAC THEN
        SUBGOAL_THEN `(x:real^3)$3 <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
      STRIP_TAC THENL
       [SUBGOAL_THEN `?u:real^2. u IN cball(vec 0,&1) /\ y = (a:real^2->real^N) u`
        STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(SPEC `u:real^2` MOI_S3L8_HEMI_LIFT) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC o CONJUNCT1) THEN
        EXISTS_TAC `x:real^3` THEN ASM_SIMP_TAC[];
        SUBGOAL_THEN `?u:real^2. u IN cball(vec 0,&1) /\
                                 y = ((b:real^2->real^N) o (k:real^2->real^2)) u`
        STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MP_TAC(SPEC `u:real^2` MOI_S3L8_HEMI_LIFT) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC o CONJUNCT2) THEN
        EXISTS_TAC `x:real^3` THEN ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  (* injectivity *)
  SUBGOAL_THEN `!x y:real^3. x IN sphere(vec 0,&1) /\ y IN sphere(vec 0,&1) /\
                             (ff:real^3->real^N) x = ff y ==> x = y` ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    MP_TAC(SPEC `x:real^3` MOI_S3L8_HEMI_CBALL) THEN
    MP_TAC(SPEC `y:real^3` MOI_S3L8_HEMI_CBALL) THEN
    MP_TAC(SPEC `x:real^3` MOI_S3L8_HEMI_RIM) THEN
    MP_TAC(SPEC `y:real^3` MOI_S3L8_HEMI_RIM) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(ff:real^3->real^N) x IN j ==> (x:real^3)$3 = &0` ASSUME_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `&0 <= (x:real^3)$3` THENL
       [SUBGOAL_THEN `(vector[(x:real^3)$1; x$2]:real^2) IN sphere(vec 0,&1)` MP_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (term_match [] `!u. u IN cball(vec 0:real^2,&1) /\
                                    (a:real^2->real^N) u IN j ==> u IN sphere(vec 0,&1)`)
              (concl th))) THEN
          ASM_MESON_TAC[];
          ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `(vector[(x:real^3)$1; x$2]:real^2) IN sphere(vec 0,&1)` MP_TAC THENL
         [SUBGOAL_THEN `(x:real^3)$3 <= &0` ASSUME_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_MESON_TAC[];
          ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(ff:real^3->real^N) y IN j ==> (y:real^3)$3 = &0` ASSUME_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `&0 <= (y:real^3)$3` THENL
       [SUBGOAL_THEN `(vector[(y:real^3)$1; y$2]:real^2) IN sphere(vec 0,&1)` MP_TAC THENL
         [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
        SUBGOAL_THEN `(vector[(y:real^3)$1; y$2]:real^2) IN sphere(vec 0,&1)` MP_TAC THENL
         [SUBGOAL_THEN `(y:real^3)$3 <= &0` ASSUME_TAC THENL
           [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          ASM_MESON_TAC[];
          ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(&0 <= (x:real^3)$3 /\ &0 <= (y:real^3)$3) \/ (x$3 <= &0 /\ y$3 <= &0)`
    ASSUME_TAC THENL
     [ASM_CASES_TAC `&0 <= (x:real^3)$3` THEN ASM_CASES_TAC `&0 <= (y:real^3)$3` THEN
      ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `(ff:real^3->real^N) y IN j` MP_TAC THENL
         [SUBGOAL_THEN `(y:real^3)$3 <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `(ff:real^3->real^N) y IN d1 INTER d2` MP_TAC THENL
           [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
             [UNDISCH_TAC `(ff:real^3->real^N) x = ff y` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
              ASM_SIMP_TAC[] THEN ASM SET_TAC[];
              ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
            ASM_REWRITE_TAC[]];
          ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
        SUBGOAL_THEN `(ff:real^3->real^N) x IN j` MP_TAC THENL
         [SUBGOAL_THEN `(x:real^3)$3 <= &0` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
          SUBGOAL_THEN `(ff:real^3->real^N) x IN d1 INTER d2` MP_TAC THENL
           [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
             [UNDISCH_TAC `(ff:real^3->real^N) x = ff y` THEN DISCH_THEN SUBST1_TAC THEN
              ASM_SIMP_TAC[] THEN ASM SET_TAC[];
              ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
            ASM_REWRITE_TAC[]];
          ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC];
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S3L8_HEMI_INJ THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THENL
     [SUBGOAL_THEN `(a:real^2->real^N) (vector[(x:real^3)$1; x$2]) =
                    a (vector[(y:real^3)$1; y$2])` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      SUBGOAL_THEN `((b:real^2->real^N) o (k:real^2->real^2)) (vector[(x:real^3)$1; x$2]) =
                    (b o k) (vector[(y:real^3)$1; y$2])` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  EXISTS_TAC `ff:real^3->real^N` THEN MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
  ASM_REWRITE_TAC[COMPACT_SPHERE]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: a good point.  Near a point P of a closed set E, suppose a       *)
(* ball around P minus E splits into two disjoint open sets W1, W2, E near  *)
(* P lies in the closure of W2, and E is locally a finite union of polytopes *)
(* of dimension at most 2 away from P.  Then some point y of E near P has a *)
(* small ball whose complement of E lies in the component Q of W1 at a     *)
(* given point and in W2.  Proof: Q has a frontier point x in E other than *)
(* P (the punctured ball is connected); near x triangulate the polytopes,  *)
(* remove the simplices of dimension at most 1 (still connected,           *)
(* CONNECTED_OPEN_DIFF_LOWDIM), find a frontier point y of Q in the        *)
(* relative interior of a triangle, and apply LOCAL_TRI there.             *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L8_COMPONENT_ABSORB = prove
 (`!(s:real^N->bool) a c.
     a IN s /\ connected c /\ c SUBSET s /\ ~(c INTER connected_component s a = {})
     ==> c SUBSET connected_component s a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[IN_COMPONENTS] THEN
  CONJ_TAC THENL [EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]]);;

let MOI_S3L8_CONNECTED_SPLIT = prove
 (`!(c:real^N->bool) u v.
     connected c /\ open u /\ open v /\ DISJOINT u v /\ c SUBSET u UNION v
     ==> c SUBSET u \/ c SUBSET v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `v:real^N->bool`] o
    REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `DISJOINT (u:real^N->bool) v` THEN
  UNDISCH_TAC `(c:real^N->bool) SUBSET u UNION v` THEN SET_TAC[]);;

let MOI_S3L8_GOOD_POINT = prove
 (`!(E:real^3->bool) W1 W2 P rho a.
     closed E /\ P IN E /\ &0 < rho /\
     open W1 /\ open W2 /\ DISJOINT W1 W2 /\
     ball(P,rho) DIFF E = W1 UNION W2 /\ a IN W1 /\
     E INTER ball(P,rho) SUBSET closure W2 /\
     (!x. x IN E INTER ball(P,rho) /\ ~(x = P)
          ==> ?c u. FINITE c /\ open u /\ x IN u /\ E INTER u SUBSET UNIONS c /\
                    !k. k IN c ==> polytope k /\ k SUBSET E /\ aff_dim k <= &2)
     ==> ?y r. y IN E INTER ball(P,rho) /\ &0 < r /\ ball(y,r) SUBSET ball(P,rho) /\
               ball(y,r) DIFF E SUBSET connected_component W1 a UNION W2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc")))))))))) THEN
  SUBGOAL_THEN `open (connected_component (W1:real^3->bool) a) /\
                connected (connected_component W1 a) /\
                (a:real^3) IN connected_component W1 a /\
                connected_component W1 a SUBSET W1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_CONNECTED_COMPONENT; CONNECTED_CONNECTED_COMPONENT;
                 CONNECTED_COMPONENT_SUBSET] THEN
    REWRITE_TAC[IN] THEN ASM_REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `Q = connected_component (W1:real^3->bool) a` THEN
  SUBGOAL_THEN `(W1:real^3->bool) SUBSET ball(P,rho) DIFF E /\ W2 SUBSET ball(P,rho) DIFF E`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `ball(P:real^3,rho) DIFF E = W1 UNION W2` THEN SET_TAC[]; ALL_TAC] THEN
  (* absorption into Q *)
  SUBGOAL_THEN `!c:real^3->bool. connected c /\ c SUBSET W1 /\ ~(c INTER Q = {})
                                 ==> c SUBSET Q` (LABEL_TAC "absorb") THENL
   [GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "Q" THEN
    MATCH_MP_TAC MOI_S3L8_COMPONENT_ABSORB THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(a:real^3) IN Q` THEN UNDISCH_TAC `(Q:real^3->bool) SUBSET W1` THEN SET_TAC[];
    ALL_TAC] THEN
  (* frontier points of Q in the ball lie in E *)
  SUBGOAL_THEN `!z:real^3. z IN ball(P,rho) /\ z IN closure Q /\ ~(z IN Q) ==> z IN E`
  (LABEL_TAC "fr") THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN W1 \/ z IN W2` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ball(P:real^3,rho) DIFF E = W1 UNION W2` THEN
      UNDISCH_TAC `(z:real^3) IN ball(P,rho)` THEN UNDISCH_TAC `~((z:real^3) IN E)` THEN
      SET_TAC[];
      FIRST_ASSUM(MP_TAC o SPEC `z:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
        check (fun th -> concl th = `open (W1:real^3->bool)`)) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ee:real` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `ball(z:real^3,ee) SUBSET Q` MP_TAC THENL
       [USE_THEN "absorb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[CONNECTED_BALL] THEN
        UNDISCH_TAC `(z:real^3) IN closure Q` THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
        DISCH_THEN(MP_TAC o SPEC `ee:real`) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
        EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `dist(q:real^3,z) < ee` THEN CONV_TAC NORM_ARITH;
        UNDISCH_TAC `~((z:real^3) IN Q)` THEN
        MP_TAC(ISPECL [`z:real^3`; `ee:real`] CENTRE_IN_BALL) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      UNDISCH_TAC `(z:real^3) IN closure Q` THEN
      MP_TAC(ISPECL [`W2:real^3->bool`; `Q:real^3->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(Q:real^3->bool) SUBSET W1` THEN
      UNDISCH_TAC `DISJOINT (W1:real^3->bool) W2` THEN
      UNDISCH_TAC `(z:real^3) IN W2` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(W2:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `E INTER ball(P:real^3,rho) SUBSET closure W2` THEN
    ASM_REWRITE_TAC[CLOSURE_EMPTY; SUBSET_EMPTY; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `P:real^3` THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    ALL_TAC] THEN
  (* a frontier point x of Q in E, other than P *)
  SUBGOAL_THEN `?x:real^3. x IN E INTER ball(P,rho) /\ ~(x = P) /\ x IN closure Q`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`P:real^3`; `rho:real`] CONNECTED_PUNCTURED_BALL) THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN
    DISCH_THEN(MP_TAC o SPEC `Q:real^3->bool`) THEN
    SUBGOAL_THEN `(Q:real^3->bool) SUBSET ball(P,rho) DELETE P` ASSUME_TAC THENL
     [UNDISCH_TAC `(Q:real^3->bool) SUBSET W1` THEN
      UNDISCH_TAC `(W1:real^3->bool) SUBSET ball(P,rho) DIFF E` THEN
      UNDISCH_TAC `(P:real^3) IN E` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_SUBSET; CLOSED_IN_INTER_CLOSURE] THEN
    SUBGOAL_THEN `~(Q:real^3->bool = {}) /\ ~(Q = ball(P,rho) DELETE P)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(a:real^3) IN Q` THEN SET_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `~(W2:real^3->bool = {})` THEN
        UNDISCH_TAC `(W2:real^3->bool) SUBSET ball(P,rho) DIFF E` THEN
        UNDISCH_TAC `(Q:real^3->bool) SUBSET W1` THEN
        UNDISCH_TAC `DISJOINT (W1:real^3->bool) W2` THEN
        UNDISCH_TAC `(Q:real^3->bool) = ball(P,rho) DELETE P` THEN
        UNDISCH_TAC `(P:real^3) IN E` THEN SET_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?x:real^3. x IN (ball(P,rho) DELETE P) INTER closure Q /\ ~(x IN Q)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `Q:real^3->bool` CLOSURE_SUBSET) THEN
      UNDISCH_TAC `(Q:real^3->bool) SUBSET ball(P,rho) DELETE P` THEN
      UNDISCH_TAC `~((ball(P:real^3,rho) DELETE P) INTER closure Q = Q)` THEN SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `x:real^3` THEN
    UNDISCH_TAC `(x:real^3) IN (ball(P,rho) DELETE P) INTER closure Q` THEN
    REWRITE_TAC[IN_INTER; IN_DELETE] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the local polytopes at x, triangulated *)
  USE_THEN "loc" (MP_TAC o C MATCH_MP
    (CONJ (ASSUME `(x:real^3) IN E INTER ball(P,rho)`) (ASSUME `~(x:real^3 = P)`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:(real^3->bool)->bool` (X_CHOOSE_THEN `u:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_polyhedron (UNIONS cc:real^3->bool)` MP_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `cc:(real^3->bool)->bool` THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
    DISCH_THEN(X_CHOOSE_THEN `tt:(real^3->bool)->bool` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `dimension (UNIONS cc:real^3->bool) <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC DIMENSION_LE_CLOSED_IN_UNIONS THEN EXISTS_TAC `(:real^3)` THEN
    ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; SUBTOPOLOGY_UNIV; GSYM CLOSED_IN] THEN
    CONV_TAC INT_REDUCE_CONV THEN X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `polytope (k:real^3->bool) /\ aff_dim k <= &2` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED; DIMENSION_EQ_AFF_DIM; POLYTOPE_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN tt ==> aff_dim s <= &2` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC `simplicial_complex (tt:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
    SUBGOAL_THEN `aff_dim (s:real^3->bool) = dimension s` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC DIMENSION_EQ_AFF_DIM THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `dimension (UNIONS cc:real^3->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC DIMENSION_SUBSET THEN
    UNDISCH_TAC `UNIONS tt = UNIONS (cc:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `(s:real^3->bool) IN tt` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `bad = UNIONS {s:real^3->bool | s IN tt /\ aff_dim s <= &1}` THEN
  SUBGOAL_THEN `dimension (bad:real^3->bool) <= &1 /\ bad SUBSET E` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "bad" THEN CONJ_TAC THENL
     [MATCH_MP_TAC DIMENSION_LE_CLOSED_IN_UNIONS THEN EXISTS_TAC `(:real^3)` THEN
      REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; IN_ELIM_THM] THEN
      CONV_TAC INT_REDUCE_CONV THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMP_COUNTABLE THEN MATCH_MP_TAC FINITE_RESTRICT THEN
        ASM_MESON_TAC[simplicial_complex];
        X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
        UNDISCH_TAC `simplicial_complex (tt:(real^3->bool)->bool)` THEN
        REWRITE_TAC[simplicial_complex] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
        CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
        SUBGOAL_THEN `dimension (s:real^3->bool) = aff_dim s` SUBST1_TAC THENL
         [MATCH_MP_TAC DIMENSION_EQ_AFF_DIM THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
          ASM_REWRITE_TAC[]]];
      UNDISCH_TAC `UNIONS tt = UNIONS (cc:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `!k:real^3->bool. k IN cc ==> polytope k /\ k SUBSET E /\ aff_dim k <= &2` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* a small ball at x, minus the low-dimensional simplices *)
  SUBGOAL_THEN `?r1. &0 < r1 /\ ball(x:real^3,r1) SUBSET u INTER ball(P,rho) /\
                     ~((P:real^3) IN ball(x,r1))` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `u INTER ball(P:real^3,rho)` OPEN_CONTAINS_BALL) THEN
    ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN E INTER ball(P,rho)` THEN
      UNDISCH_TAC `(x:real^3) IN u` THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `min r0 (dist(x:real^3,P))` THEN
    SUBGOAL_THEN `&0 < dist(x:real^3,P)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[DIST_POS_LT]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(x:real^3,r0)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
      REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (ball(x:real^3,r1) DIFF bad)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_OPEN_DIFF_LOWDIM THEN
    REWRITE_TAC[OPEN_BALL; CONNECTED_BALL; DIMINDEX_3] THEN
    CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((Q:real^3->bool) INTER (ball(x,r1) DIFF bad) = {}) /\
                ~((W2:real^3->bool) INTER (ball(x,r1) DIFF bad) = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN closure Q` THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
      DISCH_THEN(MP_TAC o SPEC `r1:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF; IN_BALL] THEN
      EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `dist(q:real^3,x) < r1` THEN CONV_TAC NORM_ARITH;
        UNDISCH_TAC `(bad:real^3->bool) SUBSET E` THEN
        UNDISCH_TAC `(q:real^3) IN Q` THEN UNDISCH_TAC `(Q:real^3->bool) SUBSET W1` THEN
        UNDISCH_TAC `(W1:real^3->bool) SUBSET ball(P,rho) DIFF E` THEN SET_TAC[]];
      SUBGOAL_THEN `(x:real^3) IN closure W2` MP_TAC THENL
       [UNDISCH_TAC `E INTER ball(P:real^3,rho) SUBSET closure W2` THEN
        UNDISCH_TAC `(x:real^3) IN E INTER ball(P,rho)` THEN SET_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
      DISCH_THEN(MP_TAC o SPEC `r1:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_DIFF; IN_BALL] THEN
      EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `dist(q:real^3,x) < r1` THEN CONV_TAC NORM_ARITH;
        UNDISCH_TAC `(bad:real^3->bool) SUBSET E` THEN
        UNDISCH_TAC `(q:real^3) IN W2` THEN
        UNDISCH_TAC `(W2:real^3->bool) SUBSET ball(P,rho) DIFF E` THEN SET_TAC[]]];
    ALL_TAC] THEN
  (* a frontier point y of Q there *)
  SUBGOAL_THEN `?y:real^3. y IN ball(x,r1) DIFF bad /\ y IN closure Q /\ ~(y IN Q)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `connected (ball(x:real^3,r1) DIFF bad)` THEN
    REWRITE_TAC[CONNECTED_CLOPEN] THEN
    DISCH_THEN(MP_TAC o SPEC `(Q:real^3->bool) INTER (ball(x,r1) DIFF bad)`) THEN
    SUBGOAL_THEN `open_in (subtopology euclidean (ball(x:real^3,r1) DIFF bad))
                          (Q INTER (ball(x,r1) DIFF bad))` (fun th -> REWRITE_TAC[th]) THENL
     [ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSED_IN_INTER_CLOSURE] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((Q:real^3->bool) INTER (ball(x,r1) DIFF bad) = ball(x,r1) DIFF bad)`
    (fun th -> REWRITE_TAC[th]) THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~((W2:real^3->bool) INTER (ball(x,r1) DIFF bad) = {})` THEN
      UNDISCH_TAC `(Q:real^3->bool) INTER (ball(x,r1) DIFF bad) = ball(x,r1) DIFF bad` THEN
      UNDISCH_TAC `(Q:real^3->bool) SUBSET W1` THEN
      UNDISCH_TAC `DISJOINT (W1:real^3->bool) W2` THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `(Q:real^3->bool) INTER (ball(x,r1) DIFF bad)` CLOSURE_SUBSET) THEN
    MP_TAC(ISPECL [`(Q:real^3->bool) INTER (ball(x,r1) DIFF bad)`; `Q:real^3->bool`]
                  SUBSET_CLOSURE) THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    UNDISCH_TAC `~((ball(x:real^3,r1) DIFF bad) INTER closure (Q INTER (ball(x,r1) DIFF bad)) =
                   Q INTER (ball(x,r1) DIFF bad))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN ball(P,rho) /\ y IN u /\ ~(y IN bad)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN ball(x,r1) DIFF bad` THEN
    UNDISCH_TAC `ball(x:real^3,r1) SUBSET u INTER ball(P,rho)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN E` ASSUME_TAC THENL
   [USE_THEN "fr" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* y lies in the relative interior of a triangle of tt *)
  SUBGOAL_THEN `?s:real^3->bool. s IN tt /\ aff_dim s = &2 /\ y IN relative_interior s`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^3) IN UNIONS tt` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `E INTER u SUBSET UNIONS (cc:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `(y:real^3) IN E` THEN UNDISCH_TAC `(y:real^3) IN u` THEN SET_TAC[];
      REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC)] THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `!f:real^3->bool. f IN tt /\ aff_dim f <= &1 ==> ~((y:real^3) IN f)`
    ASSUME_TAC THENL
     [X_GEN_TAC `f:real^3->bool` THEN STRIP_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `~((y:real^3) IN bad)` THEN EXPAND_TAC "bad" THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `f:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (s:real^3->bool) = &2` ASSUME_TAC THENL
     [MATCH_MP_TAC(INT_ARITH `(x:int) <= &2 /\ ~(x <= &1) ==> x = &2`) THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `(y:real^3) IN s` THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?n. n simplex (s:real^3->bool)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_complex (tt:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((y:real^3) IN relative_frontier s)` MP_TAC THENL
     [SUBGOAL_THEN `polyhedron (s:real^3->bool)` ASSUME_TAC THENL
       [MATCH_MP_TAC POLYTOPE_IMP_POLYHEDRON THEN MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN
        EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON] THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `f:real^3->bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `f:real^3->bool` o check (fun th ->
        can (term_match [] `!f:real^3->bool. f IN tt /\ aff_dim f <= &1 ==> ~((y:real^3) IN f)`)
          (concl th))) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `simplicial_complex (tt:(real^3->bool)->bool)` THEN
        REWRITE_TAC[simplicial_complex] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
        EXISTS_TAC `s:real^3->bool` THEN ASM_SIMP_TAC[FACET_OF_IMP_FACE_OF];
        UNDISCH_TAC `(f:real^3->bool) facet_of s` THEN REWRITE_TAC[facet_of] THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
      REWRITE_TAC[relative_frontier] THEN
      SUBGOAL_THEN `closure (s:real^3->bool) = s` SUBST1_TAC THENL
       [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC SIMPLEX_IMP_CLOSED THEN
        EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* LOCAL_TRI at y *)
  MP_TAC(ISPECL [`tt:(real^3->bool)->bool`; `s:real^3->bool`; `y:real^3`] LOCAL_TRI) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "lt"))) THEN
  SUBGOAL_THEN `dist(x:real^3,y) < r1` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN ball(x,r1) DIFF bad` THEN SIMP_TAC[IN_DIFF; IN_BALL];
    ALL_TAC] THEN
  ABBREV_TAC `r = min r0 (r1 - dist(x:real^3,y))` THEN
  SUBGOAL_THEN `&0 < r /\ r <= r0 /\ ball(y:real^3,r) SUBSET ball(x,r1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `z:real^3` THEN
      UNDISCH_TAC `dist(x:real^3,y) < r1` THEN CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  USE_THEN "lt" (MP_TAC o C MATCH_MP (CONJ (ASSUME `&0 < r`) (ASSUME `r <= r0`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u0:real^3->bool`
    (X_CHOOSE_THEN `v0:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`y:real^3`; `r:real`] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
   [UNDISCH_TAC `ball(y:real^3,r) SUBSET ball(x,r1)` THEN
    UNDISCH_TAC `ball(x:real^3,r1) SUBSET u INTER ball(P,rho)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS cc SUBSET (E:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET] THEN
    UNDISCH_TAC `!k:real^3->bool. k IN cc ==> polytope k /\ k SUBSET E /\ aff_dim k <= &2` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(y:real^3,r) INTER E = ball(y,r) INTER UNIONS cc` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!b b1 c e u (k:real^3->bool).
        b SUBSET b1 /\ b1 SUBSET u INTER c /\ e INTER u SUBSET k /\ k SUBSET e
        ==> b INTER e = b INTER k`) THEN
    MAP_EVERY EXISTS_TAC [`ball(x:real^3,r1)`; `ball(P:real^3,rho)`; `u:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(y:real^3,r) INTER E = ball(y,r) INTER affine hull s` ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `ball(y:real^3,r) INTER UNIONS cc` THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    FIRST_ASSUM ACCEPT_TAC ORELSE
    (SUBST1_TAC(SYM(ASSUME `UNIONS tt = UNIONS (cc:(real^3->bool)->bool)`)) THEN
     FIRST_ASSUM ACCEPT_TAC);
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(y:real^3,r) DIFF E = u0 UNION v0` ASSUME_TAC THENL
   [SUBST1_TAC(ASSUME `(u0:real^3->bool) UNION v0 = ball(y,r) DIFF affine hull s`) THEN
    UNDISCH_TAC `ball(y:real^3,r) INTER E = ball(y,r) INTER affine hull s` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBST1_TAC(ASSUME `ball(y:real^3,r) DIFF E = u0 UNION v0`) THEN
  SUBGOAL_THEN `(u0:real^3->bool) UNION v0 SUBSET W1 UNION W2` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `ball(y:real^3,r) DIFF E = u0 UNION v0`)) THEN
    UNDISCH_TAC `ball(y:real^3,r) SUBSET ball(x,r1)` THEN
    UNDISCH_TAC `ball(x:real^3,r1) SUBSET u INTER ball(P,rho)` THEN
    UNDISCH_TAC `ball(P:real^3,rho) DIFF E = W1 UNION W2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u0:real^3->bool) SUBSET W1 \/ u0 SUBSET W2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L8_CONNECTED_SPLIT THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `(u0:real^3->bool) UNION v0 SUBSET W1 UNION W2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v0:real^3->bool) SUBSET W1 \/ v0 SUBSET W2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L8_CONNECTED_SPLIT THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `(u0:real^3->bool) UNION v0 SUBSET W1 UNION W2` THEN SET_TAC[];
    ALL_TAC] THEN
  (* Q and W2 both meet the small ball *)
  SUBGOAL_THEN `(y:real^3) IN closure W2` ASSUME_TAC THENL
   [UNDISCH_TAC `E INTER ball(P:real^3,rho) SUBSET closure W2` THEN
    UNDISCH_TAC `(y:real^3) IN E` THEN UNDISCH_TAC `(y:real^3) IN ball(P,rho)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((Q:real^3->bool) INTER ball(y,r) = {}) /\
                ~((W2:real^3->bool) INTER ball(y,r) = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN closure Q`;
      UNDISCH_TAC `(y:real^3) IN closure W2`] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
    REWRITE_TAC[ASSUME `&0 < r`] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
    EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `dist(q:real^3,y) < r` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q:real^3->bool) INTER ball(y,r) SUBSET u0 UNION v0 /\
                (W2:real^3->bool) INTER ball(y,r) SUBSET u0 UNION v0` STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `ball(y:real^3,r) DIFF E = u0 UNION v0`)) THEN
    UNDISCH_TAC `(Q:real^3->bool) SUBSET W1` THEN
    UNDISCH_TAC `(W1:real^3->bool) SUBSET ball(P,rho) DIFF E` THEN
    UNDISCH_TAC `(W2:real^3->bool) SUBSET ball(P,rho) DIFF E` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the four cases *)
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    concl th = `(v0:real^3->bool) SUBSET W1 \/ v0 SUBSET W2`)) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
    concl th = `(u0:real^3->bool) SUBSET W1 \/ u0 SUBSET W2`)) THENL
   [UNDISCH_TAC `~((W2:real^3->bool) INTER ball(y,r) = {})` THEN
    UNDISCH_TAC `(W2:real^3->bool) INTER ball(y,r) SUBSET u0 UNION v0` THEN
    UNDISCH_TAC `(u0:real^3->bool) SUBSET W1` THEN UNDISCH_TAC `(v0:real^3->bool) SUBSET W1` THEN
    UNDISCH_TAC `DISJOINT (W1:real^3->bool) W2` THEN SET_TAC[];
    SUBGOAL_THEN `~((v0:real^3->bool) INTER Q = {})` ASSUME_TAC THENL
     [UNDISCH_TAC `~((Q:real^3->bool) INTER ball(y,r) = {})` THEN
      UNDISCH_TAC `(Q:real^3->bool) INTER ball(y,r) SUBSET u0 UNION v0` THEN
      UNDISCH_TAC `(u0:real^3->bool) SUBSET W2` THEN UNDISCH_TAC `(Q:real^3->bool) SUBSET W1` THEN
      UNDISCH_TAC `DISJOINT (W1:real^3->bool) W2` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(v0:real^3->bool) SUBSET Q` MP_TAC THENL
     [USE_THEN "absorb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(u0:real^3->bool) SUBSET W2` THEN SET_TAC[];
    SUBGOAL_THEN `~((u0:real^3->bool) INTER Q = {})` ASSUME_TAC THENL
     [UNDISCH_TAC `~((Q:real^3->bool) INTER ball(y,r) = {})` THEN
      UNDISCH_TAC `(Q:real^3->bool) INTER ball(y,r) SUBSET u0 UNION v0` THEN
      UNDISCH_TAC `(v0:real^3->bool) SUBSET W2` THEN UNDISCH_TAC `(Q:real^3->bool) SUBSET W1` THEN
      UNDISCH_TAC `DISJOINT (W1:real^3->bool) W2` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(u0:real^3->bool) SUBSET Q` MP_TAC THENL
     [USE_THEN "absorb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(v0:real^3->bool) SUBSET W2` THEN SET_TAC[];
    UNDISCH_TAC `(u0:real^3->bool) SUBSET W2` THEN UNDISCH_TAC `(v0:real^3->bool) SUBSET W2` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 4: infrastructure for the main proof.  A homeomorphism between      *)
(* compact convex sets of the same dimension respects relative interiors   *)
(* and frontiers (invariance of domain), so a PL 2-cell is a disk with its  *)
(* boundary.  Edges of a complex are segments, and the midpoint of an edge  *)
(* lies in no other simplex of dimension at most 1.  Components absorb     *)
(* connected sets and balls.  Pseudo-cells are closed and connected, have a *)
(* nonempty rim, and off the rim and the centre they are locally polyhedral *)
(* with polytopes of dimension at most 2.                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L8_HOMEO_RINT = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     aff_dim s = aff_dim t /\ homeomorphism (s,t) (f,g)
     ==> IMAGE f (relative_interior s) SUBSET relative_interior t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) (relative_interior s) SUBSET t` ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^M->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `IMAGE (f:real^M->real^N) s = t` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:real^M->real^N) (relative_interior s)`; `t:real^N->bool`]
                OPEN_IN_SUBSET_RELATIVE_INTERIOR) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN_AFFINE_SETS THEN
    EXISTS_TAC `affine hull s:real^M->bool` THEN
    REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL; OPEN_IN_RELATIVE_INTERIOR] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[INT_LE_REFL];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_SUBSET];
      MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `t:real^N->bool`] HULL_SUBSET) THEN
      UNDISCH_TAC `IMAGE (f:real^M->real^N) (relative_interior s) SUBSET t` THEN SET_TAC[];
      REPEAT STRIP_TAC THEN ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]];
    DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S3L8_HOMEO_RFRONT = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     compact s /\ compact t /\ aff_dim s = aff_dim t /\ homeomorphism (s,t) (f,g)
     ==> IMAGE f (relative_frontier s) = relative_frontier t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (t:real^N->bool,s:real^M->bool) (g,f)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `t:real^N->bool`; `f:real^M->real^N`; `g:real^N->real^M`]
                MOI_S3L8_HOMEO_RINT) THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `s:real^M->bool`; `g:real^N->real^M`; `f:real^M->real^N`]
                MOI_S3L8_HOMEO_RINT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
  UNDISCH_TAC `homeomorphism (s:real^M->bool,t:real^N->bool) (f,g)` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^M->bool` RELATIVE_INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC `IMAGE (f:real^M->real^N) (relative_interior s) SUBSET relative_interior t` THEN
  UNDISCH_TAC `IMAGE (g:real^N->real^M) (relative_interior t) SUBSET relative_interior s` THEN
  UNDISCH_TAC `!x:real^M. x IN s ==> (g:real^N->real^M) (f x) = x` THEN
  UNDISCH_TAC `!y:real^N. y IN t ==> (f:real^M->real^N) (g y) = y` THEN
  UNDISCH_TAC `IMAGE (f:real^M->real^N) s = t` THEN
  UNDISCH_TAC `IMAGE (g:real^N->real^M) t = s` THEN
  SET_TAC[]);;

let MOI_S3L8_SIMPLEX_DISK = prove
 (`!k:real^N->bool.
     &2 simplex k
     ==> ?f g. homeomorphism (cball(vec 0:real^2,&1),k) (f,g) /\
               relative_frontier k = IMAGE f (sphere(vec 0,&1))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ compact k /\ aff_dim k = &2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(cball(vec 0:real^2,&1)) = &2` ASSUME_TAC THENL
   [REWRITE_TAC[AFF_DIM_CBALL; REAL_LT_01; DIMINDEX_2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `k:real^N->bool`]
                HOMEOMORPHIC_CONVEX_COMPACT_SETS) THEN
  ASM_REWRITE_TAC[CONVEX_CBALL; COMPACT_CBALL; homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_TAC `g:real^N->real^2`)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^2->real^N`; `g:real^N->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `k:real^N->bool`; `f:real^2->real^N`;
                 `g:real^N->real^2`] MOI_S3L8_HOMEO_RFRONT) THEN
  ASM_REWRITE_TAC[COMPACT_CBALL; RELATIVE_FRONTIER_CBALL; REAL_OF_NUM_EQ; ARITH_EQ] THEN
  DISCH_THEN(ACCEPT_TAC o SYM));;

let MOI_S3L8_PL_DISK = prove
 (`!(k:real^M->bool) (d:real^N->bool) f g.
     &2 simplex k /\ pl_homeomorphism (k,d) (f,g)
     ==> disk_with_boundary d (IMAGE f (relative_frontier k))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `a:real^2->real^M` (X_CHOOSE_THEN `a':real^M->real^2`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_S3L8_SIMPLEX_DISK) THEN
  REWRITE_TAC[disk_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`(f:real^M->real^N) o (a:real^2->real^M)`;
                        `(a':real^M->real^2) o (g:real^N->real^M)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_o]]);;

(* Edges and midpoints.                                                      *)

let MOI_S3L8_EDGE = prove
 (`!s:real^N->bool.
     (?n. n simplex s) /\ aff_dim s = &1 ==> ?a b. ~(a = b) /\ s = segment[a,b]`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` COMPACT_CONVEX_COLLINEAR_SEGMENT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_REWRITE_TAC[COLLINEAR_AFF_DIM; INT_LE_REFL]];
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` SUBST_ALL_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim(segment[b:real^N,b]) = &1` THEN
    REWRITE_TAC[AFF_DIM_SEGMENT] THEN INT_ARITH_TAC]);;

let MOI_S3L8_MID_EDGE = prove
 (`!(t:(real^N->bool)->bool) a b q.
     (!s. s IN t ==> ?n. n simplex s) /\
     (!s s'. s IN t /\ s' IN t ==> (s INTER s') face_of s /\ (s INTER s') face_of s') /\
     segment[a,b] IN t /\ ~(a = b) /\ q IN t /\ aff_dim q <= &1 /\ midpoint(a,b) IN q
     ==> q = segment[a,b]`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sx") (CONJUNCTS_THEN2 (LABEL_TAC "fc")
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "fc" (STRIP_ASSUME_TAC o C MATCH_MP
    (CONJ (ASSUME `segment[a:real^N,b] IN t`) (ASSUME `(q:real^N->bool) IN t`))) THEN
  SUBGOAL_THEN `segment[a:real^N,b] INTER q = segment[a,b]` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`segment[a:real^N,b] INTER q`; `segment[a:real^N,b]`]
                  FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `midpoint(a:real^N,b)` THEN
    ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^N,b] face_of q` ASSUME_TAC THENL
   [UNDISCH_TAC `(segment[a:real^N,b] INTER q) face_of q` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `aff_dim(segment[a:real^N,b]) < aff_dim(q:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN REPEAT CONJ_TAC THENL
     [USE_THEN "sx" (MP_TAC o C MATCH_MP (ASSUME `(q:real^N->bool) IN t`)) THEN
      MESON_TAC[SIMPLEX_IMP_CONVEX];
      FIRST_ASSUM ACCEPT_TAC;
      ASM_MESON_TAC[]];
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
    UNDISCH_TAC `aff_dim(q:real^N->bool) <= &1` THEN INT_ARITH_TAC]);;

(* Components absorb connected sets and balls.                              *)

let MOI_S3L8_ABSORB_GEN = prove
 (`!(m:real^N->bool) x c.
     connected c /\ c SUBSET m /\ ~(c INTER connected_component m x = {})
     ==> c SUBSET connected_component m x`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3L8_COMPONENT_ABSORB THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `connected_component (m:real^N->bool) x = {}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONNECTED_COMPONENT_EQ_EMPTY]; ALL_TAC] THEN
  UNDISCH_TAC `~((c:real^N->bool) INTER connected_component m x = {})` THEN
  ASM_REWRITE_TAC[INTER_EMPTY]);;

let MOI_S3L8_OPEN_PIECE = prove
 (`!(m:real^N->bool) o1 x.
     open o1 /\ o1 SUBSET m
     ==> open (connected_component m x INTER o1) /\
         o1 INTER closure (connected_component m x) SUBSET connected_component m x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z e. &0 < e /\ ball(z:real^N,e) SUBSET o1 /\
                      ~(ball(z,e) INTER connected_component m x = {})
                      ==> ball(z,e) SUBSET connected_component m x`
  (LABEL_TAC "bl") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3L8_ABSORB_GEN THEN
    ASM_REWRITE_TAC[CONNECTED_BALL] THEN
    UNDISCH_TAC `ball(z:real^N,e) SUBSET o1` THEN
    UNDISCH_TAC `(o1:real^N->bool) SUBSET m` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[OPEN_CONTAINS_BALL; IN_INTER] THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
      check (fun th -> concl th = `open (o1:real^N->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[SUBSET_INTER] THEN
    USE_THEN "bl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `z:real^N` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL] o
      check (fun th -> concl th = `open (o1:real^N->bool)`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `ball(z:real^N,e) SUBSET connected_component m x` MP_TAC THENL
     [USE_THEN "bl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^N) IN closure (connected_component m x)` THEN
      REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
      EXISTS_TAC `q:real^N` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `dist(q:real^N,z) < e` THEN CONV_TAC NORM_ARITH;
      MP_TAC(ISPECL [`z:real^N`; `e:real`] CENTRE_IN_BALL) THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[]]]);;

(* Pseudo-cells.                                                             *)

let MOI_S3L8_PSEUDO_FACTS = prove
 (`!(e:real^N->bool) rim p.
     pseudo_cell e rim p
     ==> closed e /\ connected e /\ ~(rim = {}) /\ rim SUBSET e /\ p IN e /\
         ~(p IN rim) /\
         ?phi phi'. homeomorphism (e DIFF rim,ball(vec 0:real^2,&1)) (phi,phi')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pseudo_cell] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `closure((e:real^N->bool) DIFF rim) = e` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[CLOSED_CLOSURE];
    UNDISCH_TAC `closure((e:real^N->bool) DIFF rim) = e` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CONNECTED_CLOSURE THEN
    MP_TAC(MATCH_MP HOMEOMORPHIC_CONNECTEDNESS
      (ASSUME `((e:real^N->bool) DIFF rim) homeomorphic ball(vec 0:real^2,&1)`)) THEN
    REWRITE_TAC[CONNECTED_BALL];
    DISCH_TAC THEN
    UNDISCH_TAC `(rim:real^N->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `(p:real^N) IN e DIFF rim` THEN SET_TAC[];
    UNDISCH_TAC `(p:real^N) IN e DIFF rim` THEN SET_TAC[];
    UNDISCH_TAC `((e:real^N->bool) DIFF rim) homeomorphic ball(vec 0:real^2,&1)` THEN
    REWRITE_TAC[homeomorphic]]);;

let MOI_S3L8_LOCAL_POLY = prove
 (`!(e:real^N->bool) rim p U.
     pseudo_cell e rim p /\ open U /\ U INTER rim = {}
     ==> !x. x IN e INTER U /\ ~(x = p)
             ==> ?c u. FINITE c /\ open u /\ x IN u /\ e INTER u SUBSET UNIONS c /\
                       !k. k IN c ==> polytope k /\ k SUBSET e /\ aff_dim k <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3L8_PSEUDO_FACTS) THEN
  UNDISCH_TAC `pseudo_cell (e:real^N->bool) rim p` THEN
  REWRITE_TAC[pseudo_cell; locally_polyhedral] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o last o CONJUNCTS) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN e INTER U` THEN UNDISCH_TAC `~(x:real^N = p)` THEN
    UNDISCH_TAC `(U:real^N->bool) INTER rim = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` (X_CHOOSE_THEN `u0:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `(u0 INTER U) DELETE (p:real^N)`] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC OPEN_DELETE THEN ASM_SIMP_TAC[OPEN_INTER];
    UNDISCH_TAC `(x:real^N) IN e INTER U` THEN UNDISCH_TAC `~(x:real^N = p)` THEN
    UNDISCH_TAC `(x:real^N) IN u0` THEN SET_TAC[];
    UNDISCH_TAC `((e DIFF rim) DELETE (p:real^N)) INTER u0 SUBSET UNIONS c` THEN
    UNDISCH_TAC `(U:real^N->bool) INTER rim = {}` THEN SET_TAC[];
    X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `polytope (k:real^N->bool) /\ k SUBSET (e DIFF rim) DELETE p`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(k:real^N->bool) SUBSET (e DIFF rim) DELETE p` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`phi:real^N->real^2`; `k:real^N->bool`; `ball(vec 0:real^2,&1)`]
                  INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN) THEN
    REWRITE_TAC[AFF_DIM_BALL; REAL_LT_01; DIMINDEX_2] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `homeomorphism ((e:real^N->bool) DIFF rim,ball(vec 0:real^2,&1))
                   (phi,phi')` THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(e:real^N->bool) DIFF rim` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(k:real^N->bool) SUBSET (e DIFF rim) DELETE p` THEN SET_TAC[];
      MP_TAC(ISPECL [`affine:(real^2->bool)->bool`; `ball(vec 0:real^2,&1)`] HULL_SUBSET) THEN
      UNDISCH_TAC `IMAGE (phi:real^N->real^2) (e DIFF rim) = ball(vec 0,&1)` THEN
      UNDISCH_TAC `(k:real^N->bool) SUBSET (e DIFF rim) DELETE p` THEN SET_TAC[];
      REPEAT STRIP_TAC THEN
      UNDISCH_TAC `(k:real^N->bool) SUBSET (e DIFF rim) DELETE p` THEN
      ASM_MESON_TAC[SUBSET; IN_DELETE]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 5: segments, the graph of the tube, the facts used from             *)
(* MOI_S33_TUBE_FACTS, the two sides of the pseudo-cell near its centre,    *)
(* and the topological core of Lemma 8: a good point of E inside the        *)
(* sphere S, whose small ball minus S lies in one component Z of the        *)
(* complement of S, contradicts Jordan-Brouwer (the other component also   *)
(* has S as its frontier).                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3L8_DISK_FACTS = prove
 (`!(d:real^N->bool) j.
     disk_with_boundary d j ==> j SUBSET d /\ compact d /\ compact j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[disk_with_boundary; homeomorphism] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^N) (cball(vec 0,&1)) = d` THEN
    UNDISCH_TAC `(j:real^N->bool) = IMAGE (f:real^2->real^N) (sphere(vec 0,&1))` THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_SUBSET_CBALL) THEN SET_TAC[];
    UNDISCH_TAC `IMAGE (f:real^2->real^N) (cball(vec 0,&1)) = d` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[COMPACT_CBALL];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_SPHERE] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL]]);;

let MOI_S3L8_SEGMENT_MID = prove
 (`!a b c d:real^N.
     segment[a,b] = segment[c,d] ==> midpoint(a,b) = midpoint(c,d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SEGMENT_EQ; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `a:real^N` th) THEN MP_TAC(SPEC `b:real^N` th) THEN
                       MP_TAC(SPEC `c:real^N` th) THEN MP_TAC(SPEC `d:real^N` th)) THEN
  MESON_TAC[MIDPOINT_SYM]);;

let MOI_S3L8_SEG_NOT_END = prove
 (`!v m a0 x:real^N.
     a0 IN segment[v,m] /\ ~(a0 = m) /\ x IN segment[v,a0] ==> ~(x = m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `~(a0:real^N = m)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC BETWEEN_ANTISYM THEN EXISTS_TAC `v:real^N` THEN
  REWRITE_TAC[BETWEEN_IN_SEGMENT] THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
  ASM_REWRITE_TAC[]);;

(* The graph of the tube.                                                    *)

let MOI_S3L8_TUBE_BASICS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3).
     moi_s33_tube t l h
     ==> (!s. s IN l ==> ?n. n simplex s) /\
         (!s s'. s IN l /\ s' IN l
                 ==> (s INTER s') face_of s /\ (s INTER s') face_of s') /\
         (!s f. s IN l /\ f face_of s ==> f IN l) /\
         UNIONS l SUBSET UNIONS t /\
         h continuous_on UNIONS t /\
         (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_s33_tube; graph_in_complex; lf_simplicial_complex;
              simplicial_subcomplex] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  ASM_MESON_TAC[SUBSET; SUBSET_UNIONS]);;

let MOI_S3L8_VERTEX_NOT_MID = prove
 (`!(l:(real^N->bool)->bool) u a b.
     (!s. s IN l ==> ?n. n simplex s) /\
     (!s s'. s IN l /\ s' IN l ==> (s INTER s') face_of s /\ (s INTER s') face_of s') /\
     {u} IN l /\ segment[a,b] IN l /\ ~(a = b)
     ==> ~(midpoint(a,b) = u)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `{u:real^N}`]
                MOI_S3L8_MID_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_SING; IN_SING] THEN INT_ARITH_TAC;
    DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[SEGMENT_EQ_SING] THEN ASM_MESON_TAC[]]);;

let MOI_S3L8_SECOND_EDGE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) v w.
     moi_s33_tube t l h /\ FINITE l /\ ~(v = w) /\ segment[v,w] IN l
     ==> ?w'. ~(v = w') /\ ~(w' = w) /\ segment[v,w'] IN l`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3L8_TUBE_BASICS) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sx") (CONJUNCTS_THEN2 (LABEL_TAC "fc")
    (CONJUNCTS_THEN2 (LABEL_TAC "fl") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `{v:real^3} IN l` ASSUME_TAC THENL
   [USE_THEN "fl" MATCH_MP_TAC THEN EXISTS_TAC `segment[v:real^3,w]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `?s:real^3->bool. s IN l /\ aff_dim s = &1 /\ v IN s /\ ~(s = segment[v,w])`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `{s:real^3->bool | s IN l /\ aff_dim s = &1 /\ v IN s} = {segment[v,w]}`
    ASSUME_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
      X_GEN_TAC `s:real^3->bool` THEN EQ_TAC THENL
       [ASM_MESON_TAC[];
        DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT]];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_s33_tube (t:(real^3->bool)->bool) l h` THEN
    REWRITE_TAC[moi_s33_tube] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[CARD_SING];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S3L8_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "sx" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `v:real^3 = a \/ v = b` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM EXTREME_POINT_OF_SEGMENT; GSYM FACE_OF_SING] THEN
    SUBGOAL_THEN `{v:real^3} INTER segment[a,b] = {v}` (SUBST1_TAC o SYM) THENL
     [UNDISCH_TAC `(v:real^3) IN s` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "fc" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `{v:real^3} IN l`) (ASSUME `(s:real^3->bool) IN l`))) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [EXISTS_TAC `b:real^3`; EXISTS_TAC `a:real^3`] THEN
  ASM_MESON_TAC[SEGMENT_SYM]);;

(* The facts used from MOI_S33_TUBE_FACTS (an antecedent of MOI_S3L8_MAIN,  *)
(* discharged in Part 7).                                                   *)

let MOI_S3L8_TUBE_USE = prove
 (mk_imp(MOI_S33_TUBE_FACTS,
  `!(t:(real^3->bool)->bool) l (h:real^3->real^3).
     moi_s33_tube t l h
     ==> FINITE l /\ compact (IMAGE h (derived_nbhd t l)) /\
         connected (frontier (IMAGE h (derived_nbhd t l))) /\
         ~(frontier (IMAGE h (derived_nbhd t l)) = {}) /\
         IMAGE h (UNIONS l) SUBSET interior (IMAGE h (derived_nbhd t l))`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP
    (ASSUME `moi_s33_tube (t:(real^3->bool)->bool) l h`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(h:real^3->real^3) continuous_on UNIONS t` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_tube (t:(real^3->bool)->bool) l h` THEN
    REWRITE_TAC[moi_s33_tube] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `derived_frontier t l SUBSET UNIONS (t:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[derived_frontier] THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS (t:(real^3->bool)->bool))`;
                   `derived_nbhd (t:(real^3->bool)->bool) l`]
                  FRONTIER_OF_SUBSET_TOPSPACE) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS (t:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
    MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS (t:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY]]);;

(* The two sides of a pseudo-cell near its centre.                          *)

let MOI_S3L8_PIECES = prove
 (`!(N:real^3->bool) EE E1 B xv xw.
     open B /\ closed E1 /\ E1 SUBSET EE /\ B SUBSET N /\ B INTER EE SUBSET E1 /\
     B DIFF E1 SUBSET closure (connected_component (N DIFF EE) xv) UNION
                      closure (connected_component (N DIFF EE) xw) /\
     closure (connected_component (N DIFF EE) xv) INTER
     closure (connected_component (N DIFF EE) xw) = E1
     ==> open (connected_component (N DIFF EE) xv INTER B) /\
         open (connected_component (N DIFF EE) xw INTER B) /\
         DISJOINT (connected_component (N DIFF EE) xv INTER B)
                  (connected_component (N DIFF EE) xw INTER B) /\
         B DIFF E1 = (connected_component (N DIFF EE) xv INTER B) UNION
                     (connected_component (N DIFF EE) xw INTER B) /\
         E1 INTER B SUBSET closure (connected_component (N DIFF EE) xw INTER B)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open ((B:real^3->bool) DIFF E1) /\ B DIFF E1 SUBSET N DIFF EE`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_DIFF] THEN
    UNDISCH_TAC `(B:real^3->bool) SUBSET N` THEN
    UNDISCH_TAC `(B:real^3->bool) INTER EE SUBSET E1` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(B:real^3->bool) DIFF E1 SUBSET
               closure (connected_component (N DIFF EE) xv) UNION
               closure (connected_component (N DIFF EE) xw)` THEN
  UNDISCH_TAC `closure (connected_component ((N:real^3->bool) DIFF EE) xv) INTER
               closure (connected_component (N DIFF EE) xw) = E1` THEN
  MP_TAC(ISPECL [`N DIFF EE:real^3->bool`; `B DIFF E1:real^3->bool`; `xv:real^3`]
                MOI_S3L8_OPEN_PIECE) THEN
  MP_TAC(ISPECL [`N DIFF EE:real^3->bool`; `B DIFF E1:real^3->bool`; `xw:real^3`]
                MOI_S3L8_OPEN_PIECE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`N DIFF EE:real^3->bool`; `xv:real^3`] CONNECTED_COMPONENT_SUBSET) THEN
  MP_TAC(ISPECL [`N DIFF EE:real^3->bool`; `xw:real^3`] CONNECTED_COMPONENT_SUBSET) THEN
  MP_TAC(ISPEC `connected_component ((N:real^3->bool) DIFF EE) xv` CLOSURE_SUBSET) THEN
  MP_TAC(ISPEC `connected_component ((N:real^3->bool) DIFF EE) xw` CLOSURE_SUBSET) THEN
  MP_TAC(ISPECL [`B:real^3->bool`; `connected_component ((N:real^3->bool) DIFF EE) xw`]
                OPEN_INTER_CLOSURE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`connected_component ((N:real^3->bool) DIFF EE) xw`,`Cw:real^3->bool`) THEN
  SPEC_TAC(`connected_component ((N:real^3->bool) DIFF EE) xv`,`Cv:real^3->bool`) THEN
  REPEAT GEN_TAC THEN REPEAT STRIP_TAC THENL
   [SUBGOAL_THEN `(Cv:real^3->bool) INTER B = Cv INTER (B DIFF E1)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `(Cw:real^3->bool) INTER B = Cw INTER (B DIFF E1)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    ASM SET_TAC[];
    ASM SET_TAC[];
    SUBGOAL_THEN `(Cw:real^3->bool) INTER B = B INTER Cw` SUBST1_TAC THENL
     [SET_TAC[]; ASM SET_TAC[]]]);;

(* The topological core.                                                     *)

let MOI_S3L8_CORE = prove
 (`!(S:real^3->bool) E W1 W2 P rho a Z.
     S homeomorphic sphere(vec 0:real^3,&1) /\
     closed E /\ P IN E /\ &0 < rho /\
     ball(P,rho) INTER E = ball(P,rho) INTER S /\
     open W1 /\ open W2 /\ DISJOINT W1 W2 /\
     ball(P,rho) DIFF E = W1 UNION W2 /\ a IN W1 /\
     E INTER ball(P,rho) SUBSET closure W2 /\
     (!x. x IN E INTER ball(P,rho) /\ ~(x = P)
          ==> ?c u. FINITE c /\ open u /\ x IN u /\ E INTER u SUBSET UNIONS c /\
                    !k. k IN c ==> polytope k /\ k SUBSET E /\ aff_dim k <= &2) /\
     Z IN components((:real^3) DIFF S) /\
     connected_component W1 a SUBSET Z /\ W2 SUBSET Z
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`E:real^3->bool`; `W1:real^3->bool`; `W2:real^3->bool`; `P:real^3`;
                 `rho:real`; `a:real^3`] MOI_S3L8_GOOD_POINT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y:real^3) IN S` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN E INTER ball(P,rho)` THEN
    UNDISCH_TAC `ball(P:real^3,rho) INTER E = ball(P,rho) INTER S` THEN SET_TAC[];
    ALL_TAC] THEN
  (* another component *)
  SUBGOAL_THEN `?q:real^3. q IN (:real^3) DIFF S /\ ~(q IN Z)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `vec 0:real^3`; `&1`] JORDAN_BROUWER_SEPARATION) THEN
    ASM_REWRITE_TAC[REAL_LT_01] THEN
    MATCH_MP_TAC(TAUT `(~q ==> p) ==> ~p ==> q`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(:real^3) DIFF S = Z` SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET];
        ASM_MESON_TAC[IN_COMPONENTS_SUBSET]];
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component ((:real^3) DIFF S) q IN components((:real^3) DIFF S)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (connected_component ((:real^3) DIFF S) q) = S` ASSUME_TAC THENL
   [MATCH_MP_TAC JORDAN_BROUWER_FRONTIER THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^3`; `&1`] THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^3. z IN connected_component ((:real^3) DIFF S) q /\ z IN ball(y,r)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^3) IN frontier (connected_component ((:real^3) DIFF S) q)`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[frontier; IN_DIFF; CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[IN_BALL] THEN
    UNDISCH_TAC `dist(z:real^3,y) < r` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN Z` ASSUME_TAC THENL
   [SUBGOAL_THEN `~((z:real^3) IN S)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`(:real^3) DIFF S`; `q:real^3`] CONNECTED_COMPONENT_SUBSET) THEN
      UNDISCH_TAC `(z:real^3) IN connected_component ((:real^3) DIFF S) q` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `ball(y:real^3,r) DIFF E SUBSET connected_component W1 a UNION W2` THEN
    UNDISCH_TAC `connected_component W1 (a:real^3) SUBSET Z` THEN
    UNDISCH_TAC `(W2:real^3->bool) SUBSET Z` THEN
    UNDISCH_TAC `ball(P:real^3,rho) INTER E = ball(P,rho) INTER S` THEN
    UNDISCH_TAC `ball(y:real^3,r) SUBSET ball(P,rho)` THEN
    UNDISCH_TAC `(z:real^3) IN ball(y,r)` THEN UNDISCH_TAC `~((z:real^3) IN S)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DIFF S`; `Z:real^3->bool`;
                 `connected_component ((:real^3) DIFF S) q`] COMPONENTS_NONOVERLAP) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((Z:real^3->bool) INTER connected_component ((:real^3) DIFF S) q = {})`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `z:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN UNDISCH_TAC `~((q:real^3) IN Z)` THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 6: Lemma 8 from MOI_S33_TUBE_FACTS.  Suppose the disk d misses      *)
(* K'.  The disks d and dj glue to a sphere S inside Int N'.  A small ball  *)
(* B0 at the centre P1 of E1 meets S only in E1 and splits off E1 into the  *)
(* v side and the w side.  The arm from a point of the v side near P1 along *)
(* K' to v and on to the second pseudo-cell E2 at v, E2 itself and the      *)
(* w side all lie in the component Z of the complement of S that contains  *)
(* the connected frontier of N'.  This contradicts MOI_S3L8_CORE.           *)
(* ------------------------------------------------------------------------- *)

(* SET_TAC after generalizing the set-valued atoms of the goal (images,  *)
(* unions, closures, ...), so that their definitions are not expanded.    *)

let MOI_S3L8_ASET_TAC : tactic =
  let setops = ["INTER"; "UNION"; "DIFF"; "INSERT"; "EMPTY"; "UNIV"; "DELETE"] in
  let is_set_ty ty =
    (try (match dest_type ty with ("fun",[_;b]) -> b = bool_ty | _ -> false) with Failure _ -> false) in
  let rec tsize t =
    if is_comb t then tsize (rator t) + tsize (rand t) else if is_abs t then 1 + tsize (body t) else 1 in
  let rec collect bvs t acc =
    if is_abs t then
      (let v,b = dest_abs t in collect (v::bvs) b acc)
    else if is_comb t then
       (let hop,args = strip_comb t in
        let isop = is_const hop && mem (fst(dest_const hop)) setops in
        if is_set_ty (type_of t) && not isop && intersect (frees t) bvs = []
        then insert t acc
        else itlist (collect bvs) (hop::args) acc)
    else acc in
  fun (asl,w as g) ->
    let ats = collect [] w [] in
    let ats = sort (fun a b -> tsize a > tsize b) ats in
    (MAP_EVERY (fun t -> SPEC_TAC(t,genvar(type_of t))) ats THEN SET_TAC[]) g;;

let MOI_S3L8_MAIN = prove
 (mk_imp(MOI_S33_TUBE_FACTS, MOI_S33_L8_BODY),
  DISCH_THEN(LABEL_TAC "tf") THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hd") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `dj:real^3->bool` STRIP_ASSUME_TAC)
    (LABEL_TAC "oth"))))))))) THEN
  DISCH_TAC THEN
  USE_THEN "hd" (MP_TAC o REWRITE_RULE[moi_s33_hd]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pc")
    (CONJUNCTS_THEN2 (LABEL_TAC "dsj") (CONJUNCTS_THEN2 (LABEL_TAC "cv")
    (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (LABEL_TAC "cc")))))) THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`]
    (MP MOI_S3L8_TUBE_USE (ASSUME MOI_S33_TUBE_FACTS))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(MATCH_MP MOI_S3L8_TUBE_BASICS
    (ASSUME `moi_s33_tube (t:(real^3->bool)->bool) l (h:real^3->real^3)`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sx") (CONJUNCTS_THEN2 (LABEL_TAC "fc")
    (CONJUNCTS_THEN2 (LABEL_TAC "fl") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")))))) THEN
  (* vertices, the second edge, segments in the complex *)
  SUBGOAL_THEN `{v:real^3} IN l /\ {w:real^3} IN l` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "fl" MATCH_MP_TAC THEN EXISTS_TAC `segment[v:real^3,w]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                `v:real^3`; `w:real^3`] MOI_S3L8_SECOND_EDGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `segment[v:real^3,w] SUBSET UNIONS l /\ segment[v:real^3,w'] SUBSET UNIONS l /\
                segment[v:real^3,w] SUBSET UNIONS t /\ segment[v:real^3,w'] SUBSET UNIONS t`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(a /\ b) /\ (a /\ b ==> c /\ d) ==> a /\ b /\ c /\ d`) THEN
    CONJ_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN s ==> x SUBSET UNIONS s`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `UNIONS l SUBSET UNIONS (t:(real^3->bool)->bool)` THEN MOI_S3L8_ASET_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^3,midpoint(v,w)] SUBSET segment[v,w] /\
                segment[v:real^3,midpoint(v,w')] SUBSET segment[v,w']` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT; MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s SUBSET UNIONS t ==> (h:real^3->real^3) continuous_on s`
  (LABEL_TAC "hc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `UNIONS (t:(real^3->bool)->bool)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) SUBSET (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) /\ closed (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_SUBSET] THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN UNIONS l ==> (h:real^3->real^3) x IN (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` (LABEL_TAC "inNP") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`h:real^3->real^3`; `UNIONS (l:(real^3->bool)->bool)`; `x:real^3`]
                  FUN_IN_IMAGE) THEN
    UNDISCH_TAC `(IMAGE (h:real^3->real^3) (UNIONS (l:(real^3->bool)->bool))) SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN UNDISCH_TAC `interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) SUBSET (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
    UNDISCH_TAC `(x:real^3) IN UNIONS l` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  (* the pseudo-cells E1 and E2 *)
  USE_THEN "pc" (MP_TAC o C MATCH_MP
    (CONJ (ASSUME `~(v:real^3 = w)`) (ASSUME `segment[v:real^3,w] IN l`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  USE_THEN "pc" (MP_TAC o C MATCH_MP
    (CONJ (ASSUME `~(v:real^3 = w')`) (ASSUME `segment[v:real^3,w'] IN l`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(MATCH_MP MOI_S3L8_PSEUDO_FACTS (ASSUME `pseudo_cell ((e:(real^3->bool)->real^3->bool)(segment[v,w])) (moi_s33_rim t l (h:real^3->real^3) v w) ((h:real^3->real^3)(midpoint(v,w)))`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))))) THEN
  MP_TAC(MATCH_MP MOI_S3L8_PSEUDO_FACTS (ASSUME `pseudo_cell ((e:(real^3->bool)->real^3->bool)(segment[v,w'])) (moi_s33_rim t l (h:real^3->real^3) v w') ((h:real^3->real^3)(midpoint(v,w')))`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))))) THEN
  (* the pieces c v, c w *)
  USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cvv" o SYM) (K ALL_TAC)) THEN
  USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `{w:real^3} IN l`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cvw" o SYM) (K ALL_TAC)) THEN
  SUBGOAL_THEN `(c:real^3->real^3->bool) v INTER c w = ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` ASSUME_TAC THENL
   [USE_THEN "cc" (MP_TAC o C MATCH_MP (CONJ (ASSUME `{v:real^3} IN l`)
      (CONJ (ASSUME `{w:real^3} IN l`) (ASSUME `~(v:real^3 = w)`)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->real^3->bool) v SUBSET (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS {(c:real^3->real^3->bool) v | {v} IN l} = (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN s ==> x SUBSET UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `((e:(real^3->bool)->real^3->bool)(segment[v,w])) SUBSET (c:real^3->real^3->bool) v /\ ((e:(real^3->bool)->real^3->bool)(segment[v,w])) SUBSET c w /\ ((e:(real^3->bool)->real^3->bool)(segment[v,w])) SUBSET (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(c:real^3->real^3->bool) v INTER c w = ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` THEN
    UNDISCH_TAC `(c:real^3->real^3->bool) v SUBSET (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) = (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` ASSUME_TAC THENL
   [REWRITE_TAC[frontier] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC CLOSURE_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((e:(real^3->bool)->real^3->bool)(segment[v,w])) DIFF (moi_s33_rim t l (h:real^3->real^3) v w) SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` ASSUME_TAC THENL
   [UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w])) INTER frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) = (moi_s33_rim t l (h:real^3->real^3) v w)` THEN
    UNDISCH_TAC `frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) = (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
    UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w])) SUBSET (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((e:(real^3->bool)->real^3->bool)(segment[v,w])) SUBSET (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN s ==> x SUBSET UNIONS s`) THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `segment[v:real^3,w]` THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
    ALL_TAC] THEN
  (* the planar lemma and the sphere S = d UNION dj *)
  SUBGOAL_THEN `(IMAGE (f:real^3->real^3) (relative_frontier k)) SUBSET ((e:(real^3->bool)->real^3->bool)(segment[v,w])) DIFF (moi_s33_rim t l (h:real^3->real^3) v w)` ASSUME_TAC THENL
   [UNDISCH_TAC `(d:real^3->bool) INTER ((e:(real^3->bool)->real^3->bool)(segment[v,w])) = (IMAGE (f:real^3->real^3) (relative_frontier k))` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET (c:real^3->real^3->bool) v INTER interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
    SUBST1_TAC(SYM(ASSUME `((e:(real^3->bool)->real^3->bool)(segment[v,w])) INTER frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) = (moi_s33_rim t l (h:real^3->real^3) v w)`)) THEN
    REWRITE_TAC[frontier] THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`((e:(real^3->bool)->real^3->bool)(segment[v,w]))`; `(moi_s33_rim t l (h:real^3->real^3) v w)`; `((h:real^3->real^3)(midpoint(v,w)))`; `dj:real^3->bool`; `(IMAGE (f:real^3->real^3) (relative_frontier k))`] MOI_S3L8_PLANAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `disk_with_boundary (d:real^3->bool) (IMAGE (f:real^3->real^3) (relative_frontier k))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L8_PL_DISK THEN EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:real^3->bool`; `(IMAGE (f:real^3->real^3) (relative_frontier k))`] MOI_S3L8_DISK_FACTS) THEN
  MP_TAC(ISPECL [`dj:real^3->bool`; `(IMAGE (f:real^3->real^3) (relative_frontier k))`] MOI_S3L8_DISK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(d:real^3->bool) INTER dj = (IMAGE (f:real^3->real^3) (relative_frontier k))` ASSUME_TAC THENL
   [UNDISCH_TAC `(d:real^3->bool) INTER ((e:(real^3->bool)->real^3->bool)(segment[v,w])) = (IMAGE (f:real^3->real^3) (relative_frontier k))` THEN
    UNDISCH_TAC `(dj:real^3->bool) SUBSET ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` THEN
    UNDISCH_TAC `(IMAGE (f:real^3->real^3) (relative_frontier k)) SUBSET (d:real^3->bool)` THEN UNDISCH_TAC `(IMAGE (f:real^3->real^3) (relative_frontier k)) SUBSET (dj:real^3->bool)` THEN
    MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((d:real^3->bool) UNION dj) homeomorphic sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L8_DISKS_SPHERE THEN EXISTS_TAC `(IMAGE (f:real^3->real^3) (relative_frontier k))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact ((d:real^3->bool) UNION dj) /\ ((d:real^3->bool) UNION dj) SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_UNION THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(d:real^3->bool) SUBSET (c:real^3->real^3->bool) v INTER interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
    UNDISCH_TAC `(dj:real^3->bool) SUBSET ((e:(real^3->bool)->real^3->bool)(segment[v,w])) DIFF (moi_s33_rim t l (h:real^3->real^3) v w)` THEN
    UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w])) DIFF (moi_s33_rim t l (h:real^3->real^3) v w) SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(((h:real^3->real^3)(midpoint(v,w))) IN (d:real^3->bool))` ASSUME_TAC THENL
   [UNDISCH_TAC `((h:real^3->real^3)(midpoint(v,w))) IN dj DIFF (IMAGE (f:real^3->real^3) (relative_frontier k))` THEN UNDISCH_TAC `((h:real^3->real^3)(midpoint(v,w))) IN ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` THEN
    UNDISCH_TAC `(d:real^3->bool) INTER ((e:(real^3->bool)->real^3->bool)(segment[v,w])) = (IMAGE (f:real^3->real^3) (relative_frontier k))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `open_in (subtopology euclidean ((e:(real^3->bool)->real^3->bool)(segment[v,w]))) (dj DIFF (IMAGE (f:real^3->real^3) (relative_frontier k)))` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `uo:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  (* the closed sets to avoid near the centre *)
  SUBGOAL_THEN `closed (UNIONS (IMAGE (c:real^3->real^3->bool) {u | {u} IN l /\ ~(u = v) /\ ~(u = w)})) /\ closed (UNIONS (IMAGE (e:(real^3->bool)->real^3->bool) {s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])}))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{u:real^3 | {u} IN l}` THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`\u:real^3. {u}`; `l:(real^3->bool)->bool`] FINITE_IMAGE_INJ) THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; SIMP_TAC[]];
        SET_TAC[]];
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `u:real^3` THEN STRIP_TAC THEN
      USE_THEN "cv" (MP_TAC o C MATCH_MP (ASSUME `{u:real^3} IN l`)) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[CLOSED_CLOSURE];
      MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_RESTRICT THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `s:real^3->bool` THEN
      STRIP_TAC THEN
      MP_TAC(ISPEC `s:real^3->bool` MOI_S3L8_EDGE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "sx" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
      UNDISCH_TAC `(s:real^3->bool) = segment[a,b]` THEN DISCH_THEN SUBST_ALL_TAC THEN
      USE_THEN "pc" (MP_TAC o C MATCH_MP
        (CONJ (ASSUME `~(a:real^3 = b)`) (ASSUME `segment[a:real^3,b] IN l`))) THEN
      DISCH_THEN(MP_TAC o MATCH_MP MOI_S3L8_PSEUDO_FACTS o CONJUNCT1) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(((h:real^3->real^3)(midpoint(v,w))) IN (UNIONS (IMAGE (c:real^3->real^3->bool) {u | {u} IN l /\ ~(u = v) /\ ~(u = w)}))) /\ ~(((h:real^3->real^3)(midpoint(v,w))) IN (UNIONS (IMAGE (e:(real^3->bool)->real^3->bool) {s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])})))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM; NOT_EXISTS_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `u:real^3` THEN STRIP_TAC THEN
      USE_THEN "cc" (MP_TAC o C MATCH_MP (CONJ (ASSUME `{u:real^3} IN l`)
        (CONJ (ASSUME `{v:real^3} IN l`) (ASSUME `~(u:real^3 = v)`)))) THEN
      COND_CASES_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `DISJOINT ((e:(real^3->bool)->real^3->bool)(segment[u,v])) ((e:(real^3->bool)->real^3->bool)(segment[v,w]))`
        MP_TAC THENL
         [USE_THEN "dsj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT; SEGMENT_EQ] THEN
          REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
          DISCH_THEN(MP_TAC o SPEC `u:real^3`) THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(c:real^3->real^3->bool) u INTER c v =
                     (e:(real^3->bool)->real^3->bool)(segment[u,v])` THEN
        UNDISCH_TAC `((h:real^3->real^3)(midpoint(v,w))) IN (c:real^3->real^3->bool) u` THEN
        UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w])) SUBSET (c:real^3->real^3->bool) v` THEN
        UNDISCH_TAC `((h:real^3->real^3)(midpoint(v,w))) IN ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` THEN MOI_S3L8_ASET_TAC;
        DISCH_TAC THEN
        UNDISCH_TAC `(c:real^3->real^3->bool) u INTER c v = {}` THEN
        UNDISCH_TAC `((h:real^3->real^3)(midpoint(v,w))) IN (c:real^3->real^3->bool) u` THEN
        UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w])) SUBSET (c:real^3->real^3->bool) v` THEN
        UNDISCH_TAC `((h:real^3->real^3)(midpoint(v,w))) IN ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` THEN MOI_S3L8_ASET_TAC];
      X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `DISJOINT ((e:(real^3->bool)->real^3->bool) s) ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` MP_TAC THENL
       [USE_THEN "dsj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
        UNDISCH_TAC `((h:real^3->real^3)(midpoint(v,w))) IN (e:(real^3->bool)->real^3->bool) s` THEN
        UNDISCH_TAC `((h:real^3->real^3)(midpoint(v,w))) IN ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` THEN MOI_S3L8_ASET_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((h:real^3->real^3)(midpoint(v,w))) IN interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` ASSUME_TAC THENL
   [UNDISCH_TAC `(IMAGE (h:real^3->real^3) (UNIONS (l:(real^3->bool)->bool))) SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> s SUBSET t ==> x IN t`) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    UNDISCH_TAC `segment[v:real^3,w] SUBSET UNIONS l` THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> s SUBSET t ==> x IN t`) THEN
    REWRITE_TAC[MIDPOINT_IN_SEGMENT];
    ALL_TAC] THEN
  (* the ball B0 *)
  SUBGOAL_THEN `?rho. &0 < rho /\
                      (ball((h:real^3->real^3)(midpoint(v,w)),rho)) SUBSET (uo INTER interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))) DIFF
                                  ((d:real^3->bool) UNION (UNIONS (IMAGE (c:real^3->real^3->bool) {u | {u} IN l /\ ~(u = v) /\ ~(u = w)})) UNION (UNIONS (IMAGE (e:(real^3->bool)->real^3->bool) {s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])})))`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open ((uo INTER interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))) DIFF ((d:real^3->bool) UNION (UNIONS (IMAGE (c:real^3->real^3->bool) {u | {u} IN l /\ ~(u = v) /\ ~(u = w)})) UNION (UNIONS (IMAGE (e:(real^3->bool)->real^3->bool) {s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])}))))`
    MP_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
        REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN
        TRY(FIRST_ASSUM ACCEPT_TAC) THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `((h:real^3->real^3)(midpoint(v,w)))`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~(((h:real^3->real^3)(midpoint(v,w))) IN (UNIONS (IMAGE (c:real^3->real^3->bool) {u | {u} IN l /\ ~(u = v) /\ ~(u = w)})))` THEN UNDISCH_TAC `~(((h:real^3->real^3)(midpoint(v,w))) IN (UNIONS (IMAGE (e:(real^3->bool)->real^3->bool) {s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])})))` THEN
      UNDISCH_TAC `~(((h:real^3->real^3)(midpoint(v,w))) IN (d:real^3->bool))` THEN
      UNDISCH_TAC `((h:real^3->real^3)(midpoint(v,w))) IN interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
      UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w])) INTER uo = dj DIFF (IMAGE (f:real^3->real^3) (relative_frontier k))` THEN UNDISCH_TAC `((h:real^3->real^3)(midpoint(v,w))) IN dj DIFF (IMAGE (f:real^3->real^3) (relative_frontier k))` THEN
      MOI_S3L8_ASET_TAC;
      DISCH_THEN(X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `rho:real` THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) /\ (ball((h:real^3->real^3)(midpoint(v,w)),rho)) SUBSET (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) /\
                (ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER (d:real^3->bool) = {} /\ (ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER ((e:(real^3->bool)->real^3->bool)(segment[v,w])) SUBSET dj DIFF (IMAGE (f:real^3->real^3) (relative_frontier k)) /\
                (ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER (UNIONS (IMAGE (c:real^3->real^3->bool) {u | {u} IN l /\ ~(u = v) /\ ~(u = w)})) = {} /\ (ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER (UNIONS (IMAGE (e:(real^3->bool)->real^3->bool) {s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])})) = {}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) SUBSET (uo INTER interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))) DIFF
                              ((d:real^3->bool) UNION (UNIONS (IMAGE (c:real^3->real^3->bool) {u | {u} IN l /\ ~(u = v) /\ ~(u = w)})) UNION (UNIONS (IMAGE (e:(real^3->bool)->real^3->bool) {s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])})))` THEN
    UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w])) INTER uo = dj DIFF (IMAGE (f:real^3->real^3) (relative_frontier k))` THEN
    UNDISCH_TAC `interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) SUBSET (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^3. {u} IN l /\ ~(u = v) /\ ~(u = w)
                           ==> (ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER (c:real^3->real^3->bool) u = {}`
  (LABEL_TAC "avc") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(c:real^3->real^3->bool) u SUBSET (UNIONS (IMAGE (c:real^3->real^3->bool) {u | {u} IN l /\ ~(u = v) /\ ~(u = w)}))` MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN s ==> x SUBSET UNIONS s`) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      UNDISCH_TAC `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER (UNIONS (IMAGE (c:real^3->real^3->bool) {u | {u} IN l /\ ~(u = v) /\ ~(u = w)})) = {}` THEN MOI_S3L8_ASET_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])
                    ==> (ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER (e:(real^3->bool)->real^3->bool) s = {}`
  (LABEL_TAC "ave") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(e:(real^3->bool)->real^3->bool) s SUBSET (UNIONS (IMAGE (e:(real^3->bool)->real^3->bool) {s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])}))` MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(x:real^3->bool) IN s ==> x SUBSET UNIONS s`) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      UNDISCH_TAC `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER (UNIONS (IMAGE (e:(real^3->bool)->real^3->bool) {s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])})) = {}` THEN MOI_S3L8_ASET_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER (moi_s33_rim t l (h:real^3->real^3) v w) = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
    UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w])) INTER frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) = (moi_s33_rim t l (h:real^3->real^3) v w)` THEN
    UNDISCH_TAC `frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) = (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER ((e:(real^3->bool)->real^3->bool)(segment[v,w])) = (ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER ((d:real^3->bool) UNION dj)` ASSUME_TAC THENL
   [UNDISCH_TAC `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER (d:real^3->bool) = {}` THEN
    UNDISCH_TAC `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER ((e:(real^3->bool)->real^3->bool)(segment[v,w])) SUBSET dj DIFF (IMAGE (f:real^3->real^3) (relative_frontier k))` THEN
    UNDISCH_TAC `(dj:real^3->bool) SUBSET ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1}) SUBSET ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `es:real^3->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    ASM_CASES_TAC `s = segment[v:real^3,w]` THENL
     [UNDISCH_TAC `(z:real^3) IN es` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "ave" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(s:real^3->bool) IN l`)
      (CONJ (ASSUME `aff_dim(s:real^3->bool) = &1`) (ASSUME `~(s = segment[v:real^3,w])`)))) THEN
    UNDISCH_TAC `(z:real^3) IN es` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN (ball((h:real^3->real^3)(midpoint(v,w)),rho))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) DIFF ((e:(real^3->bool)->real^3->bool)(segment[v,w])) SUBSET (c:real^3->real^3->bool) v UNION c w` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN UNIONS {(c:real^3->real^3->bool) v | {v} IN l}` MP_TAC THENL
     [UNDISCH_TAC `UNIONS {(c:real^3->real^3->bool) v | {v} IN l} = (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
      UNDISCH_TAC `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) SUBSET (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN UNDISCH_TAC `(z:real^3) IN (ball((h:real^3->real^3)(midpoint(v,w)),rho))` THEN
      MOI_S3L8_ASET_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `cu:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    ASM_CASES_TAC `u:real^3 = v` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `u:real^3 = w` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "avc" (MP_TAC o C MATCH_MP (CONJ (ASSUME `{u:real^3} IN l`)
      (CONJ (ASSUME `~(u:real^3 = v)`) (ASSUME `~(u:real^3 = w)`)))) THEN
    UNDISCH_TAC `(z:real^3) IN cu` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN (ball((h:real^3->real^3)(midpoint(v,w)),rho))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  (* the two sides of E1 in B0, and the local polytopes of E1 *)
  MP_TAC(ISPECL [`(IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))`; `(UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})`; `((e:(real^3->bool)->real^3->bool)(segment[v,w]))`; `(ball((h:real^3->real^3)(midpoint(v,w)),rho))`; `(h:real^3->real^3) v`;
                 `(h:real^3->real^3) w`] MOI_S3L8_PIECES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL] THEN
    USE_THEN "cvv" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "cvw" (fun th -> REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`((e:(real^3->bool)->real^3->bool)(segment[v,w]))`; `(moi_s33_rim t l (h:real^3->real^3) v w)`; `((h:real^3->real^3)(midpoint(v,w)))`; `(ball((h:real^3->real^3)(midpoint(v,w)),rho))`] MOI_S3L8_LOCAL_POLY) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC] THEN
  (* points of K' on the pseudo-cells are midpoints of edges *)
  SUBGOAL_THEN `!x:real^3. x IN UNIONS l /\ (h:real^3->real^3) x IN (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})
                ==> ?a b. ~(a = b) /\ segment[a,b] IN l /\ midpoint(a,b) = x`
  (LABEL_TAC "midpt") THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    UNDISCH_TAC `(h:real^3->real^3) x IN (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `es:real^3->bool`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(ISPEC `s:real^3->bool` MOI_S3L8_EDGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "sx" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC))] THEN
    UNDISCH_TAC `(s:real^3->bool) = segment[a,b]` THEN DISCH_THEN SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "pc" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `~(a:real^3 = b)`) (ASSUME `segment[a:real^3,b] IN l`))) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN DISCH_TAC THEN
    USE_THEN "inj" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS l SUBSET UNIONS (t:(real^3->bool)->bool)` THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> s SUBSET t ==> x IN t`) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[a:real^3,b]` THEN
      ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
      UNDISCH_TAC `UNIONS l SUBSET UNIONS (t:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `(x:real^3) IN UNIONS l` THEN MOI_S3L8_ASET_TAC;
      SUBGOAL_THEN `(h:real^3->real^3) x IN
                    (e:(real^3->bool)->real^3->bool)(segment[a,b]) INTER (IMAGE (h:real^3->real^3) (UNIONS (l:(real^3->bool)->bool)))` MP_TAC THENL
       [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(h:real^3->real^3) x IN es` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC];
        ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[]]];
    ALL_TAC] THEN
  (* the vertices v and w lie in the complement of the pseudo-cells *)
  SUBGOAL_THEN `(v:real^3) IN UNIONS l /\ (w:real^3) IN UNIONS l` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `segment[v:real^3,w] SUBSET UNIONS l` THEN
    MP_TAC(ISPECL [`v:real^3`; `w:real^3`] ENDS_IN_SEGMENT) THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3) v IN (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1}) /\
                (h:real^3->real^3) w IN (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_DIFF] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "inNP" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN
      USE_THEN "midpt" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(v:real^3) IN UNIONS l`)
        (ASSUME `(h:real^3->real^3) v IN (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `v:real^3`; `a:real^3`; `b:real^3`]
                    MOI_S3L8_VERTEX_NOT_MID) THEN
      ASM_REWRITE_TAC[];
      USE_THEN "inNP" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISCH_TAC THEN
      USE_THEN "midpt" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(w:real^3) IN UNIONS l`)
        (ASSUME `(h:real^3->real^3) w IN (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `w:real^3`; `a:real^3`; `b:real^3`]
                    MOI_S3L8_VERTEX_NOT_MID) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* a point h a0 of the arm near the centre, on the v side *)
  SUBGOAL_THEN `(h:real^3->real^3) continuous_on segment[v,midpoint(v,w)] /\
                (h:real^3->real^3) continuous_on segment[v,midpoint(v,w')]`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "hc" MATCH_MP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
     [EXISTS_TAC `segment[v:real^3,w]`; EXISTS_TAC `segment[v:real^3,w']`] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^3. a IN IMAGE (h:real^3->real^3) (segment[v,midpoint(v,w)]) /\
                           ~(a = ((h:real^3->real^3)(midpoint(v,w)))) /\ a IN (ball((h:real^3->real^3)(midpoint(v,w)),rho))` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (h:real^3->real^3) (segment[v,midpoint(v,w)])`; `((h:real^3->real^3)(midpoint(v,w)))`]
                  CONNECTED_IMP_PERFECT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        ASM_REWRITE_TAC[CONNECTED_SEGMENT];
        DISCH_THEN(X_CHOOSE_TAC `q:real^3`) THEN
        SUBGOAL_THEN `(h:real^3->real^3) v = ((h:real^3->real^3)(midpoint(v,w)))` ASSUME_TAC THENL
         [MP_TAC(ISPECL [`h:real^3->real^3`; `segment[v:real^3,midpoint(v,w)]`; `v:real^3`]
                        FUN_IN_IMAGE) THEN
          MP_TAC(ISPECL [`h:real^3->real^3`; `segment[v:real^3,midpoint(v,w)]`;
                         `midpoint(v:real^3,w)`] FUN_IN_IMAGE) THEN
          ASM_REWRITE_TAC[ENDS_IN_SEGMENT; IN_SING] THEN MESON_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `v:real^3 = midpoint(v,w)` MP_TAC THENL
         [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `segment[v:real^3,w] SUBSET UNIONS t` THEN
          MP_TAC(ISPECL [`v:real^3`; `w:real^3`] ENDS_IN_SEGMENT) THEN
          MP_TAC(ISPECL [`v:real^3`; `w:real^3`] (CONJUNCT1 MIDPOINT_IN_SEGMENT)) THEN
          MOI_S3L8_ASET_TAC;
          ASM_REWRITE_TAC[MIDPOINT_EQ_ENDPOINT]];
        MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT]];
      ALL_TAC] THEN
    REWRITE_TAC[LIMPT_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `rho:real`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `a:real^3` THEN ASM_REWRITE_TAC[IN_BALL] THEN
    UNDISCH_TAC `dist(a:real^3,((h:real^3->real^3)(midpoint(v,w)))) < rho` THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  UNDISCH_TAC `(a:real^3) IN IMAGE (h:real^3->real^3) (segment[v,midpoint(v,w)])` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:real^3` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(a0:real^3 = midpoint(v,w))` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((h:real^3->real^3)(midpoint(v,w)) = ((h:real^3->real^3)(midpoint(v,w))))` THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^3,a0] SUBSET segment[v,w]` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `segment[v:real^3,midpoint(v,w)]` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_REWRITE_TAC[CONVEX_SEGMENT; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN segment[v,a0] ==> ~(x = midpoint(v,w))` (LABEL_TAC "nm") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3L8_SEG_NOT_END THEN
    MAP_EVERY EXISTS_TAC [`v:real^3`; `a0:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3) continuous_on segment[v,a0] /\
                connected (IMAGE (h:real^3->real^3) (segment[v,a0])) /\
                connected (IMAGE (h:real^3->real^3) (segment[v,midpoint(v,w')]))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `a /\ (a ==> b /\ c) ==> a /\ b /\ c`) THEN CONJ_TAC THENL
     [USE_THEN "hc" MATCH_MP_TAC THEN
      UNDISCH_TAC `segment[v:real^3,a0] SUBSET segment[v,w]` THEN
      UNDISCH_TAC `segment[v:real^3,w] SUBSET UNIONS t` THEN MOI_S3L8_ASET_TAC;
      DISCH_TAC THEN CONJ_TAC THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[CONNECTED_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^3->real^3) (segment[v,a0]) SUBSET (connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) v))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT];
      FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN UNIONS l` ASSUME_TAC THENL
       [UNDISCH_TAC `segment[v:real^3,a0] SUBSET segment[v,w]` THEN
        UNDISCH_TAC `segment[v:real^3,w] SUBSET UNIONS l` THEN
        UNDISCH_TAC `(x:real^3) IN segment[v,a0]` THEN MOI_S3L8_ASET_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [USE_THEN "inNP" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        DISCH_TAC THEN
        USE_THEN "midpt" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(x:real^3) IN UNIONS l`)
          (ASSUME `(h:real^3->real^3) x IN (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})`))) THEN
        DISCH_THEN(X_CHOOSE_THEN `a1:real^3` (X_CHOOSE_THEN `b1:real^3` STRIP_ASSUME_TAC)) THEN
        MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `a1:real^3`; `b1:real^3`;
                       `segment[v:real^3,w]`] MOI_S3L8_MID_EDGE) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[AFF_DIM_SEGMENT; INT_LE_REFL] THEN
          UNDISCH_TAC `segment[v:real^3,a0] SUBSET segment[v,w]` THEN
          UNDISCH_TAC `(x:real^3) IN segment[v,a0]` THEN MOI_S3L8_ASET_TAC;
          ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP MOI_S3L8_SEGMENT_MID) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        USE_THEN "nm" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN segment[v,a0]`)) THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3) a0 IN (connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) v)) INTER (ball((h:real^3->real^3)(midpoint(v,w)),rho))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^3->real^3) (segment[v,a0]) SUBSET (connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) v))` THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> s SUBSET t ==> x IN t`) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT];
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  (* the arm G misses the sphere S *)
  SUBGOAL_THEN `~(((h:real^3->real^3)(midpoint(v,w))) IN (IMAGE (h:real^3->real^3) (segment[v,a0]) UNION IMAGE h (segment[v,midpoint(v,w')])))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNION; IN_IMAGE] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `midpoint(v:real^3,w) = x` ASSUME_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN CONJ_TAC THENL
         [UNDISCH_TAC `segment[v:real^3,w] SUBSET UNIONS t` THEN
          MP_TAC(ISPECL [`v:real^3`; `w:real^3`] (CONJUNCT1 MIDPOINT_IN_SEGMENT)) THEN
          MOI_S3L8_ASET_TAC;
          CONJ_TAC THENL
           [UNDISCH_TAC `segment[v:real^3,a0] SUBSET segment[v,w]` THEN
            UNDISCH_TAC `segment[v:real^3,w] SUBSET UNIONS t` THEN
            UNDISCH_TAC `(x:real^3) IN segment[v,a0]` THEN MOI_S3L8_ASET_TAC;
            FIRST_ASSUM ACCEPT_TAC]];
        USE_THEN "nm" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN segment[v,a0]`)) THEN
        ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `midpoint(v:real^3,w) = x` ASSUME_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN CONJ_TAC THENL
         [UNDISCH_TAC `segment[v:real^3,w] SUBSET UNIONS t` THEN
          MP_TAC(ISPECL [`v:real^3`; `w:real^3`] (CONJUNCT1 MIDPOINT_IN_SEGMENT)) THEN
          MOI_S3L8_ASET_TAC;
          CONJ_TAC THENL
           [UNDISCH_TAC `segment[v:real^3,midpoint(v,w')] SUBSET segment[v,w']` THEN
            UNDISCH_TAC `segment[v:real^3,w'] SUBSET UNIONS t` THEN
            UNDISCH_TAC `(x:real^3) IN segment[v,midpoint(v,w')]` THEN MOI_S3L8_ASET_TAC;
            FIRST_ASSUM ACCEPT_TAC]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `v:real^3`; `w:real^3`;
                     `segment[v:real^3,w']`] MOI_S3L8_MID_EDGE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[AFF_DIM_SEGMENT; INT_LE_REFL] THEN
        UNDISCH_TAC `segment[v:real^3,midpoint(v,w')] SUBSET segment[v,w']` THEN
        UNDISCH_TAC `(x:real^3) IN segment[v,midpoint(v,w')]` THEN MOI_S3L8_ASET_TAC;
        REWRITE_TAC[SEGMENT_EQ; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `w':real^3`) THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(IMAGE (h:real^3->real^3) (segment[v,a0]) UNION IMAGE h (segment[v,midpoint(v,w')])) INTER ((d:real^3->bool) UNION dj) = {}` ASSUME_TAC THENL
   [SUBGOAL_THEN `(IMAGE (h:real^3->real^3) (segment[v,a0]) UNION IMAGE h (segment[v,midpoint(v,w')])) SUBSET (IMAGE (h:real^3->real^3) (UNIONS (l:(real^3->bool)->bool)))` MP_TAC THENL
     [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THENL
       [UNDISCH_TAC `segment[v:real^3,a0] SUBSET segment[v,w]` THEN
        UNDISCH_TAC `segment[v:real^3,w] SUBSET UNIONS l` THEN MOI_S3L8_ASET_TAC;
        UNDISCH_TAC `segment[v:real^3,midpoint(v,w')] SUBSET segment[v,w']` THEN
        UNDISCH_TAC `segment[v:real^3,w'] SUBSET UNIONS l` THEN MOI_S3L8_ASET_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `~(((h:real^3->real^3)(midpoint(v,w))) IN (IMAGE (h:real^3->real^3) (segment[v,a0]) UNION IMAGE h (segment[v,midpoint(v,w')])))` THEN
    UNDISCH_TAC `(d:real^3->bool) INTER (IMAGE (h:real^3->real^3) (UNIONS (l:(real^3->bool)->bool))) = {}` THEN
    UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w])) INTER (IMAGE (h:real^3->real^3) (UNIONS (l:(real^3->bool)->bool))) = {((h:real^3->real^3)(midpoint(v,w)))}` THEN
    UNDISCH_TAC `(dj:real^3->bool) SUBSET ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (h:real^3->real^3) (segment[v,a0]) UNION IMAGE h (segment[v,midpoint(v,w')]))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `(h:real^3->real^3) v` THEN
    CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  (* the component Z of the complement of S containing the frontier of N' *)
  SUBGOAL_THEN `?p0:real^3. p0 IN frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(p0:real^3) IN (:real^3) DIFF ((d:real^3->bool) UNION dj)` ASSUME_TAC THENL
   [UNDISCH_TAC `(p0:real^3) IN frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
    UNDISCH_TAC `frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) = (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
    UNDISCH_TAC `((d:real^3->bool) UNION dj) SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0) /\ (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0) IN components ((:real^3) DIFF ((d:real^3->bool) UNION dj))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_CONNECTED_COMPONENT THEN REWRITE_TAC[GSYM closed] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IN_COMPONENTS] THEN EXISTS_TAC `p0:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) SUBSET (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN REPEAT CONJ_TAC THEN
    TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) = (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
    UNDISCH_TAC `((d:real^3->bool) UNION dj) SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((e:(real^3->bool)->real^3->bool)(segment[v,w'])) INTER ((d:real^3->bool) UNION dj) = {}` ASSUME_TAC THENL
   [SUBGOAL_THEN `DISJOINT (d:real^3->bool) ((e:(real^3->bool)->real^3->bool)(segment[v,w']))` ASSUME_TAC THENL
     [USE_THEN "oth" MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT; SEGMENT_EQ] THEN
      REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `w':real^3`) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT ((e:(real^3->bool)->real^3->bool)(segment[v,w'])) ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` ASSUME_TAC THENL
     [USE_THEN "dsj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT; SEGMENT_EQ] THEN
      REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `w':real^3`) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (d:real^3->bool) ((e:(real^3->bool)->real^3->bool)(segment[v,w']))` THEN UNDISCH_TAC `DISJOINT ((e:(real^3->bool)->real^3->bool)(segment[v,w'])) ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` THEN
    UNDISCH_TAC `(dj:real^3->bool) SUBSET ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` THEN MOI_S3L8_ASET_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `((e:(real^3->bool)->real^3->bool)(segment[v,w'])) SUBSET (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L8_ABSORB_GEN THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w'])) INTER ((d:real^3->bool) UNION dj) = {}` THEN MOI_S3L8_ASET_TAC;
      UNDISCH_TAC `~((moi_s33_rim t l (h:real^3->real^3) v w') = {})` THEN UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w'])) INTER frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) = (moi_s33_rim t l (h:real^3->real^3) v w')` THEN
      UNDISCH_TAC `frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) SUBSET (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0)` THEN MOI_S3L8_ASET_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(IMAGE (h:real^3->real^3) (segment[v,a0]) UNION IMAGE h (segment[v,midpoint(v,w')])) SUBSET (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L8_ABSORB_GEN THEN REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `(IMAGE (h:real^3->real^3) (segment[v,a0]) UNION IMAGE h (segment[v,midpoint(v,w')])) INTER ((d:real^3->bool) UNION dj) = {}` THEN MOI_S3L8_ASET_TAC;
      SUBGOAL_THEN `((h:real^3->real^3)(midpoint(v,w'))) IN (IMAGE (h:real^3->real^3) (segment[v,a0]) UNION IMAGE h (segment[v,midpoint(v,w')])) /\ ((h:real^3->real^3)(midpoint(v,w'))) IN ((e:(real^3->bool)->real^3->bool)(segment[v,w']))` MP_TAC THENL
       [CONJ_TAC THENL
         [REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          REWRITE_TAC[ENDS_IN_SEGMENT];
          UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w'])) INTER (IMAGE (h:real^3->real^3) (UNIONS (l:(real^3->bool)->bool))) = {((h:real^3->real^3)(midpoint(v,w')))}` THEN MOI_S3L8_ASET_TAC];
        UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w'])) SUBSET (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0)` THEN MOI_S3L8_ASET_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) w)) SUBSET (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3L8_ABSORB_GEN THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT];
      MP_TAC(ISPECL [`(IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})`; `(h:real^3->real^3) w`] CONNECTED_COMPONENT_SUBSET) THEN
      MP_TAC(ISPEC `(connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) w))` CLOSURE_SUBSET) THEN
      USE_THEN "cvw" (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `(d:real^3->bool) SUBSET (c:real^3->real^3->bool) v INTER interior (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l))` THEN
      UNDISCH_TAC `(c:real^3->real^3->bool) v INTER c w = ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` THEN
      UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w])) SUBSET (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})` THEN
      UNDISCH_TAC `(dj:real^3->bool) SUBSET ((e:(real^3->bool)->real^3->bool)(segment[v,w]))` THEN MOI_S3L8_ASET_TAC;
      ONCE_REWRITE_TAC[INTER_COMM] THEN
      MP_TAC(ISPECL [`(connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0)`; `(connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) w))`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `~((moi_s33_rim t l (h:real^3->real^3) v w) = {})` THEN UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w])) INTER frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) = (moi_s33_rim t l (h:real^3->real^3) v w)` THEN
      UNDISCH_TAC `((e:(real^3->bool)->real^3->bool)(segment[v,w])) SUBSET (c:real^3->real^3->bool) w` THEN
      UNDISCH_TAC `frontier (IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) SUBSET (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0)` THEN MOI_S3L8_ASET_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected_component ((connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) v)) INTER (ball((h:real^3->real^3)(midpoint(v,w)),rho))) ((h:real^3->real^3) a0) SUBSET (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0) /\
                (connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) w)) INTER (ball((h:real^3->real^3)(midpoint(v,w)),rho)) SUBSET (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3L8_ABSORB_GEN THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT];
        MP_TAC(ISPECL [`(connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) v)) INTER (ball((h:real^3->real^3)(midpoint(v,w)),rho))`; `(h:real^3->real^3) a0`]
                      CONNECTED_COMPONENT_SUBSET) THEN
        UNDISCH_TAC `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) DIFF ((e:(real^3->bool)->real^3->bool)(segment[v,w])) = ((connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) v)) INTER (ball((h:real^3->real^3)(midpoint(v,w)),rho))) UNION ((connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) w)) INTER (ball((h:real^3->real^3)(midpoint(v,w)),rho)))` THEN
        UNDISCH_TAC `(ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER ((e:(real^3->bool)->real^3->bool)(segment[v,w])) = (ball((h:real^3->real^3)(midpoint(v,w)),rho)) INTER ((d:real^3->bool) UNION dj)` THEN MOI_S3L8_ASET_TAC;
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `(h:real^3->real^3) a0` THEN CONJ_TAC THENL
         [GEN_REWRITE_TAC I [IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
          FIRST_ASSUM ACCEPT_TAC;
          UNDISCH_TAC `(IMAGE (h:real^3->real^3) (segment[v,a0]) UNION IMAGE h (segment[v,midpoint(v,w')])) SUBSET (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0)` THEN
          MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> s UNION t SUBSET u ==> x IN u`) THEN
          MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT]]];
      UNDISCH_TAC `(connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) w)) SUBSET (connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0)` THEN MOI_S3L8_ASET_TAC];
    ALL_TAC] THEN
  (* the contradiction *)
  MATCH_MP_TAC MOI_S3L8_CORE THEN
  MAP_EVERY EXISTS_TAC [`((d:real^3->bool) UNION dj)`; `((e:(real^3->bool)->real^3->bool)(segment[v,w]))`; `(connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) v)) INTER (ball((h:real^3->real^3)(midpoint(v,w)),rho))`; `(connected_component ((IMAGE (h:real^3->real^3) (derived_nbhd (t:(real^3->bool)->bool) l)) DIFF (UNIONS {(e:(real^3->bool)->real^3->bool) s | s IN l /\ aff_dim s = &1})) ((h:real^3->real^3) w)) INTER (ball((h:real^3->real^3)(midpoint(v,w)),rho))`; `((h:real^3->real^3)(midpoint(v,w)))`;
                        `rho:real`; `(h:real^3->real^3) a0`; `(connected_component ((:real^3) DIFF ((d:real^3->bool) UNION dj)) p0)`] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Part 7: Lemma 8.  MOI_S3L8_MAIN with the tube facts TUBE_FACTS of        *)
(* pc_moi_s33_frame; MOISE_324 is an unused antecedent of MOI_S33_L8.       *)
(* ------------------------------------------------------------------------- *)

let S33_L8 = prove
 (MOI_S33_L8,
  DISCH_TAC THEN ACCEPT_TAC(MP MOI_S3L8_MAIN TUBE_FACTS));;

