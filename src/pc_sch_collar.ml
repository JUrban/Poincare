(* ========================================================================= *)
(* Unit pc_sch_collar: collar matching for smooth spheres in R^3,            *)
(* |- SCH_COLLAR3_STATEMENT (SCH_COLLAR3).                                   *)
(*                                                                           *)
(* If a collared sphere f(S^2) bounds the image of a ball chart c0, then it  *)
(* bounds the image of a ball chart c equal to f (or to f composed with the  *)
(* inversion, when the inner half of the collar lies outside) on            *)
(* 3/4 < |x| < 2.  Route: decide the inner side (Jordan-Brouwer); in c0     *)
(* coordinates the collar is an embedding k of a shell mapping the sphere to *)
(* itself; Smale's theorem (SMT_SMALE_RADIAL) straightens k on the sphere;  *)
(* the straightened k1 fixes the sphere pointwise and is joined to the       *)
(* identity by a linear and a radial isotopy of thin-shell embeddings;      *)
(* isotopy extension (SCHI_ISOTOPY_EXTENSION_01) gives an ambient            *)
(* diffeomorphism, and the chart is glued from it and f.                     *)
(* ========================================================================= *)

needs "src/pc_sch_generic.ml";;
needs "src/pc_sch_isoext.ml";;
needs "src/pc_smt_straight.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Spheres of a neck are topological spheres; the ball chart                 *)
(* of the bounded side maps the unit ball onto the inside and the unit      *)
(* sphere onto the sphere.                                                   *)
(* ------------------------------------------------------------------------- *)

let SCH1_NECK_HOMEOMORPHIC = prove
 (`!f f':real^3->real^3 r.
        sch_neck f f' /\ &1 / &2 < r /\ r < &2
        ==> IMAGE f (sphere(vec 0,r)) homeomorphic sphere(vec 0:real^3,&1)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,r) SUBSET annulus (&1 / &2) (&2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:real^3->real^3) (sphere(vec 0,r))`; `sphere(vec 0:real^3,r)`;
                 `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_TRANS) THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    EXISTS_TAC `f:real^3->real^3` THEN MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN
    REWRITE_TAC[COMPACT_SPHERE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM_MESON_TAC[SUBSET]];
    REWRITE_TAC[HOMEOMORPHIC_SPHERES_EQ] THEN ASM_REAL_ARITH_TAC]);;

(* The ball chart of the bounded side of a topological sphere.               *)

let SCH1_BALL_INSIDE = prove
 (`!c c':real^3->real^3 s.
        sch_ball c c' /\ s homeomorphic sphere(vec 0:real^3,&1) /\
        IMAGE c (cball(vec 0,&1)) = s UNION inside s
        ==> IMAGE c (ball(vec 0,&1)) = inside s /\
            IMAGE c (sphere(vec 0,&1)) = s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_ball] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `!x y:real^3. x IN ball(vec 0,&2) /\ y IN ball(vec 0,&2) /\ (c:real^3->real^3) x = c y
                             ==> x = y` (LABEL_TAC "inj") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `interior(s UNION inside s) = inside(s:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN s UNION inside s` MP_TAC THENL
       [ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNION] THEN
      ASM_CASES_TAC `(x:real^3) IN s` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`interior(s UNION inside s:real^3->bool)`; `outside(s:real^3->bool)`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      REWRITE_TAC[OPEN_INTERIOR] THEN
      MATCH_MP_TAC(TAUT `b /\ ~a ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `s UNION inside s:real^3->bool` INTERIOR_SUBSET) THEN
        MP_TAC(ISPEC `s:real^3->bool` OUTSIDE_NO_OVERLAP) THEN
        UNDISCH_TAC `inside s INTER outside s:real^3->bool = {}` THEN SET_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN s` THEN
        UNDISCH_TAC `frontier(outside s) = (s:real^3->bool)` THEN
        REWRITE_TAC[frontier] THEN SET_TAC[]];
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior(IMAGE (c:real^3->real^3) (cball(vec 0,&1))) =
                IMAGE c (ball(vec 0,&1))` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC;
      MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
        MATCH_MP_TAC SCH4_DIFFEO_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,&2)`;
                              `IMAGE (c:real^3->real^3) (ball(vec 0,&2))`;
                              `c':real^3->real^3`] THEN
        ASM_REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC]] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[SUBSET] INTERIOR_SUBSET)) THEN
    REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[IN_BALL_0] THEN
    ASM_REWRITE_TAC[REAL_LT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN ball(vec 0,&2)` ASSUME_TAC THENL
     [REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(c:real^3->real^3) continuous at x` MP_TAC THENL
     [MATCH_MP_TAC DIFFERENTIABLE_IMP_CONTINUOUS_AT THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `ball(vec 0:real^3,&2)` THEN ASM_REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    MP_TAC(ISPEC `interior(IMAGE (c:real^3->real^3) (cball(vec 0,&1)))`
      OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
    REWRITE_TAC[ASSUME `(y:real^3) IN interior(IMAGE (c:real^3->real^3) (cball(vec 0,&1)))`] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    REWRITE_TAC[ASSUME `&0 < e`] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    ABBREV_TAC `m = min (d / &2) (&1 / &2)` THEN
    SUBGOAL_THEN `&0 < m /\ m < d /\ m <= &1 / &2` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "m" THEN UNDISCH_TAC `&0 < d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `norm((&1 + m) % x:real^3) = &1 + m` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_MUL] THEN UNDISCH_TAC `&0 < m` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:real^3->real^3)((&1 + m) % x) IN IMAGE c (cball(vec 0,&1))`
    MP_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] INTERIOR_SUBSET) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [SUBSET]) THEN
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq(concl th) && rhs(concl th) = `(c:real^3->real^3) x`)) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      REWRITE_TAC[dist; VECTOR_ARITH `(&1 + m) % x - x:real^3 = m % x`; NORM_MUL] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < m` THEN UNDISCH_TAC `m < d` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_CBALL_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(&1 + m) % x:real^3 = z` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL_0] THEN
      UNDISCH_TAC `norm(z:real^3) <= &1` THEN UNDISCH_TAC `m <= &1 / &2` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(fun th -> UNDISCH_TAC `norm(z:real^3) <= &1` THEN
                         REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < m` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (c:real^3->real^3) (ball(vec 0,&1)) = inside s` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `s:real^3->bool` INSIDE_NO_OVERLAP) THEN
  UNDISCH_TAC `IMAGE (c:real^3->real^3) (ball(vec 0,&1)) = inside s` THEN
  UNDISCH_TAC `IMAGE (c:real^3->real^3) (cball(vec 0,&1)) = s UNION inside s` THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNION; IN_INTER; NOT_IN_EMPTY;
              IN_CBALL_0; IN_BALL_0; IN_SPHERE_0] THEN
  REPEAT DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN s \/ y IN inside s` MP_TAC THENL
     [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?z:real^3. (y:real^3) = (c:real^3->real^3) z /\ norm z < &1`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `x:real^3 = z` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL_0] THEN
      ASM_MESON_TAC[REAL_ARITH `x = &1 ==> x < &2`; REAL_ARITH `x < &1 ==> x < &2`];
      ASM_MESON_TAC[REAL_LT_REFL]];
    DISCH_TAC THEN
    SUBGOAL_THEN `?x:real^3. (y:real^3) = (c:real^3->real^3) x /\ norm x <= &1`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `norm(x:real^3) < &1` THENL
     [ASM_MESON_TAC[]; ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The two halves of a neck around the sphere of radius r lie                *)
(* on different sides of f(sphere r).                                        *)
(* ------------------------------------------------------------------------- *)

let SCH1_CONNECTED_SIDE = prove
 (`!t u v:real^N->bool.
        connected t /\ open u /\ open v /\ u INTER v = {} /\ t SUBSET u UNION v
        ==> t SUBSET u \/ t SUBSET v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPECL [`u:real^N->bool`; `v:real^N->bool`])
    STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let SCH1_ANNULUS_CONNECTED = prove
 (`!r1 r2. connected(annulus r1 r2:real^3->bool)`,
  REPEAT GEN_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^3`; `r1:real`; `r2:real`] (CONJUNCT1 CONNECTED_ANNULUS)) THEN
  REWRITE_TAC[DIMINDEX_3; ARITH; VECTOR_SUB_RZERO; annulus]);;

let SCH1_NECK_SIDES = prove
 (`!f f':real^3->real^3 r.
        sch_neck f f' /\ &1 / &2 < r /\ r < &2
        ==> ((!x. x IN annulus (&1 / &2) r
                  ==> f x IN inside(IMAGE f (sphere(vec 0,r)))) /\
             (!x. x IN annulus r (&2)
                  ==> f x IN outside(IMAGE f (sphere(vec 0,r))))) \/
            ((!x. x IN annulus (&1 / &2) r
                  ==> f x IN outside(IMAGE f (sphere(vec 0,r)))) /\
             (!x. x IN annulus r (&2)
                  ==> f x IN inside(IMAGE f (sphere(vec 0,r)))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `S = IMAGE (f:real^3->real^3) (sphere(vec 0,r))` THEN
  MP_TAC(ISPEC `S:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_3; ARITH] THEN SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^3) (sphere(vec 0,r)) = S`)) THEN
    MATCH_MP_TAC SCH1_NECK_HOMEOMORPHIC THEN EXISTS_TAC `f':real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  SUBGOAL_THEN `annulus (&1 / &2) r SUBSET annulus (&1 / &2) (&2):real^3->bool /\
                annulus r (&2) SUBSET annulus (&1 / &2) (&2):real^3->bool /\
                sphere(vec 0,r) SUBSET annulus (&1 / &2) (&2):real^3->bool`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
    REPEAT CONJ_TAC THEN GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^3. x IN annulus (&1 / &2) (&2) /\ y IN annulus (&1 / &2) (&2) /\
                             (f:real^3->real^3) x = f y ==> x = y` (LABEL_TAC "inj") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!A:real^3->bool. A SUBSET annulus (&1 / &2) (&2) /\ connected A /\
                     A INTER sphere(vec 0,r) = {}
                     ==> IMAGE (f:real^3->real^3) A SUBSET inside S \/
                         IMAGE f A SUBSET outside S`
  (LABEL_TAC "side") THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SCH1_CONNECTED_SIDE THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `inside S UNION outside S:real^3->bool`)) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^3) (sphere(vec 0,r)) = S`)) THEN
      REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `x:real^3 = y` SUBST_ALL_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM SET_TAC[]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (annulus (&1 / &2) r) SUBSET inside S \/
                IMAGE f (annulus (&1 / &2) r) SUBSET outside S`
  (LABEL_TAC "s1") THENL
   [USE_THEN "side" MATCH_MP_TAC THEN ASM_REWRITE_TAC[SCH1_ANNULUS_CONNECTED] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (annulus r (&2)) SUBSET inside S \/
                IMAGE f (annulus r (&2)) SUBSET outside S`
  (LABEL_TAC "s2") THENL
   [USE_THEN "side" MATCH_MP_TAC THEN ASM_REWRITE_TAC[SCH1_ANNULUS_CONNECTED] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->real^3)(r % basis 1) IN S` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^3) (sphere(vec 0,r)) = S`)) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    SIMP_TAC[IN_SPHERE_0; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^3->bool. w INTER S = {} /\ frontier w = S
        ==> ?x:real^3. x IN annulus (&1 / &2) (&2) /\ ~(x IN sphere(vec 0,r)) /\
                       (f:real^3->real^3) x IN w`
  (LABEL_TAC "meet") THENL
   [GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (f:real^3->real^3) (annulus (&1 / &2) (&2))`; `w:real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~a /\ (~b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(f:real^3->real^3)(r % basis 1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN
        UNDISCH_TAC `sphere(vec 0:real^3,r) SUBSET annulus (&1 / &2) (&2)` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        SIMP_TAC[IN_SPHERE_0; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
        ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `(f:real^3->real^3)(r % basis 1) IN S` THEN
        UNDISCH_TAC `frontier w = (S:real^3->bool)` THEN
        REWRITE_TAC[frontier] THEN SET_TAC[]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^3` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(q:real^3) IN S` MP_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^3) (sphere(vec 0,r)) = S`)) THEN
        FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
          is_eq(concl th) && lhs(concl th) = `q:real^3`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `(q:real^3) IN w` THEN UNDISCH_TAC `w INTER S:real^3->bool = {}` THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN annulus (&1 / &2) (&2) /\ ~(x IN sphere(vec 0,r))
                           ==> x IN annulus (&1 / &2) r \/ x IN annulus r (&2)`
  ASSUME_TAC THENL
   [REWRITE_TAC[annulus; IN_ELIM_THM; IN_SPHERE_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (f:real^3->real^3) (annulus (&1 / &2) r) SUBSET inside S /\
                  IMAGE f (annulus r (&2)) SUBSET inside S)` ASSUME_TAC THENL
   [STRIP_TAC THEN
    USE_THEN "meet" (MP_TAC o C MATCH_MP (CONJ (ISPEC `S:real^3->bool` OUTSIDE_NO_OVERLAP)
      (ASSUME `frontier(outside S) = (S:real^3->bool)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(f:real^3->real^3) x IN inside S` MP_TAC THENL
     [ASM SET_TAC[];
      UNDISCH_TAC `(f:real^3->real^3) x IN outside S` THEN
      UNDISCH_TAC `inside S INTER outside S:real^3->bool = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(IMAGE (f:real^3->real^3) (annulus (&1 / &2) r) SUBSET outside S /\
                  IMAGE f (annulus r (&2)) SUBSET outside S)` ASSUME_TAC THENL
   [STRIP_TAC THEN
    USE_THEN "meet" (MP_TAC o C MATCH_MP (CONJ (ISPEC `S:real^3->bool` INSIDE_NO_OVERLAP)
      (ASSUME `frontier(inside S) = (S:real^3->bool)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(f:real^3->real^3) x IN outside S` MP_TAC THENL
     [ASM SET_TAC[];
      UNDISCH_TAC `(f:real^3->real^3) x IN inside S` THEN
      UNDISCH_TAC `inside S INTER outside S:real^3->bool = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SET_RULE `!A w. (!x. x IN A ==> (f:real^3->real^3) x IN w) <=>
                              IMAGE f A SUBSET w`] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The inversion x |-> x / |x|^2 of the neck annulus                         *)
(* (SMT_DIFFEO_INVERSION_ANNULUS); f o inv is a neck with the same central   *)
(* sphere and the two halves swapped.                                         *)
(* ------------------------------------------------------------------------- *)

let SCH1_INV_LT_IFF = prove
 (`!a t. &0 < a /\ &0 < t ==> (inv a < inv t <=> t < a)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LT] THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_INV2 THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC REAL_LT_INV2 THEN ASM_REWRITE_TAC[]]);;

let SCH1_INV_ARITH = prove
 (`!t. (&1 / &2 < t /\ t < &1 ==> &1 < inv t /\ inv t < &2) /\
       (&1 < t /\ t < &2 ==> &1 / &2 < inv t /\ inv t < &1)`,
  GEN_TAC THEN CONJ_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `&0 < t` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC]) THEN
  (SUBGOAL_THEN `&1 / &2 = inv(&2) /\ &2 = inv(&1 / &2) /\ &1 = inv(&1)`
   (fun th -> ONCE_REWRITE_TAC[th]) THENL
   [CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC]) THEN
  ASM_SIMP_TAC[SCH1_INV_LT_IFF; REAL_ARITH `&0 < &2`; REAL_ARITH `&0 < &1 / &2`;
               REAL_LT_01] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN ASM_REAL_ARITH_TAC);;

let SCH1_INV_HALVES = prove
 (`!x:real^3.
        (x IN annulus (&1 / &2) (&1) ==> inv(norm x pow 2) % x IN annulus (&1) (&2)) /\
        (x IN annulus (&1) (&2) ==> inv(norm x pow 2) % x IN annulus (&1 / &2) (&1)) /\
        (x IN sphere(vec 0,&1) ==> inv(norm x pow 2) % x = x)`,
  GEN_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM; IN_SPHERE_0] THEN
  REPEAT CONJ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_INVERSION_NORM] THEN
    MATCH_MP_TAC(CONJUNCT1(SPEC `norm(x:real^3)` SCH1_INV_ARITH)) THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NORM_POS_LT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[SMT_INVERSION_NORM] THEN
    MATCH_MP_TAC(CONJUNCT2(SPEC `norm(x:real^3)` SCH1_INV_ARITH)) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID]]);;

let SCH1_NECK_INV = prove
 (`!f f':real^3->real^3.
        sch_neck f f'
        ==> sch_neck (\x. f(inv(norm x pow 2) % x)) (\y. inv(norm(f' y) pow 2) % f' y) /\
            IMAGE (\x. f(inv(norm x pow 2) % x)) (sphere(vec 0,&1)) =
            IMAGE f (sphere(vec 0,&1))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPECL [`&1 / &2`; `&2`]
    (INST_TYPE [`:3`,`:N`] SMT_DIFFEO_INVERSION_ANNULUS)) THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN DISCH_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[sch_neck] THEN
    SUBGOAL_THEN `(\x:real^3. (f:real^3->real^3)(inv(norm x pow 2) % x)) =
                  f o (\x. inv(norm x pow 2) % x) /\
                  (\y:real^3. inv(norm((f':real^3->real^3) y) pow 2) % f' y) =
                  (\x. inv(norm x pow 2) % x) o f'` (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    REWRITE_TAC[IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE (\x:real^3. inv(norm x pow 2) % x) (annulus (&1 / &2) (&2)) =
                  annulus (&1 / &2) (&2)` SUBST1_TAC THENL
     [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sch_neck (f:real^3->real^3) f'` THEN REWRITE_TAC[sch_neck];
    MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> g x = (f:real^3->real^3) x)
                           ==> IMAGE g s = IMAGE f s`) THEN
    SIMP_TAC[SCH1_INV_HALVES]]);;

(* ------------------------------------------------------------------------- *)
(* Embeddings g of the shell 1/2 < |x| < 1 + eta that fix the                *)
(* unit sphere pointwise and preserve its sides.  Their derivative is the     *)
(* identity on tangent vectors and has positive normal component.            *)
(* ------------------------------------------------------------------------- *)

(* Derivative of x / |x| (same statement as BEL_NORMALIZE_HAS_DERIVATIVE of  *)
(* pc_an_beltrami, reproved here to avoid that closure).                    *)

let SCH1_NORMALIZE_HAS_DERIVATIVE = prove
 (`!y:real^N. ~(y = vec 0)
        ==> ((\z. inv(norm z) % z) has_derivative
             (\h. inv(norm y) % h - ((y dot h) / norm y pow 3) % y)) (at y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(y:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((lift o (\z:real^N. inv(norm z))) has_derivative
     (lift o (\h. --((y dot h) / norm y pow 3)))) (at y)`
  ASSUME_TAC THENL
   [MP_TAC(INST [`norm(y:real^N) pow 2`,`s:real`]
      (DISCH_ALL(REAL_DIFF_CONV `((\s. inv(sqrt s)) has_real_derivative f') (atreal s)`))) THEN
    ASM_SIMP_TAC[POW_2_SQRT; NORM_POS_LE; REAL_LT_IMP_NZ; REAL_POW_LT] THEN
    REWRITE_TAC[HAS_REAL_FRECHET_DERIVATIVE_AT] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `y:real^N` HAS_DERIVATIVE_SQNORM_AT) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\x:real^N. lift(norm x pow 2)`;
                   `lift o (\s. inv(sqrt s)) o drop`;
                   `\x:real^N. &2 % lift(y dot x)`;
                   `\x:real^1. (--(&1 * inv(&2 * norm(y:real^N))) / norm y pow 2) % x`;
                   `y:real^N`] DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN BINOP_TAC THEN
    REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP] THEN X_GEN_TAC `x:real^N` THENL
     [SIMP_TAC[POW_2_SQRT; NORM_POS_LE];
      REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM LIFT_CMUL; LIFT_EQ] THEN
      UNDISCH_TAC `&0 < norm(y:real^N)` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^N. inv(norm z)`; `\h:real^N. --((y dot h) / norm y pow 3)`;
                 `\z:real^N. z`; `\h:real^N. h`; `y:real^N`] HAS_DERIVATIVE_MUL_AT) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_THM_TAC THEN AP_TERM_TAC THEN
  REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC);;

(* Shell embeddings fixing the unit sphere and preserving its sides.          *)

let sch1_shell_map = new_definition
 `sch1_shell_map (g:real^3->real^3) eta <=>
    &0 < eta /\ eta < &1 / &4 /\
    smooth_map_on (annulus (&1 / &2) (&1 + eta)) g /\
    (!x y. x IN annulus (&1 / &2) (&1 + eta) /\ y IN annulus (&1 / &2) (&1 + eta) /\
           g x = g y ==> x = y) /\
    (!x h. x IN annulus (&1 / &2) (&1 + eta) /\ frechet_derivative g (at x) h = vec 0
           ==> h = vec 0) /\
    (!x. x IN sphere(vec 0,&1) ==> g x = x) /\
    (!x. x IN annulus (&1 / &2) (&1) ==> norm(g x) < &1) /\
    (!x. x IN annulus (&1) (&1 + eta) ==> &1 < norm(g x))`;;

let SCH1_SHELL_HAS_DERIVATIVE = prove
 (`!g:real^3->real^3 eta x.
        sch1_shell_map g eta /\ x IN annulus (&1 / &2) (&1 + eta)
        ==> (g has_derivative frechet_derivative g (at x)) (at x) /\
            linear(frechet_derivative g (at x))`,
  REWRITE_TAC[sch1_shell_map] THEN REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`annulus (&1 / &2) (&1 + eta):real^3->bool`; `g:real^3->real^3`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ASM_SIMP_TAC[OPEN_ANNULUS];
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `annulus (&1 / &2) (&1 + eta):real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS]]);;

let SCH1_SPHERE_IN_SHELL = prove
 (`!eta x:real^3. &0 < eta /\ x IN sphere(vec 0,&1) ==> x IN annulus (&1 / &2) (&1 + eta)`,
  REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  ASM_REAL_ARITH_TAC);;

(* The derivative at the sphere is the identity on tangent vectors.          *)

let SCH1_SHELL_TANGENT = prove
 (`!g:real^3->real^3 eta p h.
        sch1_shell_map g eta /\ p IN sphere(vec 0,&1) /\ p dot h = &0
        ==> frechet_derivative g (at p) h = h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(p:real^3) = &1 /\ ~(p:real^3 = vec 0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[GSYM NORM_POS_LT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eta` ASSUME_TAC THENL
   [ASM_MESON_TAC[sch1_shell_map]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `eta:real`; `p:real^3`] SCH1_SHELL_HAS_DERIVATIVE) THEN
  ASM_SIMP_TAC[SCH1_SPHERE_IN_SHELL] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SCH1_NORMALIZE_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[REAL_INV_1; REAL_POW_ONE; REAL_DIV_1; VECTOR_MUL_LID] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(g:real^3->real^3)(inv(norm p) % p) = p` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID] THEN
    ASM_MESON_TAC[sch1_shell_map];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^3. inv(norm z) % z`; `g:real^3->real^3`;
                 `\h:real^3. h - (p dot h) % p`; `frechet_derivative (g:real^3->real^3) (at p)`;
                 `p:real^3`] DIFF_CHAIN_AT) THEN
  ASM_REWRITE_TAC[REAL_INV_1; VECTOR_MUL_LID] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `((\z:real^3. inv(norm z) % z) has_derivative
                 (frechet_derivative (g:real^3->real^3) (at p) o (\h. h - (p dot h) % p))) (at p)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`(g:real^3->real^3) o (\z. inv(norm z) % z)`; `&1 / &2`] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `~(z:real^3 = vec 0)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `dist(vec 0:real^3,p) < &1 / &2` THEN
      ASM_REWRITE_TAC[DIST_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `sch1_shell_map (g:real^3->real^3) eta` THEN
    REWRITE_TAC[sch1_shell_map] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^3. inv(norm z) % z`;
                 `frechet_derivative (g:real^3->real^3) (at p) o (\h. h - (p dot h) % p)`;
                 `\h:real^3. h - (p dot h) % p`; `p:real^3`] FRECHET_DERIVATIVE_UNIQUE_AT) THEN
  ASM_REWRITE_TAC[FUN_EQ_THM; o_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `h:real^3`) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_SUB_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Positive normal component of the derivative of a shell map                *)
(* at the sphere, uniform bounds, and injectivity of the linear isotopy      *)
(* (1 - a) x + a g x on a thin shell for all a in [0,1].                     *)
(* ------------------------------------------------------------------------- *)

let SCH1_SHELL_NORMAL = prove
 (`!g:real^3->real^3 eta p.
        sch1_shell_map g eta /\ p IN sphere(vec 0,&1)
        ==> &0 < p dot frechet_derivative g (at p) p`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(p:real^3) = &1 /\ ~(p:real^3 = vec 0) /\ p dot p = &1`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[GSYM NORM_POS_LT; GSYM NORM_POW_2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sch1_shell_map]) THEN
  ABBREV_TAC `D = frechet_derivative (g:real^3->real^3) (at p)` THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `eta:real`; `p:real^3`] SCH1_SHELL_HAS_DERIVATIVE) THEN
  ASM_SIMP_TAC[SCH1_SPHERE_IN_SHELL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^3->real^3) p = p` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x:real^3. x IN sphere(vec 0,&1) ==> g x = x`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= p dot (D:real^3->real^3) p` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\z:real^3. lift(norm((g:real^3->real^3) z) pow 2)`;
                   `\h:real^3. &2 % lift(p dot (D:real^3->real^3) h)`; `p:real^3`;
                   `segment[p:real^3,(&1 + eta / &2) % p]`; `1`; `&1`]
      DIFFERENTIAL_COMPONENT_POS_AT_MINIMUM) THEN
    REWRITE_TAC[DIMINDEX_1; ARITH; ENDS_IN_SEGMENT; CONVEX_SEGMENT; REAL_LT_01] THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
        MP_TAC(ISPECL [`g:real^3->real^3`; `\y:real^3. lift(norm y pow 2)`;
                       `D:real^3->real^3`; `\x:real^3. &2 % lift((g:real^3->real^3) p dot x)`;
                       `p:real^3`] DIFF_CHAIN_AT) THEN
        ASM_REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT; o_DEF];
        ALL_TAC] THEN
      X_GEN_TAC `w:real^3` THEN REWRITE_TAC[IN_INTER; IN_SEGMENT] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) (K ALL_TAC)) THEN
      ASM_REWRITE_TAC[LIFT_COMPONENT] THEN
      SUBGOAL_THEN `(&1 - u) % p + u % (&1 + eta / &2) % p:real^3 =
                    (&1 + u * eta / &2) % p` SUBST1_TAC THENL
       [REWRITE_TAC[VECTOR_MUL_ASSOC; GSYM VECTOR_ADD_RDISTRIB] THEN
        AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `u = &0` THENL
       [ASM_REWRITE_TAC[REAL_MUL_LZERO; REAL_ADD_RID; VECTOR_MUL_LID; REAL_LE_REFL];
        ALL_TAC] THEN
      SUBGOAL_THEN `&1 < norm((g:real^3->real^3)((&1 + u * eta / &2) % p))` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!x:real^3. x IN annulus (&1) (&1 + eta) ==> &1 < norm((g:real^3->real^3) x)`)
              (concl th))) THEN
        ASM_REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL; REAL_MUL_RID] THEN
        SUBGOAL_THEN `&0 < u` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `&0 < u * eta / &2 /\ u * eta / &2 <= eta / &2` MP_TAC THENL
         [CONJ_TAC THENL
           [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
            GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
            MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC];
          ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN
      SPEC_TAC(`norm((g:real^3->real^3)((&1 + u * eta / &2) % p))`,`t:real`) THEN
      GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
      MP_TAC(SPECL [`2`; `&1`; `t:real`] REAL_POW_LT2) THEN
      ASM_REWRITE_TAC[ARITH] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC;
      DISCH_THEN(MP_TAC o SPEC `(&1 + eta / &2) % p:real^3`) THEN
      REWRITE_TAC[ENDS_IN_SEGMENT; VECTOR_ARITH `(&1 + e) % p - p:real^3 = e % p`] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_CMUL th]) THEN
      REWRITE_TAC[VECTOR_MUL_COMPONENT; LIFT_COMPONENT; DOT_RMUL] THEN
      DISCH_TAC THEN MATCH_MP_TAC REAL_LE_LCANCEL_IMP THEN
      EXISTS_TAC `&2 * eta / &2` THEN REWRITE_TAC[REAL_MUL_RZERO] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]]];
    ALL_TAC] THEN
  REWRITE_TAC[REAL_LT_LE] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `!h:real^3. p dot (D:real^3->real^3) h = &0` ASSUME_TAC THENL
   [X_GEN_TAC `h:real^3` THEN
    SUBGOAL_THEN `h:real^3 = (h - (p dot h) % p) + (p dot h) % p` SUBST1_TAC THENL
     [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
    SUBGOAL_THEN `(D:real^3->real^3)(h - (p dot h) % p) = h - (p dot h) % p`
    SUBST1_TAC THENL
     [EXPAND_TAC "D" THEN MATCH_MP_TAC SCH1_SHELL_TANGENT THEN
      EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[DOT_RSUB; DOT_RMUL] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[DOT_RADD; DOT_RSUB; DOT_RMUL] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `D:real^3->real^3` LINEAR_INJECTIVE_IMP_SURJECTIVE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN DISCH_TAC THEN
    ONCE_REWRITE_TAC[GSYM VECTOR_SUB_EQ] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x h. x IN annulus (&1 / &2) (&1 + eta) /\
                               frechet_derivative (g:real^3->real^3) (at x) h = vec 0
                               ==> h = vec 0`) (concl th))) THEN
    EXISTS_TAC `p:real^3` THEN ASM_SIMP_TAC[SCH1_SPHERE_IN_SHELL] THEN
    ASM_SIMP_TAC[LINEAR_SUB; VECTOR_SUB_REFL];
    DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^3` MP_TAC) THEN
    DISCH_THEN(MP_TAC o AP_TERM `\v:real^3. p dot v`) THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Mean value bounds on segments, Lipschitz bounds for the                   *)
(* derivative, and the uniform constants of a shell map on the closed shell *)
(* 1 - eta/2 <= |x| <= 1 + eta/2.                                            *)
(* ------------------------------------------------------------------------- *)

let SCH1_MVT = prove
 (`!ff:real^3->real^3 s x y B.
        open s /\ segment[x,y] SUBSET s /\ (!z. z IN s ==> ff differentiable at z) /\
        (!z k. z IN segment[x,y] ==> norm(frechet_derivative ff (at z) k) <= B * norm k)
        ==> norm(ff x - ff y) <= B * norm(x - y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`ff:real^3->real^3`; `\z:real^3. frechet_derivative (ff:real^3->real^3) (at z)`;
                 `segment[x:real^3,y]`; `B:real`] DIFFERENTIABLE_BOUND) THEN
  REWRITE_TAC[CONVEX_SEGMENT] THEN ANTS_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    (SUBGOAL_THEN `(ff:real^3->real^3) differentiable at z` ASSUME_TAC THENL
      [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC]) THENL
     [MATCH_MP_TAC HAS_DERIVATIVE_AT_WITHIN THEN
      ASM_REWRITE_TAC[GSYM FRECHET_DERIVATIVE_WORKS];
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP LINEAR_FRECHET_DERIVATIVE) THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP ONORM_LE_EQ th]) THEN
      ASM_SIMP_TAC[]];
    DISCH_THEN(MP_TAC o SPECL [`x:real^3`; `y:real^3`]) THEN
    REWRITE_TAC[ENDS_IN_SEGMENT]]);;

(* Lipschitz bound for the derivative along segments in a compact set.        *)

let SCH1_DERIV_LIP = prove
 (`!g:real^3->real^3 s K.
        open s /\ smooth_map_on s g /\ compact K /\ K SUBSET s
        ==> ?B. &0 < B /\
                !x y h. segment[x,y] SUBSET K
                        ==> norm(frechet_derivative g (at y) h -
                                 frechet_derivative g (at x) h)
                            <= B * norm(y - x) * norm h`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!j. ?B. &0 < B /\
            !x y. segment[x,y] SUBSET K
                  ==> norm(frechet_derivative (g:real^3->real^3) (at y) (basis j) -
                           frechet_derivative g (at x) (basis j)) <= B * norm(y - x)`
  MP_TAC THENL
   [X_GEN_TAC `j:num` THEN
    MP_TAC(ISPECL [`\y. frechet_derivative (g:real^3->real^3) (at y) (basis j)`;
                   `s:real^3->bool`; `K:real^3->bool`] SCH3_DERIV_BOUND) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `B:real` THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\y. frechet_derivative (g:real^3->real^3) (at y) (basis j)`;
                   `s:real^3->bool`; `y:real^3`; `x:real^3`; `B:real`] SCH1_MVT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM SET_TAC[];
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^3->bool` THEN
      ASM_SIMP_TAC[SMOOTH_MAP_ON_FRECHET_DERIVATIVE];
      MAP_EVERY X_GEN_TAC [`z:real^3`; `k:real^3`] THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(z:real^3) IN segment[y,x]` THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:num->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(b:num->real) 1 + b 2 + b 3` THEN
  CONJ_TAC THENL [ASM_MESON_TAC[REAL_LT_ADD]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `h:real^3`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^3) IN s /\ (y:real^3) IN s` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:real^3`; `y:real^3`] ENDS_IN_SEGMENT) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(frechet_derivative (g:real^3->real^3) (at y)) /\
                linear(frechet_derivative (g:real^3->real^3) (at x))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN EXISTS_TAC `s:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!L:real^3->real^3. linear L
                ==> L h = h$1 % L(basis 1) + h$2 % L(basis 2) + h$3 % L(basis 3)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    ASM_SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL] THEN
    REWRITE_TAC[DIMINDEX_3; VSUM_3];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `linear(frechet_derivative (g:real^3->real^3) (at y))`)]) THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
    `linear(frechet_derivative (g:real^3->real^3) (at x))`)]) THEN
  REWRITE_TAC[VECTOR_ARITH
   `(a % u + b % v + c % w) - (a % u' + b % v' + c % w'):real^3 =
    a % (u - u') + b % (v - v') + c % (w - w')`] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `abs((h:real^3)$1) * (b 1 * norm(y - x:real^3)) +
              abs(h$2) * (b 2 * norm(y - x)) + abs(h$3) * (b 3 * norm(y - x))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH
     `norm(x:real^3) <= a /\ norm(y:real^3) <= b /\ norm(z:real^3) <= c
      ==> norm(x + y + z) <= a + b + c`) THEN
    REWRITE_TAC[NORM_MUL] THEN REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN
    ASM_SIMP_TAC[REAL_ABS_POS];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= (b:num->real) 1 * norm(y - x:real^3) /\
                &0 <= (b:num->real) 2 * norm(y - x:real^3) /\
                &0 <= (b:num->real) 3 * norm(y - x:real^3)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_MESON_TAC[REAL_LT_IMP_LE; NORM_POS_LE];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `norm(h:real^3) * ((b:num->real) 1 * norm(y - x:real^3)) +
              norm h * (b 2 * norm(y - x)) + norm h * (b 3 * norm(y - x))` THEN
  CONJ_TAC THENL
   [REPEAT(MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC) THEN
    MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[COMPONENT_LE_NORM];
    REAL_ARITH_TAC]);;

(* The closed working shell.                                                  *)

let SCH1_CSHELL = prove
 (`!eta. &0 < eta /\ eta < &1 / &4
         ==> compact(cball(vec 0:real^3,&1 + eta / &2) DIFF ball(vec 0,&1 - eta / &2)) /\
             cball(vec 0:real^3,&1 + eta / &2) DIFF ball(vec 0,&1 - eta / &2) SUBSET
             annulus (&1 / &2) (&1 + eta) /\
             sphere(vec 0:real^3,&1) SUBSET
             cball(vec 0,&1 + eta / &2) DIFF ball(vec 0,&1 - eta / &2) /\
             !x:real^3. x IN cball(vec 0,&1 + eta / &2) DIFF ball(vec 0,&1 - eta / &2) <=>
                        &1 - eta / &2 <= norm x /\ norm x <= &1 + eta / &2`,
  GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; annulus; IN_ELIM_THM;
              IN_SPHERE_0; REAL_NOT_LT] THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let SPDR21_SHELL_DOT_SMOOTH = prove
 (`!(g:real^3->real^3) (u:real^3->bool).
     open u /\
     smooth_map_on u (\p:real^3. frechet_derivative g (at p) (basis 1)) /\
     smooth_map_on u (\p:real^3. frechet_derivative g (at p) (basis 2)) /\
     smooth_map_on u (\p:real^3. frechet_derivative g (at p) (basis 3))
     ==> smooth_map_on u
           (\p:real^3. lift(p dot (p$1 % frechet_derivative g (at p) (basis 1) +
                                   p$2 % frechet_derivative g (at p) (basis 2) +
                                   p$3 % frechet_derivative g (at p) (basis 3))))`,
  REPEAT STRIP_TAC THEN SCH3_SMOOTH_TAC);;

(* Uniform constants of a shell map.                                          *)

let SCH1_SHELL_BOUNDS = prove
 (`!g:real^3->real^3 eta.
        sch1_shell_map g eta
        ==> ?B1 B2 lam.
              &0 < B1 /\ &0 < B2 /\ &0 < lam /\
              (!z h. z IN cball(vec 0,&1 + eta / &2) DIFF ball(vec 0,&1 - eta / &2)
                     ==> norm(frechet_derivative g (at z) h) <= B1 * norm h) /\
              (!x y h. segment[x,y] SUBSET
                       cball(vec 0,&1 + eta / &2) DIFF ball(vec 0,&1 - eta / &2)
                       ==> norm(frechet_derivative g (at y) h -
                                frechet_derivative g (at x) h)
                           <= B2 * norm(y - x) * norm h) /\
              (!p. p IN sphere(vec 0,&1) ==> lam <= p dot frechet_derivative g (at p) p)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sch1_shell_map]) THEN
  MP_TAC(SPEC `eta:real` SCH1_CSHELL) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `annulus (&1 / &2) (&1 + eta):real^3->bool`;
                 `cball(vec 0:real^3,&1 + eta / &2) DIFF ball(vec 0,&1 - eta / &2)`]
    SCH3_DERIV_BOUND) THEN
  ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `annulus (&1 / &2) (&1 + eta):real^3->bool`;
                 `cball(vec 0:real^3,&1 + eta / &2) DIFF ball(vec 0,&1 - eta / &2)`]
    SCH1_DERIV_LIP) THEN
  ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:real` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`B1:real`; `B2:real`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!p:real^3. p IN annulus (&1 / &2) (&1 + eta)
               ==> frechet_derivative (g:real^3->real^3) (at p) p =
                   p$1 % frechet_derivative g (at p) (basis 1) +
                   p$2 % frechet_derivative g (at p) (basis 2) +
                   p$3 % frechet_derivative g (at p) (basis 3)`
  (LABEL_TAC "SPDR21_EXP") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `linear(frechet_derivative (g:real^3->real^3) (at p))` ASSUME_TAC THENL
     [ASM_MESON_TAC[SCH1_SHELL_HAS_DERIVATIVE]; ALL_TAC] THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM BASIS_EXPANSION] THEN
    SIMP_TAC[LINEAR_VSUM; FINITE_NUMSEG; o_DEF; LINEAR_CMUL;
             ASSUME `linear(frechet_derivative (g:real^3->real^3) (at p))`] THEN
    REWRITE_TAC[DIMINDEX_3; VSUM_3];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(lift o (\p:real^3. p dot frechet_derivative (g:real^3->real^3) (at p) p))
    continuous_on sphere(vec 0,&1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `annulus (&1 / &2) (&1 + eta):real^3->bool` THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[SCH1_SPHERE_IN_SHELL]] THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\p:real^3. lift(p dot (p$1 % frechet_derivative (g:real^3->real^3) (at p) (basis 1) +
                                       p$2 % frechet_derivative g (at p) (basis 2) +
                                       p$3 % frechet_derivative g (at p) (basis 3)))` THEN
    CONJ_TAC THENL [USE_THEN "SPDR21_EXP" (fun th -> SIMP_TAC[o_THM; th]); ALL_TAC] THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN
    SUBGOAL_THEN `open(annulus (&1 / &2) (&1 + eta):real^3->bool)` ASSUME_TAC THENL
     [REWRITE_TAC[OPEN_ANNULUS]; ALL_TAC] THEN
    SUBGOAL_THEN
     `smooth_map_on (annulus (&1 / &2) (&1 + eta))
        (\p:real^3. frechet_derivative (g:real^3->real^3) (at p) (basis 1)) /\
      smooth_map_on (annulus (&1 / &2) (&1 + eta))
        (\p:real^3. frechet_derivative (g:real^3->real^3) (at p) (basis 2)) /\
      smooth_map_on (annulus (&1 / &2) (&1 + eta))
        (\p:real^3. frechet_derivative (g:real^3->real^3) (at p) (basis 3))`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_FRECHET_DERIVATIVE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC SPDR21_SHELL_DOT_SMOOTH THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\p:real^3. p dot frechet_derivative (g:real^3->real^3) (at p) p`;
                 `sphere(vec 0:real^3,&1)`] CONTINUOUS_ATTAINS_INF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_SPHERE; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `p0:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p0 dot frechet_derivative (g:real^3->real^3) (at p0) p0` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH1_SHELL_NORMAL THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A uniform lower bound for the derivatives of the linear                   *)
(* isotopy at the sphere.                                                     *)
(* ------------------------------------------------------------------------- *)

let SCH1_SHELL_UNIFORM = prove
 (`!g:real^3->real^3 eta B1 lam.
        sch1_shell_map g eta /\ &0 < B1 /\ &0 < lam /\
        (!z h. z IN cball(vec 0,&1 + eta / &2) DIFF ball(vec 0,&1 - eta / &2)
               ==> norm(frechet_derivative g (at z) h) <= B1 * norm h) /\
        (!p. p IN sphere(vec 0,&1) ==> lam <= p dot frechet_derivative g (at p) p)
        ==> ?m. &0 < m /\ m <= &1 / &2 /\
                !p a h. p IN sphere(vec 0,&1) /\ &0 <= a /\ a <= &1
                        ==> m * norm h <=
                            norm((&1 - a) % h + a % frechet_derivative g (at p) h)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "B1") (LABEL_TAC "lam"))))) THEN
  ABBREV_TAC `c = inv(&2 * (&2 + B1))` THEN
  ABBREV_TAC `mm = min (&1) lam` THEN
  SUBGOAL_THEN `&0 < c /\ c * (&2 + B1) = &1 / &2 /\ &0 < mm /\ mm <= &1 /\ mm <= lam`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN EXPAND_TAC "mm" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < B1` THEN CONV_TAC REAL_FIELD;
      ASM_REAL_ARITH_TAC; REAL_ARITH_TAC; REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `c * mm <= &1 / &4` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= c * B1` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `c <= &1 / &4` ASSUME_TAC THENL
     [UNDISCH_TAC `c * (&2 + B1) = &1 / &2` THEN UNDISCH_TAC `&0 <= c * B1` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `c * &1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `c * mm` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:real^3`; `a:real`; `h:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(p:real^3) = &1 /\ p dot p = &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[GSYM NORM_POW_2] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < eta /\ eta < &1 / &4` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[sch1_shell_map]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN cball(vec 0,&1 + eta / &2) DIFF ball(vec 0,&1 - eta / &2)`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `eta:real` SCH1_CSHELL) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `eta:real`; `p:real^3`] SCH1_SHELL_HAS_DERIVATIVE) THEN
  ASM_SIMP_TAC[SCH1_SPHERE_IN_SHELL] THEN STRIP_TAC THEN
  ABBREV_TAC `D = frechet_derivative (g:real^3->real^3) (at p)` THEN
  ABBREV_TAC `s = (p:real^3) dot h` THEN
  ABBREV_TAC `v = (D:real^3->real^3) p` THEN
  SUBGOAL_THEN `(D:real^3->real^3)(h - s % p) = h - s % p` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN MATCH_MP_TAC SCH1_SHELL_TANGENT THEN EXISTS_TAC `eta:real` THEN
    ASM_REWRITE_TAC[DOT_RSUB; DOT_RMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - a) % h + a % (D:real^3->real^3) h =
                (h - s % p) + s % ((&1 - a) % p + a % v)` SUBST1_TAC THENL
   [SUBGOAL_THEN `(D:real^3->real^3) h = (h - s % p) + s % v` SUBST1_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [VECTOR_ARITH `h:real^3 = (h - s % p) + s % p`] THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th; MATCH_MP LINEAR_CMUL th]) THEN
      ASM_REWRITE_TAC[];
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(v:real^3) <= B1` ASSUME_TAC THENL
   [EXPAND_TAC "v" THEN EXPAND_TAC "D" THEN
    USE_THEN "B1" (MP_TAC o C MATCH_MP (ASSUME
      `(p:real^3) IN cball(vec 0,&1 + eta / &2) DIFF ball(vec 0,&1 - eta / &2)`) o
      SPECL [`p:real^3`; `p:real^3`]) THEN
    ASM_REWRITE_TAC[REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `mm <= (&1 - a) + a * ((p:real^3) dot v)` ASSUME_TAC THENL
   [SUBGOAL_THEN `lam <= p dot (v:real^3)` ASSUME_TAC THENL
     [EXPAND_TAC "v" THEN EXPAND_TAC "D" THEN USE_THEN "lam" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 - a) * mm + a * mm` THEN CONJ_TAC THENL
     [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `c * norm(h:real^3) <= abs s` THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `abs(p dot ((h - s % p) + s % ((&1 - a) % p + a % v:real^3)))` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `p dot ((h - s % p) + s % ((&1 - a) % p + a % v:real^3)) =
                    s * ((&1 - a) + a * ((p:real^3) dot v))` SUBST1_TAC THENL
       [REWRITE_TAC[DOT_RADD; DOT_RSUB; DOT_RMUL] THEN ASM_REWRITE_TAC[] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      REWRITE_TAC[REAL_ABS_MUL] THEN
      SUBGOAL_THEN `abs((&1 - a) + a * ((p:real^3) dot v)) = (&1 - a) + a * ((p:real^3) dot v)`
      SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `abs s * mm` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c * norm(h:real^3)) * mm` THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]];
      MP_TAC(ISPECL [`p:real^3`; `(h - s % p) + s % ((&1 - a) % p + a % v:real^3)`]
        NORM_CAUCHY_SCHWARZ_ABS) THEN
      ASM_REWRITE_TAC[REAL_MUL_LID]];
    ALL_TAC] THEN
  ABBREV_TAC `w = (&1 - a) % p + a % v:real^3` THEN
  SUBGOAL_THEN `norm(w:real^3) <= &1 + B1` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN
    MATCH_MP_TAC(NORM_ARITH `norm(x:real^3) <= a /\ norm(y:real^3) <= b
                             ==> norm(x + y) <= a + b`) THEN
    REWRITE_TAC[NORM_MUL] THEN ASM_REWRITE_TAC[REAL_MUL_RID] THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * B1` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[NORM_POS_LE; REAL_ABS_POS] THEN
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(h:real^3) <= norm(h - s % p) + abs s` ASSUME_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `norm(q:real^3) = b ==> norm(h) <= norm(h - q) + b`) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `norm(h - s % p) - abs s * norm(w:real^3) <=
                norm((h - s % p) + s % w:real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC(NORM_ARITH `norm(y:real^3) = b ==> norm x - b <= norm(x + y)`) THEN
    REWRITE_TAC[NORM_MUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `abs s * norm(w:real^3) <= abs s * (&1 + B1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS]; ALL_TAC] THEN
  SUBGOAL_THEN `abs s * (&2 + B1) <= norm(h:real^3) / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(c * norm(h:real^3)) * (&2 + B1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_EQ_IMP_LE THEN
      UNDISCH_TAC `c * (&2 + B1) = &1 / &2` THEN CONV_TAC REAL_FIELD];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c * mm) * norm(h:real^3) <= norm h / &2` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(&1 / &4) * norm(h:real^3)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      MP_TAC(ISPEC `h:real^3` NORM_POS_LE) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(c * mm) * norm(h:real^3) <= norm h / &2`;
    `abs s * (&2 + B1) <= norm(h:real^3) / &2`;
    `abs s * norm(w:real^3) <= abs s * (&1 + B1)`;
    `norm(h - s % p) - abs s * norm(w:real^3) <= norm((h - s % p) + s % w:real^3)`;
    `norm(h:real^3) <= norm(h - s % p) + abs s`] THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The linear isotopy (1 - a) x + a g x of a shell map is an                 *)
(* injective immersion on a thin shell, uniformly in a in [0,1].             *)
(* ------------------------------------------------------------------------- *)

let SCH1_NORMALIZE_NEAR = prove
 (`!x:real^3 w. abs(norm x - &1) < w /\ w < &1
        ==> ~(x = vec 0) /\ inv(norm x) % x IN sphere(vec 0,&1) /\
            norm(x - inv(norm x) % x) = abs(norm x - &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^3)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = vec 0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM NORM_POS_LT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_SPHERE_0; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
  ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
  REWRITE_TAC[VECTOR_ARITH `x - c % x:real^3 = (&1 - c) % x`; NORM_MUL] THEN
  SUBGOAL_THEN `abs(&1 - inv(norm(x:real^3))) * norm x = abs((&1 - inv(norm x)) * norm x)`
  SUBST1_TAC THENL [ASM_SIMP_TAC[REAL_ABS_MUL; REAL_ABS_NORM]; ALL_TAC] THEN
  AP_TERM_TAC THEN UNDISCH_TAC `&0 < norm(x:real^3)` THEN CONV_TAC REAL_FIELD);;

let SCH1_FD_SUB_LINEAR = prove
 (`!g:real^3->real^3 L z.
        g differentiable at z /\ linear L
        ==> (\x. g x - L x) differentiable at z /\
            frechet_derivative (\x. g x - L x) (at z) =
            (\k. frechet_derivative g (at z) k - L k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `((\x. (g:real^3->real^3) x - L x) has_derivative
                 (\k. frechet_derivative g (at z) k - L k)) (at z)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^3->real^3`; `frechet_derivative (g:real^3->real^3) (at z)`;
                   `L:real^3->real^3`; `L:real^3->real^3`; `at (z:real^3)`]
      HAS_DERIVATIVE_SUB) THEN
    ASM_SIMP_TAC[GSYM FRECHET_DERIVATIVE_WORKS; HAS_DERIVATIVE_LINEAR];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[differentiable] THEN ASM_MESON_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN ASM_REWRITE_TAC[]]);;

let SCH1_SHELL_LINEAR_INJ = prove
 (`!g:real^3->real^3 eta.
        sch1_shell_map g eta
        ==> ?w. &0 < w /\ w <= eta / &2 /\
                !a. &0 <= a /\ a <= &1
                    ==> (!x y. x IN annulus (&1 - w) (&1 + w) /\
                               y IN annulus (&1 - w) (&1 + w) /\
                               (&1 - a) % x + a % g x = (&1 - a) % y + a % g y
                               ==> x = y) /\
                        (!x h. x IN annulus (&1 - w) (&1 + w) /\
                               (&1 - a) % h + a % frechet_derivative g (at x) h = vec 0
                               ==> h = vec 0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sch1_shell_map]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `B1:real` (X_CHOOSE_THEN `B2:real` (X_CHOOSE_THEN `lam:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (LABEL_TAC "B1") (CONJUNCTS_THEN2 (LABEL_TAC "B2")
      (LABEL_TAC "lam")))))))) o MATCH_MP SCH1_SHELL_BOUNDS) THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `eta:real`; `B1:real`; `lam:real`] SCH1_SHELL_UNIFORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "m")))) THEN
  MP_TAC(SPEC `eta:real` SCH1_CSHELL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "Cmem")))) THEN
  ABBREV_TAC `C = cball(vec 0:real^3,&1 + eta / &2) DIFF ball(vec 0,&1 - eta / &2)` THEN
  ABBREV_TAC `Q = &3 * B1 + &4` THEN
  ABBREV_TAC `w = min (eta / &2 / Q) (m / (&2 * B2 * Q))` THEN
  SUBGOAL_THEN `&4 <= Q /\ &0 < w /\ Q * w <= eta / &2 /\ B2 * Q * w <= m / &2 /\
                w <= eta / &2` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `&4 <= Q` ASSUME_TAC THENL
     [EXPAND_TAC "Q" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < eta / &2 / Q /\ &0 < m / (&2 * B2 * Q)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN CONJ_TAC THEN TRY(ASM_REAL_ARITH_TAC) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THEN TRY(REAL_ARITH_TAC) THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~(Q = &0) /\ ~(B2 = &0)` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `Q * (eta / &2 / Q) = eta / &2 /\
                  B2 * Q * (m / (&2 * B2 * Q)) = m / &2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN UNDISCH_TAC `~(Q = &0)` THEN UNDISCH_TAC `~(B2 = &0)` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `w <= eta / &2 / Q /\ w <= m / (&2 * B2 * Q) /\ &0 < w`
    STRIP_ASSUME_TAC THENL [EXPAND_TAC "w" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `Q * (eta / &2 / Q)` THEN
      CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]
                      THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B2 * Q * (m / (&2 * B2 * Q))` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `eta / &2 / Q` THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_ARITH `&4 <= Q ==> &0 < Q`] THEN
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_RID] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < Q * w /\ w <= Q * w` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
      GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* Points near a point p of the sphere stay in the closed shell. *)
  SUBGOAL_THEN `!p z:real^3. p IN sphere(vec 0,&1) /\ norm(z - p) < Q * w ==> z IN C`
  (LABEL_TAC "inC") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "C" THEN USE_THEN "Cmem" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `(p:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0] THEN
    DISCH_TAC THEN
    MP_TAC(SPEC `Q * w` (GEN `r:real`
      (NORM_ARITH `norm(z - p:real^3) < r ==> abs(norm z - norm p) < r`))) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `Q * w <= eta / &2` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!p y z:real^3. p IN sphere(vec 0,&1) /\ norm(y - p) < Q * w /\
                               norm(z - p) < Q * w ==> segment[y,z] SUBSET C`
  (LABEL_TAC "segC") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `u:real^3` THEN
    DISCH_TAC THEN USE_THEN "inC" MATCH_MP_TAC THEN EXISTS_TAC `p:real^3` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:real^3`; `Q * w`] CONVEX_BALL) THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `z:real^3`]) THEN
    REWRITE_TAC[IN_BALL; dist; SUBSET] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `u:real^3`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  (* The radial estimate |g x - x| <= (B1 + 1) |x - p|. *)
  SUBGOAL_THEN
   `!x:real^3. abs(norm x - &1) < w
               ==> norm(g x - x) <= (B1 + &1) * norm(x - inv(norm x) % x) /\
                   norm(x - inv(norm x) % x) < w`
  (LABEL_TAC "rad") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`x:real^3`; `w:real`] SCH1_NORMALIZE_NEAR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `p = inv(norm x) % x:real^3` THEN STRIP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    SUBGOAL_THEN `(g:real^3->real^3) p = p` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `norm((g:real^3->real^3) x - g p) <= B1 * norm(x - p)` ASSUME_TAC THENL
     [MATCH_MP_TAC SCH1_MVT THEN EXISTS_TAC `annulus (&1 / &2) (&1 + eta):real^3->bool` THEN
      REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `C:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "segC" MATCH_MP_TAC THEN
        EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
        ASM_REAL_ARITH_TAC;
        GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `annulus (&1 / &2) (&1 + eta):real^3->bool` THEN
        ASM_REWRITE_TAC[OPEN_ANNULUS];
        MAP_EVERY X_GEN_TAC [`z:real^3`; `k:real^3`] THEN DISCH_TAC THEN
        USE_THEN "B1" MATCH_MP_TAC THEN
        SUBGOAL_THEN `segment[x:real^3,p] SUBSET C` MP_TAC THENL
         [USE_THEN "segC" MATCH_MP_TAC THEN EXISTS_TAC `p:real^3` THEN
          ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN ASM_REAL_ARITH_TAC;
          EXPAND_TAC "C" THEN ASM SET_TAC[]]];
      ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((g:real^3->real^3) x - g p) + norm(x - p:real^3)` THEN CONJ_TAC THENL
     [REWRITE_TAC[ASSUME `(g:real^3->real^3) p = p`] THEN NORM_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* Local Lipschitz bound for g - Dg(p) on a ball around p. *)
  SUBGOAL_THEN
   `!p y z:real^3. p IN sphere(vec 0,&1) /\ norm(y - p) < Q * w /\ norm(z - p) < Q * w
      ==> norm(((g:real^3->real^3) y - frechet_derivative g (at p) y) -
               (g z - frechet_derivative g (at p) z)) <= (B2 * Q * w) * norm(y - z)`
  (LABEL_TAC "gl") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^3) IN annulus (&1 / &2) (&1 + eta)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SCH1_SPHERE_IN_SHELL]; ALL_TAC] THEN
    SUBGOAL_THEN `linear(frechet_derivative (g:real^3->real^3) (at p))` ASSUME_TAC THENL
     [ASM_MESON_TAC[SCH1_SHELL_HAS_DERIVATIVE]; ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
      [`\x:real^3. (g:real^3->real^3) x - frechet_derivative g (at p) x`;
       `annulus (&1 / &2) (&1 + eta):real^3->bool`; `y:real^3`; `z:real^3`;
       `B2 * Q * w`] SCH1_MVT)) THEN
    REWRITE_TAC[OPEN_ANNULUS] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `C:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "segC" MATCH_MP_TAC THEN
      EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `u:real^3` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `frechet_derivative (g:real^3->real^3) (at p)`;
                     `u:real^3`] SCH1_FD_SUB_LINEAR) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
      EXISTS_TAC `annulus (&1 / &2) (&1 + eta):real^3->bool` THEN
      ASM_REWRITE_TAC[OPEN_ANNULUS];
      MAP_EVERY X_GEN_TAC [`u:real^3`; `k:real^3`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `norm(u - p:real^3) < Q * w` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`p:real^3`; `Q * w`] CONVEX_BALL) THEN
        REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
        DISCH_THEN(MP_TAC o SPECL [`y:real^3`; `z:real^3`]) THEN
        REWRITE_TAC[IN_BALL; dist; SUBSET] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `u:real^3`) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[NORM_SUB];
        ALL_TAC] THEN
      SUBGOAL_THEN `(u:real^3) IN annulus (&1 / &2) (&1 + eta)` ASSUME_TAC THENL
       [UNDISCH_TAC `C SUBSET annulus (&1 / &2) (&1 + eta):real^3->bool` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        USE_THEN "inC" MATCH_MP_TAC THEN EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `frechet_derivative (g:real^3->real^3) (at p)`;
                     `u:real^3`] SCH1_FD_SUB_LINEAR) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
        EXISTS_TAC `annulus (&1 / &2) (&1 + eta):real^3->bool` THEN
        ASM_REWRITE_TAC[OPEN_ANNULUS];
        DISCH_THEN(SUBST1_TAC o CONJUNCT2)] THEN
      REWRITE_TAC[] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `B2 * norm(u - p:real^3) * norm(k:real^3)` THEN
      CONJ_TAC THENL
       [USE_THEN "B2" MATCH_MP_TAC THEN USE_THEN "segC" MATCH_MP_TAC THEN
        EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC[NORM_POS_LE; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE]]];
    ALL_TAC] THEN
  EXISTS_TAC `w:real` THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `a:real` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `abs(norm(x:real^3) - &1) < w /\ abs(norm(y:real^3) - &1) < w`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN annulus (&1 - w) (&1 + w)` THEN
      UNDISCH_TAC `(y:real^3) IN annulus (&1 - w) (&1 + w)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "rad" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(norm(x:real^3) - &1) < w`))) THEN
    USE_THEN "rad" (fun th -> MP_TAC(MATCH_MP th (ASSUME `abs(norm(y:real^3) - &1) < w`))) THEN
    MP_TAC(SPECL [`x:real^3`; `w:real`] SCH1_NORMALIZE_NEAR) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ABBREV_TAC `p = inv(norm x) % x:real^3` THEN
    ABBREV_TAC `q = inv(norm y) % y:real^3` THEN
    REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `&3 * (B1 + &1) * w <= norm(x - y:real^3)` THENL
     [SUBGOAL_THEN `x - y:real^3 = a % (((g:real^3->real^3) y - y) - (g x - x))`
      ASSUME_TAC THENL
       [UNDISCH_TAC `(&1 - a) % x + a % (g:real^3->real^3) x = (&1 - a) % y + a % g y` THEN
        VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `norm(x - y:real^3) <= norm((g:real^3->real^3) x - x) + norm(g y - y)`
      ASSUME_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o check (fun th ->
          is_eq(concl th) && lhs(concl th) = `x - y:real^3`)) THEN REWRITE_TAC[NORM_MUL] THEN
        MATCH_MP_TAC REAL_LE_TRANS THEN
        EXISTS_TAC `&1 * norm(((g:real^3->real^3) y - y) - (g x - x))` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN ASM_REAL_ARITH_TAC;
          REWRITE_TAC[REAL_MUL_LID] THEN NORM_ARITH_TAC];
        ALL_TAC] THEN
      SUBGOAL_THEN `(B1 + &1) * norm(x - p:real^3) <= (B1 + &1) * w /\
                    (B1 + &1) * norm(y - q:real^3) <= (B1 + &1) * w` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < (B1 + &1) * w` ASSUME_TAC THENL
       [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`&3 * (B1 + &1) * w <= norm(x - y:real^3)`;
        `norm(x - y:real^3) <= norm((g:real^3->real^3) x - x) + norm(g y - y)`;
        `norm((g:real^3->real^3) x - x) <= (B1 + &1) * norm(x - p)`;
        `norm((g:real^3->real^3) y - y) <= (B1 + &1) * norm(y - q)`;
        `(B1 + &1) * norm(x - p:real^3) <= (B1 + &1) * w`;
        `(B1 + &1) * norm(y - q:real^3) <= (B1 + &1) * w`;
        `&0 < (B1 + &1) * w`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `norm(x - p:real^3) < Q * w /\ norm(y - p:real^3) < Q * w`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(NORM_ARITH `norm(y - p:real^3) <= norm(x - y) + norm(x - p)`) THEN
      SUBGOAL_THEN `Q * w = &3 * (B1 + &1) * w + w` ASSUME_TAC THENL
       [EXPAND_TAC "Q" THEN REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `linear(frechet_derivative (g:real^3->real^3) (at p))` ASSUME_TAC THENL
     [ASM_MESON_TAC[SCH1_SHELL_HAS_DERIVATIVE; SCH1_SPHERE_IN_SHELL]; ALL_TAC] THEN
    USE_THEN "gl" (MP_TAC o SPECL [`p:real^3`; `x:real^3`; `y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "m" (MP_TAC o SPECL [`p:real^3`; `a:real`; `x - y:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `(&1 - a) % (x - y) + a % frechet_derivative (g:real^3->real^3) (at p) (x - y) =
      --(a % (((g:real^3->real^3) x - frechet_derivative g (at p) x) -
              (g y - frechet_derivative g (at p) y)))` ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_SUB th]) THEN
      UNDISCH_TAC `(&1 - a) % x + a % (g:real^3->real^3) x = (&1 - a) % y + a % g y` THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `m * norm(x - y:real^3) <= m / &2 * norm(x - y)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `norm((&1 - a) % (x - y) +
                       a % frechet_derivative (g:real^3->real^3) (at p) (x - y))` THEN
      ASM_REWRITE_TAC[NORM_NEG; NORM_MUL] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN
      EXISTS_TAC `&1 * ((B2 * Q * w) * norm(x - y:real^3))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[REAL_MUL_LID; REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC[NORM_POS_LE] THEN ASM_REWRITE_TAC[GSYM REAL_MUL_ASSOC]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM VECTOR_SUB_EQ; GSYM NORM_EQ_0] THEN
    MP_TAC(ISPEC `x - y:real^3` NORM_POS_LE) THEN
    SPEC_TAC(`norm(x - y:real^3)`,`d:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `(m / &2) * d <= &0` MP_TAC THENL
     [UNDISCH_TAC `m * d <= m / &2 * d` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `&0 <= d /\ ~(&0 < d) ==> d = &0`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < m / &2 * d` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^3`; `h:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs(norm(x:real^3) - &1) < w` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN annulus (&1 - w) (&1 + w)` THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPECL [`x:real^3`; `w:real`] SCH1_NORMALIZE_NEAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `p = inv(norm x) % x:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm(x - p:real^3) < Q * w` ASSUME_TAC THENL
   [SUBGOAL_THEN `w <= Q * w` ASSUME_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM REAL_MUL_LID] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  USE_THEN "m" (MP_TAC o SPECL [`p:real^3`; `a:real`; `h:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `norm(frechet_derivative (g:real^3->real^3) (at x) h - frechet_derivative g (at p) h)
    <= B2 * norm(x - p) * norm(h:real^3)` ASSUME_TAC THENL
   [USE_THEN "B2" MATCH_MP_TAC THEN USE_THEN "segC" MATCH_MP_TAC THEN
    EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - a) % h + a % frechet_derivative (g:real^3->real^3) (at p) h =
                a % (frechet_derivative g (at p) h - frechet_derivative g (at x) h)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(&1 - a) % h + a % frechet_derivative (g:real^3->real^3) (at x) h = vec 0` THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `m * norm(h:real^3) <= m / &2 * norm h` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN
    EXISTS_TAC `norm((&1 - a) % h + a % frechet_derivative (g:real^3->real^3) (at p) h)` THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * (B2 * norm(x - p:real^3) * norm(h:real^3))` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_MESON_TAC[NORM_SUB]];
      REWRITE_TAC[REAL_MUL_LID] THEN
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(B2 * Q * w) * norm(h:real^3)` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
        REWRITE_TAC[NORM_POS_LE; GSYM REAL_MUL_ASSOC] THEN MATCH_MP_TAC REAL_LE_LMUL THEN
        ASM_SIMP_TAC[REAL_LT_IMP_LE];
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE]]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM NORM_EQ_0] THEN
  MP_TAC(ISPEC `h:real^3` NORM_POS_LE) THEN
  SPEC_TAC(`norm(h:real^3)`,`d:real`) THEN GEN_TAC THEN REPEAT DISCH_TAC THEN
  MATCH_MP_TAC(REAL_ARITH `&0 <= d /\ ~(&0 < d) ==> d = &0`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < m / &2 * d` MP_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The isotopy of thin-shell embeddings from the identity to                 *)
(* x |-> g((3/4) x) (first the linear isotopy to g, then the radial one),    *)
(* and its extension to a diffeomorphism of R^3 (SCHI_ISOTOPY_EXTENSION_01). *)
(* ------------------------------------------------------------------------- *)

let SCH1_SCALE_IN_SHELL = prove
 (`!eta w r x:real^3.
        &0 < eta /\ eta < &1 / &4 /\ &0 < w /\ w <= eta / &2 /\
        &3 / &4 <= r /\ r <= &1 /\ x IN annulus (&1 - w) (&1 + w)
        ==> r % x IN annulus (&1 / &2) (&1 + eta)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `abs r = r` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `&3 / &4 * (&1 - w)` THEN CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL2 THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * norm(x:real^3)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      ASM_REAL_ARITH_TAC]]);;

let SCH1_HH_DERIV = prove
 (`!g:real^3->real^3 eta a r x.
        sch1_shell_map g eta /\ r % x IN annulus (&1 / &2) (&1 + eta)
        ==> ((\x. (&1 - a) % x + a % g(r % x)) has_derivative
             (\h. (&1 - a) % h + a % frechet_derivative g (at (r % x)) (r % h))) (at x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^3->real^3`; `eta:real`; `r % x:real^3`] SCH1_SHELL_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `((\x:real^3. (g:real^3->real^3)(r % x)) has_derivative
                 (\h. frechet_derivative g (at (r % x)) (r % h))) (at x)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^3. r % x`; `g:real^3->real^3`; `\h:real^3. r % h`;
                   `frechet_derivative (g:real^3->real^3) (at (r % x))`; `x:real^3`]
      DIFF_CHAIN_AT) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_DERIVATIVE_ID];
    ALL_TAC] THEN
  MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN REWRITE_TAC[HAS_DERIVATIVE_ID];
    MATCH_MP_TAC HAS_DERIVATIVE_CMUL THEN ASM_REWRITE_TAC[]]);;

let SCH1_HH_SMOOTH = prove
 (`!g:real^3->real^3 eta w.
        sch1_shell_map g eta /\ &0 < w /\ w <= eta / &2
        ==> smooth_family (annulus (&1 - w) (&1 + w))
              (\t x. (&1 - smooth_step(&2 * t)) % x +
                     smooth_step(&2 * t) %
                     g((&1 - &1 / &4 * smooth_step(&2 * t - &1)) % x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[smooth_family] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sch1_shell_map]) THEN
  ABBREV_TAC `S = (:real^1) PCROSS (annulus (&1 - w) (&1 + w):real^3->bool)` THEN
  SUBGOAL_THEN `open(S:real^(1,3)finite_sum->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN SIMP_TAC[OPEN_PCROSS; OPEN_UNIV; OPEN_ANNULUS]; ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (sndcart:real^(1,3)finite_sum->real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^(1,3)finite_sum->bool`; `\z:real^(1,3)finite_sum. z`]
      SMOOTH_MAP_ON_SNDCART_OPEN) THEN
    ASM_REWRITE_TAC[SMOOTH_MAP_ON_ID; o_DEF; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (\z:real^(1,3)finite_sum. lift(drop(fstcart z)))`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[LIFT_DROP; ETA_AX; SCHI_FSTCART_SMOOTH]; ALL_TAC] THEN
  SUBGOAL_THEN `!c d. smooth_map_on S
                  (\z:real^(1,3)finite_sum. lift(smooth_step(c * drop(fstcart z) + d)))`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN
     `(\z:real^(1,3)finite_sum. lift(smooth_step(c * drop(fstcart z) + d))) =
      (\z. (lift o smooth_step o drop) ((\z. lift(c * drop(fstcart z) + d)) z))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC SCH3_SV_COMPOSE THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; SMOOTH_STEP_SMOOTH] THEN
    SCH3_SMOOTH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on S (\z:real^(1,3)finite_sum. lift(smooth_step(&2 * drop(fstcart z)))) /\
    smooth_map_on S (\z:real^(1,3)finite_sum. lift(smooth_step(&2 * drop(fstcart z) - &1)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`&2`; `&0`]) THEN REWRITE_TAC[REAL_ADD_RID];
      FIRST_X_ASSUM(MP_TAC o SPECL [`&2`; `-- &1`]) THEN
      REWRITE_TAC[real_sub]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `smooth_map_on S (\z:real^(1,3)finite_sum.
      (g:real^3->real^3)((&1 - &1 / &4 * smooth_step(&2 * drop(fstcart z) - &1)) % sndcart z))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH3_SV_COMPOSE THEN
    EXISTS_TAC `annulus (&1 / &2) (&1 + eta):real^3->bool` THEN
    ASM_REWRITE_TAC[OPEN_ANNULUS] THEN CONJ_TAC THENL [SCH3_SMOOTH_TAC; ALL_TAC] THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_PCROSS; IN_UNIV; FSTCART_PASTECART;
                                    SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`t:real^1`; `x:real^3`] THEN DISCH_TAC THEN
    MATCH_MP_TAC SCH1_SCALE_IN_SHELL THEN EXISTS_TAC `w:real` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `&2 * drop t - &1` SMOOTH_STEP_BOUNDS) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[] THEN SCH3_SMOOTH_TAC);;

let SCH1_SHELL_ISOTOPY = prove
 (`!g:real^3->real^3 eta.
        sch1_shell_map g eta
        ==> ?w Phi Psi. &0 < w /\ w <= eta / &2 /\
                        diffeomorphism_on (:real^3) (:real^3) Phi Psi /\
                        (!x. &1 - w / &2 <= norm x /\ norm x <= &1 + w / &2
                             ==> Phi x = g((&3 / &4) % x))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [sch1_shell_map]) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `w:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "lin"))) o MATCH_MP SCH1_SHELL_LINEAR_INJ) THEN
  SUBGOAL_THEN `!r x:real^3. &3 / &4 <= r /\ r <= &1 /\ x IN annulus (&1 - w) (&1 + w)
                             ==> r % x IN annulus (&1 / &2) (&1 + eta)`
  (LABEL_TAC "sc") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SCH1_SCALE_IN_SHELL THEN EXISTS_TAC `w:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\t x. (&1 - smooth_step(&2 * t)) % x +
           smooth_step(&2 * t) % (g:real^3->real^3)((&1 - &1 / &4 * smooth_step(&2 * t - &1)) % x)`;
    `annulus (&1 - w) (&1 + w):real^3->bool`;
    `cball(vec 0:real^3,&1 + w / &2) DIFF ball(vec 0,&1 - w / &2)`; `(:real^3)`]
    SCHI_ISOTOPY_EXTENSION_01) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[OPEN_ANNULUS];
      SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_CBALL_0; IN_BALL_0; annulus; IN_ELIM_THM;
                  REAL_NOT_LT] THEN
      ASM_REAL_ARITH_TAC;
      REWRITE_TAC[OPEN_UNIV];
      MATCH_MP_TAC SCH1_HH_SMOOTH THEN EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `t <= &1 / &2` THENL
       [SUBGOAL_THEN `smooth_step(&2 * t - &1) = &0` ASSUME_TAC THENL
         [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(&1 - smooth_step(&2 * t)) % x +
                     smooth_step(&2 * t) %
                     (g:real^3->real^3)((&1 - &1 / &4 * smooth_step(&2 * t - &1)) % x) =
                     (&1 - smooth_step(&2 * t)) % y +
                     smooth_step(&2 * t) %
                     g((&1 - &1 / &4 * smooth_step(&2 * t - &1)) % y)` THEN
        ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; VECTOR_MUL_LID] THEN DISCH_TAC THEN
        USE_THEN "lin" (MP_TAC o SPEC `smooth_step(&2 * t)`) THEN
        REWRITE_TAC[SMOOTH_STEP_BOUNDS] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `smooth_step(&2 * t) = &1` ASSUME_TAC THENL
         [MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        UNDISCH_TAC `(&1 - smooth_step(&2 * t)) % x +
                     smooth_step(&2 * t) %
                     (g:real^3->real^3)((&1 - &1 / &4 * smooth_step(&2 * t - &1)) % x) =
                     (&1 - smooth_step(&2 * t)) % y +
                     smooth_step(&2 * t) %
                     g((&1 - &1 / &4 * smooth_step(&2 * t - &1)) % y)` THEN
        ASM_REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_LID] THEN
        ABBREV_TAC `r = &1 - &1 / &4 * smooth_step(&2 * t - &1)` THEN DISCH_TAC THEN
        SUBGOAL_THEN `&3 / &4 <= r /\ r <= &1` STRIP_ASSUME_TAC THENL
         [EXPAND_TAC "r" THEN MP_TAC(SPEC `&2 * t - &1` SMOOTH_STEP_BOUNDS) THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `r % x:real^3 = r % y` MP_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (term_match [] `!x y. x IN annulus (&1 / &2) (&1 + eta) /\
                                     y IN annulus (&1 / &2) (&1 + eta) /\
                                     (g:real^3->real^3) x = g y ==> x = y`) (concl th))) THEN
          ASM_REWRITE_TAC[] THEN CONJ_TAC THEN USE_THEN "sc" MATCH_MP_TAC THEN
          ASM_REWRITE_TAC[];
          REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
          SUBGOAL_THEN `~(r = &0)` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC]];
      MAP_EVERY X_GEN_TAC [`t:real`; `x:real^3`; `h:real^3`] THEN STRIP_TAC THEN
      ABBREV_TAC `a = smooth_step(&2 * t)` THEN
      ABBREV_TAC `r = &1 - &1 / &4 * smooth_step(&2 * t - &1)` THEN
      SUBGOAL_THEN `&3 / &4 <= r /\ r <= &1 /\ &0 <= a /\ a <= &1` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "r" THEN EXPAND_TAC "a" THEN
        MP_TAC(SPEC `&2 * t - &1` SMOOTH_STEP_BOUNDS) THEN
        MP_TAC(SPEC `&2 * t` SMOOTH_STEP_BOUNDS) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(r % x:real^3) IN annulus (&1 / &2) (&1 + eta)` ASSUME_TAC THENL
       [USE_THEN "sc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`g:real^3->real^3`; `eta:real`; `a:real`; `r:real`; `x:real^3`]
        SCH1_HH_DERIV) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(fun th -> UNDISCH_TAC
        `frechet_derivative (\x. (&1 - a) % x + a % (g:real^3->real^3)(r % x)) (at x) h =
         vec 0` THEN REWRITE_TAC[GSYM(MATCH_MP FRECHET_DERIVATIVE_AT th)]) THEN
      DISCH_TAC THEN ASM_CASES_TAC `t <= &1 / &2` THENL
       [SUBGOAL_THEN `r = &1` SUBST_ALL_TAC THENL
         [EXPAND_TAC "r" THEN
          SUBGOAL_THEN `smooth_step(&2 * t - &1) = &0` SUBST1_TAC THENL
           [MATCH_MP_TAC SMOOTH_STEP_0 THEN ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
          ALL_TAC] THEN
        UNDISCH_TAC `(&1 - a) % h + a % frechet_derivative (g:real^3->real^3) (at (&1 % x))
                       (&1 % h) = vec 0` THEN
        REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_TAC THEN
        USE_THEN "lin" (MP_TAC o C MATCH_MP
          (CONJ (ASSUME `&0 <= a`) (ASSUME `a <= &1`))) THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `x:real^3` THEN
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `a = &1` SUBST_ALL_TAC THENL
         [EXPAND_TAC "a" THEN MATCH_MP_TAC SMOOTH_STEP_1 THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        UNDISCH_TAC `(&1 - &1) % h + &1 % frechet_derivative (g:real^3->real^3) (at (r % x))
                       (r % h) = vec 0` THEN
        REWRITE_TAC[REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_LID] THEN
        DISCH_TAC THEN
        SUBGOAL_THEN `r % h:real^3 = vec 0` MP_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (term_match [] `!x h. x IN annulus (&1 / &2) (&1 + eta) /\
                                     frechet_derivative (g:real^3->real^3) (at x) h = vec 0
                                     ==> h = vec 0`) (concl th))) THEN
          EXISTS_TAC `r % x:real^3` THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[VECTOR_MUL_EQ_0] THEN
          SUBGOAL_THEN `~(r = &0)` (fun th -> REWRITE_TAC[th]) THEN ASM_REAL_ARITH_TAC]];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SIMP_TAC[SMOOTH_STEP_0; REAL_ARITH `&2 * &0 <= &0`; REAL_ARITH `&2 * &0 - &1 <= &0`] THEN
      REWRITE_TAC[REAL_MUL_RZERO; REAL_SUB_RZERO; VECTOR_MUL_LID; VECTOR_MUL_LZERO;
                  VECTOR_ADD_RID];
      REWRITE_TAC[IN_UNIV]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->real^3` (X_CHOOSE_THEN `Psi:real^3->real^3`
    (X_CHOOSE_THEN `L:real^3->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`w:real`; `Phi:real^3->real^3`; `Psi:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3` o check (fun th ->
    can (term_match [] `!x. x IN cball(vec 0:real^3,&1 + w / &2) DIFF ball(vec 0,&1 - w / &2)
                            ==> (Phi:real^3->real^3) x = H x`) (concl th))) THEN
  REWRITE_TAC[IN_DIFF; IN_CBALL_0; IN_BALL_0; REAL_NOT_LT] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  SIMP_TAC[SMOOTH_STEP_1; REAL_ARITH `&1 <= &2 * &1`; REAL_ARITH `&1 <= &2 * &1 - &1`] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID; VECTOR_MUL_LID]);;

(* ------------------------------------------------------------------------- *)
(* The collar in the coordinates of the ball chart c0, its                   *)
(* straightening by Smale's theorem, and the resulting shell map k1.         *)
(* ------------------------------------------------------------------------- *)

let SCH1_SHELL_NBHD = prove
 (`!U:real^3->bool.
        open U /\ sphere(vec 0,&1) SUBSET U
        ==> ?e. &0 < e /\ e < &1 / &8 /\ !x. abs(norm x - &1) < e ==> x IN U`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`sphere(vec 0:real^3,&1)`; `(:real^3) DIFF U`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_SPHERE; GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `min d (&1 / &16)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  MP_TAC(SPECL [`x:real^3`; `min d (&1 / &16)`] SCH1_NORMALIZE_NEAR) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`inv(norm x) % x:real^3`; `x:real^3`]) THEN
  ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[REAL_NOT_LE] THEN DISCH_TAC THEN
  REWRITE_TAC[dist] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;

(* The collar k = c0^-1 o f near the sphere.                                 *)

let SCH1_K_SETUP = prove
 (`!f f' c0 c0':real^3->real^3.
        sch_neck f f' /\ sch_ball c0 c0' /\
        IMAGE c0 (ball(vec 0,&1)) = inside(IMAGE f (sphere(vec 0,&1))) /\
        IMAGE c0 (sphere(vec 0,&1)) = IMAGE f (sphere(vec 0,&1)) /\
        IMAGE c0 (cball(vec 0,&1)) =
        IMAGE f (sphere(vec 0,&1)) UNION inside(IMAGE f (sphere(vec 0,&1))) /\
        (!x. x IN annulus (&1 / &2) (&1)
             ==> f x IN inside(IMAGE f (sphere(vec 0,&1)))) /\
        (!x. x IN annulus (&1) (&2) ==> f x IN outside(IMAGE f (sphere(vec 0,&1))))
        ==> ?eta. &0 < eta /\ eta < &1 / &8 /\
                  diffeomorphism_on (annulus (&1 / &2) (&1 + eta))
                    (IMAGE (\x. c0'(f x)) (annulus (&1 / &2) (&1 + eta)))
                    (\x. c0'(f x)) (\y. f'(c0 y)) /\
                  (!x. x IN annulus (&1 / &2) (&1 + eta)
                       ==> c0(c0'(f x)) = f x /\ c0'(f x) IN ball(vec 0,&2)) /\
                  (!x. x IN sphere(vec 0,&1) ==> c0'(f x) IN sphere(vec 0,&1)) /\
                  (!x. x IN annulus (&1 / &2) (&1) ==> norm(c0'(f x)) < &1) /\
                  (!x. x IN annulus (&1) (&1 + eta) ==> &1 < norm(c0'(f x)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_ball] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "dc")
    (CONJUNCTS_THEN2 (LABEL_TAC "c1") (CONJUNCTS_THEN2 (LABEL_TAC "cs")
    (CONJUNCTS_THEN2 (LABEL_TAC "cc") (CONJUNCTS_THEN2 (LABEL_TAC "in")
     (LABEL_TAC "out"))))))) THEN
  ABBREV_TAC `S = IMAGE (f:real^3->real^3) (sphere(vec 0,&1))` THEN
  USE_THEN "nk" (STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  USE_THEN "dc" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  ABBREV_TAC `B = IMAGE (c0:real^3->real^3) (ball(vec 0,&2))` THEN
  SUBGOAL_THEN `!x. x IN annulus (&1 / &2) (&2) /\ (f:real^3->real^3) x IN B
                    ==> c0((c0':real^3->real^3)(f x)) = f x /\ c0'(f x) IN ball(vec 0,&2)`
  (LABEL_TAC "back") THENL
   [REPEAT STRIP_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]]; ALL_TAC] THEN
  SUBGOAL_THEN `open {x:real^3 | x IN annulus (&1 / &2) (&2) /\ (f:real^3->real^3) x IN B}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `{x:real^3 | x IN annulus (&1 / &2) (&2) /\ (f:real^3->real^3) x IN B}`
    SCH1_SHELL_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET]; ALL_TAC] THEN
    EXPAND_TAC "B" THEN
    SUBGOAL_THEN `(f:real^3->real^3) x IN IMAGE (c0:real^3->real^3) (sphere(vec 0,&1))` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> x IN IMAGE (f:real^3->real^3) s ==> x IN IMAGE f t`) THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_BALL_0] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "e")))) THEN
  SUBGOAL_THEN `!x:real^3. x IN annulus (&1 / &2) (&1 + eta)
                           ==> x IN annulus (&1 / &2) (&2) /\ (f:real^3->real^3) x IN B`
  (LABEL_TAC "fB") THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_CASES_TAC `norm(x:real^3) < &1` THENL
     [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      EXPAND_TAC "B" THEN
      SUBGOAL_THEN `(f:real^3->real^3) x IN IMAGE (c0:real^3->real^3) (ball(vec 0,&1))` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "in" MATCH_MP_TAC THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET t ==> x IN IMAGE (f:real^3->real^3) s ==> x IN IMAGE f t`) THEN
        MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC];
      USE_THEN "e" (MP_TAC o SPEC `x:real^3`) THEN REWRITE_TAC[IN_ELIM_THM; annulus] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `eta:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `annulus (&1 / &2) (&1 + eta) SUBSET annulus (&1 / &2) (&2):real^3->bool`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\x:real^3. (c0':real^3->real^3)((f:real^3->real^3) x)) = c0' o f /\
                  (\y:real^3. (f':real^3->real^3)((c0:real^3->real^3) y)) = f' o c0`
    (fun th -> REWRITE_TAC[th; IMAGE_o]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) (annulus (&1 / &2) (&1 + eta))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SCH4_DIFFEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`annulus (&1 / &2) (&2):real^3->bool`;
                            `IMAGE (f:real^3->real^3) (annulus (&1 / &2) (&2))`] THEN
      USE_THEN "nk" (fun th -> REWRITE_TAC[REWRITE_RULE[sch_neck] th]) THEN
      ASM_REWRITE_TAC[OPEN_ANNULUS];
      MATCH_MP_TAC SCH4_DIFFEO_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`B:real^3->bool`; `ball(vec 0:real^3,&2)`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC DIFFEOMORPHISM_ON_SYM THEN USE_THEN "dc" ACCEPT_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SCH4_DIFFEO_IMAGE_OPEN THEN
        MAP_EVERY EXISTS_TAC [`annulus (&1 / &2) (&2):real^3->bool`;
                              `IMAGE (f:real^3->real^3) (annulus (&1 / &2) (&2))`;
                              `f':real^3->real^3`] THEN
        USE_THEN "nk" (fun th -> REWRITE_TAC[REWRITE_RULE[sch_neck] th]) THEN
        ASM_REWRITE_TAC[OPEN_ANNULUS];
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]]];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "back" MATCH_MP_TAC THEN
    ASM_MESON_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^3->real^3) x IN IMAGE (c0:real^3->real^3) (sphere(vec 0,&1))` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c0':real^3->real^3)(c0 z) = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x:real^3. x IN ball(vec 0,&2) ==> (c0':real^3->real^3)(c0 x) = x`)
          (concl th))) THEN
    UNDISCH_TAC `(z:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; IN_BALL_0] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^3->real^3) x IN IMAGE (c0:real^3->real^3) (ball(vec 0,&1))` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "in" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c0':real^3->real^3)(c0 z) = z` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x:real^3. x IN ball(vec 0,&2) ==> (c0':real^3->real^3)(c0 x) = x`)
            (concl th))) THEN
      UNDISCH_TAC `(z:real^3) IN ball(vec 0,&1)` THEN
      REWRITE_TAC[IN_BALL_0] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `(z:real^3) IN ball(vec 0,&1)` THEN REWRITE_TAC[IN_BALL_0]];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN annulus (&1 / &2) (&1 + eta) /\ x IN annulus (&1) (&2)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN annulus (&1) (&1 + eta)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "fB" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN annulus (&1 / &2) (&1 + eta)`)) THEN
    DISCH_THEN(fun th -> USE_THEN "back" (MP_TAC o C MATCH_MP th)) THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^3->real^3) x IN IMAGE (c0:real^3->real^3) (cball(vec 0,&1))` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `(c0:real^3->real^3)(c0'((f:real^3->real^3) x))`)) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_CBALL_0];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "out" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN annulus (&1) (&2)`)) THEN
    MP_TAC(ISPEC `S:real^3->bool` OUTSIDE_NO_OVERLAP) THEN
    MP_TAC(ISPEC `S:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
    SET_TAC[]]);;

(* Smale's theorem straightens the collar on the sphere: k1 = H^-1 o k is a   *)
(* shell map (it fixes the sphere pointwise).                                *)

let SCH1_STRAIGHTEN = prove
 (`!f f' c0 c0':real^3->real^3 eta.
        sch_neck f f' /\ sch_ball c0 c0' /\
        IMAGE c0 (sphere(vec 0,&1)) = IMAGE f (sphere(vec 0,&1)) /\
        &0 < eta /\ eta < &1 / &8 /\
        diffeomorphism_on (annulus (&1 / &2) (&1 + eta))
          (IMAGE (\x. c0'(f x)) (annulus (&1 / &2) (&1 + eta)))
          (\x. c0'(f x)) (\y. f'(c0 y)) /\
        (!x. x IN annulus (&1 / &2) (&1 + eta)
             ==> c0(c0'(f x)) = f x /\ c0'(f x) IN ball(vec 0,&2)) /\
        (!x. x IN sphere(vec 0,&1) ==> c0'(f x) IN sphere(vec 0,&1)) /\
        (!x. x IN annulus (&1 / &2) (&1) ==> norm(c0'(f x)) < &1) /\
        (!x. x IN annulus (&1) (&1 + eta) ==> &1 < norm(c0'(f x)))
        ==> ?H Hk. diffeomorphism_on (:real^3) (:real^3) H Hk /\
                   (!x. norm(H x) = norm x) /\ (!x. norm(Hk x) = norm x) /\
                   sch1_shell_map (\x. Hk(c0'(f x))) eta`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_ball] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 (LABEL_TAC "dc")
    (CONJUNCTS_THEN2 (LABEL_TAC "cs") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dk")
    (CONJUNCTS_THEN2 (LABEL_TAC "back") (CONJUNCTS_THEN2 (LABEL_TAC "sph")
    (CONJUNCTS_THEN2 (LABEL_TAC "in") (LABEL_TAC "out")))))))))) THEN
  USE_THEN "nk" (STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  USE_THEN "dc" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  USE_THEN "dk" (STRIP_ASSUME_TAC o BETA_RULE o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  ABBREV_TAC `D = annulus (&1 / &2) (&1 + eta):real^3->bool` THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) SUBSET D` ASSUME_TAC THENL
   [EXPAND_TAC "D" THEN REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[SCH1_SPHERE_IN_SHELL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1)
                           ==> (c0:real^3->real^3) x IN IMAGE (f:real^3->real^3) (sphere(vec 0,&1))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN USE_THEN "cs" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN sphere(vec 0,&1) ==> x IN ball(vec 0,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SPHERE_0; IN_BALL_0] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `sphere_diffeo (\x. (c0':real^3->real^3)((f:real^3->real^3) x))
                              (\y. (f':real^3->real^3)((c0:real^3->real^3) y))`
  ASSUME_TAC THENL
   [REWRITE_TAC[sphere_diffeo; smooth_near] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `{y:real^3 | y IN ball(vec 0,&2) /\
                              (c0:real^3->real^3) y IN IMAGE (f:real^3->real^3) (annulus (&1 / &2) (&2))}` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
        MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        CONJ_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`f:real^3->real^3`; `sphere(vec 0:real^3,&1)`;
                       `annulus (&1 / &2) (&2):real^3->bool`] IMAGE_SUBSET) THEN
        REWRITE_TAC[SCH4_SPHERE_SUBSET_ANNULUS] THEN
        MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> s SUBSET t ==> x IN t`) THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC SCH3_SV_COMPOSE THEN
        EXISTS_TAC `IMAGE (f:real^3->real^3) (annulus (&1 / &2) (&2))` THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[OPEN_BALL] THEN
          MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `ball(vec 0:real^3,&2)` THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[];
          SIMP_TAC[IN_ELIM_THM]]];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?z:real^3. z IN sphere(vec 0,&1) /\ (c0:real^3->real^3) x = f z`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1)` THEN
        USE_THEN "cs" (MP_TAC o SYM) THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN
        MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^3) IN annulus (&1 / &2) (&2) /\ (x:real^3) IN D /\
                    (x:real^3) IN annulus (&1 / &2) (&2)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SCH4_SPHERE_SUBSET_ANNULUS; SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `(f':real^3->real^3)((f:real^3->real^3) x) = x /\
                    (c0:real^3->real^3)((c0':real^3->real^3)(f x)) = f x`
      STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [USE_THEN "sph" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[];
        ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(f':real^3->real^3)((f:real^3->real^3) z) = z /\
                      (c0':real^3->real^3)((c0:real^3->real^3) x) = x`
        STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[] THEN
        MESON_TAC[ASSUME `(c0:real^3->real^3) x = (f:real^3->real^3) z`;
                  ASSUME `(f':real^3->real^3)((f:real^3->real^3) z) = z`;
                  ASSUME `(c0':real^3->real^3)((c0:real^3->real^3) x) = x`]]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`\x. (c0':real^3->real^3)((f:real^3->real^3) x)`;
                `\y. (f':real^3->real^3)((c0:real^3->real^3) y)`]
    (REWRITE_RULE[SMT_SMALE_RADIAL_STATEMENT] SMT_SMALE_RADIAL)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^3->real^3` (X_CHOOSE_THEN `Hk:real^3->real^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "dH") (CONJUNCTS_THEN2 (LABEL_TAC "nH") (LABEL_TAC "rH"))))) THEN
  USE_THEN "dH" (STRIP_ASSUME_TAC o REWRITE_RULE[IN_UNIV] o
    GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `!y:real^3. norm((Hk:real^3->real^3) y) = norm y` ASSUME_TAC THENL
   [GEN_TAC THEN USE_THEN "nH" (MP_TAC o SPEC `(Hk:real^3->real^3) y`) THEN
    REWRITE_TAC[ASSUME `!y:real^3. (H:real^3->real^3)((Hk:real^3->real^3) y) = y`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`H:real^3->real^3`; `Hk:real^3->real^3`] THEN
  ASM_REWRITE_TAC[sch1_shell_map] THEN
  SUBGOAL_THEN `eta < &1 / &4` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `diffeomorphism_on D (IMAGE (\x. (Hk:real^3->real^3)(c0'((f:real^3->real^3) x))) D)
                  (\x. Hk(c0'(f x))) (\y. (f':real^3->real^3)((c0:real^3->real^3)((H:real^3->real^3) y)))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(\x:real^3. (Hk:real^3->real^3)(c0'((f:real^3->real^3) x))) =
                  Hk o (\x. c0'(f x)) /\
                  (\y:real^3. (f':real^3->real^3)((c0:real^3->real^3)((H:real^3->real^3) y))) =
                  (\y. f'(c0 y)) o H`
    (fun th -> REWRITE_TAC[th; IMAGE_o]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN
    EXISTS_TAC `IMAGE (\x. (c0':real^3->real^3)((f:real^3->real^3) x)) D` THEN
    CONJ_TAC THENL [USE_THEN "dk" (fun th -> ASM_REWRITE_TAC[th]); ALL_TAC] THEN
    MATCH_MP_TAC SCH_DIFFEO_RESTRICT_UNIV THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFFEOMORPHISM_ON_SYM THEN USE_THEN "dH" ACCEPT_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SCH3_SV_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN EXPAND_TAC "D" THEN
    REWRITE_TAC[OPEN_ANNULUS];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c0':real^3->real^3)((f:real^3->real^3) x) = c0'(f y)` MP_TAC THENL
     [UNDISCH_TAC `(Hk:real^3->real^3)((c0':real^3->real^3)((f:real^3->real^3) x)) =
                   Hk(c0'(f y))` THEN
      DISCH_THEN(MP_TAC o AP_TERM `H:real^3->real^3`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\u:real^3. (f':real^3->real^3)((c0:real^3->real^3) u)`) THEN
    REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `h:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`D:real^3->bool`;
                   `IMAGE (\x. (Hk:real^3->real^3)(c0'((f:real^3->real^3) x))) D`;
                   `\x. (Hk:real^3->real^3)(c0'((f:real^3->real^3) x))`;
                   `\y. (f':real^3->real^3)((c0:real^3->real^3)((H:real^3->real^3) y))`;
                   `x:real^3`; `h:real^3`] SCH4_DIFFEO_DERIV_INV) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `linear(frechet_derivative
        (\y. (f':real^3->real^3)((c0:real^3->real^3)((H:real^3->real^3) y)))
        (at ((Hk:real^3->real^3)((c0':real^3->real^3)((f:real^3->real^3) x)))))`
    (fun th -> REWRITE_TAC[MATCH_MP LINEAR_0 th]) THEN
    MATCH_MP_TAC LINEAR_FRECHET_DERIVATIVE THEN
    MATCH_MP_TAC SMOOTH_MAP_ON_DIFFERENTIABLE THEN
    EXISTS_TAC `IMAGE (\x. (Hk:real^3->real^3)(c0'((f:real^3->real^3) x))) D` THEN
    UNDISCH_TAC `diffeomorphism_on D (IMAGE (\x. (Hk:real^3->real^3)(c0'((f:real^3->real^3) x))) D)
                  (\x. Hk(c0'(f x))) (\y. (f':real^3->real^3)((c0:real^3->real^3)((H:real^3->real^3) y)))` THEN
    REWRITE_TAC[diffeomorphism_on] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `norm(x:real^3) = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1)` THEN REWRITE_TAC[IN_SPHERE_0];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 / &2 <= norm(x:real^3) /\ norm x <= &2` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "rH" (MP_TAC o C MATCH_MP
      (ASSUME `&1 / &2 <= norm(x:real^3) /\ norm x <= &2`)) THEN
    ASM_REWRITE_TAC[radial_ext; REAL_INV_1; VECTOR_MUL_LID] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Gluing diffeomorphisms, sides at an inner radius, and the                 *)
(* nesting of the bounded sides.                                             *)
(* ------------------------------------------------------------------------- *)

(* Same statement and proof as SCH2_GLUE_DIFFEO of pc_sch_planar,           *)
(* repeated here to avoid loading that complex-analytic unit.                *)

let SCH1_GLUE_DIFFEO = prove
 (`!(c:real^N->real^N) d1 d1' d2 d2' u1 u2.
        diffeomorphism_on u1 (IMAGE d1 u1) d1 d1' /\
        diffeomorphism_on u2 (IMAGE d2 u2) d2 d2' /\
        (!x. x IN u1 ==> c x = d1 x) /\ (!x. x IN u2 ==> c x = d2 x) /\
        (!x y. x IN u1 UNION u2 /\ y IN u1 UNION u2 /\ c x = c y ==> x = y)
        ==> ?c'. diffeomorphism_on (u1 UNION u2) (IMAGE c (u1 UNION u2)) c c'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "C1") (CONJUNCTS_THEN2 (LABEL_TAC "C2")
       (LABEL_TAC "INJ"))))) THEN
  SUBGOAL_THEN `IMAGE (c:real^N->real^N) u1 = IMAGE d1 u1 /\
                IMAGE (c:real^N->real^N) u2 = IMAGE d2 u2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC IMAGE_EQ THENL
     [USE_THEN "C1" ACCEPT_TAC; USE_THEN "C2" ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN IMAGE (d1:real^N->real^N) u1 /\ y IN IMAGE (d2:real^N->real^N) u2
                    ==> (d1':real^N->real^N) y = d2' y` (LABEL_TAC "AGREE") THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `x2:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(c:real^N->real^N) x1 = y /\ (c:real^N->real^N) x2 = y`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "C1" (fun th -> REWRITE_TAC[MP (SPEC `x1:real^N` th)
        (ASSUME `(x1:real^N) IN u1`)]) THEN
      USE_THEN "C2" (fun th -> REWRITE_TAC[MP (SPEC `x2:real^N` th)
        (ASSUME `(x2:real^N) IN u2`)]) THEN
      CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `x1:real^N = x2` SUBST_ALL_TAC THENL
     [USE_THEN "INJ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
    SUBGOAL_THEN `(d1':real^N->real^N) y = x2 /\ (d2':real^N->real^N) y = x2`
    (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
     [UNDISCH_TAC `(y:real^N) = (d1:real^N->real^N) x2` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[];
      UNDISCH_TAC `(y:real^N) = (d2:real^N->real^N) x2` THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `c' = \y. if y IN IMAGE (d1:real^N->real^N) u1 then (d1':real^N->real^N) y
                       else d2' y` THEN
  SUBGOAL_THEN `(!y. y IN IMAGE (d1:real^N->real^N) u1 ==> (c':real^N->real^N) y = d1' y) /\
                (!y. y IN IMAGE (d2:real^N->real^N) u2 ==> (c':real^N->real^N) y = d2' y)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c'" THEN CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "AGREE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!y. y IN IMAGE (d1:real^N->real^N) u1 ==> (d1':real^N->real^N) y IN u1) /\
                (!y. y IN IMAGE (d2:real^N->real^N) u2 ==> (d2':real^N->real^N) y IN u2)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THENL
     [UNDISCH_TAC `IMAGE (d1':real^N->real^N) (IMAGE d1 u1) = u1`;
      UNDISCH_TAC `IMAGE (d2':real^N->real^N) (IMAGE d2 u2) = u2`] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `c':real^N->real^N` THEN
  REWRITE_TAC[IMAGE_UNION] THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[OPEN_UNION] THEN REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE (c':real^N->real^N) (IMAGE (d1:real^N->real^N) u1) =
                  IMAGE (d1':real^N->real^N) (IMAGE d1 u1) /\
                  IMAGE (c':real^N->real^N) (IMAGE (d2:real^N->real^N) u2) =
                  IMAGE (d2':real^N->real^N) (IMAGE d2 u2)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]; ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_UNION] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
     [USE_THEN "C1" (fun th -> REWRITE_TAC[MP (SPEC `x:real^N` th)
        (ASSUME `(x:real^N) IN u1`)]) THEN
      SUBGOAL_THEN `(d1:real^N->real^N) x IN IMAGE d1 u1` ASSUME_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]];
      USE_THEN "C2" (fun th -> REWRITE_TAC[MP (SPEC `x:real^N` th)
        (ASSUME `(x:real^N) IN u2`)]) THEN
      SUBGOAL_THEN `(d2:real^N->real^N) x IN IMAGE d2 u2` ASSUME_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ASM_SIMP_TAC[]]];
    REWRITE_TAC[IN_UNION] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THENL
     [SUBGOAL_THEN `(d1':real^N->real^N) y IN u1` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `(d2':real^N->real^N) y IN u2` ASSUME_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_SIMP_TAC[OPEN_UNION; IN_UNION] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
     [EXISTS_TAC `u1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `d1:real^N->real^N` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "C1" (fun th -> SIMP_TAC[th]);
      EXISTS_TAC `u2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `d2:real^N->real^N` THEN
      ASM_REWRITE_TAC[] THEN USE_THEN "C2" (fun th -> SIMP_TAC[th])];
    MATCH_MP_TAC SMOOTH_MAP_ON_LOCAL THEN ASM_SIMP_TAC[OPEN_UNION; IN_UNION] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THENL
     [EXISTS_TAC `IMAGE (d1:real^N->real^N) u1` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `d1':real^N->real^N` THEN
      ASM_SIMP_TAC[];
      EXISTS_TAC `IMAGE (d2:real^N->real^N) u2` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SMOOTH_MAP_ON_EQ THEN EXISTS_TAC `d2':real^N->real^N` THEN
      ASM_SIMP_TAC[]]]);;

(* Same statement and proof as SCH2_UNBOUNDED_IN_OUTSIDE of pc_sch_planar.   *)

let SCH1_UNBOUNDED_IN_OUTSIDE = prove
 (`!s c:real^N->bool. connected c /\ ~bounded c /\ c INTER s = {} ==> c SUBSET outside s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; outside; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET (:real^N) DIFF s` ASSUME_TAC THENL
   [UNDISCH_TAC `(c:real^N->bool) INTER s = {}` THEN SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(c:real^N->bool) SUBSET (:real^N) DIFF s` THEN
    UNDISCH_TAC `(x:real^N) IN c` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET connected_component ((:real^N) DIFF s) x` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN DISCH_TAC THEN
  UNDISCH_TAC `~bounded(c:real^N->bool)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC BOUNDED_SUBSET THEN
  EXISTS_TAC `connected_component ((:real^N) DIFF s) (x:real^N)` THEN ASM_REWRITE_TAC[]);;

(* Rescaling a circle of radius r to the unit circle. *)

(* A connected set equals any nonempty open subset that is closed in it.     *)

let SCH1_CLOPEN_EQ = prove
 (`!s t k:real^N->bool.
        connected s /\ open t /\ t SUBSET s /\ ~(t = {}) /\
        closed k /\ t SUBSET k /\ s INTER k SUBSET t
        ==> t = s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOPEN]) THEN
  DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* With the inner half of the neck inside, the sides at an inner radius r.   *)

let SCH1_SIDES_INNER = prove
 (`!f f':real^3->real^3 r.
        sch_neck f f' /\ &1 / &2 < r /\ r < &1 /\
        (!x. x IN annulus (&1 / &2) (&1)
             ==> f x IN inside(IMAGE f (sphere(vec 0,&1)))) /\
        (!x. x IN annulus (&1) (&2) ==> f x IN outside(IMAGE f (sphere(vec 0,&1))))
        ==> (!x. x IN annulus (&1 / &2) r ==> f x IN inside(IMAGE f (sphere(vec 0,r)))) /\
            (!x. x IN annulus r (&2) ==> f x IN outside(IMAGE f (sphere(vec 0,r)))) /\
            outside(IMAGE f (sphere(vec 0,&1))) SUBSET outside(IMAGE f (sphere(vec 0,r))) /\
            IMAGE f (sphere(vec 0,r)) SUBSET inside(IMAGE f (sphere(vec 0,&1)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "in") (LABEL_TAC "out"))))) THEN
  ABBREV_TAC `S = IMAGE (f:real^3->real^3) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `Sr = IMAGE (f:real^3->real^3) (sphere(vec 0,r))` THEN
  MP_TAC(ISPEC `S:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_3; ARITH] THEN EXPAND_TAC "S" THEN
    MATCH_MP_TAC SCH1_NECK_HOMEOMORPHIC THEN EXISTS_TAC `f':real^3->real^3` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  MP_TAC(ISPEC `Sr:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_3; ARITH] THEN EXPAND_TAC "Sr" THEN
    MATCH_MP_TAC SCH1_NECK_HOMEOMORPHIC THEN EXISTS_TAC `f':real^3->real^3` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `Sr SUBSET inside(S:real^3->bool)` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^3) (sphere(vec 0,r)) = Sr`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "in" MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^3) IN sphere(vec 0,r)` THEN
    REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `outside S SUBSET outside(Sr:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH1_UNBOUNDED_IN_OUTSIDE THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `Sr SUBSET inside(S:real^3->bool)` THEN
    UNDISCH_TAC `inside S INTER outside S:real^3->bool = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `r:real`] SCH1_NECK_SIDES) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~(b /\ c) ==> a \/ b /\ c ==> a`) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^3->real^3)((&3 / &2) % basis 1) IN outside Sr /\
                (f:real^3->real^3)((&3 / &2) % basis 1) IN inside Sr` MP_TAC THENL
   [SUBGOAL_THEN `(&3 / &2) % basis 1 IN annulus (&1) (&2):real^3->bool /\
                  (&3 / &2) % basis 1 IN annulus r (&2):real^3->bool` STRIP_ASSUME_TAC THENL
     [SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `outside S SUBSET outside(Sr:real^3->bool)` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "out" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x:real^3. x IN annulus r (&2) ==> (f:real^3->real^3) x IN inside Sr`)
            (concl th))) THEN
      ASM_REWRITE_TAC[]];
    UNDISCH_TAC `inside Sr INTER outside Sr:real^3->bool = {}` THEN SET_TAC[]]);;

(* The bounded side of S is the bounded side of the inner sphere f(|x|=3/4)  *)
(* together with the image of the shell 3/4 < |x| <= 1.                      *)

let SCH1_NEST = prove
 (`!f f':real^3->real^3.
        sch_neck f f' /\
        (!x. x IN annulus (&1 / &2) (&1)
             ==> f x IN inside(IMAGE f (sphere(vec 0,&1)))) /\
        (!x. x IN annulus (&1) (&2) ==> f x IN outside(IMAGE f (sphere(vec 0,&1))))
        ==> IMAGE f (sphere(vec 0,&1)) UNION inside(IMAGE f (sphere(vec 0,&1))) =
            (IMAGE f (sphere(vec 0,&3 / &4)) UNION
             inside(IMAGE f (sphere(vec 0,&3 / &4)))) UNION
            IMAGE f {x | &3 / &4 < norm x /\ norm x <= &1}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "in") (LABEL_TAC "out"))) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `&3 / &4`] SCH1_SIDES_INNER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "in34") (CONJUNCTS_THEN2 (LABEL_TAC "out34")
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  USE_THEN "in" MP_TAC THEN USE_THEN "out" MP_TAC THEN
  USE_THEN "in34" MP_TAC THEN USE_THEN "out34" MP_TAC THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `&1`] SCH1_NECK_HOMEOMORPHIC) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `&3 / &4`] SCH1_NECK_HOMEOMORPHIC) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
  ABBREV_TAC `S = IMAGE (f:real^3->real^3) (sphere(vec 0,&1))` THEN
  ABBREV_TAC `S3 = IMAGE (f:real^3->real^3) (sphere(vec 0,&3 / &4))` THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPEC `S:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `S3:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  SUBGOAL_THEN `S SUBSET outside(S3:real^3->bool)` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^3) (sphere(vec 0,&1)) = S`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "out34" MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inside S3 SUBSET inside(S:real^3->bool)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`S SUBSET outside(S3:real^3->bool)`; `outside S SUBSET outside(S3:real^3->bool)`;
      `inside S3 INTER outside S3:real^3->bool = {}`;
      `inside S UNION outside S = (:real^3) DIFF S`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(IMAGE (f:real^3->real^3) (annulus (&5 / &8) (&1)))` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH4_DIFFEO_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`annulus (&1 / &2) (&2):real^3->bool`;
                          `IMAGE (f:real^3->real^3) (annulus (&1 / &2) (&2))`;
                          `f':real^3->real^3`] THEN
    UNDISCH_TAC `sch_neck (f:real^3->real^3) f'` THEN REWRITE_TAC[sch_neck] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[OPEN_ANNULUS] THEN
    REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `inside S3 UNION IMAGE (f:real^3->real^3) (annulus (&5 / &8) (&1)) = inside S`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SCH1_CLOPEN_EQ THEN
    EXISTS_TAC `closure(inside S3 UNION IMAGE (f:real^3->real^3) (annulus (&5 / &8) (&1)))` THEN
    ASM_SIMP_TAC[OPEN_UNION; CLOSED_CLOSURE; CLOSURE_SUBSET] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[UNION_SUBSET] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "in" MATCH_MP_TAC THEN
      UNDISCH_TAC `(x:real^3) IN annulus (&5 / &8) (&1)` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `closure(IMAGE (f:real^3->real^3) (annulus (&5 / &8) (&1))) SUBSET
      IMAGE f (cball(vec 0,&1) DIFF ball(vec 0,&5 / &8))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
        REAL_ARITH_TAC;
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
        SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `annulus (&1 / &2) (&2):real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; annulus; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (f:real^3->real^3) (cball(vec 0,&1) DIFF ball(vec 0,&5 / &8)) SUBSET
      (inside S3 UNION IMAGE f (annulus (&5 / &8) (&1))) UNION S`
    ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_CBALL_0; IN_BALL_0; IN_UNION;
                  REAL_NOT_LT] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      ASM_CASES_TAC `norm(x:real^3) = &1` THENL
       [DISJ2_TAC THEN
        SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^3) (sphere(vec 0,&1)) = S`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
        ALL_TAC] THEN
      ASM_CASES_TAC `norm(x:real^3) = &5 / &8` THENL
       [DISJ1_TAC THEN DISJ1_TAC THEN USE_THEN "in34" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
        DISJ1_TAC THEN DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPEC `S3:real^3->bool` CLOSURE_INSIDE_SUBSET) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[COMPACT_IMP_CLOSED; HOMEOMORPHIC_COMPACTNESS;
                                  COMPACT_SPHERE]; DISCH_TAC] THEN
    SUBGOAL_THEN `S3 SUBSET IMAGE (f:real^3->real^3) (annulus (&5 / &8) (&1))` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^3) (sphere(vec 0,&3 / &4)) = S3`)) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_UNION] THEN
    MP_TAC(ISPEC `S:real^3->bool` INSIDE_NO_OVERLAP) THEN
    MAP_EVERY UNDISCH_TAC
     [`closure(inside S3) SUBSET S3 UNION inside(S3:real^3->bool)`;
      `S3 SUBSET IMAGE (f:real^3->real^3) (annulus (&5 / &8) (&1))`;
      `IMAGE (f:real^3->real^3) (cball(vec 0,&1) DIFF ball(vec 0,&5 / &8)) SUBSET
       (inside S3 UNION IMAGE f (annulus (&5 / &8) (&1))) UNION S`;
      `closure(IMAGE (f:real^3->real^3) (annulus (&5 / &8) (&1))) SUBSET
       IMAGE f (cball(vec 0,&1) DIFF ball(vec 0,&5 / &8))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET u /\ i SUBSET u ==> s UNION i SUBSET u`) THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(s:real^3->bool) SUBSET v ==> s SUBSET a UNION v`) THEN
      SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^3) (sphere(vec 0,&1)) = S`)) THEN
      MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN X_GEN_TAC `x:real^3` THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_CASES_TAC `norm(x:real^3) < &3 / &4` THENL
       [DISJ1_TAC THEN DISJ2_TAC THEN USE_THEN "in34" MATCH_MP_TAC THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `norm(x:real^3) = &3 / &4` THENL
       [DISJ1_TAC THEN DISJ1_TAC THEN
        SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^3) (sphere(vec 0,&3 / &4)) = S3`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
        DISJ2_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `S3 SUBSET inside(S:real^3->bool)` THEN SET_TAC[];
      UNDISCH_TAC `inside S3 SUBSET inside(S:real^3->bool)` THEN SET_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      ASM_CASES_TAC `norm(x:real^3) = &1` THENL
       [DISJ1_TAC THEN
        SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^3) (sphere(vec 0,&1)) = S`)) THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_SPHERE_0];
        DISJ2_TAC THEN USE_THEN "in" MATCH_MP_TAC THEN
        REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]]]);;

(* ------------------------------------------------------------------------- *)
(* The inner ball chart c0 o H o Phi o (4/3), and the image of               *)
(* the ball of radius 3/4 under a chart that agrees with f near |x| = 3/4.   *)
(* ------------------------------------------------------------------------- *)

let SCH1_DIFFEO_HOMEO = prove
 (`!Phi Psi:real^N->real^N.
        diffeomorphism_on (:real^N) (:real^N) Phi Psi
        ==> homeomorphism ((:real^N),(:real^N)) (Phi,Psi)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[diffeomorphism_on; homeomorphism] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]);;

let SCH1_SCALE_DIFFEO = prove
 (`!R. &0 < R
       ==> diffeomorphism_on (ball(vec 0:real^3,&3 / &4 * R)) (ball(vec 0,R))
                             (\y. (&4 / &3) % y) (\z. (&3 / &4) % z)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SMT_DIFFEOMORPHISM_ON_INVERSES THEN
  REWRITE_TAC[OPEN_BALL; IN_BALL_0; NORM_MUL] THEN
  SUBGOAL_THEN `open(ball(vec 0:real^3,&3 / &4 * R)) /\ open(ball(vec 0:real^3,R))`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[OPEN_BALL]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SCH3_SMOOTH_TAC; SCH3_SMOOTH_TAC;
    GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN ASM_REAL_ARITH_TAC;
    GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN ASM_REAL_ARITH_TAC]);;

let SCH1_INNER_CHART = prove
 (`!c0 c0' H Hk Phi Psi:real^3->real^3 R.
        sch_ball c0 c0' /\ diffeomorphism_on (:real^3) (:real^3) H Hk /\
        (!x. norm(H x) = norm x) /\
        diffeomorphism_on (:real^3) (:real^3) Phi Psi /\ &0 < R /\
        IMAGE Phi (ball(vec 0,R)) SUBSET ball(vec 0,&1)
        ==> ?E'. diffeomorphism_on (ball(vec 0,&3 / &4 * R))
                   (IMAGE (\y. c0(H(Phi((&4 / &3) % y)))) (ball(vec 0,&3 / &4 * R)))
                   (\y. c0(H(Phi((&4 / &3) % y)))) E'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[sch_ball] THEN STRIP_TAC THEN
  ABBREV_TAC `V1 = IMAGE (Phi:real^3->real^3) (ball(vec 0,R))` THEN
  ABBREV_TAC `V2 = IMAGE (H:real^3->real^3) V1` THEN
  SUBGOAL_THEN `diffeomorphism_on (ball(vec 0:real^3,R)) V1 (Phi:real^3->real^3) Psi` ASSUME_TAC THENL
   [EXPAND_TAC "V1" THEN MATCH_MP_TAC SCH_DIFFEO_RESTRICT_UNIV THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `open(V1:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on V1 V2 (H:real^3->real^3) Hk` ASSUME_TAC THENL
   [EXPAND_TAC "V2" THEN MATCH_MP_TAC SCH_DIFFEO_RESTRICT_UNIV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `V2 SUBSET ball(vec 0:real^3,&2)` ASSUME_TAC THENL
   [EXPAND_TAC "V2" THEN
    UNDISCH_TAC `V1 SUBSET ball(vec 0:real^3,&1)` THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_BALL_0] THEN
    MESON_TAC[REAL_ARITH `x < &1 ==> x < &2`];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on V2 (IMAGE (c0:real^3->real^3) V2) c0 c0'` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH4_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,&2)`; `IMAGE (c0:real^3->real^3) (ball(vec 0,&2))`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[diffeomorphism_on];
    ALL_TAC] THEN
  MP_TAC(SPEC `R:real` SCH1_SCALE_DIFFEO) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `diffeomorphism_on (ball(vec 0,&3 / &4 * R)) (IMAGE (c0:real^3->real^3) V2)
      ((c0:real^3->real^3) o (H:real^3->real^3) o (Phi:real^3->real^3) o (\y. (&4 / &3) % y))
      ((((\z. (&3 / &4) % z) o (Psi:real^3->real^3)) o (Hk:real^3->real^3)) o
       (c0':real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `V2:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `V1:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC DIFFEOMORPHISM_ON_COMPOSE THEN EXISTS_TAC `ball(vec 0:real^3,R)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(((\z. (&3 / &4) % z) o (Psi:real^3->real^3)) o (Hk:real^3->real^3)) o
              (c0':real^3->real^3)` THEN
  SUBGOAL_THEN
   `(\y:real^3. (c0:real^3->real^3)((H:real^3->real^3)((Phi:real^3->real^3)((&4 / &3) % y)))) =
    c0 o H o Phi o (\y. (&4 / &3) % y)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((c0:real^3->real^3) o (H:real^3->real^3) o (Phi:real^3->real^3) o
                       (\y. (&4 / &3) % y)) (ball(vec 0,&3 / &4 * R)) =
                IMAGE c0 V2` SUBST1_TAC THENL
   [ASM_MESON_TAC[diffeomorphism_on]; ASM_REWRITE_TAC[]]);;

(* A chart E of a ball of radius rho > 3/4 that agrees with the neck f on a  *)
(* shell around |x| = 3/4 maps the ball of radius 3/4 onto the bounded side  *)
(* of f(|x| = 3/4).                                                          *)

let SCH1_EBALL = prove
 (`!f f' (E:real^3->real^3) E' rho a.
        sch_neck f f' /\
        (!x. x IN annulus (&1 / &2) (&3 / &4)
             ==> f x IN inside(IMAGE f (sphere(vec 0,&3 / &4)))) /\
        &3 / &4 < rho /\ &1 / &2 < a /\ a < &3 / &4 /\
        diffeomorphism_on (ball(vec 0,rho)) (IMAGE E (ball(vec 0,rho))) E E' /\
        (!y. y IN annulus a rho ==> E y = f y)
        ==> IMAGE E (ball(vec 0,&3 / &4)) = inside(IMAGE f (sphere(vec 0,&3 / &4))) /\
            IMAGE E (sphere(vec 0,&3 / &4)) = IMAGE f (sphere(vec 0,&3 / &4))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "in")
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "dE") (LABEL_TAC "Ef"))))))) THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&3 / &4) SUBSET annulus a rho` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^3->real^3) (sphere(vec 0,&3 / &4)) =
                IMAGE (f:real^3->real^3) (sphere(vec 0,&3 / &4))` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> (E:real^3->real^3) x = f x)
                           ==> IMAGE E s = IMAGE f s`) THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S3 = IMAGE (f:real^3->real^3) (sphere(vec 0,&3 / &4))` THEN
  MP_TAC(ISPEC `S3:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN ANTS_TAC THENL
   [REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^3) (sphere(vec 0,&3 / &4)) = S3`)) THEN
    MATCH_MP_TAC SCH1_NECK_HOMEOMORPHIC THEN EXISTS_TAC `f':real^3->real^3` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    STRIP_TAC] THEN
  USE_THEN "dE" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `ball(vec 0:real^3,&3 / &4) SUBSET ball(vec 0,rho) /\
                cball(vec 0:real^3,&3 / &4) SUBSET ball(vec 0,rho)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL_0; IN_CBALL_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^3. x IN ball(vec 0,rho) /\ y IN ball(vec 0,rho) /\ (E:real^3->real^3) x = E y
                             ==> x = y` (LABEL_TAC "inj") THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^3->real^3) continuous_on ball(vec 0,rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC SMOOTH_MAP_ON_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SCH1_CLOPEN_EQ THEN
  EXISTS_TAC `IMAGE (E:real^3->real^3) (cball(vec 0,&3 / &4))` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SCH4_DIFFEO_IMAGE_OPEN THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^3,rho)`; `IMAGE (E:real^3->real^3) (ball(vec 0,rho))`;
                          `E':real^3->real^3`] THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    MP_TAC(ISPECL [`IMAGE (E:real^3->real^3) (ball(vec 0,&3 / &4))`; `inside S3:real^3->bool`;
                   `outside S3:real^3->bool`] SCH1_CONNECTED_SIDE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_BALL] THEN
        ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
        X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
        SUBST1_TAC(SYM(ASSUME `IMAGE (E:real^3->real^3) (sphere(vec 0,&3 / &4)) = S3`)) THEN
        REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `y:real^3 = z` MP_TAC THENL
         [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(y:real^3) IN ball(vec 0,&3 / &4)` THEN
          UNDISCH_TAC `(z:real^3) IN sphere(vec 0,&3 / &4)` THEN
          REWRITE_TAC[IN_BALL_0; IN_SPHERE_0] THEN ASM_REAL_ARITH_TAC;
          DISCH_THEN SUBST_ALL_TAC THEN
          UNDISCH_TAC `(z:real^3) IN ball(vec 0,&3 / &4)` THEN
          UNDISCH_TAC `(z:real^3) IN sphere(vec 0,&3 / &4)` THEN
          REWRITE_TAC[IN_BALL_0; IN_SPHERE_0] THEN REAL_ARITH_TAC]];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~b ==> a \/ b ==> a`) THEN DISCH_TAC THEN
    ABBREV_TAC `y0 = ((a + &3 / &4) / &2) % basis 1:real^3` THEN
    SUBGOAL_THEN `norm(y0:real^3) = (a + &3 / &4) / &2` ASSUME_TAC THENL
     [EXPAND_TAC "y0" THEN SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(E:real^3->real^3) y0 IN inside S3 /\ E y0 IN outside S3` MP_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `(E:real^3->real^3) y0 = f y0` SUBST1_TAC THENL
         [USE_THEN "Ef" MATCH_MP_TAC THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
          ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        USE_THEN "in" MATCH_MP_TAC THEN ASM_REWRITE_TAC[annulus; IN_ELIM_THM] THEN
        ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `IMAGE (E:real^3->real^3) (ball(vec 0,&3 / &4)) SUBSET outside S3` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC];
      UNDISCH_TAC `inside S3 INTER outside S3:real^3->bool = {}` THEN SET_TAC[]];
    REWRITE_TAC[IMAGE_EQ_EMPTY; BALL_EQ_EMPTY] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[BALL_SUBSET_CBALL];
    REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN
    MP_TAC(ISPEC `S3:real^3->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `IMAGE (E:real^3->real^3) (sphere(vec 0,&3 / &4)) = S3` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The core case (inner half of the neck on the bounded side)                *)
(* and the headline SCH_COLLAR3 |- SCH_COLLAR3_STATEMENT.                    *)
(* ------------------------------------------------------------------------- *)

(* Gluing the inner chart E (on a ball of radius rho > 3/4) with the neck f  *)
(* (on the annulus a < |x| < 2) along the shell where they agree.           *)

let SCH1_GLUE_CHART = prove
 (`!f f' E E':real^3->real^3 a rho.
        sch_neck f f' /\ &1 / &2 < a /\ a < &3 / &4 /\ &3 / &4 < rho /\ rho < &1 /\
        diffeomorphism_on (ball(vec 0,rho)) (IMAGE E (ball(vec 0,rho))) E E' /\
        (!y. y IN annulus a rho ==> E y = f y) /\
        IMAGE E (ball(vec 0,&3 / &4)) = inside(IMAGE f (sphere(vec 0,&3 / &4))) /\
        IMAGE E (sphere(vec 0,&3 / &4)) = IMAGE f (sphere(vec 0,&3 / &4)) /\
        (!x. x IN annulus (&3 / &4) (&2)
             ==> f x IN outside(IMAGE f (sphere(vec 0,&3 / &4))))
        ==> ?c c'. sch_ball c c' /\
                   IMAGE c (cball(vec 0,&3 / &4)) =
                   IMAGE f (sphere(vec 0,&3 / &4)) UNION
                   inside(IMAGE f (sphere(vec 0,&3 / &4))) /\
                   (!x. x IN annulus (&3 / &4) (&2) ==> c x = f x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "dE") (CONJUNCTS_THEN2 (LABEL_TAC "Ef")
    (CONJUNCTS_THEN2 (LABEL_TAC "Eb") (CONJUNCTS_THEN2 (LABEL_TAC "Es")
     (LABEL_TAC "out34")))))))))) THEN
  ABBREV_TAC `c = \x:real^3. if norm x <= &3 / &4 then (E:real^3->real^3) x
                              else (f:real^3->real^3) x` THEN
  SUBGOAL_THEN `(!x:real^3. x IN ball(vec 0,rho) ==> (c:real^3->real^3) x = E x) /\
                (!x:real^3. x IN annulus a (&2) ==> (c:real^3->real^3) x = f x)`
  (CONJUNCTS_THEN2 (LABEL_TAC "cE") (LABEL_TAC "cf")) THENL
   [EXPAND_TAC "c" THEN REWRITE_TAC[IN_BALL_0; annulus; IN_ELIM_THM] THEN CONJ_TAC THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [CONV_TAC SYM_CONV THEN USE_THEN "Ef" MATCH_MP_TAC THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
      USE_THEN "Ef" MATCH_MP_TAC THEN
      REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `diffeomorphism_on (annulus a (&2)) (IMAGE (f:real^3->real^3) (annulus a (&2)))
                  f f'` ASSUME_TAC THENL
   [MATCH_MP_TAC SCH4_DIFFEO_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`annulus (&1 / &2) (&2):real^3->bool`;
                          `IMAGE (f:real^3->real^3) (annulus (&1 / &2) (&2))`] THEN
    USE_THEN "nk" (fun th -> REWRITE_TAC[REWRITE_RULE[sch_neck] th]) THEN
    REWRITE_TAC[OPEN_ANNULUS; SUBSET; annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "nk" (STRIP_ASSUME_TAC o MATCH_MP SCH4_NECK_FACTS) THEN
  USE_THEN "dE" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  SUBGOAL_THEN `!x:real^3. norm x <= a
                ==> (c:real^3->real^3) x IN
                    inside(IMAGE (f:real^3->real^3) (sphere(vec 0,&3 / &4)))`
  (LABEL_TAC "P1") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(c:real^3->real^3) x = E x` SUBST1_TAC THENL
     [USE_THEN "cE" MATCH_MP_TAC THEN REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "Eb" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. rho <= norm y /\ norm y < &2
                ==> (c:real^3->real^3) y IN
                    outside(IMAGE (f:real^3->real^3) (sphere(vec 0,&3 / &4)))`
  (LABEL_TAC "P2") THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(c:real^3->real^3) y = f y` SUBST1_TAC THENL
     [USE_THEN "cf" MATCH_MP_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    USE_THEN "out34" MATCH_MP_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(vec 0:real^3,rho) UNION annulus a (&2) = ball(vec 0,&2)` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_BALL_0; annulus; IN_ELIM_THM] THEN
    GEN_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^3->real^3`; `E:real^3->real^3`; `E':real^3->real^3`;
                 `f:real^3->real^3`; `f':real^3->real^3`; `ball(vec 0:real^3,rho)`;
                 `annulus a (&2):real^3->bool`] SCH1_GLUE_DIFFEO) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
    REWRITE_TAC[IN_BALL_0] THEN STRIP_TAC THEN
    ASM_CASES_TAC `norm(x:real^3) < rho /\ norm(y:real^3) < rho` THENL
     [SUBGOAL_THEN `(E:real^3->real^3) x = E y` MP_TAC THENL
       [SUBGOAL_THEN `(c:real^3->real^3) x = E x /\ (c:real^3->real^3) y = E y` MP_TAC THENL
         [CONJ_TAC THEN USE_THEN "cE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL_0];
          MESON_TAC[ASSUME `(c:real^3->real^3) x = c y`]];
        DISCH_THEN(MP_TAC o AP_TERM `E':real^3->real^3`) THEN
        SUBGOAL_THEN `(x:real^3) IN ball(vec 0,rho) /\ (y:real^3) IN ball(vec 0,rho)`
        STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_BALL_0]; ALL_TAC] THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `a < norm(x:real^3) /\ a < norm(y:real^3)` THENL
     [SUBGOAL_THEN `(f:real^3->real^3) x = f y` MP_TAC THENL
       [SUBGOAL_THEN `(c:real^3->real^3) x = f x /\ (c:real^3->real^3) y = f y` MP_TAC THENL
         [CONJ_TAC THEN USE_THEN "cf" MATCH_MP_TAC THEN
          REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC;
          MESON_TAC[ASSUME `(c:real^3->real^3) x = c y`]];
        DISCH_THEN(MP_TAC o AP_TERM `f':real^3->real^3`) THEN
        SUBGOAL_THEN `(x:real^3) IN annulus (&1 / &2) (&2) /\
                      (y:real^3) IN annulus (&1 / &2) (&2)`
        STRIP_ASSUME_TAC THENL
         [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(norm(x:real^3) <= a /\ rho <= norm(y:real^3)) \/
                  (norm(y:real^3) <= a /\ rho <= norm(x:real^3))` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPEC `IMAGE (f:real^3->real^3) (sphere(vec 0,&3 / &4))` INSIDE_INTER_OUTSIDE) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(c:real^3->real^3) x`) THEN
    MATCH_MP_TAC(TAUT `(d ==> a /\ b) ==> ~(a /\ b) ==> d ==> e`) THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [USE_THEN "P1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN USE_THEN "P2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN USE_THEN "P1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "P2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `c':real^3->real^3`) THEN
  MAP_EVERY EXISTS_TAC [`c:real^3->real^3`; `c':real^3->real^3`] THEN
  ASM_REWRITE_TAC[sch_ball] THEN CONJ_TAC THENL
   [REWRITE_TAC[GSYM BALL_UNION_SPHERE; IMAGE_UNION] THEN
    SUBGOAL_THEN `IMAGE (c:real^3->real^3) (ball(vec 0,&3 / &4)) =
                  IMAGE (E:real^3->real^3) (ball(vec 0,&3 / &4)) /\
                  IMAGE (c:real^3->real^3) (sphere(vec 0,&3 / &4)) =
                  IMAGE (E:real^3->real^3) (sphere(vec 0,&3 / &4))`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THEN
      MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> (c:real^3->real^3) x = g x)
                             ==> IMAGE c s = IMAGE g s`) THEN
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_BALL_0; IN_SPHERE_0] THEN
      DISCH_TAC THEN USE_THEN "cE" MATCH_MP_TAC THEN
      REWRITE_TAC[IN_BALL_0] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    USE_THEN "cf" MATCH_MP_TAC THEN
    REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]);;

let SCH1_CORE = prove
 (`!f f':real^3->real^3.
        sch_neck f f' /\ sch_bounds_ball (IMAGE f (sphere(vec 0,&1))) /\
        (!x. x IN annulus (&1 / &2) (&1)
             ==> f x IN inside(IMAGE f (sphere(vec 0,&1))))
        ==> ?c c'. sch_ball c c' /\
                   IMAGE c (cball(vec 0,&1)) =
                   IMAGE f (sphere(vec 0,&1)) UNION inside(IMAGE f (sphere(vec 0,&1))) /\
                   (!x. x IN annulus (&3 / &4) (&2) ==> c x = f x)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "in"))) THEN
  REWRITE_TAC[sch_bounds_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:real^3->real^3` (X_CHOOSE_THEN `c0':real^3->real^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "bc") (LABEL_TAC "cc")))) THEN
  (* The outer half of the neck lies outside. *)
  SUBGOAL_THEN `!x. x IN annulus (&1) (&2)
                    ==> (f:real^3->real^3) x IN outside(IMAGE f (sphere(vec 0,&1)))`
  (LABEL_TAC "out") THENL
   [MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `&1`] SCH1_NECK_SIDES) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(&3 / &4) % basis 1 IN annulus (&1 / &2) (&1):real^3->bool`
    ASSUME_TAC THENL
     [SIMP_TAC[annulus; IN_ELIM_THM; NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `IMAGE (f:real^3->real^3) (sphere(vec 0,&1))` INSIDE_INTER_OUTSIDE) THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^3->real^3)((&3 / &4) % basis 1)`) THEN
    MATCH_MP_TAC(TAUT `a /\ b ==> ~(a /\ b) ==> c`) THEN CONJ_TAC THENL
     [USE_THEN "in" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x:real^3. x IN annulus (&1 / &2) (&1)
                                       ==> (f:real^3->real^3) x IN outside s`) (concl th))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* The ball chart c0 of the bounded side. *)
  MP_TAC(ISPECL [`c0:real^3->real^3`; `c0':real^3->real^3`;
                 `IMAGE (f:real^3->real^3) (sphere(vec 0,&1))`] SCH1_BALL_INSIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SCH1_NECK_HOMEOMORPHIC THEN
    EXISTS_TAC `f':real^3->real^3` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "c1") (LABEL_TAC "cs"))] THEN
  (* The collar k in c0-coordinates. *)
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `c0:real^3->real^3`;
                 `c0':real^3->real^3`] SCH1_K_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dk") (CONJUNCTS_THEN2 (LABEL_TAC "back")
    (CONJUNCTS_THEN2 (LABEL_TAC "ksph") (CONJUNCTS_THEN2 (LABEL_TAC "kin")
     (LABEL_TAC "kout")))))))) THEN
  (* Smale. *)
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `c0:real^3->real^3`;
                 `c0':real^3->real^3`; `eta:real`] SCH1_STRAIGHTEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^3->real^3` (X_CHOOSE_THEN `Hk:real^3->real^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "dH") (CONJUNCTS_THEN2 (LABEL_TAC "nH")
    (CONJUNCTS_THEN2 (LABEL_TAC "nHk") (LABEL_TAC "sm")))))) THEN
  USE_THEN "dH" (STRIP_ASSUME_TAC o REWRITE_RULE[IN_UNIV] o
    GEN_REWRITE_RULE I [diffeomorphism_on]) THEN
  (* The isotopy and its ambient extension. *)
  USE_THEN "sm" (MP_TAC o MATCH_MP SCH1_SHELL_ISOTOPY) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real` (X_CHOOSE_THEN `Phi:real^3->real^3`
    (X_CHOOSE_THEN `Psi:real^3->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "dPhi")
     (LABEL_TAC "Phik" o BETA_RULE))))))) THEN
  USE_THEN "sm" (STRIP_ASSUME_TAC o BETA_RULE o GEN_REWRITE_RULE I [sch1_shell_map]) THEN
  ABBREV_TAC `R = &1 + w / &2` THEN
  ABBREV_TAC `a = &3 / &4 * (&1 - w / &2)` THEN
  SUBGOAL_THEN `&1 < R /\ R < &1 + eta /\ &1 / &2 < a /\ a < &3 / &4 /\
                &3 / &4 < &3 / &4 * R /\ &3 / &4 * R < &1 /\ &4 / &3 * a = &1 - w / &2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN EXPAND_TAC "a" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* Phi maps the ball of radius R into the unit ball. *)
  SUBGOAL_THEN `IMAGE (Phi:real^3->real^3) (ball(vec 0,R)) SUBSET ball(vec 0,&1)`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM INSIDE_SPHERE] THEN
    USE_THEN "dPhi" (fun th -> REWRITE_TAC[GSYM(MATCH_MP SCH_INSIDE_HOMEOMORPHISM
      (MATCH_MP SCH1_DIFFEO_HOMEO th))]) THEN
    MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN REWRITE_TAC[CONVEX_BALL] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_SPHERE_0; IN_BALL_0] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    USE_THEN "Phik" (MP_TAC o SPEC `z:real^3`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!x:real^3. x IN annulus (&1 / &2) (&1)
                                     ==> norm((Hk:real^3->real^3)
                                              ((c0':real^3->real^3)((f:real^3->real^3) x))) < &1`)
          (concl th))) THEN
    REWRITE_TAC[annulus; IN_ELIM_THM; NORM_MUL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* The inner chart E. *)
  MP_TAC(ISPECL [`c0:real^3->real^3`; `c0':real^3->real^3`; `H:real^3->real^3`;
                 `Hk:real^3->real^3`; `Phi:real^3->real^3`; `Psi:real^3->real^3`;
                 `R:real`] SCH1_INNER_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC `E = \y. (c0:real^3->real^3)((H:real^3->real^3)((Phi:real^3->real^3)
                        ((&4 / &3) % y)))` THEN
  DISCH_THEN(X_CHOOSE_THEN `E':real^3->real^3` (LABEL_TAC "dE")) THEN
  (* E agrees with f near the sphere of radius 3/4. *)
  SUBGOAL_THEN `!y:real^3. y IN annulus a (&3 / &4 * R) ==> (E:real^3->real^3) y = f y`
  (LABEL_TAC "Ef") THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN STRIP_TAC THEN
    EXPAND_TAC "E" THEN REWRITE_TAC[] THEN
    USE_THEN "Phik" (MP_TAC o SPEC `(&4 / &3) % y:real^3`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[NORM_MUL] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      UNDISCH_TAC `&4 / &3 * a = &1 - w / &2` THEN UNDISCH_TAC `&1 + w / &2 = R` THEN
      UNDISCH_TAC `a < norm(y:real^3)` THEN UNDISCH_TAC `norm(y:real^3) < &3 / &4 * R` THEN
      REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[VECTOR_MUL_LID] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "back" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
     [REWRITE_TAC[annulus; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  (* Sides at radius 3/4 and the image of the ball of radius 3/4. *)
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `&3 / &4`] SCH1_SIDES_INNER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "in34") (CONJUNCTS_THEN2 (LABEL_TAC "out34")
    (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `E:real^3->real^3`;
                 `E':real^3->real^3`; `&3 / &4 * R`; `a:real`] SCH1_EBALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "Eb") (LABEL_TAC "Es")) THEN
  (* The glued chart. *)
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `E:real^3->real^3`;
                 `E':real^3->real^3`; `a:real`; `&3 / &4 * R`] SCH1_GLUE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^3->real^3` (X_CHOOSE_THEN `c':real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cb") (LABEL_TAC "cf"))))) THEN
  MAP_EVERY EXISTS_TAC [`c:real^3->real^3`; `c':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  (* The image of the closed unit ball. *)
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`] SCH1_NEST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `cball(vec 0:real^3,&1) =
                cball(vec 0,&3 / &4) UNION {x | &3 / &4 < norm x /\ norm x <= &1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_CBALL_0; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_UNION] THEN USE_THEN "cb" SUBST1_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> (c:real^3->real^3) x = g x)
                         ==> IMAGE c s = IMAGE g s`) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
  USE_THEN "cf" MATCH_MP_TAC THEN REWRITE_TAC[annulus; IN_ELIM_THM] THEN
  UNDISCH_TAC `&3 / &4 < norm(x:real^3)` THEN UNDISCH_TAC `norm(x:real^3) <= &1` THEN
  REAL_ARITH_TAC);;

(* The headline: either the inner half of the neck lies on the bounded side *)
(* (SCH1_CORE applies to f), or the outer half does, and then SCH1_CORE      *)
(* applies to f composed with the inversion in the unit sphere.             *)

let SCH_COLLAR3 = prove
 (`SCH_COLLAR3_STATEMENT`,
  REWRITE_TAC[SCH_COLLAR3_STATEMENT; sch_fills] THEN
  MAP_EVERY X_GEN_TAC [`f:real^3->real^3`; `f':real^3->real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "nk") (LABEL_TAC "bb")) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`; `&1`] SCH1_NECK_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (CONJUNCTS_THEN2 (LABEL_TAC "h1") (LABEL_TAC "h2"))) THENL
   [MP_TAC(ISPECL [`f:real^3->real^3`; `f':real^3->real^3`] SCH1_CORE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3->real^3` (X_CHOOSE_THEN `c':real^3->real^3`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`c:real^3->real^3`; `c':real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "nk" (STRIP_ASSUME_TAC o MATCH_MP SCH1_NECK_INV) THEN
    MP_TAC(ISPECL [`\x:real^3. (f:real^3->real^3)(inv(norm x pow 2) % x)`;
                   `\y:real^3. inv(norm((f':real^3->real^3) y) pow 2) % f' y`] SCH1_CORE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "h2" MATCH_MP_TAC THEN
      MATCH_MP_TAC(CONJUNCT1(SPEC `x:real^3` SCH1_INV_HALVES)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^3->real^3` (X_CHOOSE_THEN `c':real^3->real^3`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`c:real^3->real^3`; `c':real^3->real^3`] THEN
    ASM_REWRITE_TAC[]]);;

