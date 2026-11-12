(* ========================================================================= *)
(* pc_moi_polytope: common simplicial refinements of finite families of     *)
(* polytopes, closure properties of PL polyhedra (pl_polyhedron of           *)
(* pc_moi_stmt.ml), refinement of a simplicial complex compatible with given *)
(* polytopes, and a subdivision on whose simplices a PL map is affine.       *)
(* Moise, Geometric Topology in Dimensions 2 and 3, Secs 5-7;                *)
(* Rourke-Sanderson, Ch 2 (every polyhedron is triangulable).                *)
(* ========================================================================= *)

needs "src/pc_moi_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Elementary closure properties of PL polyhedra.                         *)
(* ------------------------------------------------------------------------- *)

let POLYTOPE_IMP_PL_POLYHEDRON = prove
 (`!s:real^N->bool. polytope s ==> pl_polyhedron s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{s:real^N->bool}` THEN
  REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN ASM_MESON_TAC[]);;

let PL_POLYHEDRON_UNION = prove
 (`!s t:real^N->bool.
        pl_polyhedron s /\ pl_polyhedron t ==> pl_polyhedron (s UNION t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `c UNION d:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[FINITE_UNION; UNIONS_UNION; IN_UNION] THEN
  ASM_MESON_TAC[]);;

let MOI_PLT_UNIONS_INTER_UNIONS = prove
 (`!c d:(real^N->bool)->bool.
        UNIONS c INTER UNIONS d = UNIONS {k INTER l | k IN c /\ l IN d}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  MESON_TAC[IN_INTER]);;

let PL_POLYHEDRON_INTER = prove
 (`!s t:real^N->bool.
        pl_polyhedron s /\ pl_polyhedron t ==> pl_polyhedron (s INTER t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `d:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `{k INTER l | (k:real^N->bool) IN c /\ (l:real^N->bool) IN d}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN ASM_MESON_TAC[POLYTOPE_INTER];
    ASM_REWRITE_TAC[MOI_PLT_UNIONS_INTER_UNIONS]]);;

let PL_POLYHEDRON_IMP_COMPACT = prove
 (`!s:real^N->bool. pl_polyhedron s ==> compact s`,
  REWRITE_TAC[pl_polyhedron] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_UNIONS THEN
  ASM_MESON_TAC[POLYTOPE_IMP_COMPACT]);;

let PL_POLYHEDRON_LINEAR_IMAGE = prove
 (`!(f:real^M->real^N) s.
        linear f /\ pl_polyhedron s ==> pl_polyhedron (IMAGE f s)`,
  REWRITE_TAC[pl_polyhedron] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `IMAGE (IMAGE (f:real^M->real^N)) c` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_UNIONS; FORALL_IN_IMAGE] THEN
  ASM_MESON_TAC[POLYTOPE_LINEAR_IMAGE]);;

let PL_POLYHEDRON_TRANSLATION = prove
 (`!(a:real^N) s. pl_polyhedron s ==> pl_polyhedron (IMAGE (\x. a + x) s)`,
  REWRITE_TAC[pl_polyhedron] THEN REPEAT STRIP_TAC THEN
  EXISTS_TAC `IMAGE (IMAGE (\x:real^N. a + x)) c` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_UNIONS; FORALL_IN_IMAGE] THEN
  ASM_MESON_TAC[POLYTOPE_TRANSLATION_EQ]);;

(* ------------------------------------------------------------------------- *)
(* 2. Cutting a cell complex by finitely many hyperplanes.  This is lemma2   *)
(* in the proof of CELL_COMPLEX_SUBDIVISION_EXISTS                           *)
(* (Multivariate/polytope.ml), which is local to that proof and hence not    *)
(* accessible; statement and proof copied, with three type annotations added *)
(* (type_invention_error is on here).                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_PLT_CELL_COMPLEX_CUT = prove
   (`!m:(real^N->bool)->bool d.
        FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c. c IN m ==> aff_dim c <= d) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2)
        ==> !i. FINITE i
                ==> ?m'. UNIONS m' = UNIONS m /\
                         FINITE m' /\
                         (!c. c IN m' ==> ?d. d IN m /\ c SUBSET d) /\
                         (!c x. c IN m /\ x IN c
                                ==> ?d. d IN m' /\ x IN d /\ d SUBSET c) /\
                         (!c. c IN m' ==> polytope c) /\
                         (!c. c IN m' ==> aff_dim c <= d) /\
                         (!c1 c2. c1 IN m' /\ c2 IN m'
                                  ==> c1 INTER c2 face_of c1 /\
                                      c1 INTER c2 face_of c2) /\
                         (!c x y. c IN m' /\ x IN c /\ y IN c
                                  ==> !a b. (a,b) IN i
                                            ==> a dot x <= b /\ a dot y <= b \/
                                                a dot x >= b /\ a dot y >= b)`,
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
    REWRITE_TAC[NOT_IN_EMPTY; FORALL_PAIR_THM] THEN CONJ_TAC THENL
     [EXISTS_TAC `m:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[SUBSET_REFL];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`; `i:(real^N#real)->bool`] THEN
    GEN_REWRITE_TAC I [IMP_CONJ] THEN
    DISCH_THEN(X_CHOOSE_THEN `n:(real^N->bool)->bool` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (SUBST1_TAC o SYM) MP_TAC) THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `{c INTER {x:real^N | a dot x <= b} | c IN n} UNION
                {c INTER {x:real^N | a dot x >= b} | c IN n}` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_UNION; GSYM INTER_UNIONS; GSYM UNION_OVER_INTER] THEN
      MATCH_MP_TAC(SET_RULE `(!x:real^N. x IN s) ==> t INTER s = t`) THEN
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN REAL_ARITH_TAC;
      ASM_SIMP_TAC[FINITE_UNION; SIMPLE_IMAGE; FINITE_IMAGE];
      REWRITE_TAC[FORALL_IN_UNION; FORALL_IN_GSPEC] THEN
      ASM_MESON_TAC[SUBSET_TRANS; INTER_SUBSET];
      REWRITE_TAC[EXISTS_IN_UNION; EXISTS_IN_GSPEC] THEN
      MAP_EVERY X_GEN_TAC [`c:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
      REWRITE_TAC[OR_EXISTS_THM] THEN
      UNDISCH_THEN
       `!c x:real^N. c IN m /\ x IN c ==> ?d. d IN n /\ x IN d /\ d SUBSET c`
       (MP_TAC o SPECL [`c:real^N->bool`; `x:real^N`]) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
      SIMP_TAC[IN_INTER; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`(a:real^N) dot x`; `b:real`] REAL_LE_TOTAL) THEN
      REWRITE_TAC[real_ge] THEN ASM SET_TAC[];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_SIMP_TAC[POLYTOPE_INTER_POLYHEDRON; POLYHEDRON_HALFSPACE_LE;
                   POLYHEDRON_HALFSPACE_GE];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_MESON_TAC[INT_LE_TRANS; AFF_DIM_SUBSET; INTER_SUBSET];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[SET_RULE
      `(s INTER t) INTER (s' INTER t') = (s INTER s') INTER (t INTER (t':real^N->bool))`] THEN
      MATCH_MP_TAC FACE_OF_INTER_INTER THEN ASM_SIMP_TAC[] THEN
      SIMP_TAC[SET_RULE `(s:real^N->bool) INTER s = s`; FACE_OF_REFL; CONVEX_HALFSPACE_LE;
               CONVEX_HALFSPACE_GE] THEN
      REWRITE_TAC[INTER; IN_ELIM_THM; HYPERPLANE_FACE_OF_HALFSPACE_LE;
                  HYPERPLANE_FACE_OF_HALFSPACE_GE;
                  REAL_ARITH `a <= b /\ a >= b <=> a = b`;
                  REAL_ARITH `a >= b /\ a <= b <=> a = b`];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; IN_UNION; FORALL_AND_THM;
                  IN_INSERT;
                  TAUT `p \/ q ==> r <=> (p ==> r) /\ (q ==> r)`] THEN
      REWRITE_TAC[FORALL_IN_GSPEC; IN_INTER; IN_ELIM_THM; PAIR_EQ] THEN
      SIMP_TAC[] THEN ASM_MESON_TAC[]]);;

(* The same, with the side condition stated cell by cell.                   *)

let MOI_PLT_CELL_COMPLEX_HYPERPLANES = prove
 (`!m:(real^N->bool)->bool i.
        FINITE m /\
        (!c. c IN m ==> polytope c) /\
        (!c1 c2. c1 IN m /\ c2 IN m
                 ==> c1 INTER c2 face_of c1 /\ c1 INTER c2 face_of c2) /\
        FINITE i
        ==> ?m'. UNIONS m' = UNIONS m /\
                 FINITE m' /\
                 (!c. c IN m' ==> polytope c) /\
                 (!c1 c2. c1 IN m' /\ c2 IN m'
                          ==> c1 INTER c2 face_of c1 /\
                              c1 INTER c2 face_of c2) /\
                 (!c a b. c IN m' /\ (a,b) IN i
                          ==> c SUBSET {x | a dot x <= b} \/
                              c SUBSET {x | a dot x >= b})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `&(dimindex(:N)):int`]
    MOI_PLT_CELL_COMPLEX_CUT) THEN
  ASM_REWRITE_TAC[AFF_DIM_LE_UNIV] THEN
  DISCH_THEN(MP_TAC o SPEC `i:real^N#real->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:(real^N->bool)->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`c:real^N->bool`; `a:real^N`; `b:real`] THEN
  STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  MATCH_MP_TAC(TAUT `(~p ==> q) ==> p \/ q`) THEN
  REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LE] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`c:real^N->bool`; `x:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real`]) THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 3. A common cell-complex refinement of finitely many polytopes, and the   *)
(* common simplicial refinement.                                             *)
(* ------------------------------------------------------------------------- *)

(* A polyhedron is cut out by finitely many pairs (a,b): a dot y <= b.      *)

let MOI_PLT_POLYHEDRON_PAIRS = prove
 (`!k:real^N->bool.
        polyhedron k
        ==> ?j. FINITE j /\ k = {y | !a b. (a,b) IN j ==> a dot y <= b}`,
  GEN_TAC THEN REWRITE_TAC[polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `A:(real^N->bool)->real^N`
    (X_CHOOSE_TAC `B:(real^N->bool)->real`)) THEN
  SUBGOAL_THEN
   `!h y:real^N. h IN f ==> (y IN h <=> (A:(real^N->bool)->real^N) h dot y <=
                                        (B:(real^N->bool)->real) h)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `h:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CONJUNCT2 th]) THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\h:real^N->bool. ((A:(real^N->bool)->real^N) h,
                                       (B:(real^N->bool)->real) h)) f` THEN
  ASM_SIMP_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[EXTENSION; IN_INTERS; IN_ELIM_THM; IN_IMAGE; PAIR_EQ] THEN
  ASM_MESON_TAC[]);;

(* Through a point x of a convex set d lying on one side of each of a       *)
(* family of hyperplanes, with x in the polyhedron cut out by the family,   *)
(* there is a face of d through x inside that polyhedron.                    *)

let MOI_PLT_FACE_THROUGH_POINT = prove
 (`!d:real^N->bool j x.
        convex d /\ x IN d /\
        (!a b. (a,b) IN j ==> a dot x <= b) /\
        (!a b. (a,b) IN j ==> d SUBSET {y | a dot y <= b} \/
                              d SUBSET {y | a dot y >= b})
        ==> ?f. f face_of d /\ x IN f /\
                !y. y IN f ==> !a b. (a,b) IN j ==> a dot y <= b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "le") (LABEL_TAC "side")))) THEN
  EXISTS_TAC `INTERS (d INSERT {d INTER {y:real^N | a dot y = b} |
                                (a:real^N,b:real) IN j /\ a dot x = b})` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FACE_OF_INTERS THEN REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN
    ASM_SIMP_TAC[FACE_OF_REFL] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN STRIP_TAC THEN
    REMOVE_THEN "side" (MP_TAC o SPECL [`a:real^N`; `b:real`]) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN STRIP_TAC THENL
     [MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_LE;
      MATCH_MP_TAC FACE_OF_INTER_SUPPORTING_HYPERPLANE_GE] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INTERS; FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[IN_INTERS; FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`] THEN DISCH_TAC THEN
    ASM_CASES_TAC `(a:real^N) dot x = b` THENL
     [ASM_MESON_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    REMOVE_THEN "side" (MP_TAC o SPECL [`a:real^N`; `b:real`]) THEN
    REMOVE_THEN "le" (MP_TAC o SPECL [`a:real^N`; `b:real`]) THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    DISCH_TAC THEN STRIP_TAC THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC]]);;

(* Transitivity of being a union of members of a family.                   *)

let MOI_PLT_UNIONS_REFINE_TRANS = prove
 (`!m t (k:real^N->bool).
        (!d. d IN m ==> ?f. f SUBSET t /\ d = UNIONS f) /\
        (?f. f SUBSET m /\ k = UNIONS f)
        ==> ?f. f SUBSET t /\ k = UNIONS f`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `{s:real^N->bool | s IN t /\ s SUBSET k}` THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?d:real^N->bool. d IN f /\ x IN d` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real^N->bool`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN g /\ x IN s` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

(* A cell complex m with UNIONS m = UNIONS c refining each member of c:     *)
(* cut a box containing UNIONS c by all hyperplanes bounding members of c   *)
(* and keep the faces of the cells that lie in some member of c.             *)

let MOI_PLT_POLYTOPES_CELL_REFINEMENT = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ (!k. k IN c ==> polytope k)
        ==> ?m. FINITE m /\ (!d. d IN m ==> polytope d) /\
                (!d1 d2. d1 IN m /\ d2 IN m
                         ==> d1 INTER d2 face_of d1 /\
                             d1 INTER d2 face_of d2) /\
                UNIONS m = UNIONS c /\
                (!k. k IN c ==> ?f. f SUBSET m /\ k = UNIONS f)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a b:real^N. UNIONS c SUBSET interval[a,b]`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC BOUNDED_SUBSET_CLOSED_INTERVAL THEN
    MATCH_MP_TAC BOUNDED_UNIONS THEN ASM_SIMP_TAC[POLYTOPE_IMP_BOUNDED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?J:(real^N->bool)->(real^N#real)->bool.
      !k. k IN c ==> FINITE (J k) /\
                     !y. y IN k <=> !a b. (a,b) IN J k ==> a dot y <= b`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
    X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `k:real^N->bool` MOI_PLT_POLYHEDRON_PAIRS) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[POLYTOPE_IMP_POLYHEDRON]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `j:real^N#real->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{interval[a:real^N,b]}`;
                 `UNIONS (IMAGE (J:(real^N->bool)->(real^N#real)->bool) c)`]
    MOI_PLT_CELL_COMPLEX_HYPERPLANES) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_SING; IN_SING; POLYTOPE_INTERVAL] THEN
    REPEAT CONJ_TAC THENL
     [MESON_TAC[POLYTOPE_INTERVAL];
      REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
      SIMP_TAC[INTER_IDEMPOT; FACE_OF_REFL; CONVEX_INTERVAL];
      REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!k x:real^N. k IN c /\ x IN k
                 ==> ?f. (?d. d IN n /\ f face_of d) /\ f SUBSET k /\ x IN f`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?d:real^N->bool. d IN n /\ x IN d` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(x:real^N) IN UNIONS n` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; REWRITE_TAC[IN_UNIONS]] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`d:real^N->bool`;
                   `(J:(real^N->bool)->(real^N#real)->bool) k`; `x:real^N`]
      MOI_PLT_FACE_THROUGH_POINT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[POLYTOPE_IMP_CONVEX];
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[];
        MAP_EVERY X_GEN_TAC [`a':real^N`; `b':real`] THEN DISCH_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `{f:real^N->bool | (?d. d IN n /\ f face_of d) /\
                                (?k. k IN c /\ f SUBSET k)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `UNIONS (IMAGE (\d:real^N->bool. {f | f face_of d}) n)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[FINITE_IMAGE; FINITE_POLYTOPE_FACES];
      REWRITE_TAC[SUBSET; UNIONS_IMAGE; IN_ELIM_THM] THEN MESON_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[FACE_OF_INTER_SUBFACE];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
    X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `{f:real^N->bool | (?d. d IN n /\ f face_of d) /\
                                  f SUBSET k}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET]]);;

(* Theorem: a common simplicial refinement of finitely many polytopes.       *)

let POLYTOPES_SIMPLICIAL_REFINEMENT = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ (!k. k IN c ==> polytope k)
     ==> ?t. simplicial_complex t /\ UNIONS t = UNIONS c /\
             !k. k IN c ==> ?f. f SUBSET t /\ k = UNIONS f`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_PLT_POLYTOPES_CELL_REFINEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `m:(real^N->bool)->bool`
    SIMPLICIAL_SUBDIVISION_OF_CELL_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_PLT_UNIONS_REFINE_TRANS THEN
  EXISTS_TAC `m:(real^N->bool)->bool` THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 4. PL polyhedra are the underlying sets of simplicial complexes;          *)
(* refining a simplicial complex compatibly with given polytopes; a         *)
(* subdivision on whose simplices a PL map is affine.                        *)
(* ------------------------------------------------------------------------- *)

let PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX = prove
 (`!s:real^N->bool.
        pl_polyhedron s <=> ?t. simplicial_complex t /\ UNIONS t = s`,
  GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `c:(real^N->bool)->bool` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[simplicial_complex]) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]]);;

(* In a simplicial complex t, a simplex whose relative interior meets a     *)
(* union of simplices of t lies in that union.                               *)

let MOI_PLT_SIMPLEX_SUBSET_UNIONS = prove
 (`!t s f (x:real^N).
        simplicial_complex t /\ s IN t /\ f SUBSET t /\
        x IN relative_interior s /\ x IN UNIONS f
        ==> s SUBSET UNIONS f`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `s INTER s':real^N->bool`;
                 `s:real^N->bool`] SUBSET_OF_FACE_OF) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SUBSET];
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `x:real^N` THEN
      MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[]];
    ASM SET_TAC[]]);;

(* A nonempty simplex of a simplicial complex lies in any union of          *)
(* simplices of the complex that contains it, provided some point of its     *)
(* relative interior is covered: the form used below.                        *)

let MOI_PLT_SIMPLEX_IN_COVER = prove
 (`!t s (u:(real^N->bool)->bool).
        simplicial_complex t /\ s IN t /\ ~(s = {}) /\
        s SUBSET UNIONS {k | k IN u /\ ?f. f SUBSET t /\ k = UNIONS f}
        ==> ?k. k IN u /\ s SUBSET k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x:real^N. x IN relative_interior s` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `convex(s:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    ASM_SIMP_TAC[MEMBER_NOT_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?k f. k IN u /\ f SUBSET t /\ k = UNIONS f /\ (x:real^N) IN k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC
     `s SUBSET UNIONS {k:real^N->bool | k IN u /\
                                        ?f. f SUBSET t /\ k = UNIONS f}` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_PLT_SIMPLEX_SUBSET_UNIONS THEN
  MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `x:real^N`] THEN
  ASM_MESON_TAC[]);;

(* Theorem: refining a simplicial complex compatibly with finitely many     *)
(* polytopes inside its polyhedron.                                          *)

let SIMPLICIAL_COMPLEX_REFINE_POLYTOPES = prove
 (`!c d:(real^N->bool)->bool.
     simplicial_complex c /\ FINITE d /\
     (!k. k IN d ==> polytope k /\ k SUBSET UNIONS c)
     ==> ?t. simplicial_complex t /\ UNIONS t = UNIONS c /\
             (!s. s IN t ==> ?s'. s' IN c /\ s SUBSET s') /\
             (!s. s IN c ==> ?f. f SUBSET t /\ s = UNIONS f) /\
             (!k. k IN d ==> ?f. f SUBSET t /\ k = UNIONS f)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c:(real^N->bool)->bool = {}` THENL
   [EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    UNDISCH_TAC
     `!k:real^N->bool. k IN d ==> polytope k /\ k SUBSET UNIONS c` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; UNIONS_0; SUBSET_EMPTY] THEN
    REWRITE_TAC[simplicial_complex; FINITE_EMPTY; NOT_IN_EMPTY] THEN
    MESON_TAC[UNIONS_0];
    ALL_TAC] THEN
  MP_TAC(ISPEC `c UNION d:(real^N->bool)->bool`
    POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION; IN_UNION] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[simplicial_complex]) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIONS t = UNIONS (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNIONS_UNION] THEN
    REWRITE_TAC[SET_RULE `(a:real^N->bool) UNION b = a <=> b SUBSET a`;
                UNIONS_SUBSET] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_THEN `UNIONS t = UNIONS (c UNION d:(real^N->bool)->bool)`
    (K ALL_TAC) THEN
  EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THENL
     [ASM_MESON_TAC[MEMBER_NOT_EMPTY; EMPTY_SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_PLT_SIMPLEX_IN_COVER THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{k:real^N->bool | k IN c /\ ?f. f SUBSET t /\ k = UNIONS f} = c`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[IN_UNION];
      ALL_TAC] THEN
    UNDISCH_TAC `(s:real^N->bool) IN t` THEN
    UNDISCH_TAC `UNIONS t = UNIONS (c:(real^N->bool)->bool)` THEN
    SET_TAC[];
    ASM_MESON_TAC[IN_UNION];
    ASM_MESON_TAC[IN_UNION]]);;

(* A PL map on a compact set is affine on each of finitely many polytopes   *)
(* inside the set that cover it.                                             *)

let MOI_PLT_PL_MAP_ON_COMPACT_PIECES = prove
 (`!s (f:real^M->real^N).
        compact s /\ pl_map_on s f
        ==> ?d. FINITE d /\ s SUBSET UNIONS d /\
                !k. k IN d ==> polytope k /\ k SUBSET s /\
                               ?l y. linear l /\ !z. z IN k ==> f z = l z + y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_map_on] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^M->(real^M->bool)->bool`
    (X_CHOOSE_TAC `U:real^M->real^M->bool`)) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COMPACT_EQ_HEINE_BOREL]) THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (U:real^M->real^M->bool) s`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^M->real^M->bool`; `s:real^M->bool`;
                 `v:(real^M->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `UNIONS (IMAGE (C:real^M->(real^M->bool)->bool) s0)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SUBSET]];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?x:real^M. x IN s0 /\ y IN (U:real^M->real^M->bool) x`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `s SUBSET UNIONS (v:(real^M->bool)->bool)` THEN
      ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^M) IN s` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(y:real^M) IN UNIONS ((C:real^M->(real^M->bool)->bool) x)`
    MP_TAC THENL
     [SUBGOAL_THEN
       `s INTER (U:real^M->real^M->bool) x SUBSET
        UNIONS ((C:real^M->(real^M->bool)->bool) x)`
      MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM SET_TAC[];
      REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET]]);;

(* Theorem: a subdivision of a simplicial complex on whose simplices a PL   *)
(* map is affine.                                                            *)

let SIMPLICIAL_SUBDIVISION_PL_MAP = prove
 (`!c (f:real^M->real^N).
     simplicial_complex c /\ pl_map_on (UNIONS c) f
     ==> ?t. simplicial_complex t /\ UNIONS t = UNIONS c /\
             (!s. s IN t ==> ?s'. s' IN c /\ s SUBSET s') /\
             (!s. s IN t ==> ?l y. linear l /\ !x. x IN s ==> f x = l x + y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS c:real^M->bool`; `f:real^M->real^N`]
    MOI_PLT_PL_MAP_ON_COMPACT_PIECES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
    REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `d:(real^M->bool)->bool`]
    SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`(\x. vec 0):real^M->real^N`; `vec 0:real^N`] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; LINEAR_ZERO];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^M->bool)->bool`; `s:real^M->bool`;
                 `d:(real^M->bool)->bool`] MOI_PLT_SIMPLEX_IN_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{k:real^M->bool | k IN d /\ ?f. f SUBSET t /\ k = UNIONS f} = d`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(s:real^M->bool) IN t` THEN
    UNDISCH_TAC `UNIONS t = UNIONS (c:(real^M->bool)->bool)` THEN
    UNDISCH_TAC `UNIONS c SUBSET UNIONS (d:(real^M->bool)->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
  ASM_MESON_TAC[SUBSET]);;

