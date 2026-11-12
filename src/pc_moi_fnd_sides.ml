(* ========================================================================= *)
(* pc_moi_fnd_sides: Moise 26.8 in the form proved by sides. Main theorem    *)
(* SURFACE_SIDES_ORIENTABLE_3 : |- MOI_FND_SIDES_ORIENT_R3: a finite closed  *)
(* combinatorial surface in real^3 whose complement is two disjoint open     *)
(* sets i and e, each with frontier |s|, is orientable_surface_complex. The  *)
(* local sign of pc_moi_fnd_sgn (the normal half-ball at a relative interior *)
(* point of a triangle lies in the side D of a two-sided ball; antisymmetric *)
(* and opposite across edges: MOI_FSTR_SG_SWAP, MOI_FSTR_SG_EDGE) is made    *)
(* global: |s| is bounded, i and e restrict to two-sided balls containing    *)
(* |s|, and the sign does not depend on the ball.                            *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_sgn.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* |s| is bounded; the two global sides restrict to two-sided               *)
(* balls (moi_fstr_sides); in a ball containing the triangle, moi_fstr_posn *)
(* of the restricted side does not depend on the ball.                      *)
(* ========================================================================= *)

let MOI_FSD_BOUNDED = prove
 (`!s:(real^3->bool)->bool.
     FINITE s /\ combinatorial_manifold 2 s
     ==> ?R. &0 < R /\ !v. v IN UNIONS s ==> UNIONS s SUBSET ball(v,R)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `bounded(UNIONS (s:(real^3->bool)->bool))` MP_TAC THENL
   [MATCH_MP_TAC BOUNDED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
    UNDISCH_TAC `combinatorial_manifold 2 (s:(real^3->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold; lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^3->bool` o CONJUNCT1 o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  REWRITE_TAC[BOUNDED_POS] THEN DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `&2 * B + &1` THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`v:real^3`; `z:real^3`] DIST_TRIANGLE_LE) THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `v:real^3` th) THEN MP_TAC(SPEC `z:real^3` th)) THEN
  ASM_REWRITE_TAC[dist] THEN NORM_ARITH_TAC);;

let MOI_FSD_SIDES_BALL = prove
 (`!(M:real^3->bool) i e v R.
     open i /\ open e /\ DISJOINT i e /\ i UNION e = (:real^3) DIFF M /\
     frontier i = M /\ frontier e = M /\ &0 < R
     ==> moi_fstr_sides M v R (i INTER ball(v,R)) (e INTER ball(v,R))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fstr_sides] THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_BALL] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ASSUME `DISJOINT (i:real^3->bool) e`) THEN SET_TAC[];
    MP_TAC(ASSUME `(i:real^3->bool) UNION e = (:real^3) DIFF M`) THEN SET_TAC[];
    MP_TAC(ISPECL [`ball(v:real^3,R)`; `i:real^3->bool`] OPEN_INTER_CLOSURE_SUBSET) THEN
    REWRITE_TAC[OPEN_BALL] THEN
    SUBGOAL_THEN `ball(v:real^3,R) INTER i = i INTER ball(v,R)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(M:real^3->bool) SUBSET closure i` MP_TAC THENL
     [UNDISCH_TAC `frontier(i:real^3->bool) = M` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      SET_TAC[]];
    MP_TAC(ISPECL [`ball(v:real^3,R)`; `e:real^3->bool`] OPEN_INTER_CLOSURE_SUBSET) THEN
    REWRITE_TAC[OPEN_BALL] THEN
    SUBGOAL_THEN `ball(v:real^3,R) INTER e = e INTER ball(v,R)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(M:real^3->bool) SUBSET closure e` MP_TAC THENL
     [UNDISCH_TAC `frontier(e:real^3->bool) = M` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      SET_TAC[]]]);;

let MOI_FSD_POSN_GLOBAL = prove
 (`!(i:real^3->bool) v R tau n.
     tau SUBSET ball(v,R)
     ==> (moi_fstr_posn (i INTER ball(v,R)) v R tau n <=>
          ?p d. p IN relative_interior tau /\ &0 < d /\
                !z. z IN ball(p,d) /\ &0 < n dot (z - p) ==> z IN i)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fstr_posn; IN_INTER] THEN EQ_TAC THENL
   [MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(p:real^3) IN ball(v,R)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `tau:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:real^3`; `min d (R - dist(v:real^3,p))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(p:real^3) IN ball(v,R)` THEN REWRITE_TAC[IN_BALL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_BALL; REAL_LT_MIN] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_BALL];
    MP_TAC(ISPECL [`v:real^3`; `p:real^3`; `z:real^3`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The global sign (the normal half-ball at some relative interior point of  *)
(* the triangle lies in i) agrees with the local sign of pc_moi_fnd_sgn at   *)
(* every vertex ball containing |s|; MOI_FSTR_SG_SWAP and MOI_FSTR_SG_EDGE   *)
(* at the vertex a give the two clauses of orientable_surface_complex.       *)
(* ========================================================================= *)

let MOI_FSD_SG_GLOBAL = prove
 (`!(i:real^3->bool) v R a b c.
     convex hull {a,b,c} SUBSET ball(v,R)
     ==> moi_fstr_sg (i INTER ball(v,R)) v R a b c =
         (if ?p d. p IN relative_interior(convex hull {a,b,c}) /\ &0 < d /\
                   !z. z IN ball(p,d) /\ &0 < ((b - a) cross (c - a)) dot (z - p)
                       ==> z IN i
          then &1 else -- &1)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fstr_sg] THEN
  ASM_SIMP_TAC[MOI_FSD_POSN_GLOBAL]);;

let SURFACE_SIDES_ORIENTABLE_3 = prove
 (MOI_FND_SIDES_ORIENT_R3,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `i:real^3->bool` (X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPEC `s:(real^3->bool)->bool` MOI_FSD_BOUNDED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!v. moi_fstr_sides (UNIONS s) v R (i INTER ball(v,R)) (e INTER ball(v:real^3,R))`
  (LABEL_TAC "sd") THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_FSD_SIDES_BALL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b c:real^3. convex hull {a,b,c} IN s ==> a IN UNIONS s /\
                   convex hull {a,b,c} SUBSET UNIONS s`
  (LABEL_TAC "in") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `convex hull {a:real^3,b,c} SUBSET UNIONS s` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(a:real^3) IN convex hull {a,b,c}` MP_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      UNDISCH_TAC `convex hull {a:real^3,b,c} SUBSET UNIONS s` THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[orientable_surface_complex] THEN
  EXISTS_TAC
   `\a b c:real^3.
      if ?p d. p IN relative_interior(convex hull {a,b,c}) /\ &0 < d /\
               !z. z IN ball(p,d) /\ &0 < ((b - a) cross (c - a)) dot (z - p) ==> z IN i
      then &1 else -- &1` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`; `c:real^3`] THEN STRIP_TAC THEN
    USE_THEN "in" (fun th -> STRIP_ASSUME_TAC(MP (SPECL [`a:real^3`; `b:real^3`; `c:real^3`] th)
      (ASSUME `convex hull {a:real^3,b,c} IN s`))) THEN
    SUBGOAL_THEN `convex hull {a:real^3,b,c} SUBSET ball(a,R) /\
                  convex hull {b:real^3,a,c} SUBSET ball(a,R) /\
                  convex hull {a:real^3,c,b} SUBSET ball(a,R)` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SET_RULE `{b:real^3,a,c} = {a,b,c} /\ {a,c,b} = {a,b,c}`] THEN
      ASM_MESON_TAC[SUBSET_TRANS];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:(real^3->bool)->bool`; `a:real^3`; `R:real`;
                   `i INTER ball(a:real^3,R)`; `e INTER ball(a:real^3,R)`;
                   `a:real^3`; `b:real^3`; `c:real^3`] MOI_FSTR_SG_SWAP) THEN
    ASM_SIMP_TAC[MOI_FSD_SG_GLOBAL] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`; `c:real^3`; `c':real^3`] THEN STRIP_TAC THEN
  USE_THEN "in" (fun th -> STRIP_ASSUME_TAC(MP (SPECL [`a:real^3`; `b:real^3`; `c:real^3`] th)
    (ASSUME `convex hull {a:real^3,b,c} IN s`))) THEN
  USE_THEN "in" (fun th -> STRIP_ASSUME_TAC(MP (SPECL [`a:real^3`; `b:real^3`; `c':real^3`] th)
    (ASSUME `convex hull {a:real^3,b,c'} IN s`))) THEN
  SUBGOAL_THEN `convex hull {a:real^3,b,c} SUBSET ball(a,R) /\
                convex hull {a:real^3,b,c'} SUBSET ball(a,R)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(real^3->bool)->bool`; `a:real^3`; `R:real`;
                 `i INTER ball(a:real^3,R)`; `e INTER ball(a:real^3,R)`;
                 `a:real^3`; `b:real^3`; `c:real^3`; `c':real^3`] MOI_FSTR_SG_EDGE) THEN
  ASM_SIMP_TAC[MOI_FSD_SG_GLOBAL]);;

