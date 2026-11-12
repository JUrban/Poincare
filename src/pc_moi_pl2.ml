(* ========================================================================= *)
(* pc_moi_pl2: polygons in the plane and the 2D PL Schoenflies theorem.      *)
(* Moise GTM 47, Sec 2 (polygons, p.16; interior and exterior, p.18) and     *)
(* Sec 3 (Thms 3.4-3.7, pp.28-29).  The polygon induction follows HOL's      *)
(* Pick theorem (100/pick.ml: PICK and POLYGON_CHOP_IN_TWO), with the area  *)
(* additivity replaced by the gluing of two PL 2-balls along an arc.        *)
(* ========================================================================= *)

needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_real.ml";;
needs "src/pc_moi_cone.ml";;
type_invention_error := false;;
loadt "100/pick.ml";;
type_invention_error := true;;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. PL paths: paths real^1 -> real^N that are PL on the unit interval.    *)
(* ------------------------------------------------------------------------- *)

let MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL = prove
 (`!a b:real^N. locally_polyhedral(interval[a,b])`,
  SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL]);;

let MOI_PL2_PL_AFFINE_SCALE = prove
 (`!(s:real^N->bool) (c:real) (d:real^N).
     locally_polyhedral s ==> pl_map_on s (\x. c % x + d)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `linear(\x:real^N. c % x)` ASSUME_TAC THENL
   [REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. c % x`; `d:real^N`]
    PL_MAP_ON_AFFINE) THEN
  ASM_SIMP_TAC[]);;

let MOI_PL2_PL_LINEPATH = prove
 (`!(s:real^1->bool) (a:real^N) b.
     locally_polyhedral s ==> pl_map_on s (linepath(a,b))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\x:real^1. drop x % (b - a) + (a:real^N)` THEN CONJ_TAC THENL
   [REWRITE_TAC[linepath] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `linear(\x:real^1. drop x % (b - a:real^N))` ASSUME_TAC THENL
   [REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^1->bool`; `\x:real^1. drop x % (b - a:real^N)`;
                 `a:real^N`] PL_MAP_ON_AFFINE) THEN
  ASM_SIMP_TAC[]);;

let MOI_PL2_PL_COMPOSE_AFFINE1 = prove
 (`!(g:real^1->real^N) (s:real^1->bool) t (c:real) (d:real^1).
     pl_map_on t g /\ locally_polyhedral s /\
     (!x. x IN s ==> c % x + d IN t)
     ==> pl_map_on s (\x. g(c % x + d))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x. (g:real^1->real^N)(c % x + d)) = g o (\x. c % x + d)`
  SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `t:real^1->bool` THEN
  ASM_SIMP_TAC[MOI_PL2_PL_AFFINE_SCALE] THEN ASM SET_TAC[]);;

let MOI_PL2_PL_JOINPATHS = prove
 (`!g1 g2:real^1->real^N.
     pl_map_on (interval[vec 0,vec 1]) g1 /\
     pl_map_on (interval[vec 0,vec 1]) g2 /\
     pathfinish g1 = pathstart g2
     ==> pl_map_on (interval[vec 0,vec 1]) (g1 ++ g2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `interval[vec 0:real^1,vec 1] =
    interval[vec 0,lift(&1 / &2)] UNION interval[lift(&1 / &2),vec 1]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; DROP_VEC; LIFT_DROP] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x. (g1:real^1->real^N)(&2 % x + vec 0)` THEN CONJ_TAC THENL
     [REWRITE_TAC[joinpaths; IN_INTERVAL_1; LIFT_DROP; VECTOR_ADD_RID] THEN
      SIMP_TAC[];
      MATCH_MP_TAC MOI_PL2_PL_COMPOSE_AFFINE1 THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL; IN_INTERVAL_1;
                      DROP_ADD; DROP_CMUL; DROP_VEC; LIFT_DROP] THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x. (g2:real^1->real^N)(&2 % x + --vec 1)` THEN CONJ_TAC THENL
     [REWRITE_TAC[joinpaths; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
      X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN COND_CASES_TAC THENL
       [SUBGOAL_THEN `x = lift(&1 / &2)` SUBST1_TAC THENL
         [REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `&2 % lift(&1 / &2) = vec 1:real^1` SUBST1_TAC THENL
         [REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP; DROP_VEC] THEN
          REAL_ARITH_TAC;
          ALL_TAC] THEN
        REWRITE_TAC[VECTOR_ARITH `vec 1 + --vec 1:real^1 = vec 0`] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[pathfinish; pathstart]) THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[VECTOR_ARITH `a + --b:real^1 = a - b`]];
      MATCH_MP_TAC MOI_PL2_PL_COMPOSE_AFFINE1 THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL; IN_INTERVAL_1;
                      DROP_ADD; DROP_CMUL; DROP_VEC; LIFT_DROP; DROP_NEG] THEN
      REAL_ARITH_TAC];
    MATCH_MP_TAC CLOSED_SUBSET THEN
    REWRITE_TAC[CLOSED_INTERVAL; SUBSET_UNION];
    MATCH_MP_TAC CLOSED_SUBSET THEN
    REWRITE_TAC[CLOSED_INTERVAL; SUBSET_UNION]]);;

let MOI_PL2_PL_POLYGONAL_PATH = prove
 (`!p:(real^N)list. pl_map_on (interval[vec 0,vec 1]) (polygonal_path p)`,
  SUBGOAL_THEN
   `!p (a:real^N).
      pl_map_on (interval[vec 0,vec 1]) (polygonal_path (CONS a p))`
  ASSUME_TAC THENL
   [LIST_INDUCT_TAC THENL
     [REWRITE_TAC[polygonal_path] THEN
      SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL];
      X_GEN_TAC `a:real^N` THEN ASM_CASES_TAC `t:(real^N)list = []` THENL
       [ASM_REWRITE_TAC[polygonal_path] THEN
        SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL];
        ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS] THEN
        MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
        ASM_SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL;
                     PATHFINISH_LINEPATH; PATHSTART_POLYGONAL_PATH;
                     NOT_CONS_NIL; HD]]];
    LIST_INDUCT_TAC THEN ASM_REWRITE_TAC[polygonal_path] THEN
    SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL]]);;

let MOI_PL2_PL_SUBPATH = prove
 (`!u v g:real^1->real^N.
     pl_map_on (interval[vec 0,vec 1]) g /\
     u IN interval[vec 0,vec 1] /\ v IN interval[vec 0,vec 1]
     ==> pl_map_on (interval[vec 0,vec 1]) (subpath u v g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[subpath] THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\x. (g:real^1->real^N)(drop(v - u) % x + u)` THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_SYM]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_PL2_PL_COMPOSE_AFFINE1 THEN
  EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
  ASM_REWRITE_TAC[MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_ADD; DROP_CMUL; DROP_SUB; DROP_VEC] THEN
  X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `&0 <= (&1 - drop x) * drop u /\ &0 <= drop x * drop v /\
    (&1 - drop x) * drop u <= (&1 - drop x) * &1 /\
    drop x * drop v <= drop x * &1`
  MP_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC];
    REAL_ARITH_TAC]);;

let MOI_PL2_REVERSEPATH_SUBPATH = prove
 (`!g:real^1->real^N. reversepath g = subpath (vec 1) (vec 0) g`,
  REWRITE_TAC[reversepath; subpath; FUN_EQ_THM] THEN REPEAT GEN_TAC THEN
  AP_TERM_TAC THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_SUB; DROP_CMUL; DROP_VEC] THEN
  REAL_ARITH_TAC);;

let MOI_PL2_PL_REVERSEPATH = prove
 (`!g:real^1->real^N.
     pl_map_on (interval[vec 0,vec 1]) g
     ==> pl_map_on (interval[vec 0,vec 1]) (reversepath g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_PL2_REVERSEPATH_SUBPATH] THEN
  MATCH_MP_TAC MOI_PL2_PL_SUBPATH THEN
  ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]);;

let MOI_PL2_PL_SHIFTPATH = prove
 (`!a g:real^1->real^N.
     pl_map_on (interval[vec 0,vec 1]) g /\ pathfinish g = pathstart g /\
     a IN interval[vec 0,vec 1]
     ==> pl_map_on (interval[vec 0,vec 1]) (shiftpath a g)`,
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  SUBGOAL_THEN
   `interval[vec 0:real^1,vec 1] =
    interval[vec 0,vec 1 - a] UNION interval[vec 1 - a,vec 1]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; DROP_VEC; DROP_SUB] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_UNION THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x. (g:real^1->real^N)(&1 % x + a)` THEN CONJ_TAC THENL
     [REWRITE_TAC[shiftpath; IN_INTERVAL_1; DROP_VEC; DROP_SUB; DROP_ADD] THEN
      X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
      COND_CASES_TAC THENL
       [REWRITE_TAC[VECTOR_ARITH `&1 % x + a:real^1 = a + x`];
        ASM_REAL_ARITH_TAC];
      MATCH_MP_TAC MOI_PL2_PL_COMPOSE_AFFINE1 THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL; IN_INTERVAL_1;
                      DROP_ADD; DROP_CMUL; DROP_VEC; DROP_SUB] THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x. (g:real^1->real^N)(&1 % x + (a - vec 1))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[shiftpath; IN_INTERVAL_1; DROP_VEC; DROP_SUB; DROP_ADD] THEN
      X_GEN_TAC `x:real^1` THEN STRIP_TAC THEN
      COND_CASES_TAC THENL
       [SUBGOAL_THEN `a + x:real^1 = vec 1 /\ &1 % x + (a - vec 1) = vec 0`
        (CONJUNCTS_THEN SUBST1_TAC) THENL
         [REWRITE_TAC[GSYM DROP_EQ; DROP_ADD; DROP_CMUL; DROP_SUB; DROP_VEC] THEN
          ASM_REAL_ARITH_TAC;
          RULE_ASSUM_TAC(REWRITE_RULE[pathfinish; pathstart]) THEN
          ASM_REWRITE_TAC[]];
        REWRITE_TAC[VECTOR_ARITH `&1 % x + (a - b):real^1 = a + x - b`]];
      MATCH_MP_TAC MOI_PL2_PL_COMPOSE_AFFINE1 THEN
      EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
      ASM_REWRITE_TAC[MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL; IN_INTERVAL_1;
                      DROP_ADD; DROP_CMUL; DROP_VEC; DROP_SUB] THEN
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC CLOSED_SUBSET THEN
    REWRITE_TAC[CLOSED_INTERVAL; SUBSET_UNION];
    MATCH_MP_TAC CLOSED_SUBSET THEN
    REWRITE_TAC[CLOSED_INTERVAL; SUBSET_UNION]]);;

let MOI_PL2_ARC_PL_HOMEOMORPHISM = prove
 (`!g:real^1->real^N.
     arc g /\ pl_map_on (interval[vec 0,vec 1]) g
     ==> ?h. pl_homeomorphism (interval[vec 0,vec 1],path_image g) (g,h)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHISM_ARC) THEN
  MATCH_MP_TAC MONO_EXISTS THEN
  ASM_SIMP_TAC[HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* 2. Gluing PL homeomorphisms along closed pieces; frontiers of balls;     *)
(* 1- and 2-simplices; the boundary of a triangle as a closed polygon.      *)
(* ------------------------------------------------------------------------- *)

let SPDR5_PL2_INV_AGREE = prove
 (`!(s1:real^M->bool) s2 (t1:real^N->bool) t2 f1 f2 g1 g2.
     (!x. x IN s1 ==> g1(f1 x) = x) /\ (!x. x IN s2 ==> g2(f2 x) = x) /\
     (!x. x IN s1 INTER s2 ==> f1 x = f2 x) /\
     IMAGE f1 (s1 INTER s2) = t1 INTER t2
     ==> !y. y IN t1 INTER t2 ==> g1 y = g2 y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[IN_INTER]);;

let SPDR5_PL2_INJ_AGREE = prove
 (`!(s1:real^M->bool) s2 (f1:real^M->real^N) f2 (g2:real^N->real^M) x z.
     (!x. x IN s2 ==> g2(f2 x) = x) /\ (!x. x IN s1 INTER s2 ==> f1 x = f2 x) /\
     x IN s2 /\ z IN s1 /\ z IN s2 /\ f2 x = f1 z
     ==> x = z`,
  REWRITE_TAC[IN_INTER] THEN MESON_TAC[]);;

let MOI_PL2_PL_HOMEOMORPHISM_UNION = prove
 (`!(s1:real^M->bool) s2 (t1:real^N->bool) t2 f1 g1 f2 g2.
     pl_homeomorphism (s1,t1) (f1,g1) /\ pl_homeomorphism (s2,t2) (f2,g2) /\
     closed s1 /\ closed s2 /\ closed t1 /\ closed t2 /\
     (!x. x IN s1 INTER s2 ==> f1 x = f2 x) /\
     IMAGE f1 (s1 INTER s2) = t1 INTER t2
     ==> pl_homeomorphism (s1 UNION s2,t1 UNION t2)
           ((\x. if x IN s1 then f1 x else f2 x),
            (\y. if y IN t1 then g1 y else g2 y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
  SUBGOAL_THEN `!y. y IN t1 INTER t2 ==> (g1:real^N->real^M) y = g2 y`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s1:real^M->bool`; `s2:real^M->bool`; `t1:real^N->bool`;
                   `t2:real^N->bool`; `f1:real^M->real^N`; `f2:real^M->real^N`;
                   `g1:real^N->real^M`; `g2:real^N->real^M`]
      SPDR5_PL2_INV_AGREE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `fu = \x. if x IN s1 then (f1:real^M->real^N) x else f2 x` THEN
  ABBREV_TAC `gu = \y. if y IN t1 then (g1:real^N->real^M) y else g2 y` THEN
  SUBGOAL_THEN
   `(!x. x IN s1 ==> (fu:real^M->real^N) x = f1 x) /\
    (!x. x IN s2 ==> fu x = f2 x) /\
    (!y. y IN t1 ==> (gu:real^N->real^M) y = g1 y) /\
    (!y. y IN t2 ==> gu y = g2 y)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["fu"; "gu"] THEN REPEAT CONJ_TAC THEN
    GEN_TAC THEN
    DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN s2 /\ ~(x IN s1) ==> ~((f2:real^M->real^N) x IN t1)) /\
    (!y. y IN t2 /\ ~(y IN t1) ==> ~((g2:real^N->real^M) y IN s1))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(f2:real^M->real^N) x IN IMAGE (f1:real^M->real^N) (s1 INTER s2)`
      MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^M` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `x:real^M = z` (fun th -> ASM_MESON_TAC[th]) THEN
      MP_TAC(ISPECL [`s1:real^M->bool`; `s2:real^M->bool`; `f1:real^M->real^N`;
                     `f2:real^M->real^N`; `g2:real^N->real^M`; `x:real^M`;
                     `z:real^M`] SPDR5_PL2_INJ_AGREE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC];
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(g2:real^N->real^M) y IN s1 INTER s2` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^N) IN t1 INTER t2` (fun th -> ASM SET_TAC[th]) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on (s1 UNION s2) (fu:real^M->real^N) /\
    pl_map_on (t1 UNION t2) (gu:real^N->real^M)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PL_MAP_ON_UNION THEN
    ASM_SIMP_TAC[CLOSED_SUBSET; SUBSET_UNION] THEN CONJ_TAC THEN
    MATCH_MP_TAC PL_MAP_ON_EQ THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[homeomorphism] THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNION] THEN
  REPEAT CONJ_TAC THEN ASM SET_TAC[]);;

let MOI_PL2_HOMEOMORPHISM_FRONTIER = prove
 (`!(s:real^N->bool) (t:real^N->bool) f g.
     homeomorphism (s,t) (f,g) /\ closed s /\ closed t
     ==> IMAGE f (frontier s) = frontier t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `IMAGE (f:real^N->real^N) (interior s) SUBSET interior t /\
    IMAGE (g:real^N->real^N) (interior t) SUBSET interior s`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [SUBGOAL_THEN `interior t = interior(IMAGE (f:real^N->real^N) s)`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_INTERIOR THEN
      ASM_REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `interior s = interior(IMAGE (g:real^N->real^N) t)`
      SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_IMAGE_SUBSET_INTERIOR THEN
      ASM_REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN
  MP_TAC(ISPEC `s:real^N->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `t:real^N->bool` INTERIOR_SUBSET) THEN
  ASM SET_TAC[]);;

let MOI_PL2_SIMPLEX_2 = prove
 (`!k:real^N->bool.
     &2 simplex k <=> ?a b c. ~collinear{a,b,c} /\ k = convex hull {a,b,c}`,
  GEN_TAC THEN
  REWRITE_TAC[SIMPLEX; INT_ARITH `&2 + &1:int = &3`; INT_OF_NUM_EQ] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(c:real^N->bool) HAS_SIZE 3` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real^N`] THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `d:real^N`] THEN
    REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT] THEN ASM_MESON_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `d:real^N`] THEN
    STRIP_TAC THEN EXISTS_TAC `{a:real^N,b,d}` THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    UNDISCH_TAC `~collinear{a:real^N,b,d}` THEN
    REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT; DE_MORGAN_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV]);;

let MOI_PL2_SIMPLEX_1 = prove
 (`!k:real^N->bool. &1 simplex k <=> ?a b. ~(a = b) /\ k = segment[a,b]`,
  GEN_TAC THEN
  REWRITE_TAC[SIMPLEX; INT_ARITH `&1 + &1:int = &2`; INT_OF_NUM_EQ;
              SEGMENT_CONVEX_HULL] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(c:real^N->bool) HAS_SIZE 2` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN ASM_MESON_TAC[];
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
    EXISTS_TAC `{a:real^N,b}` THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; AFFINE_INDEPENDENT_2] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV]);;

let MOI_PL2_NONCOLLINEAR_DISTINCT = prove
 (`!a b c:real^N.
     ~collinear{a,b,c} ==> ~(a = b) /\ ~(b = c) /\ ~(c = a)`,
  REPEAT GEN_TAC THEN ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN
  REWRITE_TAC[DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2]);;

let MOI_PL2_TRIANGLE_POLYGON = prove
 (`!a b c:real^N.
     ~collinear{a,b,c}
     ==> simple_path(polygonal_path[a;b;c;a]) /\
         pathstart(polygonal_path[a;b;c;a]) = a /\
         pathfinish(polygonal_path[a;b;c;a]) = a /\
         path_image(polygonal_path[a;b;c;a]) =
           segment[a,b] UNION segment[b,c] UNION segment[c,a]`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_NONCOLLINEAR_DISTINCT) THEN
  SUBGOAL_THEN
   `segment[a:real^N,b] INTER segment[b,c] = {b} /\
    segment[b:real^N,c] INTER segment[c,a] = {c} /\
    segment[c:real^N,a] INTER segment[a,b] = {a}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC INTER_SEGMENT THEN DISJ2_TAC THEN
    POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    REWRITE_TAC[INSERT_AC] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[polygonal_path] THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
              PATHFINISH_LINEPATH] THEN
  SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_LINEPATH;
           PATHSTART_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_JOIN; PATHFINISH_JOIN;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ASM_SIMP_TAC[ARC_JOIN_EQ; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
               ARC_LINEPATH_EQ; PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH] THEN
  ASM SET_TAC[]);;

let MOI_PL2_FRONTIER_TRIANGLE = prove
 (`!a b c:real^2.
     ~collinear{a,b,c}
     ==> frontier(convex hull {a,b,c}) = relative_frontier(convex hull {a,b,c})`,
  SIMP_TAC[FRONTIER_OF_TRIANGLE; RELATIVE_FRONTIER_OF_TRIANGLE]);;

(* ------------------------------------------------------------------------- *)
(* 3. An arc in a PL simple closed curve has a PL complementary arc; PL     *)
(* homeomorphisms of triangle boundaries prescribed on one edge.            *)
(* ------------------------------------------------------------------------- *)

let MOI_PL2_IMAGE_LOOP_COMPLEMENT = prove
 (`!(g:real^1->real^N) t.
     g(vec 0) = g(vec 1) /\ t IN interval[vec 0,vec 1]
     ==> IMAGE g (interval[vec 0,vec 1] DIFF interval(vec 0,t)) =
         IMAGE g (interval[t,vec 1])`,
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
  SUBGOAL_THEN
   `interval[vec 0,vec 1] DIFF interval(vec 0,t) =
    (vec 0:real^1) INSERT interval[t,vec 1]`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_INSERT; IN_INTERVAL_1; DROP_VEC;
                GSYM DROP_EQ] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IMAGE_CLAUSES] THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N) IN s ==> x INSERT s = s`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC]);;

let MOI_PL2_ARC_IN_LOOP = prove
 (`!(g:real^1->real^N) (h:real^1->real^N).
     simple_path g /\ pathfinish g = pathstart g /\
     pl_map_on (interval[vec 0,vec 1]) g /\
     arc h /\ path_image h SUBSET path_image g
     ==> ?k. arc k /\ pl_map_on (interval[vec 0,vec 1]) k /\
             pathstart k = pathfinish h /\ pathfinish k = pathstart h /\
             path_image h INTER path_image k = {pathstart h,pathfinish h} /\
             path_image h UNION path_image k = path_image g`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
  SUBGOAL_THEN `pathstart(h:real^1->real^N) IN path_image g` MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; PATHSTART_IN_PATH_IMAGE]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [path_image] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:real^1`
   (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?gg:real^1->real^N.
      simple_path gg /\ pathfinish gg = pathstart gg /\
      pl_map_on (interval[vec 0,vec 1]) gg /\ path_image gg = path_image g /\
      pathstart gg = pathstart h`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `shiftpath a0 (g:real^1->real^N)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_SHIFTPATH; CLOSED_SHIFTPATH; MOI_PL2_PL_SHIFTPATH;
                 PATH_IMAGE_SHIFTPATH] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_SIMP_TAC[PATHSTART_SHIFTPATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathfinish(h:real^1->real^N) IN path_image gg` MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; PATHFINISH_IN_PATH_IMAGE]; ALL_TAC] THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [path_image] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1`
   (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(gg:real^1->real^N)(vec 0) = pathstart h /\
    gg(vec 1) = pathstart h`
  STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    REWRITE_TAC[pathstart; pathfinish] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`gg:real^1->real^N`; `vec 0:real^1`; `t:real^1`]
    EXISTS_DOUBLE_ARC_EXPLICIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_REWRITE_TAC[DROP_VEC];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`u:real^1->real^N`; `d:real^1->real^N`] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (gg:real^1->real^N)
      (interval[vec 0,vec 1] DIFF interval(vec 0,t)) =
    IMAGE gg (interval[t,vec 1])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PL2_IMAGE_LOOP_COMPLEMENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop t <= &1 /\ &0 <= drop t` STRIP_ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[IN_INTERVAL_1; DROP_VEC]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^1->real^N`; `reversepath d:real^1->real^N`;
                 `path_image h:real^N->bool`] CONNECTED_SUBSET_ARC_PAIR) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ARC_REVERSEPATH; PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                 PATH_IMAGE_REVERSEPATH; CONNECTED_ARC_IMAGE;
                 PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[PATH_IMAGE_REVERSEPATH] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `path_image u = path_image(h:real^1->real^N)` ASSUME_TAC THENL
     [MATCH_MP_TAC ARC_IMAGE_UNIQUE THEN ASM_SIMP_TAC[ARC_IMP_PATH];
      ALL_TAC] THEN
    EXISTS_TAC `subpath t (vec 1) (gg:real^1->real^N)` THEN
    ASM_SIMP_TAC[MOI_PL2_PL_SUBPATH; ENDS_IN_UNIT_INTERVAL;
                 PATHSTART_SUBPATH; PATHFINISH_SUBPATH; PATH_IMAGE_SUBPATH;
                 DROP_VEC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
      ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
      ASM_MESON_TAC[]];
    SUBGOAL_THEN `path_image d = path_image(h:real^1->real^N)` ASSUME_TAC THENL
     [MATCH_MP_TAC ARC_IMAGE_UNIQUE THEN ASM_SIMP_TAC[ARC_IMP_PATH] THEN
      SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `subpath t (vec 0) (gg:real^1->real^N)` THEN
    ASM_SIMP_TAC[MOI_PL2_PL_SUBPATH; ENDS_IN_UNIT_INTERVAL;
                 PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
    REWRITE_TAC[PATH_IMAGE_SUBPATH_GEN] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    ASM_REWRITE_TAC[SEGMENT_1; DROP_VEC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN
      ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
      ASM_MESON_TAC[INTER_COMM; UNION_COMM]]]);;

let MOI_PL2_PL_BALL_1_ARC = prove
 (`!s:real^N->bool.
     pl_ball 1 s
     ==> ?h. arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\ path_image h = s`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; MOI_PL2_SIMPLEX_1] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC))
   ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o
    REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  EXISTS_TAC `(f:real^N->real^N) o linepath(a,b)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[PATH_IMAGE_LINEPATH; ARC_LINEPATH_EQ] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `segment[a:real^N,b]` THEN
    ASM_SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
    REWRITE_TAC[GSYM path_image; PATH_IMAGE_LINEPATH; SUBSET_REFL];
    ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE; PATH_IMAGE_LINEPATH]]);;

let MOI_PL2_PL_HOMEO_LINV = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g x.
     pl_homeomorphism (s,t) (f,g) /\ x IN s ==> g(f x) = x`,
  SIMP_TAC[pl_homeomorphism; homeomorphism]);;

let MOI_PL2_PL_HOMEO_RINV = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g y.
     pl_homeomorphism (s,t) (f,g) /\ y IN t ==> f(g y) = y`,
  SIMP_TAC[pl_homeomorphism; homeomorphism]);;

let MOI_PL2_PL_HOMEO_IMAGE = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     pl_homeomorphism (s,t) (f,g) ==> IMAGE f s = t /\ IMAGE g t = s`,
  SIMP_TAC[pl_homeomorphism; homeomorphism]);;

let MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS = prove
 (`!g:real^1->real^N.
     arc g /\ pl_map_on (interval[vec 0,vec 1]) g
     ==> ?h. pl_homeomorphism (interval[vec 0,vec 1],path_image g) (g,h) /\
             h(pathstart g) = vec 0 /\ h(pathfinish g) = vec 1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `g:real^1->real^N` MOI_PL2_ARC_PL_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `k:real^N->real^1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[pathstart; pathfinish] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_PL2_PL_HOMEO_LINV THEN
  MAP_EVERY EXISTS_TAC
   [`interval[vec 0:real^1,vec 1]`; `path_image(g:real^1->real^N)`] THEN
  ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]);;

let MOI_PL2_TRIANGLE_BOUNDARY_EXTENSION = prove
 (`!(k:real^N->bool) (e0:real^M) e1 e2 (h:real^1->real^N).
     &2 simplex k /\ ~collinear{e0,e1,e2} /\
     arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\
     path_image h SUBSET relative_frontier k
     ==> ?f g. pl_homeomorphism (relative_frontier(convex hull {e0,e1,e2}),
                                 relative_frontier k) (f,g) /\
               !x. x IN interval[vec 0,vec 1]
                   ==> f(linepath(e0,e1) x) = h x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
     (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `relative_frontier(convex hull {a:real^N,b,c}) =
    segment[a,b] UNION segment[b,c] UNION segment[c,a]`
  SUBST_ALL_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  (* the complementary arc kk in the boundary of the triangle abc *)
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`]
    MOI_PL2_TRIANGLE_POLYGON) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`polygonal_path[a:real^N;b;c;a]`; `h:real^1->real^N`]
    MOI_PL2_ARC_IN_LOOP) THEN
  ASM_REWRITE_TAC[MOI_PL2_PL_POLYGONAL_PATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:real^1->real^N` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_NONCOLLINEAR_DISTINCT) THEN
  (* the arc pp: e1 -> e2 -> e0 of the boundary of the triangle e0 e1 e2 *)
  SUBGOAL_THEN
   `?pp:real^1->real^M.
      arc pp /\ pl_map_on (interval[vec 0,vec 1]) pp /\
      pathstart pp = e1 /\ pathfinish pp = e0 /\
      path_image pp = segment[e1,e2] UNION segment[e2,e0] /\
      segment[e0,e1] INTER path_image pp = {e0,e1}`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `linepath(e1:real^M,e2) ++ linepath(e2,e0)` THEN
    SIMP_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
             PATHFINISH_LINEPATH; PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH] THEN
    SUBGOAL_THEN
     `segment[e0:real^M,e1] INTER segment[e1,e2] = {e1} /\
      segment[e1:real^M,e2] INTER segment[e2,e0] = {e2} /\
      segment[e2:real^M,e0] INTER segment[e0,e1] = {e0}`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC INTER_SEGMENT THEN DISJ2_TAC THEN
      UNDISCH_TAC `~collinear{e0:real^M,e1,e2}` THEN
      REWRITE_TAC[INSERT_AC];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_JOIN THEN
      ASM_REWRITE_TAC[ARC_LINEPATH_EQ; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                      PATH_IMAGE_LINEPATH] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
      SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* PL parametrizations by the unit interval *)
  MP_TAC(ISPEC `linepath(e0:real^M,e1)` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_SIMP_TAC[ARC_LINEPATH_EQ; MOI_PL2_PL_LINEPATH;
               MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL; PATHSTART_LINEPATH;
               PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  DISCH_THEN(X_CHOOSE_THEN `l1:real^M->real^1` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `pp:real^1->real^M` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l2:real^M->real^1` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `h:real^1->real^N` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l3:real^N->real^1` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `kk:real^1->real^N` MOI_PL2_ARC_PL_HOMEOMORPHISM_ENDS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l4:real^N->real^1` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (segment[e0:real^M,e1],path_image h)
                     ((h:real^1->real^N) o l1,linepath(e0,e1) o l3) /\
    pl_homeomorphism (path_image pp,path_image kk)
                     ((kk:real^1->real^N) o l2,(pp:real^1->real^M) o l4)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`segment[e0:real^M,e1]`; `path_image(pp:real^1->real^M)`;
    `path_image(h:real^1->real^N)`; `path_image(kk:real^1->real^N)`;
    `(h:real^1->real^N) o (l1:real^M->real^1)`;
    `linepath(e0:real^M,e1) o (l3:real^N->real^1)`;
    `(kk:real^1->real^N) o (l2:real^M->real^1)`;
    `(pp:real^1->real^M) o (l4:real^N->real^1)`]
   MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CLOSED_SEGMENT] THEN
    ASM_SIMP_TAC[CLOSED_PATH_IMAGE; ARC_IMP_PATH; CLOSED_UNION;
                 CLOSED_SEGMENT] THEN
    REWRITE_TAC[o_THM; FORALL_IN_INSERT; NOT_IN_EMPTY; IMAGE_CLAUSES] THEN
    ASM_REWRITE_TAC[] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_REWRITE_TAC[pathstart; pathfinish];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[e0:real^M,e1] UNION segment[e1,e2] UNION segment[e2,e0] =
    segment[e0,e1] UNION path_image pp /\
    segment[a:real^N,b] UNION segment[b,c] UNION segment[c,a] =
    path_image h UNION path_image kk`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x. if x IN segment[e0:real^M,e1] then ((h:real^1->real^N) o l1) x
         else ((kk:real^1->real^N) o l2) x`;
    `\y. if y IN path_image(h:real^1->real^N)
         then (linepath(e0:real^M,e1) o l3) y
         else ((pp:real^1->real^M) o l4) y`] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  BETA_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `linepath(e0:real^M,e1) x IN segment[e0,e1]`
  (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH; path_image] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC MOI_PL2_PL_HOMEO_LINV THEN
  MAP_EVERY EXISTS_TAC
   [`interval[vec 0:real^1,vec 1]`; `segment[e0:real^M,e1]`] THEN
  ASM_REWRITE_TAC[ETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* 4. A PL 2-ball in the plane is the image of any triangle under a PL      *)
(* homeomorphism prescribed on one edge by a PL arc in its frontier (cone   *)
(* extension of a boundary homeomorphism); two PL 2-balls meeting in a      *)
(* common frontier arc form a PL 2-ball (theorem PL_BALL_2_UNION).          *)
(* ------------------------------------------------------------------------- *)

let MOI_PL2_PL_HOMEO_CONTINUOUS = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     pl_homeomorphism (s,t) (f,g) ==> f continuous_on s /\ g continuous_on t`,
  SIMP_TAC[pl_homeomorphism; homeomorphism]);;

let MOI_PL2_PL_HOMEO_COMPACT = prove
 (`!(s:real^M->bool) (t:real^N->bool) f g.
     pl_homeomorphism (s,t) (f,g) /\ compact s ==> compact t`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_PL_HOMEO_IMAGE) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_PL_HOMEO_CONTINUOUS) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th] THEN
    ASSUME_TAC th) THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]);;

let MOI_PL2_FRONTIER_PL_BALL_2 = prove
 (`!(k:real^2->bool) (d:real^2->bool) f g.
     &2 simplex k /\ pl_homeomorphism (k,d) (f,g)
     ==> frontier d = IMAGE f (relative_frontier k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact(k:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(d:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_COMPACT]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_2]) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier k = frontier(k:real^2->bool)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[MOI_PL2_FRONTIER_TRIANGLE]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_PL2_HOMEOMORPHISM_FRONTIER THEN
  EXISTS_TAC `g:real^2->real^2` THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  ASM_MESON_TAC[pl_homeomorphism]);;

let MOI_PL2_BALL_BOUNDARY_ARC = prove
 (`!(d:real^2->bool) (h:real^1->real^2) (e0:real^2) e1 e2.
     pl_ball 2 d /\ arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\
     path_image h SUBSET frontier d /\ ~collinear{e0,e1,e2}
     ==> ?f g. pl_homeomorphism (convex hull {e0,e1,e2},d) (f,g) /\
               !x. x IN interval[vec 0,vec 1]
                   ==> f(linepath(e0,e1) x) = h x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `phi:real^2->real^2`
     (X_CHOOSE_THEN `psi:real^2->real^2` STRIP_ASSUME_TAC)))
   STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `frontier d = IMAGE (phi:real^2->real^2) (relative_frontier k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PL2_FRONTIER_PL_BALL_2 THEN
    EXISTS_TAC `psi:real^2->real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(k:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `compact(d:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^2->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image h SUBSET (d:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `frontier d:real^2->bool` THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_PL_HOMEO_CONTINUOUS) THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `e0:real^2`; `e1:real^2`; `e2:real^2`;
                 `(psi:real^2->real^2) o (h:real^1->real^2)`]
    MOI_PL2_TRIANGLE_BOUNDARY_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        ASM_MESON_TAC[MOI_PL2_PL_HOMEO_RINV; SUBSET]];
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `d:real^2->bool` THEN
      ASM_REWRITE_TAC[GSYM path_image] THEN ASM_MESON_TAC[pl_homeomorphism];
      REWRITE_TAC[PATH_IMAGE_COMPOSE; SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(z:real^2) IN IMAGE (phi:real^2->real^2) (relative_frontier k)`
      MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(psi:real^2->real^2) (phi y) = y`
       (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC MOI_PL2_PL_HOMEO_LINV THEN
      MAP_EVERY EXISTS_TAC [`k:real^2->bool`; `d:real^2->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^2->real^2`
   (X_CHOOSE_THEN `g0:real^2->real^2` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`convex hull {e0:real^2,e1,e2}`; `k:real^2->bool`; `2`;
                 `f0:real^2->real^2`; `g0:real^2->real^2`]
    PL_HOMEOMORPHISM_CONE_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^2`
   (X_CHOOSE_THEN `g1:real^2->real^2` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(phi:real^2->real^2) o (f1:real^2->real^2)` THEN
  EXISTS_TAC `(g1:real^2->real^2) o (psi:real^2->real^2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN
   `linepath(e0:real^2,e1) x IN relative_frontier(convex hull {e0,e1,e2})`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
    REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH; path_image] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[o_THM] THEN
  MATCH_MP_TAC MOI_PL2_PL_HOMEO_RINV THEN
  MAP_EVERY EXISTS_TAC [`k:real^2->bool`; `d:real^2->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `path_image h SUBSET (d:real^2->bool)` THEN
  REWRITE_TAC[path_image; SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]);;

(* Three standard triangles: the triangle with vertices basis 1, basis 2,    *)
(* --basis 2 is cut by the segment from vec 0 to basis 1 into two halves.   *)

let MOI_PL2_IN_TRIANGLE_UP = prove
 (`!x:real^2.
     x IN convex hull {vec 0,basis 1,basis 2} <=>
     &0 <= x$1 /\ &0 <= x$2 /\ x$1 + x$2 <= &1`,
  GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real`; `v:real`; `w:real`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`&1 - (x:real^2)$1 - x$2`; `(x:real^2)$1`; `(x:real^2)$2`] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_PL2_IN_TRIANGLE_DOWN = prove
 (`!x:real^2.
     x IN convex hull {vec 0,basis 1,--basis 2} <=>
     &0 <= x$1 /\ x$2 <= &0 /\ x$1 - x$2 <= &1`,
  GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real`; `v:real`; `w:real`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`&1 - (x:real^2)$1 + x$2`; `(x:real^2)$1`; `--((x:real^2)$2)`] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_PL2_IN_TRIANGLE_BIG = prove
 (`!x:real^2.
     x IN convex hull {basis 1,basis 2,--basis 2} <=>
     &0 <= x$1 /\ x$1 + x$2 <= &1 /\ x$1 - x$2 <= &1`,
  GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real`; `v:real`; `w:real`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(x:real^2)$1`; `(&1 - (x:real^2)$1 + x$2) / &2`;
      `(&1 - (x:real^2)$1 - x$2) / &2`] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             VECTOR_NEG_COMPONENT; BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_PL2_IN_SEGMENT_BASE = prove
 (`!x:real^2.
     x IN segment[vec 0,basis 1] <=> &0 <= x$1 /\ x$1 <= &1 /\ x$2 = &0`,
  GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN EQ_TAC THENL
   [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN X_GEN_TAC `u:real` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC;
    STRIP_TAC THEN EXISTS_TAC `(x:real^2)$1` THEN
    ASM_REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT;
             BASIS_COMPONENT; DIMINDEX_2; ARITH] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_PL2_STD_TRIANGLES = prove
 (`~collinear{vec 0:real^2,basis 1,basis 2} /\
   ~collinear{vec 0:real^2,basis 1,--basis 2} /\
   ~collinear{basis 1:real^2,basis 2,--basis 2} /\
   convex hull {vec 0:real^2,basis 1,basis 2} UNION
   convex hull {vec 0,basis 1,--basis 2} =
   convex hull {basis 1,basis 2,--basis 2} /\
   convex hull {vec 0:real^2,basis 1,basis 2} INTER
   convex hull {vec 0,basis 1,--basis 2} =
   segment[vec 0,basis 1]`,
  REWRITE_TAC[COLLINEAR_3_2D] THEN
  SIMP_TAC[VECTOR_NEG_COMPONENT; VEC_COMPONENT; BASIS_COMPONENT;
           DIMINDEX_2; ARITH] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; MOI_PL2_IN_TRIANGLE_UP;
              MOI_PL2_IN_TRIANGLE_DOWN; MOI_PL2_IN_TRIANGLE_BIG;
              MOI_PL2_IN_SEGMENT_BASE] THEN
  CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC);;

let PL_BALL_2_UNION = prove
 (`!d1 d2:real^2->bool.
     pl_ball 2 d1 /\ pl_ball 2 d2 /\ pl_ball 1 (d1 INTER d2) /\
     d1 INTER d2 SUBSET frontier d1 INTER frontier d2
     ==> pl_ball 2 (d1 UNION d2)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `h:real^1->real^2` STRIP_ASSUME_TAC o
    MATCH_MP MOI_PL2_PL_BALL_1_ARC) THEN
  MP_TAC(ISPECL [`d1:real^2->bool`; `h:real^1->real^2`; `vec 0:real^2`;
                 `basis 1:real^2`; `basis 2:real^2`]
    MOI_PL2_BALL_BOUNDARY_ARC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^2`
   (X_CHOOSE_THEN `g1:real^2->real^2` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`d2:real^2->bool`; `h:real^1->real^2`; `vec 0:real^2`;
                 `basis 1:real^2`; `--basis 2:real^2`]
    MOI_PL2_BALL_BOUNDARY_ARC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^2`
   (X_CHOOSE_THEN `g2:real^2->real^2` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL
   [`convex hull {vec 0:real^2,basis 1,basis 2}`;
    `convex hull {vec 0:real^2,basis 1,--basis 2}`;
    `d1:real^2->bool`; `d2:real^2->bool`;
    `f1:real^2->real^2`; `g1:real^2->real^2`;
    `f2:real^2->real^2`; `g2:real^2->real^2`]
   MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN
    SUBGOAL_THEN
     `compact(convex hull {vec 0:real^2,basis 1,basis 2}) /\
      compact(convex hull {vec 0:real^2,basis 1,--basis 2})`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
      MATCH_MP_TAC FINITE_IMP_COMPACT THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `compact(d1:real^2->bool) /\ compact(d2:real^2->bool)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_COMPACT]; ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH; path_image; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `path_image h = (d1:real^2->bool) INTER d2` THEN
    REWRITE_TAC[path_image] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^1. x IN s ==> (f:real^1->real^2) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN DISCH_TAC THEN
  REWRITE_TAC[pl_ball] THEN
  EXISTS_TAC `convex hull {basis 1:real^2,basis 2,--basis 2}` THEN
  REWRITE_TAC[RIGHT_EXISTS_AND_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN MESON_TAC[MOI_PL2_STD_TRIANGLES];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 5. The closed inside of a simple closed polygon is a PL 2-ball (theorem  *)
(* POLYGON_INSIDE_PL_BALL), by induction on the number of vertices as in    *)
(* HOL's proof of Pick's theorem (100/pick.ml, PICK): POLYGON_CHOP_IN_TWO   *)
(* gives a chord inside, SPLIT_INSIDE_SIMPLE_CLOSED_CURVE splits the        *)
(* inside, and PL_BALL_2_UNION glues the two PL 2-balls along the chord.    *)
(* ------------------------------------------------------------------------- *)

let MOI_PL2_FRONTIER_JORDAN_REGION = prove
 (`!c:real^1->real^2.
     simple_path c /\ pathfinish c = pathstart c
     ==> frontier(path_image c UNION inside(path_image c)) = path_image c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `path_image c UNION inside(path_image c) =
    (:real^2) DIFF outside(path_image(c:real^1->real^2))`
  SUBST1_TAC THENL
   [REWRITE_TAC[INSIDE_OUTSIDE] THEN
    MP_TAC(ISPEC `path_image(c:real^1->real^2)` OUTSIDE_NO_OVERLAP) THEN
    SET_TAC[];
    REWRITE_TAC[FRONTIER_COMPLEMENT] THEN ASM_MESON_TAC[JORDAN_INSIDE_OUTSIDE]]);;

let MOI_PL2_TRIANGLE_CLOSED_INSIDE = prove
 (`!a b c:real^2.
     (segment[a,b] UNION segment[b,c] UNION segment[c,a]) UNION
     inside(segment[a,b] UNION segment[b,c] UNION segment[c,a]) =
     convex hull {a,b,c}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[INSIDE_OF_TRIANGLE] THEN
  REWRITE_TAC[GSYM FRONTIER_OF_TRIANGLE] THEN REWRITE_TAC[frontier] THEN
  SUBGOAL_THEN `closure(convex hull {a:real^2,b,c}) = convex hull {a,b,c}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    MP_TAC(ISPEC `convex hull {a:real^2,b,c}` INTERIOR_SUBSET) THEN
    SET_TAC[]]);;

let MOI_PL2_SPLIT_BALL = prove
 (`!(g1:real^1->real^2) (g2:real^1->real^2) Q R a b.
     ~(a = b) /\
     simple_path g1 /\ pathfinish g1 = pathstart g1 /\
     path_image g1 = Q UNION segment[a,b] /\
     simple_path g2 /\ pathfinish g2 = pathstart g2 /\
     path_image g2 = R UNION segment[a,b] /\
     Q INTER R = {a,b} /\
     inside(Q UNION segment[a,b]) INTER inside(R UNION segment[a,b]) = {} /\
     inside(Q UNION segment[a,b]) UNION inside(R UNION segment[a,b]) UNION
     (segment[a,b] DIFF {a,b}) = inside(Q UNION R) /\
     pl_ball 2 (path_image g1 UNION inside(path_image g1)) /\
     pl_ball 2 (path_image g2 UNION inside(path_image g2))
     ==> pl_ball 2 ((Q UNION R) UNION inside(Q UNION R))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `g1:real^1->real^2` MOI_PL2_FRONTIER_JORDAN_REGION) THEN
  MP_TAC(ISPEC `g2:real^1->real^2` MOI_PL2_FRONTIER_JORDAN_REGION) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  UNDISCH_THEN `path_image g1 = (Q:real^2->bool) UNION segment[a,b]`
    SUBST_ALL_TAC THEN
  UNDISCH_THEN `path_image g2 = (R:real^2->bool) UNION segment[a,b]`
    SUBST_ALL_TAC THEN
  MP_TAC(ISPEC `(Q:real^2->bool) UNION segment[a,b]` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `(R:real^2->bool) UNION segment[a,b]` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPEC `(Q:real^2->bool) UNION R` INSIDE_NO_OVERLAP) THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`] ENDS_IN_SEGMENT) THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `(Q UNION R) UNION inside(Q UNION R) =
    ((Q UNION segment[a,b]) UNION inside(Q UNION segment[a:real^2,b])) UNION
    ((R UNION segment[a,b]) UNION inside(R UNION segment[a,b]))`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PL_BALL_2_UNION THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `((Q UNION segment[a,b]) UNION inside(Q UNION segment[a:real^2,b])) INTER
    ((R UNION segment[a,b]) UNION inside(R UNION segment[a,b])) =
    segment[a,b]`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_BALL_SIMPLEX THEN REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN
    ASM_MESON_TAC[];
    SET_TAC[]]);;

let MOI_PL2_POLYGON_SHORT = prove
 (`!p:(real^2)list.
     LENGTH p <= 4 /\
     simple_path(polygonal_path p) /\
     pathfinish(polygonal_path p) = pathstart(polygonal_path p)
     ==> pl_ball 2 (path_image(polygonal_path p) UNION
                    inside(path_image(polygonal_path p)))`,
  REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ] THEN
  X_GEN_TAC `a:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
  REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ] THEN
  X_GEN_TAC `b:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REWRITE_TAC[polygonal_path; SIMPLE_PATH_LINEPATH_EQ;
                PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `c:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPLICATE_TAC 4 (DISCH_THEN(K ALL_TAC)) THEN
    REWRITE_TAC[polygonal_path] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                PATHFINISH_LINEPATH] THEN
    ASM_CASES_TAC `c:real^2 = a` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH] THEN
    REWRITE_TAC[ARC_LINEPATH_EQ] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    SUBST1_TAC(ISPECL [`b:real^2`; `a:real^2`] (CONJUNCT1 SEGMENT_SYM)) THEN
    REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_THEN(MP_TAC o MATCH_MP
     (REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
    ASM_REWRITE_TAC[FINITE_SEGMENT; FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  X_GEN_TAC `d:real^2` THEN MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
   [REPLICATE_TAC 5 (DISCH_THEN(K ALL_TAC));
    REWRITE_TAC[LENGTH; ARITH_RULE `~(SUC(SUC(SUC(SUC(SUC n)))) <= 4)`]] THEN
  REWRITE_TAC[polygonal_path; PATHSTART_JOIN; PATHFINISH_JOIN] THEN
  REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ASM_CASES_TAC `d:real^2 = a` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATH_IMAGE_JOIN; PATHSTART_LINEPATH;
    ARC_JOIN_EQ; PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
  ASM_CASES_TAC `collinear{a:real^2,b,c}` THENL
   [ALL_TAC;
    DISCH_THEN(K ALL_TAC) THEN
    REWRITE_TAC[MOI_PL2_TRIANGLE_CLOSED_INSIDE] THEN
    MATCH_MP_TAC PL_BALL_SIMPLEX THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
    ASM_MESON_TAC[]] THEN
  REWRITE_TAC[ARC_LINEPATH_EQ] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[UNION_OVER_INTER] THEN
  REWRITE_TAC[UNION_SUBSET] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `segment[b:real^2,c] INTER segment [c,a] = segment[b,c] \/
    segment[b,c] INTER segment [c,a] = segment[c,a] \/
    segment[a,b] INTER segment [b,c] = segment[b,c]`
  (REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [REWRITE_TAC[SET_RULE `(s:real^2->bool) INTER t = s <=> s SUBSET t`;
                SET_RULE `(s:real^2->bool) INTER t = t <=> t SUBSET s`] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [COLLINEAR_BETWEEN_CASES]) THEN
    REWRITE_TAC[SUBSET_SEGMENT; BETWEEN_IN_SEGMENT; ENDS_IN_SEGMENT] THEN
    REWRITE_TAC[SEGMENT_SYM; DISJ_ACI];
    UNDISCH_TAC `segment [b,c] SUBSET {c:real^2}`;
    UNDISCH_TAC `segment [c,a] SUBSET {c:real^2}`;
    UNDISCH_TAC `segment [b,c] SUBSET {a:real^2, b}`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP
   (REWRITE_RULE[IMP_CONJ_ALT] FINITE_SUBSET)) THEN
  ASM_REWRITE_TAC[FINITE_SEGMENT; FINITE_INSERT; FINITE_EMPTY]);;

let POLYGON_INSIDE_PL_BALL = prove
 (`!p:(real^2)list.
     simple_path(polygonal_path p) /\
     pathfinish(polygonal_path p) = pathstart(polygonal_path p)
     ==> pl_ball 2 (path_image(polygonal_path p) UNION
                    inside(path_image(polygonal_path p)))`,
  GEN_TAC THEN WF_INDUCT_TAC `LENGTH(p:(real^2)list)` THEN DISJ_CASES_TAC
  (ARITH_RULE `LENGTH(p:(real^2)list) <= 4 \/ 5 <= LENGTH p`) THENL
   [STRIP_TAC THEN MATCH_MP_TAC MOI_PL2_POLYGON_SHORT THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPEC `p:(real^2)list` POLYGON_CHOP_IN_TWO) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^2`;`b:real^2`] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?p':(real^2)list.
        HD p' = a /\
        LENGTH p' = LENGTH p /\
        path_image(polygonal_path p') = path_image(polygonal_path p) /\
        set_of_list p' = set_of_list p /\
        simple_path(polygonal_path p') /\
        pathfinish(polygonal_path p') = pathstart(polygonal_path p')`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC ROTATE_LIST_TO_FRONT_0 THEN
    EXISTS_TAC `p:(real^2)list` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `5 <= p ==> 3 <= p`] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
      GEN_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[LENGTH] THEN
      ASM_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`pathfinish(polygonal_path(p:(real^2)list)) =
       pathstart(polygonal_path p)`;
      `5 <= LENGTH(p:(real^2)list)`] THEN
    ASM_CASES_TAC `p:(real^2)list = []` THEN
    ASM_REWRITE_TAC[LENGTH; ARITH] THEN
    ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH] THEN
    DISCH_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `l:(real^2)list` THEN
    REWRITE_TAC[APPEND_EQ_NIL; NOT_CONS_NIL] THEN
    ASM_CASES_TAC `l:(real^2)list = []` THENL
     [ASM_MESON_TAC[LENGTH_EQ_NIL]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC o GSYM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(TL l:(real^2)list = [])` ASSUME_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `LENGTH:(real^2)list->num`) THEN
      ASM_SIMP_TAC[LENGTH; LENGTH_TL] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[LAST_APPEND; LENGTH_APPEND; LENGTH_TL; NOT_CONS_NIL] THEN
    ASM_REWRITE_TAC[LAST; HD_APPEND; LENGTH] THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      MATCH_MP_TAC PATH_IMAGE_POLYGONAL_PATH_ROTATE THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      MAP_EVERY UNDISCH_TAC
       [`HD(l:(real^2)list) = LAST l`; `5 <= LENGTH(p:(real^2)list)`;
        `~(l:(real^2)list = [])`] THEN
      ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`l:(real^2)list`,`l:(real^2)list`) THEN
      LIST_INDUCT_TAC THEN REWRITE_TAC[HD; TL; APPEND] THEN
      REWRITE_TAC[SET_OF_LIST_APPEND; set_of_list] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC(SET_RULE
       `(a:real^2) IN s /\ b IN s ==> s UNION {a} = b INSERT s`) THEN
      ASM_REWRITE_TAC[LAST] THEN ONCE_ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[LAST] THEN UNDISCH_TAC `5 <= LENGTH(CONS (h:real^2) t)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH] THEN
      REWRITE_TAC[IN_SET_OF_LIST; MEM_EXISTS_EL; LENGTH] THEN
      DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `0` THEN REWRITE_TAC[EL] THEN ASM_ARITH_TAC;
        EXISTS_TAC `LENGTH(t:(real^2)list) - 1` THEN
        ASM_SIMP_TAC[LAST_EL] THEN ASM_ARITH_TAC];
      MP_TAC(ISPEC `l:(real^2)list` SIMPLE_PATH_POLYGONAL_PATH_ROTATE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^2. MEM x p <=> MEM x p'`
   (fun th -> REWRITE_TAC[th] THEN
              RULE_ASSUM_TAC(REWRITE_RULE[th]))
  THENL [ASM_REWRITE_TAC[GSYM IN_SET_OF_LIST]; ALL_TAC] THEN
  MAP_EVERY (C UNDISCH_THEN (SUBST_ALL_TAC o SYM))
   [`set_of_list(p':(real^2)list) = set_of_list p`;
    `path_image(polygonal_path(p':(real^2)list)) =
     path_image (polygonal_path p)`;
    `LENGTH(p':(real^2)list) = LENGTH(p:(real^2)list)`] THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC))
   [`simple_path(polygonal_path(p:(real^2)list))`;
    `pathfinish(polygonal_path(p:(real^2)list)) =
     pathstart(polygonal_path p)`] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o rev) THEN
  SPEC_TAC(`p':(real^2)list`,`p:(real^2)list`) THEN
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?q r. 2 <= LENGTH q /\ 2 <= LENGTH r /\
          LENGTH q + LENGTH r = LENGTH p + 1 /\
          set_of_list q UNION set_of_list r = set_of_list p /\
          pathstart(polygonal_path q) = pathstart(polygonal_path p) /\
          pathfinish(polygonal_path q) = (b:real^2) /\
          pathstart(polygonal_path r) = b /\
          pathfinish(polygonal_path r) = pathfinish(polygonal_path p) /\
          simple_path(polygonal_path q ++ polygonal_path r) /\
          path_image(polygonal_path q ++ polygonal_path r) =
          path_image(polygonal_path p)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `simple_path(polygonal_path p) /\
      2 <= LENGTH p /\ MEM (b:real^2) p /\
      ~(pathstart(polygonal_path p) = b) /\
      ~(pathfinish(polygonal_path p) = b)`
    MP_TAC THENL
     [ASM_SIMP_TAC[ARITH_RULE `5 <= p ==> 2 <= p`] THEN
      ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; CONJ_ASSOC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEM];
      POP_ASSUM_LIST(K ALL_TAC)] THEN
    WF_INDUCT_TAC `LENGTH(p:(real^2)list)` THEN POP_ASSUM MP_TAC THEN
    SPEC_TAC(`p:(real^2)list`,`p:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `x:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN CONJ_TAC THENL
     [REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                  MEM] THEN
      MESON_TAC[];
      REWRITE_TAC[LENGTH; ARITH]] THEN
    MAP_EVERY X_GEN_TAC [`y:real^2`; `l:(real^2)list`] THEN
    REPLICATE_TAC 3 (DISCH_THEN(K ALL_TAC)) THEN DISCH_TAC THEN
    REWRITE_TAC[polygonal_path] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
    REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    ONCE_REWRITE_TAC[MEM] THEN
    ASM_CASES_TAC `a:real^2 = b` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[MEM] THEN
    ASM_CASES_TAC `x:real^2 = b` THEN ASM_REWRITE_TAC[] THENL
     [FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl) THEN STRIP_TAC THEN
      EXISTS_TAC `[a:real^2;b]` THEN
      EXISTS_TAC `CONS (b:real^2) (CONS y l)` THEN
      ASM_REWRITE_TAC[polygonal_path; LENGTH] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      REPEAT(CONJ_TAC THENL [ARITH_TAC; ALL_TAC]) THEN
      REWRITE_TAC[set_of_list] THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `CONS (x:real^2) (CONS y l)`) THEN
    REWRITE_TAC[LENGTH; ARITH_RULE `n < SUC n`] THEN ANTS_TAC THENL
     [REWRITE_TAC[ARITH_RULE `2 <= SUC(SUC n)`] THEN
      ONCE_REWRITE_TAC[MEM] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ]
        SIMPLE_PATH_JOIN_IMP)) THEN
      ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      SIMP_TAC[PATHFINISH_LINEPATH; ARC_IMP_SIMPLE_PATH];
      ALL_TAC] THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`q:(real^2)list`; `r:(real^2)list`] THEN
    STRIP_TAC THEN MAP_EVERY EXISTS_TAC
     [`CONS (a:real^2) q`; `r:(real^2)list`] THEN
    ASM_REWRITE_TAC[LENGTH; NOT_CONS_NIL; HD] THEN
    REPLICATE_TAC 2 (CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC]) THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[set_of_list; SET_RULE
       `((a:real^2) INSERT s) UNION t = a INSERT (s UNION t)`];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `pathfinish(polygonal_path q) = (b:real^2)` THEN
      REWRITE_TAC[PATHFINISH_POLYGONAL_PATH; LAST; NOT_CONS_NIL] THEN
      UNDISCH_TAC `2 <= LENGTH(q:(real^2)list)` THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `polygonal_path(CONS (a:real^2) q) =
      linepath(a,x) ++ polygonal_path q`
    SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`pathstart(polygonal_path q) =
         pathstart(polygonal_path (CONS (x:real^2) (CONS y l)))`;
        `2 <= LENGTH(q:(real^2)list)`] THEN
      SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
      GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
      REWRITE_TAC[LENGTH; ARITH; polygonal_path] THEN
      SIMP_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `pathstart(polygonal_path(CONS x (CONS y l))) = (x:real^2)`
     (fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THENL
     [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD]; ALL_TAC] THEN
    CONJ_TAC THENL
     [W(MP_TAC o PART_MATCH (rand o rand) SIMPLE_PATH_ASSOC o snd) THEN
      ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `simple_path(linepath(a:real^2,x) ++
                               polygonal_path (CONS x (CONS y l)))` THEN
      ASM_CASES_TAC `pathfinish(polygonal_path r) = (a:real^2)` THENL
       [SUBGOAL_THEN
         `pathfinish(polygonal_path(CONS (x:real^2) (CONS y l))) = a`
        ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHFINISH_LINEPATH;
                     PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH] THEN
        STRIP_TAC THEN MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
        ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        ASM_MESON_TAC[ARC_LINEPATH_EQ];
        SUBGOAL_THEN
         `~(pathfinish(polygonal_path(CONS (x:real^2) (CONS y l))) = a)`
        ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_SIMP_TAC[SIMPLE_PATH_EQ_ARC; PATHSTART_JOIN; PATHSTART_LINEPATH;
                     PATHFINISH_JOIN] THEN
        ASM_SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_JOIN] THEN
        REWRITE_TAC[ARC_LINEPATH_EQ] THEN STRIP_TAC THEN
        SUBGOAL_THEN
         `arc(polygonal_path q ++ polygonal_path r:real^1->real^2)`
        MP_TAC THENL
         [ALL_TAC;
          ASM_SIMP_TAC[ARC_JOIN_EQ; PATHFINISH_LINEPATH; PATHSTART_JOIN]] THEN
        MATCH_MP_TAC SIMPLE_PATH_IMP_ARC THEN
        ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN] THEN
        FIRST_X_ASSUM(MP_TAC o MATCH_MP ARC_DISTINCT_ENDS) THEN
        REWRITE_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL]];
      ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
      SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; NOT_CONS_NIL; HD;
               PATHSTART_POLYGONAL_PATH] THEN
      UNDISCH_THEN
       `path_image(polygonal_path q ++ polygonal_path r) =
        path_image(polygonal_path(CONS (x:real^2) (CONS y l)))`
       (SUBST1_TAC o SYM) THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathstart(polygonal_path p) = (a:real^2)` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `5 <= LENGTH(p:(real^2)list)` THEN
    REWRITE_TAC[PATHSTART_POLYGONAL_PATH] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[LENGTH; ARITH];
    ALL_TAC] THEN
  UNDISCH_THEN `pathfinish (polygonal_path p) = (a:real^2)` SUBST_ALL_TAC THEN
  UNDISCH_THEN `path_image(polygonal_path q ++ polygonal_path r):real^2->bool =
                path_image(polygonal_path p)` (SUBST_ALL_TAC o SYM) THEN
  ABBREV_TAC `n = LENGTH(p:(real^2)list)` THEN
  MAP_EVERY (C UNDISCH_THEN (K ALL_TAC))
   [`MEM (a:real^2) p`;
    `MEM (b:real^2) p`;
    `HD p = (a:real^2)`;
    `(set_of_list q UNION set_of_list r):real^2->bool = set_of_list p`;
    `simple_path(polygonal_path p :real^1->real^2)`] THEN
  SUBGOAL_THEN `3 <= LENGTH(q:(real^2)list)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl)) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a0:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a1:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; ARITH_RULE `3 <= SUC(SUC(SUC n))`] THEN
    REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN `a0:real^2 = a` SUBST_ALL_TAC THEN
    UNDISCH_THEN `a1:real^2 = b` SUBST_ALL_TAC THEN
    UNDISCH_TAC `segment(a:real^2,b) SUBSET
                 inside(path_image(linepath(a,b) ++ polygonal_path r))` THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH; PATHFINISH_LINEPATH] THEN
    MATCH_MP_TAC(SET_RULE
     `inside((s':real^2->bool) UNION t) INTER (s' UNION t) = {} /\ ~(s = {}) /\ s SUBSET s'
      ==> ~(s SUBSET inside(s' UNION t))`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
    ASM_REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SEGMENT_EQ_EMPTY];
    UNDISCH_THEN `2 <= LENGTH(q:(real^2)list)` (K ALL_TAC)] THEN
  SUBGOAL_THEN `3 <= LENGTH(r:(real^2)list)` ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(K ALL_TAC o check is_forall o concl)) THEN
    REPEAT(POP_ASSUM MP_TAC) THEN
    SPEC_TAC(`r:(real^2)list`,`r:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a0:real^2` THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    X_GEN_TAC `a1:real^2` THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; ARITH_RULE `3 <= SUC(SUC(SUC n))`] THEN
    REWRITE_TAC[polygonal_path; PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_THEN `a0:real^2 = b` SUBST_ALL_TAC THEN
    UNDISCH_THEN `a1:real^2 = a` SUBST_ALL_TAC THEN
    UNDISCH_TAC `segment(a:real^2,b) SUBSET
                 inside(path_image(polygonal_path q ++ linepath(b,a)))` THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH] THEN
    ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN
    MATCH_MP_TAC(SET_RULE
     `inside((t:real^2->bool) UNION s') INTER (t UNION s') = {} /\ ~(s = {}) /\ s SUBSET s'
      ==> ~(s SUBSET inside(t UNION s'))`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
    ASM_REWRITE_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SEGMENT_EQ_EMPTY];
    UNDISCH_THEN `2 <= LENGTH(r:(real^2)list)` (K ALL_TAC)] THEN
  SUBGOAL_THEN `simple_path(linepath(b:real^2,a) ++ polygonal_path q)`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH; ARC_LINEPATH_EQ] THEN
    STRIP_TAC THEN REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `(s:real^2->bool) SUBSET i
      ==> c INTER i = {}
          ==> (s UNION {a,b}) INTER c SUBSET {b,a}`)) THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN
    MATCH_MP_TAC(SET_RULE
     `inside((s:real^2->bool) UNION t) INTER (s UNION t) = {}
      ==> s INTER inside(s UNION t) = {}`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    ALL_TAC] THEN
  SUBGOAL_THEN `simple_path(linepath(a:real^2,b) ++ polygonal_path r)`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATHSTART_LINEPATH;
                 PATHFINISH_LINEPATH; ARC_LINEPATH_EQ] THEN
    STRIP_TAC THEN REWRITE_TAC[PATH_IMAGE_LINEPATH] THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
     `(s:real^2->bool) SUBSET i
      ==> c INTER i = {}
          ==> (s UNION {a,b}) INTER c SUBSET {a,b}`)) THEN
    ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN
    MATCH_MP_TAC(SET_RULE
     `inside((s:real^2->bool) UNION t) INTER (s UNION t) = {}
      ==> t INTER inside(s UNION t) = {}`) THEN
    REWRITE_TAC[INSIDE_NO_OVERLAP];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(ISPEC `CONS (a:real^2) r` th) THEN
    MP_TAC(ISPEC `CONS (b:real^2) q` th)) THEN
  REWRITE_TAC[LENGTH] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `polygonal_path(CONS (b:real^2) q) = linepath(b,a) ++ polygonal_path q`
  SUBST_ALL_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SPEC_TAC(`q:(real^2)list`,`q:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; polygonal_path] THEN
    SIMP_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH];
    STRIP_TAC] THEN
  REWRITE_TAC[LENGTH] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `polygonal_path(CONS (a:real^2) r) = linepath(a,b) ++ polygonal_path r`
  SUBST_ALL_TAC THENL
   [POP_ASSUM_LIST(MP_TAC o end_itlist CONJ) THEN
    SPEC_TAC(`r:(real^2)list`,`r:(real^2)list`) THEN
    MATCH_MP_TAC list_INDUCT THEN REWRITE_TAC[LENGTH; ARITH] THEN
    GEN_TAC THEN MATCH_MP_TAC list_INDUCT THEN
    REWRITE_TAC[LENGTH; ARITH; polygonal_path] THEN
    SIMP_TAC[PATHSTART_POLYGONAL_PATH; HD; NOT_CONS_NIL];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`polygonal_path q:real^1->real^2`;
                 `reversepath(polygonal_path r):real^1->real^2`;
                 `linepath(a:real^2,b)`; `a:real^2`; `b:real^2`]
        SPLIT_INSIDE_SIMPLE_CLOSED_CURVE) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                    PATHSTART_REVERSEPATH; PATHFINISH_REVERSEPATH;
                    SIMPLE_PATH_LINEPATH_EQ] THEN
    UNDISCH_TAC
     `simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ; PATH_IMAGE_LINEPATH] THEN
    ASM_SIMP_TAC[PATH_IMAGE_REVERSEPATH; ARC_IMP_SIMPLE_PATH;
     SIMPLE_PATH_REVERSEPATH] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(s:real^2->bool) INTER t SUBSET {a,b} /\
        a IN s /\ b IN s /\ a IN t /\ b IN t
        ==> s INTER t = {a,b}`) THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
      REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      UNDISCH_TAC
       `segment(a:real^2,b) SUBSET
        inside(path_image(polygonal_path q ++ polygonal_path r))` THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN MATCH_MP_TAC(SET_RULE
       `(a:real^2) IN t /\ b IN t /\ inside(t UNION u) INTER (t UNION u) = {}
        ==> s SUBSET inside(t UNION u)
            ==> t INTER (s UNION {a,b}) = {a,b}`) THEN
      REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
      REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      UNDISCH_TAC
       `segment(a:real^2,b) SUBSET
        inside(path_image(polygonal_path q ++ polygonal_path r))` THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN] THEN MATCH_MP_TAC(SET_RULE
       `(a:real^2) IN u /\ b IN u /\ inside(t UNION u) INTER (t UNION u) = {}
        ==> s SUBSET inside(t UNION u)
            ==> u INTER (s UNION {a,b}) = {a,b}`) THEN
      REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
      ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
      REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE
       `(s:real^2->bool) SUBSET i
        ==> inside(q UNION r) INTER (q UNION r) = {} /\
            inside(q UNION r) = i /\
            ~(s = {})
            ==> ~((s UNION {a,b}) INTER inside(q UNION r) = {})`)) THEN
      ASM_REWRITE_TAC[INSIDE_NO_OVERLAP; SEGMENT_EQ_EMPTY] THEN
      ASM_SIMP_TAC[PATH_IMAGE_JOIN]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATH_IMAGE_REVERSEPATH; PATH_IMAGE_LINEPATH] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `path_image(polygonal_path q) INTER path_image(polygonal_path r) =
    {a:real^2,b}`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `simple_path(polygonal_path q ++ polygonal_path r :real^1->real^2)` THEN
    ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ] THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `s INTER t SUBSET {a,b} /\ a IN s /\ b IN s /\ a IN t /\ b IN t
      ==> s INTER t = {a:real^2,b}`) THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PL2_SPLIT_BALL THEN
  MAP_EVERY EXISTS_TAC
   [`linepath(b:real^2,a) ++ polygonal_path q`;
    `linepath(a:real^2,b) ++ polygonal_path r`; `a:real^2`; `b:real^2`] THEN
  ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH;
                  PATHFINISH_LINEPATH] THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 6. A PL 1-sphere in the plane is a simple closed polygon (theorem        *)
(* PL_SPHERE_1_POLYGON): refine each edge of the triangle so that the PL    *)
(* homeomorphism is affine on every segment of the refinement, and map the  *)
(* refined vertex list.                                                      *)
(* ------------------------------------------------------------------------- *)

(* moi_pl2_affsteps f l: f is affine on every segment between consecutive    *)
(* entries of the list l.                                                     *)

let moi_pl2_affsteps = define
 `(moi_pl2_affsteps (f:real^M->real^N) [] <=> T) /\
  (moi_pl2_affsteps f [a] <=> T) /\
  (moi_pl2_affsteps f (CONS a (CONS b l)) <=>
     (?l0:real^M->real^N y. linear l0 /\
                            !z. z IN segment[a,b] ==> f z = l0 z + y) /\
     moi_pl2_affsteps f (CONS b l))`;;

let MOI_PL2_AFFINE_LINEPATH = prove
 (`!(f:real^M->real^N) a b l0 y x.
     linear l0 /\ (!z. z IN segment[a,b] ==> f z = l0 z + y) /\
     x IN interval[vec 0,vec 1]
     ==> f(linepath(a,b) x) = linepath(f a,f b) x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linepath(a:real^M,b) x IN segment[a,b]` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM PATH_IMAGE_LINEPATH; path_image] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[ENDS_IN_SEGMENT] THEN
  REWRITE_TAC[linepath] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th;
                                    MATCH_MP LINEAR_CMUL th]) THEN
  VECTOR_ARITH_TAC);;

let MOI_PL2_AFFSTEPS_POLYGONAL = prove
 (`!(f:real^M->real^N) l a.
     moi_pl2_affsteps f (CONS a l)
     ==> !x. x IN interval[vec 0,vec 1]
             ==> f(polygonal_path (CONS a l) x) =
                 polygonal_path (MAP f (CONS a l)) x`,
  GEN_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[MAP; polygonal_path; linepath] THEN
    REPEAT STRIP_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - x) % a + x % a:real^N = a`;
                VECTOR_ARITH `(&1 - x) % a + x % a:real^M = a`];
    ALL_TAC] THEN
  X_GEN_TAC `a:real^M` THEN ASM_CASES_TAC `t:(real^M)list = []` THENL
   [ASM_REWRITE_TAC[MAP; polygonal_path; moi_pl2_affsteps] THEN
    MESON_TAC[MOI_PL2_AFFINE_LINEPATH];
    ALL_TAC] THEN
  REWRITE_TAC[moi_pl2_affsteps] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `l0:real^M->real^N` (X_CHOOSE_TAC `y:real^N`))
   ASSUME_TAC) THEN
  X_GEN_TAC `x:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(MAP (f:real^M->real^N) t = [])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MAP_EQ_NIL]; ALL_TAC] THEN
  ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS; MAP] THEN
  REWRITE_TAC[GSYM(CONJUNCT2 MAP)] THEN
  UNDISCH_TAC `x IN interval[vec 0:real^1,vec 1]` THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN DISCH_TAC THEN
  REWRITE_TAC[joinpaths] THEN COND_CASES_TAC THEN REWRITE_TAC[] THENL
   [MATCH_MP_TAC MOI_PL2_AFFINE_LINEPATH THEN
    MAP_EVERY EXISTS_TAC [`l0:real^M->real^N`; `y:real^N`] THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `h:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_CMUL; DROP_SUB; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_PL2_AFFSTEPS_APPEND = prove
 (`!(f:real^M->real^N) l2.
     ~(l2 = [])
     ==> !t a. LAST(CONS a t) = HD l2
               ==> (moi_pl2_affsteps f (APPEND (CONS a t) (TL l2)) <=>
                    moi_pl2_affsteps f (CONS a t) /\ moi_pl2_affsteps f l2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN LIST_INDUCT_TAC THENL
   [REWRITE_TAC[LAST; APPEND; moi_pl2_affsteps] THEN
    GEN_TAC THEN DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[GSYM CONS_HD_TL];
    ALL_TAC] THEN
  X_GEN_TAC `a:real^M` THEN REWRITE_TAC[LAST_CLAUSES] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `h:real^M`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[APPEND; moi_pl2_affsteps] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONJ_ACI]);;

let MOI_PL2_JOIN_CONGRUENCE = prove
 (`!(g0:real^1->real^N) g h.
     pathfinish g0 = pathstart g /\ pathstart g = pathstart h /\
     pathfinish g = pathfinish h /\ path_image g = path_image h /\
     (arc g <=> arc h)
     ==> path_image(g0 ++ g) = path_image(g0 ++ h) /\
         (arc(g0 ++ g) <=> arc(g0 ++ h)) /\
         (simple_path(g0 ++ g) <=> simple_path(g0 ++ h))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pathfinish g0 = pathstart(h:real^1->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; ARC_JOIN_EQ] THEN
  ASM_CASES_TAC `pathfinish(h:real^1->real^N) = pathstart g0` THENL
   [ASM_SIMP_TAC[SIMPLE_PATH_JOIN_LOOP_EQ];
    ASM_SIMP_TAC[SIMPLE_PATH_EQ_ARC; PATHSTART_JOIN; PATHFINISH_JOIN;
                 ARC_JOIN_EQ]]);;

let MOI_PL2_POLYGONAL_PATH_APPEND = prove
 (`!l2:(real^N)list.
     2 <= LENGTH l2
     ==> !t a b.
           LAST(CONS a (CONS b t)) = HD l2
           ==> pathstart(polygonal_path(APPEND (CONS a (CONS b t)) (TL l2))) =
               a /\
               pathfinish(polygonal_path(APPEND (CONS a (CONS b t)) (TL l2))) =
               LAST l2 /\
               path_image(polygonal_path(APPEND (CONS a (CONS b t)) (TL l2))) =
               path_image(polygonal_path(CONS a (CONS b t)) ++
                          polygonal_path l2) /\
               (arc(polygonal_path(APPEND (CONS a (CONS b t)) (TL l2))) <=>
                arc(polygonal_path(CONS a (CONS b t)) ++ polygonal_path l2)) /\
               (simple_path(polygonal_path(APPEND (CONS a (CONS b t))
                                                  (TL l2))) <=>
                simple_path(polygonal_path(CONS a (CONS b t)) ++
                            polygonal_path l2))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `?h2 t2. l2 = CONS (h2:real^N) t2 /\ ~(t2 = [])`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(l2:(real^N)list = [])` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `2 <= LENGTH(l2:(real^N)list)` THEN
      ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`HD(l2:(real^N)list)`; `TL(l2:(real^N)list)`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONS_HD_TL]; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `2 <= LENGTH(l2:(real^N)list)` THEN
    MP_TAC(ISPEC `l2:(real^N)list` LENGTH_TL) THEN
    ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `l2:(real^N)list = CONS h2 t2` SUBST_ALL_TAC THEN
  REWRITE_TAC[HD; TL] THEN
  SUBGOAL_THEN
   `pathstart(polygonal_path(CONS (h2:real^N) t2)) = h2 /\
    pathfinish(polygonal_path(CONS (h2:real^N) t2)) = LAST(CONS h2 t2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                NOT_CONS_NIL; HD];
    ALL_TAC] THEN
  LIST_INDUCT_TAC THENL
   [REPEAT GEN_TAC THEN
    REWRITE_TAC[LAST_CLAUSES; APPEND] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS] THEN
    REWRITE_TAC[polygonal_path; PATHSTART_JOIN; PATHFINISH_JOIN;
                PATHSTART_LINEPATH] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN
  REWRITE_TAC[LAST_CLAUSES] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`b:real^N`; `h:real^N`]) THEN
  ASM_REWRITE_TAC[LAST_CLAUSES] THEN
  REWRITE_TAC[APPEND; polygonal_path] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `pathstart(polygonal_path(CONS (b:real^N) (CONS h t))) = b /\
    pathfinish(polygonal_path(CONS (b:real^N) (CONS h t))) = h2`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                NOT_CONS_NIL; HD] THEN
    ASM_REWRITE_TAC[LAST_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`linepath(a:real^N,b)`;
    `polygonal_path(CONS b (CONS h (APPEND t t2))):real^1->real^N`;
    `polygonal_path(CONS (b:real^N) (CONS h t)) ++ polygonal_path(CONS h2 t2)`]
   MOI_PL2_JOIN_CONGRUENCE) THEN
  ASM_REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHFINISH_LINEPATH;
                  PATHSTART_LINEPATH] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`linepath(a:real^N,b)`;
                 `polygonal_path(CONS (b:real^N) (CONS h t))`;
                 `polygonal_path(CONS (h2:real^N) t2)`] ARC_ASSOC) THEN
  MP_TAC(ISPECL [`linepath(a:real^N,b)`;
                 `polygonal_path(CONS (b:real^N) (CONS h t))`;
                 `polygonal_path(CONS (h2:real^N) t2)`] SIMPLE_PATH_ASSOC) THEN
  ASM_REWRITE_TAC[PATHFINISH_LINEPATH] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
               PATHFINISH_LINEPATH] THEN
  REWRITE_TAC[UNION_ASSOC]);;

let MOI_PL2_EQ_ON_PATH = prove
 (`!g h:real^1->real^N.
     (!x. x IN interval[vec 0,vec 1] ==> g x = h x)
     ==> (simple_path g <=> simple_path h) /\ path_image g = path_image h /\
         pathstart g = pathstart h /\ pathfinish g = pathfinish h`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[simple_path; path; path_image; pathstart; pathfinish] THEN
  ASM_SIMP_TAC[ENDS_IN_UNIT_INTERVAL] THEN CONJ_TAC THENL
   [BINOP_TAC THENL
     [EQ_TAC THEN MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_EQ) THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ASM SET_TAC[]]);;

let MOI_PL2_SEGMENT_DIST_MONO = prove
 (`!u v t y:real^N.
     t IN segment[u,v] /\ y IN segment[t,v] /\ ~(y = t)
     ==> dist(u,t) < dist(u,y)`,
  REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `between (t:real^N) (u,y)` MP_TAC THENL
   [ASM_MESON_TAC[BETWEEN_TRANS_2; BETWEEN_SYM]; ALL_TAC] THEN
  REWRITE_TAC[between] THEN
  MP_TAC(ISPECL [`t:real^N`; `y:real^N`] DIST_POS_LT) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_PL2_SEGMENT_NEAR_START = prove
 (`!u v:real^N e.
     ~(u = v) /\ &0 < e
     ==> ?x. x IN segment[u,v] /\ ~(x = u) /\ dist(u,x) < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^N`; `segment(u:real^N,v)`] CLOSURE_APPROACHABLE) THEN
  ASM_REWRITE_TAC[CLOSURE_SEGMENT; ENDS_IN_SEGMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
  MESON_TAC[DIST_SYM]);;

let MOI_PL2_EDGE_LIST = prove
 (`!(f:real^M->real^N) n (c:(real^M->bool)->bool) u v.
     FINITE c /\ CARD c = n /\ ~(u = v) /\ segment[u,v] SUBSET UNIONS c /\
     (!k. k IN c ==> closed k /\ convex k /\
                     ?l y. linear l /\ !z. z IN k ==> f z = l z + y)
     ==> ?L. HD L = u /\ LAST L = v /\ 2 <= LENGTH L /\
             arc(polygonal_path L) /\
             path_image(polygonal_path L) = segment[u,v] /\
             moi_pl2_affsteps f L`,
  GEN_TAC THEN MATCH_MP_TAC num_WF THEN X_GEN_TAC `n:num` THEN
  DISCH_TAC THEN REPEAT STRIP_TAC THEN
  (* a piece k containing u and a further point x of the segment *)
  SUBGOAL_THEN
   `?k x. k IN c /\ (u:real^M) IN k /\ x IN k /\ x IN segment[u,v] /\
          ~(x = u)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `closed(UNIONS {k:real^M->bool | k IN c /\ ~(u IN k)})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?e. &0 < e /\
          !y:real^M. y IN UNIONS {k | k IN c /\ ~(u IN k)} ==> e <= dist(y,u)`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`u:real^M`; `UNIONS {k:real^M->bool | k IN c /\ ~(u IN k)}`]
        CLOSED_APPROACHABLE) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((u:real^M) IN UNIONS {k | k IN c /\ ~(u IN k)})`
       (fun th -> REWRITE_TAC[th]) THENL
       [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM; REAL_NOT_LT;
                  DE_MORGAN_THM] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`u:real^M`; `v:real^M`; `e:real`]
      MOI_PL2_SEGMENT_NEAR_START) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^M) IN UNIONS c` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(u:real^M) IN k` THENL
     [MAP_EVERY EXISTS_TAC [`k:real^M->bool`; `x:real^M`] THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the point t of k INTER segment[u,v] farthest from u *)
  MP_TAC(ISPECL [`(k:real^M->bool) INTER segment[u,v]`; `u:real^M`]
    DISTANCE_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_INTER_COMPACT THEN
      ASM_SIMP_TAC[COMPACT_SEGMENT];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(t:real^M = u)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
    ASM_REWRITE_TAC[DIST_REFL; REAL_NOT_LE] THEN
    ASM_MESON_TAC[DIST_POS_LT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?l0 y0. linear l0 /\
            !z. z IN segment[u:real^M,t] ==> (f:real^M->real^N) z = l0 z + y0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `segment[u:real^M,t] SUBSET k` MP_TAC THENL
     [ASM_MESON_TAC[CONVEX_CONTAINS_SEGMENT]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  ASM_CASES_TAC `t:real^M = v` THENL
   [EXISTS_TAC `[u:real^M; v]` THEN
    REWRITE_TAC[HD; LAST; NOT_CONS_NIL; LENGTH; polygonal_path;
                moi_pl2_affsteps; ARC_LINEPATH_EQ; PATH_IMAGE_LINEPATH] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the rest of the segment is covered by the other pieces *)
  SUBGOAL_THEN `segment(t:real^M,v) SUBSET UNIONS (c DELETE k)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY;
                DE_MORGAN_THM] THEN
    X_GEN_TAC `y:real^M` THEN STRIP_TAC THEN
    SUBGOAL_THEN `dist(u:real^M,t) < dist(u,y)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_PL2_SEGMENT_DIST_MONO THEN EXISTS_TAC `v:real^M` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^M) IN segment[u,v]` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `~((y:real^M) IN k)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `dist(u:real^M,t) < dist(u,y)` THEN
      REWRITE_TAC[REAL_NOT_LT] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_DELETE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[t:real^M,v] SUBSET UNIONS (c DELETE k)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:real^M`; `v:real^M`] (CONJUNCT2 CLOSURE_SEGMENT)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD((c:(real^M->bool)->bool) DELETE k) < n` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_DELETE] THEN
    MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n - 1 < n`) THEN
    DISCH_TAC THEN UNDISCH_TAC `CARD(c:(real^M->bool)->bool) = n` THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `CARD((c:(real^M->bool)->bool) DELETE k)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL
   [`(c:(real^M->bool)->bool) DELETE k`; `t:real^M`; `v:real^M`]) THEN
  ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^M)list` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?L1. L = CONS (t:real^M) L1 /\ ~(L1 = [])` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(L:(real^M)list = [])` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `2 <= LENGTH(L:(real^M)list)` THEN
      ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
      ALL_TAC] THEN
    EXISTS_TAC `TL(L:(real^M)list)` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONS_HD_TL]; ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `2 <= LENGTH(L:(real^M)list)` THEN
    MP_TAC(ISPEC `L:(real^M)list` LENGTH_TL) THEN
    ASM_REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_THEN `L = CONS (t:real^M) L1` SUBST_ALL_TAC THEN
  EXISTS_TAC `CONS (u:real^M) (CONS t L1)` THEN
  ASM_REWRITE_TAC[HD; LAST_CLAUSES; moi_pl2_affsteps] THEN
  ASM_SIMP_TAC[POLYGONAL_PATH_CONS_CONS] THEN
  SUBGOAL_THEN `pathstart(polygonal_path(CONS (t:real^M) L1)) = t`
  ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_POLYGONAL_PATH; NOT_CONS_NIL; HD]; ALL_TAC] THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
  ASM_SIMP_TAC[UNION_SEGMENT] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[LENGTH] THEN ARITH_TAC;
    MATCH_MP_TAC ARC_JOIN THEN
    ASM_REWRITE_TAC[ARC_LINEPATH_EQ; PATHFINISH_LINEPATH;
                    PATH_IMAGE_LINEPATH] THEN
    ASM_SIMP_TAC[INTER_SEGMENT; SUBSET_REFL];
    ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. Refinement of a triangle boundary by the pieces of a PL map, and the  *)
(* theorems PL_SPHERE_1_POLYGON and PL_SCHOENFLIES_2.                       *)
(* ------------------------------------------------------------------------- *)

let MOI_PL2_LIST_CONS_CONS = prove
 (`!l:(A)list. 2 <= LENGTH l ==> ?u x t. l = CONS u (CONS x t)`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[LENGTH; ARITH] THEN
  SPEC_TAC(`t:(A)list`,`t:(A)list`) THEN LIST_INDUCT_TAC THEN
  REWRITE_TAC[LENGTH; ARITH; CONS_11] THEN MESON_TAC[]);;

let MOI_PL2_LIST_CONS = prove
 (`!(l:(A)list) a. ~(l = []) /\ HD l = a ==> ?t. l = CONS a t`,
  LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL; HD; CONS_11] THEN
  MESON_TAC[]);;

let MOI_PL2_AFFSTEPS_APPEND_GEN = prove
 (`!(f:real^M->real^N) l1 l2.
     ~(l1 = []) /\ ~(l2 = []) /\ LAST l1 = HD l2
     ==> (moi_pl2_affsteps f (APPEND l1 (TL l2)) <=>
          moi_pl2_affsteps f l1 /\ moi_pl2_affsteps f l2)`,
  GEN_TAC THEN LIST_INDUCT_TAC THEN REWRITE_TAC[NOT_CONS_NIL] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `l2:(real^M)list`]
    MOI_PL2_AFFSTEPS_APPEND) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_PL2_ARC_APPEND = prove
 (`!l1 l2:(real^N)list.
     2 <= LENGTH l1 /\ 2 <= LENGTH l2 /\ LAST l1 = HD l2 /\
     arc(polygonal_path l1) /\ arc(polygonal_path l2) /\
     path_image(polygonal_path l1) INTER path_image(polygonal_path l2)
       SUBSET {HD l2}
     ==> arc(polygonal_path(APPEND l1 (TL l2))) /\
         path_image(polygonal_path(APPEND l1 (TL l2))) =
           path_image(polygonal_path l1) UNION path_image(polygonal_path l2) /\
         HD(APPEND l1 (TL l2)) = HD l1 /\
         LAST(APPEND l1 (TL l2)) = LAST l2 /\
         2 <= LENGTH(APPEND l1 (TL l2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `l1:(real^N)list` MOI_PL2_LIST_CONS_CONS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `x:real^N`; `t:(real^N)list`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPEC `l2:(real^N)list` MOI_PL2_LIST_CONS_CONS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:real^N`; `y:real^N`; `s:(real^N)list`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HD; TL]) THEN REWRITE_TAC[HD; TL] THEN
  MP_TAC(SPEC `CONS (b:real^N) (CONS y s)` MOI_PL2_POLYGONAL_PATH_APPEND) THEN
  ASM_REWRITE_TAC[HD; TL] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:(real^N)list`; `a:real^N`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `pathfinish(polygonal_path(CONS a (CONS x t))) = (b:real^N) /\
    pathstart(polygonal_path(CONS (b:real^N) (CONS y s))) = b`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                    NOT_CONS_NIL; HD];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_JOIN THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[PATH_IMAGE_JOIN];
    REWRITE_TAC[APPEND; HD];
    REWRITE_TAC[LAST_APPEND; NOT_CONS_NIL; LAST_CLAUSES];
    REWRITE_TAC[LENGTH_APPEND; LENGTH] THEN ARITH_TAC]);;

let MOI_PL2_LOOP_APPEND = prove
 (`!l1 l2:(real^N)list.
     2 <= LENGTH l1 /\ 2 <= LENGTH l2 /\ LAST l1 = HD l2 /\ LAST l2 = HD l1 /\
     arc(polygonal_path l1) /\ arc(polygonal_path l2) /\
     path_image(polygonal_path l1) INTER path_image(polygonal_path l2)
       SUBSET {HD l1,HD l2}
     ==> simple_path(polygonal_path(APPEND l1 (TL l2))) /\
         pathstart(polygonal_path(APPEND l1 (TL l2))) = HD l1 /\
         pathfinish(polygonal_path(APPEND l1 (TL l2))) = HD l1 /\
         path_image(polygonal_path(APPEND l1 (TL l2))) =
           path_image(polygonal_path l1) UNION path_image(polygonal_path l2) /\
         HD(APPEND l1 (TL l2)) = HD l1 /\ ~(APPEND l1 (TL l2) = [])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `l1:(real^N)list` MOI_PL2_LIST_CONS_CONS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `x:real^N`; `t:(real^N)list`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  MP_TAC(ISPEC `l2:(real^N)list` MOI_PL2_LIST_CONS_CONS) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`b:real^N`; `y:real^N`; `s:(real^N)list`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[HD; TL]) THEN REWRITE_TAC[HD; TL] THEN
  MP_TAC(SPEC `CONS (b:real^N) (CONS y s)` MOI_PL2_POLYGONAL_PATH_APPEND) THEN
  ASM_REWRITE_TAC[HD; TL] THEN
  DISCH_THEN(MP_TAC o SPECL [`t:(real^N)list`; `a:real^N`; `x:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `pathfinish(polygonal_path(CONS a (CONS x t))) = (b:real^N) /\
    pathstart(polygonal_path(CONS a (CONS x t))) = (a:real^N) /\
    pathstart(polygonal_path(CONS (b:real^N) (CONS y s))) = b /\
    pathfinish(polygonal_path(CONS (b:real^N) (CONS y s))) = a`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_POLYGONAL_PATH; PATHFINISH_POLYGONAL_PATH;
                    NOT_CONS_NIL; HD];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[PATH_IMAGE_JOIN];
    REWRITE_TAC[APPEND; HD];
    REWRITE_TAC[APPEND; NOT_CONS_NIL]]);;

let MOI_PL2_TRIANGLE_REFINE = prove
 (`!(f:real^M->real^N) cc a b c.
     ~collinear{a,b,c} /\ FINITE cc /\
     segment[a,b] UNION segment[b,c] UNION segment[c,a] SUBSET UNIONS cc /\
     (!k. k IN cc ==> closed k /\ convex k /\
                      ?l y. linear l /\ !z. z IN k ==> f z = l z + y)
     ==> ?L. simple_path(polygonal_path L) /\
             pathstart(polygonal_path L) = a /\
             pathfinish(polygonal_path L) = a /\
             path_image(polygonal_path L) =
               segment[a,b] UNION segment[b,c] UNION segment[c,a] /\
             HD L = a /\ ~(L = []) /\ moi_pl2_affsteps f L`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_PL2_NONCOLLINEAR_DISTINCT) THEN
  SUBGOAL_THEN
   `segment[a:real^M,b] INTER segment[b,c] = {b} /\
    segment[b:real^M,c] INTER segment[c,a] = {c} /\
    segment[c:real^M,a] INTER segment[a,b] = {a}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC INTER_SEGMENT THEN DISJ2_TAC THEN
    UNDISCH_TAC `~collinear{a:real^M,b,c}` THEN REWRITE_TAC[INSERT_AC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `CARD(cc:(real^M->bool)->bool)`;
                 `cc:(real^M->bool)->bool`] MOI_PL2_EDGE_LIST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPECL [`a:real^M`; `b:real^M`]) THEN
  FIRST_ASSUM(MP_TAC o SPECL [`b:real^M`; `c:real^M`]) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`c:real^M`; `a:real^M`]) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L3:(real^M)list` STRIP_ASSUME_TAC) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L2:(real^M)list` STRIP_ASSUME_TAC) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L1:(real^M)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L2:(real^M)list`; `L3:(real^M)list`] MOI_PL2_ARC_APPEND) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`L1:(real^M)list`; `APPEND (L2:(real^M)list) (TL L3)`]
    MOI_PL2_LOOP_APPEND) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  EXISTS_TAC `APPEND (L1:(real^M)list) (TL(APPEND L2 (TL L3)))` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `~(L1:(real^M)list = []) /\ ~(L2:(real^M)list = []) /\
    ~(L3:(real^M)list = []) /\ ~(APPEND (L2:(real^M)list) (TL L3) = [])`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM LENGTH_EQ_NIL] THEN
    ASM_MESON_TAC[ARITH_RULE `2 <= n ==> ~(n = 0)`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_PL2_AFFSTEPS_APPEND_GEN]);;

let PL_SPHERE_1_POLYGON = prove
 (`!s:real^2->bool.
     pl_sphere 1 s
     ==> ?p. simple_path(polygonal_path p) /\
             pathfinish(polygonal_path p) = pathstart(polygonal_path p) /\
             path_image(polygonal_path p) = s`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
  REWRITE_TAC[MOI_PL2_SIMPLEX_2; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`k:real^2->bool`; `f:real^2->real^2`; `g:real^2->real^2`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2`
     (X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `relative_frontier(convex hull {a:real^2,b,c}) =
    segment[a,b] UNION segment[b,c] UNION segment[c,a]`
  SUBST_ALL_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`segment[a:real^2,b] UNION segment[b,c] UNION segment[c,a]`;
                 `f:real^2->real^2`] MOI_PLM_PL_MAP_ON_COMPACT_FINITE) THEN
  ANTS_TAC THENL
   [SIMP_TAC[COMPACT_UNION; COMPACT_SEGMENT] THEN
    ASM_MESON_TAC[pl_homeomorphism];
    DISCH_THEN(X_CHOOSE_THEN `cc:(real^2->bool)->bool` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`f:real^2->real^2`; `cc:(real^2->bool)->bool`;
                 `a:real^2`; `b:real^2`; `c:real^2`] MOI_PL2_TRIANGLE_REFINE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN
    ASM_MESON_TAC[POLYTOPE_IMP_CLOSED; POLYTOPE_IMP_CONVEX];
    DISCH_THEN(X_CHOOSE_THEN `L:(real^2)list` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`L:(real^2)list`; `a:real^2`] MOI_PL2_LIST_CONS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L0:(real^2)list` SUBST_ALL_TAC) THEN
  EXISTS_TAC `MAP (f:real^2->real^2) (CONS a L0)` THEN
  MP_TAC(ISPECL [`(f:real^2->real^2) o polygonal_path (CONS a L0)`;
                 `polygonal_path(MAP (f:real^2->real^2) (CONS a L0))`]
    MOI_PL2_EQ_ON_PATH) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[o_THM] THEN MATCH_MP_TAC MOI_PL2_AFFSTEPS_POLYGONAL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o
    CONJUNCT1 o REWRITE_RULE[pl_homeomorphism]) THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

let PL_SCHOENFLIES_2 = prove
 (`PL_SCHOENFLIES_2_STATEMENT`,
  REWRITE_TAC[PL_SCHOENFLIES_2_STATEMENT] THEN
  X_GEN_TAC `s:real^2->bool` THEN
  DISCH_THEN(MP_TAC o MATCH_MP PL_SPHERE_1_POLYGON) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^2)list` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC POLYGON_INSIDE_PL_BALL THEN ASM_REWRITE_TAC[]);;

