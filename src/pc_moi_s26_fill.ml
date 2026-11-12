(* ========================================================================= *)
(* pc_moi_s26_fill: Moise GTM 47 p.193 (D), the PL singular disk of 26.4: a *)
(* loop in a polyhedron |c|, null-homotopic in an open set u containing     *)
(* |c|, bounds a PL map of the standard triangle into u whose boundary      *)
(* loop lies in |c| and is homotopic there to the given loop.               *)
(* Main theorem PL_FILL : |- MOI_S26_PL_FILL (pc_moi_s2628_stmt.ml).         *)
(* Route:                                                                    *)
(*   S1 the null-homotopy factors through the cone quotient of the square   *)
(*      onto the triangle (exact boundary values, MOI_S6F_DISK_FILL);       *)
(*   S2 cubes in u around the image and the simplices of c refine to one   *)
(*      simplicial complex l (|c| a union of simplices of l);               *)
(*   S3 a simplicial approximation (MOI_FND_SIMPLICIAL_APPROX of             *)
(*      pc_moi_fnd_stmt5) keeps the boundary in the carriers inside |c|.    *)
(* MOI_S6F_PL_FILL_SA : |- SA(2,3) ==> MOI_S26_PL_FILL; PL_FILL discharges   *)
(* SA(2,3) with SIMPLICIAL_APPROX (pc_moi_fnd_sapprox).                      *)
(* ========================================================================= *)

needs "src/pc_moi_s2628_stmt.ml";;
needs "src/pc_moi_fnd_stmt5.ml";;
needs "src/pc_moi_loop_stmt.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_fnd_sapprox.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The boundary loop of std_triangle is a simple closed path;                *)
(* the cone map (s,t) |-> b + (1 - s) (loop t - b) from the square onto the *)
(* triangle, b in the relative interior: into, onto, and its fibres (the    *)
(* side s = 1 and the pairs t, t' with the same loop point).               *)
(* ========================================================================= *)

let MOI_S6F_LOOP_SIMPLE = prove
 (`simple_path std_triangle_loop`,
  SUBGOAL_THEN
   `segment[vec 0:real^2,basis 1] INTER segment[basis 1,basis 2] = {basis 1} /\
    segment[basis 1:real^2,basis 2] INTER segment[basis 2,vec 0] = {basis 2} /\
    segment[basis 2:real^2,vec 0] INTER segment[vec 0,basis 1] = {vec 0}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC INTER_SEGMENT THEN DISJ2_TAC THEN
    MP_TAC MOI_LTD_STD_TRIANGLE_NONCOLLINEAR THEN REWRITE_TAC[INSERT_AC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(vec 0:real^2 = basis 1) /\ ~(basis 1:real^2 = basis 2) /\
                ~(basis 2:real^2 = vec 0)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN MP_TAC MOI_LTD_STD_TRIANGLE_NONCOLLINEAR THEN
    ASM_REWRITE_TAC[INSERT_AC; COLLINEAR_2];
    ALL_TAC] THEN
  REWRITE_TAC[std_triangle_loop] THEN MATCH_MP_TAC SIMPLE_PATH_JOIN_LOOP THEN
  REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
              PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH; ARC_LINEPATH_EQ] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC ARC_JOIN THEN
    ASM_REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH;
                    ARC_LINEPATH_EQ; SUBSET_REFL];
    SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    UNDISCH_TAC `segment[vec 0:real^2,basis 1] INTER segment[basis 1,basis 2] = {basis 1}` THEN
    UNDISCH_TAC `segment[basis 2:real^2,vec 0] INTER segment[vec 0,basis 1] = {vec 0}` THEN
    SET_TAC[]]);;

let MOI_S6F_LOOP_FRONTIER = prove
 (`!t. t IN interval[vec 0,vec 1]
       ==> std_triangle_loop t IN relative_frontier std_triangle`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `relative_frontier std_triangle = path_image std_triangle_loop` SUBST1_TAC THENL
   [REWRITE_TAC[MOI_LTD_STD_TRIANGLE_LOOP]; ALL_TAC] THEN
  REWRITE_TAC[path_image] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;

let MOI_S6F_FRONTIER_FACTS = prove
 (`!y:real^2. y IN relative_frontier std_triangle
              ==> y IN std_triangle /\ ~(y IN relative_interior std_triangle)`,
  GEN_TAC THEN REWRITE_TAC[relative_frontier; IN_DIFF] THEN
  SIMP_TAC[CLOSURE_CLOSED; MOI_LTD_STD_TRIANGLE_BASIC]);;

let MOI_S6F_CONE_IN = prove
 (`!(b:real^2) s t.
     b IN relative_interior std_triangle /\
     s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1]
     ==> b + (&1 - drop s) % (std_triangle_loop t - b) IN std_triangle`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPEC `t:real^1` MOI_S6F_LOOP_FRONTIER) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S6F_FRONTIER_FACTS) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(b:real^2) IN std_triangle` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH `b + u % (y - b):real^2 = (&1 - u) % b + u % y`] THEN
  MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN
  UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
  REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC);;

let MOI_S6F_CONE_ONTO = prove
 (`!(b:real^2) x.
     b IN relative_interior std_triangle /\ x IN std_triangle
     ==> ?s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
               x = b + (&1 - drop s) % (std_triangle_loop t - b)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `x:real^2 = b` THENL
   [MAP_EVERY EXISTS_TAC [`vec 1:real^1`; `vec 0:real^1`] THEN
    ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL; DROP_VEC] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`std_triangle`; `b:real^2`; `x:real^2`] MOI_BAR_RAY_EXIT) THEN
  ASM_SIMP_TAC[MOI_LTD_STD_TRIANGLE_BASIC; COMPACT_IMP_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^2` (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y:real^2) IN path_image std_triangle_loop` MP_TAC THENL
   [REWRITE_TAC[MOI_LTD_STD_TRIANGLE_LOOP; relative_frontier; IN_DIFF] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; MOI_LTD_STD_TRIANGLE_BASIC];
    ALL_TAC] THEN
  REWRITE_TAC[path_image; IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`lift(&1 - u)`; `t:real^1`] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[LIFT_DROP] THEN VECTOR_ARITH_TAC]);;

let MOI_S6F_CONE_B = prove
 (`!(b:real^2) y u.
     b IN relative_interior std_triangle /\ y IN relative_frontier std_triangle /\
     b + u % (y - b) = b
     ==> u = &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[VECTOR_ARITH `b + u % (y - b):real^2 = b <=> u % (y - b) = vec 0`] THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(y:real^2) IN relative_frontier std_triangle` THEN
  ASM_REWRITE_TAC[relative_frontier; IN_DIFF]);;

let MOI_S6F_CONE_FIBRE = prove
 (`!(b:real^2) s t s' t'.
     b IN relative_interior std_triangle /\
     s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
     s' IN interval[vec 0,vec 1] /\ t' IN interval[vec 0,vec 1] /\
     b + (&1 - drop s) % (std_triangle_loop t - b) =
     b + (&1 - drop s') % (std_triangle_loop t' - b)
     ==> s = vec 1 /\ s' = vec 1 \/
         s = s' /\ (t = t' \/ t = vec 0 /\ t' = vec 1 \/ t = vec 1 /\ t' = vec 0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eq")))))) THEN
  MP_TAC(SPEC `t:real^1` MOI_S6F_LOOP_FRONTIER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(SPEC `t':real^1` MOI_S6F_LOOP_FRONTIER) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `std_triangle_loop t` MOI_S6F_FRONTIER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `std_triangle_loop t'` MOI_S6F_FRONTIER_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(drop s = &1 <=> drop s' = &1)` ASSUME_TAC THENL
   [EQ_TAC THEN DISCH_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH `&1 - x = &0 ==> x = &1`) THEN
      MATCH_MP_TAC MOI_S6F_CONE_B THEN
      MAP_EVERY EXISTS_TAC [`b:real^2`; `std_triangle_loop t'`] THEN
      REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      USE_THEN "eq" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[ASSUME `drop s = &1`; REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
      MATCH_MP_TAC(REAL_ARITH `&1 - x = &0 ==> x = &1`) THEN
      MATCH_MP_TAC MOI_S6F_CONE_B THEN
      MAP_EVERY EXISTS_TAC [`b:real^2`; `std_triangle_loop t`] THEN
      REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      USE_THEN "eq" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[ASSUME `drop s' = &1`; REAL_SUB_REFL; VECTOR_MUL_LZERO; VECTOR_ADD_RID]];
    ALL_TAC] THEN
  ASM_CASES_TAC `drop s = &1` THENL
   [DISJ1_TAC THEN REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN `~(drop s' = &1)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`std_triangle`; `b:real^2`; `std_triangle_loop t`; `std_triangle_loop t'`;
                 `drop s`; `drop s'`] MOI_BAR_RAY_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CLOSURE_CLOSED; MOI_LTD_STD_TRIANGLE_BASIC] THEN
    SUBGOAL_THEN `&0 <= drop s /\ drop s <= &1 /\ &0 <= drop s' /\ drop s' <= &1` MP_TAC THENL
     [UNDISCH_TAC `(s:real^1) IN interval[vec 0,vec 1]` THEN
      UNDISCH_TAC `(s':real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `~(drop s = &1)` THEN UNDISCH_TAC `~(drop s' = &1)` THEN
    USE_THEN "eq" MP_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `b + (&1 - u) % (y - b):real^2 = u % b + (&1 - u) % y`] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[GSYM DROP_EQ]; ALL_TAC] THEN
  MP_TAC MOI_S6F_LOOP_SIMPLE THEN REWRITE_TAC[simple_path] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* A loop null-homotopic in s (as a loop) extends over the                 *)
(* standard triangle with the exact boundary values.  The null-homotopy h  *)
(* on the square (h(0,t) = p t, h(1,t) = p(0), h(s,1) = h(s,0)) is         *)
(* constant on the fibres of the cone map onto the triangle, a quotient    *)
(* map since the square is compact (LIFT_TO_QUOTIENT_SPACE).               *)
(* ========================================================================= *)

let MOI_S6F_CONE_CONTINUOUS = prove
 (`!b:real^2.
     (\z:real^(1,1)finite_sum.
        b + (&1 - drop(fstcart z)) % (std_triangle_loop(sndcart z) - b))
     continuous_on (interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1])`,
  GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
   [REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP; LIFT_NUM] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART];
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    SUBGOAL_THEN `(\z:real^(1,1)finite_sum. std_triangle_loop(sndcart z)) =
                  std_triangle_loop o sndcart` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; IMAGE_SNDCART_PCROSS] THEN
    REWRITE_TAC[UNIT_INTERVAL_NONEMPTY] THEN
    MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN SIMP_TAC[path]]);;

let MOI_S6F_DISK_FILL = prove
 (`!(p:real^1->real^N) s.
     homotopic_loops s p (linepath(pathstart p,pathstart p))
     ==> ?f. f continuous_on std_triangle /\ IMAGE f std_triangle SUBSET s /\
             !t. t IN interval[vec 0,vec 1] ==> f(std_triangle_loop t) = p t`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homotopic_loops; HOMOTOPIC_WITH_EUCLIDEAN; LINEPATH_REFL;
              pathstart; pathfinish] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^(1,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`&2:int`; `std_triangle`] SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR) THEN
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX; MOI_LTD_STD_TRIANGLE_BASIC] THEN
  ABBREV_TAC `b = simplex_barycentre std_triangle` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `IMAGE (\z:real^(1,1)finite_sum.
             b + (&1 - drop(fstcart z)) % (std_triangle_loop(sndcart z) - b))
          (interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1]) =
    std_triangle`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART;
                  SNDCART_PASTECART] THEN
      MAP_EVERY X_GEN_TAC [`s0:real^1`; `t0:real^1`] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_S6F_CONE_IN THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
                  FSTCART_PASTECART; SNDCART_PASTECART] THEN
      X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`b:real^2`; `x:real^2`] MOI_S6F_CONE_ONTO) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\z:real^(1,1)finite_sum.
       b + (&1 - drop(fstcart z)) % (std_triangle_loop(sndcart z) - b)`;
    `interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1]`;
    `std_triangle`] CONTINUOUS_IMP_QUOTIENT_MAP_EXPLICIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_S6F_CONE_CONTINUOUS] THEN
    SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL];
    DISCH_TAC] THEN
  MP_TAC(ISPECL
   [`\z:real^(1,1)finite_sum.
       b + (&1 - drop(fstcart z)) % (std_triangle_loop(sndcart z) - b)`;
    `h:real^(1,1)finite_sum->real^N`;
    `interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1]`;
    `std_triangle`;
    `IMAGE (h:real^(1,1)finite_sum->real^N)
           (interval[vec 0:real^1,vec 1] PCROSS interval[vec 0:real^1,vec 1])`]
   LIFT_TO_QUOTIENT_SPACE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      REFL_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; FSTCART_PASTECART;
                SNDCART_PASTECART] THEN
    MAP_EVERY X_GEN_TAC [`s1:real^1`; `t1:real^1`; `s2:real^1`; `t2:real^1`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`b:real^2`; `s1:real^1`; `t1:real^1`; `s2:real^1`; `t2:real^1`]
                  MOI_S6F_CONE_FIBRE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^2->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fac")))) THEN
  EXISTS_TAC `g:real^2->real^N` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
  SUBGOAL_THEN `pastecart (vec 0:real^1) (t:real^1) IN
                interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL]; ALL_TAC] THEN
  USE_THEN "fac" (MP_TAC o C MP (ASSUME `pastecart (vec 0:real^1) (t:real^1) IN
                interval[vec 0,vec 1] PCROSS interval[vec 0,vec 1]`) o
    SPEC `pastecart (vec 0:real^1) (t:real^1)`) THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC;
              VECTOR_ARITH `b + (&1 - &0) % (y - b):real^2 = y`] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM));;

(* ========================================================================= *)
(* PL_FILL from the simplicial approximation term at (2,3).                *)
(* The disk ff above; cubes in u around ff(triangle) (MOI_FMB_COMPACT_CUBE_ *)
(* NBHD) refined with the simplices of c to one complex l, so every point  *)
(* of |c| lies in a simplex of l inside |c| (carrier property "car").  The *)
(* l0 = {} side conditions of MOI_FND_SIMPLICIAL_APPROX are MOI_FS5_SAN_ID *)
(* (the empty set is a subcomplex; every nonempty simplex of l has a vertex *)
(* {v} in l and {v} IN {} is false, so the fullness clause holds), and l is *)
(* nonempty since it covers ff(triangle).  The approximation g lies in the *)
(* simplices of l that contain ff x: in u, on the frontier in |c|, and the  *)
(* segments from g to ff = p stay in those simplices.                        *)
(* ========================================================================= *)

let MOI_S6F_SIMPLICIAL_PL = prove
 (`!(k:(real^M->bool)->bool) (l:(real^N->bool)->bool) g s.
     simplicial_complex k /\ UNIONS k = s /\ simplicial_map_on k l g
     ==> pl_map_on s g`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex; simplicial_map_on; pl_map_on] THEN
  STRIP_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`k:(real^M->bool)->bool`; `(:real^M)`] THEN
  ASM_REWRITE_TAC[OPEN_UNIV; IN_UNIV; INTER_UNIV; SUBSET_REFL] THEN
  X_GEN_TAC `t:real^M->bool` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    EXPAND_TAC "s" THEN UNDISCH_TAC `(t:real^M->bool) IN k` THEN SET_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S6F_PL_FILL_SA = prove
 (mk_imp(inst [`:2`,`:M`; `:3`,`:N`] MOI_FND_SIMPLICIAL_APPROX, MOI_S26_PL_FILL),
  DISCH_THEN(LABEL_TAC "sa") THEN
  MAP_EVERY X_GEN_TAC [`c:(real^3->bool)->bool`; `u:real^3->bool`; `p:real^1->real^3`] THEN
  STRIP_TAC THEN
  (* -------------------------------------------------------------------- *)
  (* S1: the disk ff with ff(loop t) = p t                                 *)
  (* -------------------------------------------------------------------- *)
  MP_TAC(ISPECL [`p:real^1->real^3`; `u:real^3->bool`] MOI_S6F_DISK_FILL) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^2->real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bd")))) THEN
  (* -------------------------------------------------------------------- *)
  (* S2: the complex l                                                     *)
  (* -------------------------------------------------------------------- *)
  MP_TAC(ISPECL [`IMAGE (ff:real^2->real^3) std_triangle`; `u:real^3->bool`]
                MOI_FMB_COMPACT_CUBE_NBHD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `(P:(real^3->bool)->bool) UNION c` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION; IN_UNION] THEN
    X_GEN_TAC `k:real^3->bool` THEN STRIP_TAC THENL
     [ASM_MESON_TAC[];
      MP_TAC(ASSUME `simplicial_complex (c:(real^3->bool)->bool)`) THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `k:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_POLYTOPE]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:(real^3->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "ul") (LABEL_TAC "ref")))) THEN
  SUBGOAL_THEN `!y:real^3. y IN UNIONS c ==> ?r. r IN l /\ y IN r /\ r SUBSET UNIONS c`
  (LABEL_TAC "car") THENL
   [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "ref" (MP_TAC o SPEC `k:real^3->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(y:real^3) IN k` THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(f:(real^3->bool)->bool) SUBSET l` THEN
    UNDISCH_TAC `(r:real^3->bool) IN f` THEN
    UNDISCH_TAC `(k:real^3->bool) IN c` THEN
    UNDISCH_TAC `(k:real^3->bool) = UNIONS f` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (ff:real^2->real^3) std_triangle SUBSET UNIONS l /\
                UNIONS l SUBSET u` STRIP_ASSUME_TAC THENL
   [USE_THEN "ul" SUBST1_TAC THEN REWRITE_TAC[UNIONS_UNION] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `UNIONS P:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `IMAGE (ff:real^2->real^3) std_triangle SUBSET interior (UNIONS P)` THEN
      SET_TAC[];
      REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[UNIONS_SUBSET] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REMOVE_THEN "ul" (K ALL_TAC) THEN
  SUBGOAL_THEN `~(l:(real^3->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `IMAGE (ff:real^2->real^3) std_triangle SUBSET
                 UNIONS ({}:(real^3->bool)->bool)` THEN
    REWRITE_TAC[UNIONS_0; SUBSET_EMPTY; IMAGE_EQ_EMPTY; MOI_LTD_STD_TRIANGLE_BASIC];
    ALL_TAC] THEN
  (* -------------------------------------------------------------------- *)
  (* S3: the simplicial approximation g                                    *)
  (* -------------------------------------------------------------------- *)
  MP_TAC(ISPEC `l:(real^3->bool)->bool` MOI_FS5_SAN_ID) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`&2:int`; `std_triangle`] MOI_FMB_FACE_COMPLEX) THEN
  REWRITE_TAC[MOI_LTD_STD_TRIANGLE_SIMPLEX] THEN STRIP_TAC THEN
  USE_THEN "sa" (MP_TAC o SPECL
   [`{f:real^2->bool | f face_of std_triangle}`; `l:(real^3->bool)->bool`;
    `{}:(real^3->bool)->bool`; `ff:real^2->real^3`; `{}:real^2->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[COMPACT_EMPTY; EMPTY_SUBSET; IMAGE_CLAUSES; UNIONS_0; DISJOINT_EMPTY];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `g:real^2->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "gin")
     (CONJUNCTS_THEN2 (K ALL_TAC) ASSUME_TAC))))) THEN
  SUBGOAL_THEN
   `simplicial_complex
      (ITER n barycentric_subdivision {f:real^2->bool | f face_of std_triangle}) /\
    UNIONS (ITER n barycentric_subdivision {f:real^2->bool | f face_of std_triangle}) =
    std_triangle`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `{f:real^2->bool | f face_of std_triangle}` MOI_BAR_ITER_SUBDIVISION) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`{f:real^2->bool | f face_of std_triangle}`; `{}:(real^2->bool)->bool`;
                     `n:num`] MOI_FDN_ITER_SUBCOMPLEX) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[simplicial_subcomplex; EMPTY_SUBSET; NOT_IN_EMPTY]; ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^2->real^3) continuous_on std_triangle` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the frontier: g and ff = p share a simplex of l inside |c| *)
  SUBGOAL_THEN
   `!t. t IN interval[vec 0,vec 1]
        ==> ?r. r IN l /\ r SUBSET UNIONS c /\
                (g:real^2->real^3)(std_triangle_loop t) IN r /\ (p:real^1->real^3) t IN r`
  (LABEL_TAC "bdr") THENL
   [X_GEN_TAC `t:real^1` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^1->real^3) t IN UNIONS c` ASSUME_TAC THENL
     [UNDISCH_TAC `path_image (p:real^1->real^3) SUBSET UNIONS c` THEN
      REWRITE_TAC[path_image] THEN UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
      SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "car" (MP_TAC o C MP (ASSUME `(p:real^1->real^3) t IN UNIONS c`) o
                    SPEC `(p:real^1->real^3) t`) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(ff:real^2->real^3)(std_triangle_loop t) = p t` ASSUME_TAC THENL
     [USE_THEN "bd" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    USE_THEN "gin" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(SPEC `t:real^1` MOI_S6F_LOOP_FRONTIER) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC MOI_LTD_FRONTIER_SUBSET_TRIANGLE THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `g:real^2->real^3` THEN REPEAT CONJ_TAC THENL
   [(* PL *)
    MATCH_MP_TAC MOI_S6F_SIMPLICIAL_PL THEN
    MAP_EVERY EXISTS_TAC
     [`ITER n barycentric_subdivision {f:real^2->bool | f face_of std_triangle}`;
      `l:(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    (* the image lies in u *)
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(ff:real^2->real^3) x IN UNIONS l` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (ff:real^2->real^3) std_triangle SUBSET UNIONS l` THEN
      UNDISCH_TAC `(x:real^2) IN std_triangle` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "gin" (MP_TAC o SPECL [`x:real^2`; `r:real^3->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    UNDISCH_TAC `UNIONS l SUBSET (u:real^3->bool)` THEN
    UNDISCH_TAC `(r:real^3->bool) IN l` THEN UNDISCH_TAC `(g:real^2->real^3) x IN r` THEN
    SET_TAC[];
    (* the frontier lies in |c| *)
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN
    MP_TAC MOI_LTD_STD_TRIANGLE_LOOP THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[path_image; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    USE_THEN "bdr" (MP_TAC o C MP (ASSUME `(t:real^1) IN interval[vec 0,vec 1]`) o
                    SPEC `t:real^1`) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(g:real^2->real^3)(std_triangle_loop t) IN r` THEN
    UNDISCH_TAC `(r:real^3->bool) SUBSET UNIONS c` THEN SET_TAC[];
    (* the boundary loop *)
    MATCH_MP_TAC HOMOTOPIC_LOOPS_LINEAR THEN
    MP_TAC(ISPEC `g:real^2->real^3` MOI_LTD_LOOP_COMPOSE) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    USE_THEN "bdr" (MP_TAC o C MP (ASSUME `(t:real^1) IN interval[vec 0,vec 1]`) o
                    SPEC `t:real^1`) THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `r:real^3->bool` THEN
    ASM_REWRITE_TAC[o_THM] THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `simplicial_complex (l:(real^3->bool)->bool)`) THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX]]);;

(* ========================================================================= *)
(* The main theorem PL_FILL.  The simplicial approximation term is the       *)
(* theorem SIMPLICIAL_APPROX of pc_moi_fnd_sapprox at M = 2, N = 3.          *)
(* ========================================================================= *)

let PL_FILL = prove
 (MOI_S26_PL_FILL,
  ACCEPT_TAC(MP MOI_S6F_PL_FILL_SA
                (INST_TYPE [`:2`,`:M`; `:3`,`:N`] SIMPLICIAL_APPROX)));;

