(* ========================================================================= *)
(* pc_moi_cglue: glue lemmas of the Moise PL core (the statements of         *)
(* pc_moi_core_stmt.ml): MOI_CORE_GLUE_LOOP3 (the loop theorem in real^3     *)
(* from the internal form in real^7, Moise 25.2 as used in Secs 30, 33), and *)
(* the reductions MOI_CORE_GLUE_341, MOI_CORE_GLUE_352,                      *)
(* MOI_CORE_GLUE_341_NBHD (Moise p.239, p.251).                              *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_m3a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The coordinate embedding of real^3 in real^7 and its left inverse.       *)
(* ------------------------------------------------------------------------- *)

let moi_cgl_e = new_definition
 `moi_cgl_e (x:real^3) = (lambda i. if i <= 3 then x$i else &0):real^7`;;

let moi_cgl_p = new_definition
 `moi_cgl_p (y:real^7) = (lambda i. y$i):real^3`;;

let MOI_CGL_DIMINDEX_7 = prove
 (`dimindex(:7) = 7`,
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:7)`]);;

let MOI_CGL_LINEAR_E = prove
 (`linear moi_cgl_e`,
  REWRITE_TAC[linear; moi_cgl_e] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN COND_CASES_TAC THEN REAL_ARITH_TAC);;

let MOI_CGL_LINEAR_P = prove
 (`linear moi_cgl_p`,
  REWRITE_TAC[linear; moi_cgl_p] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT]);;

let MOI_CGL_PE = prove
 (`!x:real^3. moi_cgl_p (moi_cgl_e x) = x`,
  GEN_TAC THEN REWRITE_TAC[moi_cgl_p; moi_cgl_e] THEN
  SIMP_TAC[CART_EQ; LAMBDA_BETA] THEN REWRITE_TAC[DIMINDEX_3] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((lambda i. if i <= 3 then (x:real^3)$i else &0):real^7)$i =
                (if i <= 3 then x$i else &0)` SUBST1_TAC THENL
   [MATCH_MP_TAC LAMBDA_BETA THEN REWRITE_TAC[MOI_CGL_DIMINDEX_7] THEN ASM_ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

let MOI_CGL_E_INJ = prove
 (`!x y:real^3. moi_cgl_e x = moi_cgl_e y ==> x = y`,
  MESON_TAC[MOI_CGL_PE]);;

let MOI_CGL_HOMEO_E = prove
 (`!s:real^3->bool. homeomorphism (s,IMAGE moi_cgl_e s) (moi_cgl_e,moi_cgl_p)`,
  GEN_TAC THEN REWRITE_TAC[homeomorphism; FORALL_IN_IMAGE; MOI_CGL_PE] THEN
  SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_CGL_LINEAR_E; MOI_CGL_LINEAR_P] THEN
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; MOI_CGL_PE; IMAGE_ID]);;

let MOI_CGL_EP = prove
 (`!s:real^3->bool y. y IN IMAGE moi_cgl_e s ==> moi_cgl_e (moi_cgl_p y) = y`,
  REWRITE_TAC[FORALL_IN_IMAGE; MOI_CGL_PE]);;

let MOI_CGL_PIMAGE = prove
 (`!s:real^3->bool. IMAGE moi_cgl_p (IMAGE moi_cgl_e s) = s`,
  REWRITE_TAC[GSYM IMAGE_o; o_DEF; MOI_CGL_PE; IMAGE_ID]);;

(* ------------------------------------------------------------------------- *)
(* MOI_CORE_GLUE_LOOP3: the loop theorem for complexes in real^3 from the    *)
(* internal form in real^7: move the complex into real^7 by the coordinate   *)
(* embedding (combinatorial structure, boundary and orientation are          *)
(* transported, pc_moi_fnd_m3a), apply the internal form, and project the    *)
(* disk back.                                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_CGL_PE_O = prove
 (`!g:A->real^3. moi_cgl_p o moi_cgl_e o g = g`,
  REWRITE_TAC[FUN_EQ_THM; o_THM; MOI_CGL_PE]);;

let MOI_CGL_NONCONTRACTIBLE_TRANSPORT = prove
 (`!(j:real^7->bool) (b:real^3->bool).
     j SUBSET IMAGE moi_cgl_e (:real^3) /\
     ~(?a. homotopic_with (\h. T)
             (subtopology euclidean j,subtopology euclidean (IMAGE moi_cgl_e b))
             (\x. x) (\x. a))
     ==> ~(?a. homotopic_with (\h. T)
                 (subtopology euclidean (IMAGE moi_cgl_p j),subtopology euclidean b)
                 (\x. x) (\x. a))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  REWRITE_TAC[CONTRAPOS_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^3`) THEN
  EXISTS_TAC `moi_cgl_e a` THEN
  SUBGOAL_THEN
   `homotopic_with (\h:real^7->real^7. T)
      (subtopology euclidean j,subtopology euclidean (IMAGE moi_cgl_e b))
      ((moi_cgl_e o (\x:real^3. x)) o moi_cgl_p)
      ((moi_cgl_e o (\x:real^3. a)) o moi_cgl_p)`
  MP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_RIGHT THEN
    EXISTS_TAC `\h:real^3->real^7. T` THEN
    EXISTS_TAC `subtopology euclidean (IMAGE moi_cgl_p (j:real^7->bool))` THEN
    REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_CGL_LINEAR_P; SUBSET_REFL] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_LEFT THEN
    EXISTS_TAC `\h:real^3->real^3. T` THEN
    EXISTS_TAC `subtopology euclidean (b:real^3->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_CGL_LINEAR_E; SUBSET_REFL];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`(moi_cgl_e o (\x:real^3. x)) o moi_cgl_p`;
    `(moi_cgl_e o (\x:real^3. a)) o moi_cgl_p`] THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM] THEN
  ASM_MESON_TAC[MOI_CGL_EP; SUBSET]);;

let MOI_CGL_LOOP3 = prove
 (`LOOP_THEOREM_N_STATEMENT (:7) ==> LOOP_THEOREM_3_STATEMENT`,
  REWRITE_TAC[LOOP_THEOREM_N_STATEMENT; LOOP_THEOREM_3_STATEMENT;
              MOI_CGL_DIMINDEX_7; LE_REFL] THEN
  DISCH_THEN(LABEL_TAC "LN") THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^3->bool)->bool`; `b:real^3->bool`; `p:real^1->real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_cgl_e`; `c:(real^3->bool)->bool`]
    MOI_FM3_LINEAR_IMAGE_COMPLEX_LF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_CGL_LINEAR_E; MOI_CGL_E_INJ]; STRIP_TAC] THEN
  SUBGOAL_THEN `complex_boundary (c:(real^3->bool)->bool) = frontier (UNIONS c)`
  ASSUME_TAC THENL [ASM_MESON_TAC[COMPLEX_BOUNDARY_FRONTIER_3]; ALL_TAC] THEN
  SUBGOAL_THEN `orientable_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORIENTABLE_COMPLEX_3]; ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (IMAGE (IMAGE moi_cgl_e) c) =
    IMAGE moi_cgl_e (UNIONS (c:(real^3->bool)->bool))`
  ASSUME_TAC THENL [REWRITE_TAC[IMAGE_UNIONS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE moi_cgl_e (b:real^3->bool) IN
    components (IMAGE moi_cgl_e (frontier (UNIONS (c:(real^3->bool)->bool))))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `frontier (UNIONS (c:(real^3->bool)->bool))` MOI_CGL_HOMEO_E) THEN
    DISCH_THEN(SUBST1_TAC o MATCH_MP HOMEOMORPHISM_COMPONENTS) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `b:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path (moi_cgl_e o (p:real^1->real^3))` ASSUME_TAC THENL
   [ASM_MESON_TAC[PATH_LINEAR_IMAGE_EQ; MOI_CGL_LINEAR_E; MOI_CGL_E_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image (moi_cgl_e o (p:real^1->real^3)) SUBSET IMAGE moi_cgl_e b`
  ASSUME_TAC THENL
   [SIMP_TAC[PATH_IMAGE_LINEAR_IMAGE; MOI_CGL_LINEAR_E] THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pathstart (moi_cgl_e o (p:real^1->real^3)) = moi_cgl_e (pathstart p) /\
    pathfinish (moi_cgl_e o p) = moi_cgl_e (pathfinish p)`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[PATHSTART_LINEAR_IMAGE_EQ; PATHFINISH_LINEAR_IMAGE;
             MOI_CGL_LINEAR_E];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_loops (IMAGE moi_cgl_e (UNIONS (c:(real^3->bool)->bool)))
      (moi_cgl_e o (p:real^1->real^3))
      (linepath(moi_cgl_e(pathstart p),moi_cgl_e(pathstart p)))`
  ASSUME_TAC THENL
   [SIMP_TAC[LINEPATH_LINEAR_IMAGE; MOI_CGL_LINEAR_E] THEN
    MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
    EXISTS_TAC `UNIONS (c:(real^3->bool)->bool)` THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_CGL_LINEAR_E; SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~homotopic_loops (IMAGE moi_cgl_e (b:real^3->bool))
       (moi_cgl_e o (p:real^1->real^3))
       (linepath(moi_cgl_e(pathstart p),moi_cgl_e(pathstart p)))`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN
     `homotopic_loops (b:real^3->bool)
        (moi_cgl_p o moi_cgl_e o (p:real^1->real^3))
        (moi_cgl_p o linepath(moi_cgl_e(pathstart p),moi_cgl_e(pathstart p)))`
    MP_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_LOOPS_CONTINUOUS_IMAGE THEN
      EXISTS_TAC `IMAGE moi_cgl_e (b:real^3->bool)` THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_CGL_LINEAR_P; MOI_CGL_PIMAGE;
                   SUBSET_REFL];
      ALL_TAC] THEN
    SIMP_TAC[GSYM LINEPATH_LINEAR_IMAGE; MOI_CGL_LINEAR_P] THEN
    REWRITE_TAC[MOI_CGL_PE; MOI_CGL_PE_O] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "LN" (MP_TAC o SPECL
   [`IMAGE (IMAGE moi_cgl_e) (c:(real^3->bool)->bool)`;
    `IMAGE moi_cgl_e (b:real^3->bool)`;
    `moi_cgl_e o (p:real^1->real^3)`]) THEN
  ASM_REWRITE_TAC[FINITE_IMAGE] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`k7:real^7->bool`; `d7:real^7->bool`;
    `f7:real^7->real^7`; `g7:real^7->real^7`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!x. x IN d7 ==> moi_cgl_e (moi_cgl_p x) = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_CGL_EP; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?k3:real^3->bool. &2 simplex k3` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC CHOOSE_SIMPLEX THEN REWRITE_TAC[DIMINDEX_3] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k3:real^3->bool`; `k7:real^7->bool`; `&2:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^3->real^7`; `a':real^7->real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_homeomorphism (d7,IMAGE moi_cgl_p d7) (moi_cgl_p,moi_cgl_e)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
    REWRITE_TAC[homeomorphism; FORALL_IN_IMAGE; MOI_CGL_PE] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_CGL_LINEAR_E; MOI_CGL_LINEAR_P] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^7. moi_cgl_p x + vec 0` THEN
    CONJ_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN REWRITE_TAC[MOI_CGL_LINEAR_P] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    SUBGOAL_THEN `d7 = IMAGE (f7:real^7->real^7) k7` SUBST1_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[POLYTOPE_IMP_PL_POLYHEDRON; SIMPLEX_IMP_POLYTOPE];
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (k3,IMAGE moi_cgl_p d7)
      (moi_cgl_p o ((f7:real^7->real^7) o (a:real^3->real^7)),
       ((a':real^7->real^3) o (g7:real^7->real^7)) o moi_cgl_e)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `d7:real^7->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k7:real^7->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`k3:real^3->bool`; `IMAGE moi_cgl_p (d7:real^7->bool)`;
    `moi_cgl_p o ((f7:real^7->real^7) o (a:real^3->real^7))`;
    `((a':real^7->real^3) o (g7:real^7->real^7)) o moi_cgl_e`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `IMAGE (moi_cgl_p o ((f7:real^7->real^7) o (a:real^3->real^7)))
          (relative_frontier k3) =
    IMAGE moi_cgl_p (IMAGE f7 (relative_frontier k7))`
  SUBST1_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    ASM_MESON_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN
     `IMAGE moi_cgl_p (d7:real^7->bool) SUBSET
      IMAGE moi_cgl_p (IMAGE moi_cgl_e (UNIONS (c:(real^3->bool)->bool)))`
    MP_TAC THENL
     [ASM_SIMP_TAC[IMAGE_SUBSET]; REWRITE_TAC[MOI_CGL_PIMAGE]];
    FIRST_X_ASSUM(fun th ->
      if is_eq(concl th) &&
         lhand(concl th) = `d7 INTER IMAGE moi_cgl_e (frontier (UNIONS (c:(real^3->bool)->bool)))`
      then REWRITE_TAC[GSYM th] else failwith "not H4") THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_IMAGE] THEN
    ASM_MESON_TAC[MOI_CGL_PE];
    SUBGOAL_THEN
     `IMAGE moi_cgl_p (IMAGE (f7:real^7->real^7) (relative_frontier k7)) SUBSET
      IMAGE moi_cgl_p (IMAGE moi_cgl_e (b:real^3->bool))`
    MP_TAC THENL
     [ASM_SIMP_TAC[IMAGE_SUBSET]; REWRITE_TAC[MOI_CGL_PIMAGE]];
    MATCH_MP_TAC MOI_CGL_NONCONTRACTIBLE_TRANSPORT THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Basic facts on PL balls; MOI_CORE_GLUE_341 (the reduction of p.239: push  *)
(* the cell into its interior, where h is defined on an open set), and      *)
(* MOI_CORE_GLUE_352 (35.2 from Sec 34 and 35.1, p.251).                    *)
(* ------------------------------------------------------------------------- *)

let MOI_CGL_PL_BALL_BASIC = prove
 (`!n c:real^N->bool.
     pl_ball n c ==> compact c /\ connected c /\ ~(c = {}) /\ pl_polyhedron c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball; pl_homeomorphism; homeomorphism] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  STRIP_TAC THEN EXPAND_TAC "c" THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `&n simplex (k:real^N->bool)` THEN
    ASM_REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC;
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_MESON_TAC[POLYTOPE_IMP_PL_POLYHEDRON; SIMPLEX_IMP_POLYTOPE]]);;

let MOI_CGL_341 = prove
 (`MOISE_341_NBHD_STATEMENT ==> MOISE_341_STATEMENT`,
  REWRITE_TAC[MOISE_341_NBHD_STATEMENT; MOISE_341_STATEMENT] THEN
  DISCH_THEN(LABEL_TAC "NB") THEN
  MAP_EVERY X_GEN_TAC [`c:real^3->bool`; `h:real^3->real^3`; `e:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_CGL_PL_BALL_BASIC) THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !x x'. x IN c /\ x' IN c /\ dist(x',x) < d
               ==> dist((h:real^3->real^3) x',h x) < e / &2`
  (X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "uc")))
  THENL
   [MP_TAC(ISPECL [`h:real^3->real^3`; `c:real^3->bool`]
      COMPACT_UNIFORMLY_CONTINUOUS) THEN
    ASM_REWRITE_TAC[uniformly_continuous_on] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `d:real`] PL_BALL_PUSH_IN) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:real^3->real^3`; `q:real^3->real^3`] THEN
  STRIP_TAC THEN
  REMOVE_THEN "NB" (MP_TAC o SPECL
   [`IMAGE (p:real^3->real^3) c`; `interior (c:real^3->bool)`;
    `h:real^3->real^3`; `e / &2`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_INTERIOR] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[PL_BALL_PL_HOMEOMORPHIC];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTERIOR_SUBSET];
      ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f':real^3->real^3`; `g':real^3->real^3`] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`(f':real^3->real^3) o (p:real^3->real^3)`;
    `(q:real^3->real^3) o (g':real^3->real^3)`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `IMAGE (p:real^3->real^3) c` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  SUBGOAL_THEN `(p:real^3->real^3) x IN IMAGE p c /\ p x IN c`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `dist((f':real^3->real^3)(p x),(h:real^3->real^3)(p x)) < e / &2 /\
    dist((h:real^3->real^3)((p:real^3->real^3) x),h x) < e / &2`
  MP_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[];
      USE_THEN "uc" MATCH_MP_TAC THEN ASM_MESON_TAC[]];
    CONV_TAC NORM_ARITH]);;

let MOI_CGL_352 = prove
 (`!u:N->bool. MOISE_34_EXT_STATEMENT u /\ MOISE_351_STATEMENT u
              ==> MOISE_352_COMPLEX_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[MOISE_34_EXT_STATEMENT; MOISE_351_STATEMENT;
              MOISE_352_COMPLEX_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EXT") (LABEL_TAC "A351")) THEN
  MAP_EVERY X_GEN_TAC
   [`c:(real^N->bool)->bool`; `h:real^N->real^3`; `e:real^N->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `lf_simplicial_complex (c:(real^N->bool)->bool) /\
    !v. {v} IN c ==> pl_sphere 2 (UNIONS (simplicial_link c v))`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[combinatorial_manifold] o
      check (fun th -> try fst(dest_const(fst(strip_comb(concl th)))) =
                           "combinatorial_manifold" with Failure _ -> false)) THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN SIMP_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "EXT" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `c:(real^N->bool)->bool`;
    `h:real^N->real^3`; `e:real^N->real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[simplicial_subcomplex; SUBSET_REFL;
                   combinatorial_manifold_with_boundary] THEN
    CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[lf_simplicial_complex];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`t':(real^N->bool)->bool`; `k':(real^N->bool)->bool`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  REMOVE_THEN "A351" MATCH_MP_TAC THEN
  SUBGOAL_THEN `UNIONS t' = UNIONS (c:(real^N->bool)->bool)` SUBST1_TAC THENL
   [ASM_MESON_TAC[subdivides]; ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MOI_CORE_GLUE_341_NBHD: triangulate a neighbourhood of the cell           *)
(* (MOI_FND_BALL_TRIANGULATION, proved as BALL_TRIANGULATION_IN_OPEN in      *)
(* pc_moi_fnd_m3b and a hypothesis here), apply the Sec 34 extension in      *)
(* real^3, and feed tube approximability from 33.1 (finite subdivision,      *)
(* connected 1-skeleton, vertex degrees at least 3, pc_moi_fnd1).            *)
(* ------------------------------------------------------------------------- *)

let MOI_CGL_SKEL_EDGES = prove
 (`!(k:(real^N->bool)->bool) v.
     {e | e IN skeleton 1 k /\ aff_dim e = &1 /\ v IN e} =
     {e | e IN k /\ aff_dim e = &1 /\ v IN e}`,
  REWRITE_TAC[skeleton; EXTENSION; IN_ELIM_THM] THEN
  MESON_TAC[INT_LE_REFL]);;

let MOI_CGL_EDGE_EXISTS = prove
 (`!k:(real^N->bool)->bool.
     combinatorial_manifold_with_boundary 3 k /\ ~(UNIONS k = {})
     ==> ?e. e IN skeleton 1 k /\ aff_dim e = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (k:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN k /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_FM3_LF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:(real^N->bool)->bool`; `v:real^N`] COMBINATORIAL_DEGREE_3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~({e | e IN k /\ aff_dim e = &1 /\ (v:real^N) IN e} = {})`
  MP_TAC THENL
   [DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th; CARD_CLAUSES])) THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM; skeleton] THEN
  MESON_TAC[INT_LE_REFL]);;

let MOI_CGL_341_NBHD = prove
 (mk_imp(MOI_FND_BALL_TRIANGULATION, MOI_CORE_GLUE_341_NBHD),
  DISCH_THEN(LABEL_TAC "BT") THEN
  REWRITE_TAC[MOISE_34_EXT_STATEMENT; MOISE_331_STATEMENT;
              MOISE_341_NBHD_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "EXT") (LABEL_TAC "A331")) THEN
  MAP_EVERY X_GEN_TAC
   [`c:real^3->bool`; `u:real^3->bool`; `h:real^3->real^3`; `e:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_CGL_PL_BALL_BASIC) THEN
  REMOVE_THEN "BT" (MP_TAC o SPECL [`c:real^3->bool`; `u:real^3->bool`]) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`t:(real^3->bool)->bool`; `k:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (t:(real^3->bool)->bool) /\ lf_simplicial_complex t`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(h:real^3->real^3) continuous_on UNIONS t /\
    (!x y. x IN UNIONS t /\ y IN UNIONS t /\ h x = h y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET]; ALL_TAC] THEN
  REMOVE_THEN "EXT" (MP_TAC o SPECL
   [`t:(real^3->bool)->bool`; `k:(real^3->bool)->bool`;
    `h:real^3->real^3`; `\x:real^3. (e:real)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_DEF; CONTINUOUS_ON_CONST]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`t':(real^3->bool)->bool`; `k':(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS t' = UNIONS (t:(real^3->bool)->bool) /\
                UNIONS k' = UNIONS (k:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[subdivides]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (k':(real^3->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `graph_approximable t' (skeleton 1 k') (h:real^3->real^3)`
  ASSUME_TAC THENL
   [REMOVE_THEN "A331" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SUBDIVISION_FINITE];
      MATCH_MP_TAC SKELETON_1_CONNECTED THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_CGL_EDGE_EXISTS THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      REWRITE_TAC[MOI_CGL_SKEL_EDGES] THEN
      MP_TAC(ISPECL [`k':(real^3->bool)->bool`; `v:real^3`]
        COMBINATORIAL_DEGREE_3) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `{v:real^3} IN skeleton 1 k'` THEN
        REWRITE_TAC[skeleton; IN_ELIM_THM] THEN SIMP_TAC[];
        ARITH_TAC]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
   `graph_approximable t' (skeleton 1 k') (h:real^3->real^3)`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:real^3->bool`; `f:real^3->real^3`] PL_INJECTIVE_INVERSE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^3`) THEN
  MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_MESON_TAC[]);;

