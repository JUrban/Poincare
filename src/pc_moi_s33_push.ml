(* ========================================================================= *)
(* pc_moi_s33_push: the push-off of Lemma 9 (Moise GTM 47, p.234; DG         *)
(* exists_isLoopTheoremDisk_pushOff).  Main theorem                          *)
(*   S39_PUSH : |- MOI_S39_PUSH_BODY   (pc_moi_s33_l9stmt.ml)                *)
(* The part of a loop theorem disk d inside an open u SUBSET W that lies in  *)
(* one piece c v and meets the pseudo-cells only in a compact z is pushed    *)
(* off the pseudo-cells inside u by an ambient PL homeomorphism fixing the   *)
(* complement of u and keeping X.                                            *)
(*   Part 1  the model push in the unit cube (a cone map, a shear in z1);    *)
(*   Part 2  pushes in charts and their composition (generic);               *)
(*   Part 3  vertex links of surfaces are PL circles (local form);           *)
(*   Part 4  flat charts of locally polyhedral surfaces in real^3 (generic); *)
(*           the statements of pieces 1-4 and the proofs of pieces 1 and 2;  *)
(*   Part 5  the pieces and the pseudo-cells near a point of z; piece 3;     *)
(*   Part 6  the local push at a point of z INTER PCS; piece 4;              *)
(*   Part 7  S39_PUSH.                                                       *)
(* ========================================================================= *)

needs "src/pc_moi_s33_l9stmt.ml";;
needs "src/pc_moi_s33_frame.ml";;
needs "src/pc_moi_s33_x2.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_s34_outer.ml";;
needs "src/pc_moi_comb.ml";;
needs "src/pc_moi_s28_trib.ml";;
needs "src/pc_moi_s30_tame.ml";;
needs "src/pc_moi_ptri.ml";;
needs "src/pc_moi_cells.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_s32_sides.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Part 1: the model push.  In the unit cube interval[--vec 1,vec 1] of      *)
(* real^3, the cone map from the apex vec 0 to the apex t % basis 1         *)
(* (abs t < 1) that is the identity on the frontier, extended by the        *)
(* identity outside the cube, is a PL homeomorphism of real^3.  It keeps    *)
(* the second and third coordinates and moves the first one by l * t, with *)
(* l > 0 exactly inside the open cube.                                       *)
(* ========================================================================= *)

let MOI_S3PU_CUBE_FACTS = prove
 (`convex(interval[--vec 1:real^3,vec 1]) /\ compact(interval[--vec 1:real^3,vec 1]) /\
   polytope(interval[--vec 1:real^3,vec 1]) /\ closed(interval[--vec 1:real^3,vec 1]) /\
   open(interval(--vec 1:real^3,vec 1)) /\
   interval(--vec 1:real^3,vec 1) SUBSET interval[--vec 1,vec 1] /\
   interior(interval[--vec 1:real^3,vec 1]) = interval(--vec 1,vec 1) /\
   relative_interior(interval[--vec 1:real^3,vec 1]) = interval(--vec 1,vec 1) /\
   relative_frontier(interval[--vec 1:real^3,vec 1]) =
     interval[--vec 1,vec 1] DIFF interval(--vec 1,vec 1) /\
   (!t. abs t < &1 ==> t % basis 1 IN interval(--vec 1:real^3,vec 1)) /\
   (vec 0:real^3) IN interval(--vec 1,vec 1) /\
   ~(relative_frontier(interval[--vec 1:real^3,vec 1]) = {}) /\
   pl_polyhedron(relative_frontier(interval[--vec 1:real^3,vec 1]))`,
  SUBGOAL_THEN `!t. abs t < &1 ==> t % basis 1 IN interval(--vec 1:real^3,vec 1)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    SIMP_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT; VECTOR_MUL_COMPONENT;
             BASIS_COMPONENT] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN COND_CASES_TAC THEN
    UNDISCH_TAC `abs t < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(vec 0:real^3) IN interval(--vec 1,vec 1)` ASSUME_TAC THENL
   [SUBGOAL_THEN `vec 0:real^3 = &0 % basis 1` SUBST1_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_LZERO]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior(interval[--vec 1:real^3,vec 1]) = interval(--vec 1,vec 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `interior(interval[--vec 1:real^3,vec 1])` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[INTERIOR_INTERVAL]] THEN
    MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR THEN
    REWRITE_TAC[INTERIOR_INTERVAL; GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[CONVEX_INTERVAL; COMPACT_INTERVAL; POLYTOPE_INTERVAL; CLOSED_INTERVAL;
                  OPEN_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED; INTERIOR_INTERVAL] THEN
  SIMP_TAC[MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER; POLYTOPE_INTERVAL] THEN
  REWRITE_TAC[relative_frontier; CLOSURE_INTERVAL] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN EXISTS_TAC `vec 1:real^3` THEN
  REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT; DIMINDEX_3; FORALL_3] THEN
  REAL_ARITH_TAC);;

let MOI_S3PU_CUBE_COMPL_LP = prove
 (`locally_polyhedral((:real^3) DIFF interval(--vec 1,vec 1))`,
  REWRITE_TAC[locally_polyhedral] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  ABBREV_TAC `B = interval[x - vec 2:real^3,x + vec 2]` THEN
  EXISTS_TAC
   `{B INTER {y:real^3 | basis 1 dot y >= &1}, B INTER {y:real^3 | basis 1 dot y <= -- &1},
     B INTER {y:real^3 | basis 2 dot y >= &1}, B INTER {y:real^3 | basis 2 dot y <= -- &1},
     B INTER {y:real^3 | basis 3 dot y >= &1}, B INTER {y:real^3 | basis 3 dot y <= -- &1}}` THEN
  EXISTS_TAC `ball(x:real^3,&1)` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; OPEN_BALL; CENTRE_IN_BALL; REAL_LT_01] THEN
  SUBGOAL_THEN `polytope(B:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[POLYTOPE_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. polytope (B INTER {y:real^3 | basis i dot y >= &1}) /\
        polytope (B INTER {y:real^3 | basis i dot y <= -- &1})`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THEN MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
    ASM_REWRITE_TAC[POLYHEDRON_HALFSPACE_GE; POLYHEDRON_HALFSPACE_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. basis 1 dot y = y$1 /\ basis 2 dot y = y$2 /\ basis 3 dot y = y$3`
  ASSUME_TAC THENL
   [GEN_TAC THEN SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_UNIV; IN_BALL; UNIONS_INSERT; UNIONS_0;
                IN_UNION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN B` ASSUME_TAC THENL
     [EXPAND_TAC "B" THEN
      REWRITE_TAC[IN_INTERVAL; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VEC_COMPONENT] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`x - y:real^3`; `i:num`] COMPONENT_LE_NORM) THEN
      ASM_REWRITE_TAC[VECTOR_SUB_COMPONENT; GSYM dist] THEN
      UNDISCH_TAC `dist(x:real^3,y) < &1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((y:real^3) IN interval(--vec 1,vec 1))` THEN
    REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT; DIMINDEX_3; FORALL_3] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_UNIV; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT; DIMINDEX_3; FORALL_3] THEN
  REAL_ARITH_TAC);;

let MOI_S3PU_CUBE_RF = prove
 (`!p:real^3. p IN relative_frontier(interval[--vec 1,vec 1]) <=>
              p IN interval[--vec 1,vec 1] /\ ~(p IN interval(--vec 1,vec 1))`,
  REWRITE_TAC[MOI_S3PU_CUBE_FACTS; IN_DIFF]);;

let MOI_S3PU_MODEL_PUSH = prove
 (`!t. abs t < &1
       ==> ?(P:real^3->real^3) P'.
             pl_homeomorphism ((:real^3),(:real^3)) (P,P') /\
             (!p. ~(p IN interval(--vec 1,vec 1)) ==> P p = p) /\
             (!p. p IN interval[--vec 1,vec 1] ==> P p IN interval[--vec 1,vec 1]) /\
             (!p. (P p)$2 = p$2 /\ (P p)$3 = p$3) /\
             (!p. ?l. &0 <= l /\ (&0 < l <=> p IN interval(--vec 1,vec 1)) /\
                      (P p)$1 = p$1 + l * t)`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC MOI_S3PU_CUBE_FACTS THEN MP_TAC MOI_S3PU_CUBE_COMPL_LP THEN
  ABBREV_TAC `Q = interval[--vec 1:real^3,vec 1]` THEN
  ABBREV_TAC `I0 = interval(--vec 1:real^3,vec 1)` THEN
  DISCH_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq (concl th) &&
    lhs (concl th) = `relative_frontier Q:real^3->bool`)) THEN
  SUBGOAL_THEN `!p:real^3. p IN relative_frontier Q <=> p IN Q /\ ~(p IN I0)`
  (LABEL_TAC "rfq") THENL
   [MP_TAC MOI_S3PU_CUBE_RF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `a:real^3 = t % basis 1` THEN
  SUBGOAL_THEN `(a:real^3) IN I0` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!b:real^3. b IN I0
                ==> ~(b IN relative_frontier Q) /\
                    (!x y. x IN relative_frontier Q /\ y IN relative_frontier Q /\
                           y IN segment[b,x] ==> y = x) /\
                    UNIONS {segment[b,x] | x IN relative_frontier Q} = Q`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [USE_THEN "rfq" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_RF_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`Q:real^3->bool`; `b:real^3`] THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_CON_CONE_RF THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(vec 0:real^3) IN I0`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(a:real^3) IN I0`)) THEN
  MP_TAC(ISPECL [`relative_frontier Q:real^3->bool`; `relative_frontier Q:real^3->bool`;
                 `vec 0:real^3`; `a:real^3`; `\x:real^3. x`; `\x:real^3. x`]
    MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID;
                GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `cm = moi_con_conemap (relative_frontier Q) (vec 0:real^3) a (\x:real^3. x)` THEN
  ABBREV_TAC `cm' = moi_con_conemap (relative_frontier Q) (a:real^3) (vec 0) (\x:real^3. x)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "base")) THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN Q /\ ~(x IN I0) ==> cm' x = x` (LABEL_TAC "base'") THENL
   [X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(cm:real^3->real^3) x = x` ASSUME_TAC THENL
     [USE_THEN "base" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^3. p IN Q
               ==> ?r. &0 <= r /\ r <= &1 /\ cm p = p + (&1 - r) % a /\
                       (r < &1 <=> p IN I0)`
  (LABEL_TAC "form") THENL
   [X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^3) IN UNIONS {segment[vec 0,x] | x IN relative_frontier Q}`
    MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[MOI_CON_IN_CONE; VECTOR_ADD_LID; VECTOR_SUB_RZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`relative_frontier Q:real^3->bool`; `vec 0:real^3`; `a:real^3`;
                   `\x:real^3. x`; `x:real^3`; `r:real`] MOI_CON_CONEMAP_EQ) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_LID; VECTOR_SUB_RZERO] THEN DISCH_THEN SUBST1_TAC THEN
    CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN Q /\ ~(x IN I0)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EQ_TAC THENL
     [DISCH_TAC THEN ASM_CASES_TAC `r = &0` THENL
       [ASM_REWRITE_TAC[VECTOR_MUL_LZERO]; ALL_TAC] THEN
      SUBGOAL_THEN `r % x IN relative_interior (Q:real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC MOI_CMB_RAY_INTERIOR THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
        UNDISCH_TAC `&0 <= r` THEN UNDISCH_TAC `~(r = &0)` THEN
        UNDISCH_TAC `r < &1` THEN REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]];
      DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `r <= &1 /\ ~(r = &1) ==> r < &1`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `r % x IN (I0:real^3->bool)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LID]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^3->real^3. pl_map_on Q h /\ (!x. x IN Q /\ ~(x IN I0) ==> h x = x)
          ==> pl_map_on (:real^3) (\p. if p IN Q then h p else p)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(:real^3) = Q UNION ((:real^3) DIFF I0)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `h:real^3->real^3` THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\x:real^3. x` THEN
      ASM_REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID; IN_DIFF; IN_UNIV] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN COND_CASES_TAC THEN ASM_SIMP_TAC[];
      SUBGOAL_THEN `Q UNION ((:real^3) DIFF I0) = (:real^3)` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN];
      SUBGOAL_THEN `Q UNION ((:real^3) DIFF I0) = (:real^3)` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; closed;
                  SET_RULE `(:real^3) DIFF ((:real^3) DIFF s) = s`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\p:real^3. if p IN Q then (cm:real^3->real^3) p else p`;
                        `\p:real^3. if p IN Q then (cm':real^3->real^3) p else p`] THEN
  SUBGOAL_THEN `pl_map_on (:real^3) (\p:real^3. if p IN Q then cm p else p) /\
                pl_map_on (:real^3) (\p:real^3. if p IN Q then cm' p else p)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(\p:real^3. if p IN Q then cm p else p) continuous_on (:real^3) /\
                (\p:real^3. if p IN Q then cm' p else p) continuous_on (:real^3)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNIV] THEN
  SUBGOAL_THEN
   `(!x:real^3. (if (if x IN Q then cm x else x) IN Q
                 then cm' (if x IN Q then cm x else x)
                 else if x IN Q then cm x else x) = x) /\
    (!y:real^3. (if (if y IN Q then cm' y else y) IN Q
                 then cm (if y IN Q then cm' y else y)
                 else if y IN Q then cm' y else y) = y)`
  (CONJUNCTS_THEN2 (LABEL_TAC "inv1") (LABEL_TAC "inv2")) THENL
   [CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN
    ASM_CASES_TAC `(x:real^3) IN Q` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `x:real^3` THEN
    EXISTS_TAC `if (x:real^3) IN Q then cm' x else x` THEN
    USE_THEN "inv2" (fun th -> REWRITE_TAC[th]);
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `x:real^3` THEN
    EXISTS_TAC `if (x:real^3) IN Q then cm x else x` THEN
    USE_THEN "inv1" (fun th -> REWRITE_TAC[th]);
    X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "base" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    X_GEN_TAC `p:real^3` THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "form" (MP_TAC o C MATCH_MP (ASSUME `(p:real^3) IN Q`)) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "a" THEN
    SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3;
             ARITH] THEN REAL_ARITH_TAC;
    X_GEN_TAC `p:real^3` THEN COND_CASES_TAC THEN REWRITE_TAC[] THENL
     [USE_THEN "form" (MP_TAC o C MATCH_MP (ASSUME `(p:real^3) IN Q`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `&1 - r` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [UNDISCH_TAC `r <= &1` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_iff(concl th) &&
          rand(concl th) = `(p:real^3) IN I0`)) THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      EXPAND_TAC "a" THEN
      SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3;
               ARITH] THEN REAL_ARITH_TAC;
      EXISTS_TAC `&0` THEN REWRITE_TAC[REAL_LE_REFL; REAL_LT_REFL; REAL_MUL_LZERO;
                                        REAL_ADD_RID] THEN
      ASM SET_TAC[]]]);;

(* ========================================================================= *)
(* Part 2: pushes in charts and their composition (generic).  A chart       *)
(* push: in a PL chart f of an open U onto an open set containing the unit *)
(* cube, in which A is the plane z1 = 0, C the side s * z1 >= 0, and       *)
(* membership in X depends only on z2 and z3 over the cube, the model push *)
(* conjugated by f moves the points of C near x off A, keeps C and X, and *)
(* is the identity outside U.  Finitely many such pushes compose.          *)
(* ========================================================================= *)

let MOI_S3PU_CHART_PUSH = prove
 (`!(U:real^3->bool) (f:real^3->real^3) g x (C:real^3->bool) A X G s.
     open U /\ pl_homeomorphism (U,IMAGE f U) (f,g) /\ open (IMAGE f U) /\
     x IN U /\ f x = vec 0 /\ U SUBSET G /\ (s = &1 \/ s = -- &1) /\
     interval[--vec 1,vec 1] SUBSET IMAGE f U /\
     (!y. y IN U /\ f y IN interval[--vec 1,vec 1] ==> (y IN A <=> (f y)$1 = &0)) /\
     (!y. y IN U /\ f y IN interval[--vec 1,vec 1] ==> (y IN C <=> &0 <= s * (f y)$1)) /\
     (!y y'. y IN U /\ y' IN U /\ f y IN interval[--vec 1,vec 1] /\
             f y' IN interval[--vec 1,vec 1] /\
             (f y)$2 = (f y')$2 /\ (f y)$3 = (f y')$3
             ==> (y IN X <=> y' IN X))
     ==> ?(Psi:real^3->real^3) Psi' W.
           pl_homeomorphism ((:real^3),(:real^3)) (Psi,Psi') /\
           open W /\ x IN W /\
           (!y. ~(y IN G) ==> Psi y = y) /\
           (!y. Psi y IN X <=> y IN X) /\
           (!y. y IN C ==> Psi y IN C /\
                           (Psi y IN A ==> y IN A /\ ~(y IN W) /\ Psi y = y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IMP_IMP]) THEN
  FIRST_X_ASSUM(LABEL_TAC "hX" o check (fun th ->
    can (find_term ((=) `X:real^3->bool`)) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "hC" o check (fun th ->
    can (find_term ((=) `C:real^3->bool`)) (concl th))) THEN
  FIRST_X_ASSUM(LABEL_TAC "hA" o check (fun th ->
    can (find_term ((=) `A:real^3->bool`)) (concl th))) THEN
  MP_TAC(SPEC `s / &2` MOI_S3PU_MODEL_PUSH) THEN ANTS_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:real^3->real^3` (X_CHOOSE_THEN `P':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!z:real^3. z IN IMAGE f U ==> f((g:real^3->real^3) z) = z /\ g z IN U`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (U,IMAGE f U) (f:real^3->real^3,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN U ==> g((f:real^3->real^3) y) = y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (U,IMAGE f U) (f:real^3->real^3,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!p:real^3. P'(P p) = p) /\ (!p:real^3. P(P' p) = p)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3)) (P,P')` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^3. ~(p IN interval[--vec 1,vec 1]) ==> P p = p /\ P' p = p`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(P:real^3->real^3) p = p` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `interval(--vec 1:real^3,vec 1)`)) (concl th) &&
        is_forall (concl th) && is_imp (snd(dest_forall(concl th))) &&
        is_neg (lhand(snd(dest_forall(concl th)))))) THEN
      MP_TAC(ISPECL [`--vec 1:real^3`; `vec 1:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
      ASM SET_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^3. p IN interval[--vec 1,vec 1]
                           ==> (P':real^3->real^3) p IN interval[--vec 1,vec 1]`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~q ==> F) ==> q`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(P:real^3->real^3) ((P':real^3->real^3) p) = P' p` MP_TAC THENL
     [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN IMAGE (f:real^3->real^3) U
               ==> (P:real^3->real^3) z IN IMAGE f U /\ (P':real^3->real^3) z IN IMAGE f U`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(z:real^3) IN interval[--vec 1,vec 1]` THENL
     [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (g:real^3->real^3) (interval[--vec 1,vec 1])) /\
                IMAGE (g:real^3->real^3) (interval[--vec 1,vec 1]) SUBSET U`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN REWRITE_TAC[COMPACT_INTERVAL] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `IMAGE (f:real^3->real^3) U` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `pl_homeomorphism (U,IMAGE f U) (f:real^3->real^3,g)` THEN
      SIMP_TAC[pl_homeomorphism; homeomorphism];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. ~(y IN IMAGE (g:real^3->real^3) (interval[--vec 1,vec 1]))
               ==> (if y IN U then g((P:real^3->real^3)(f y)) else y) = y /\
                   (if y IN U then g((P':real^3->real^3)(f y)) else y) = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((f:real^3->real^3) y IN interval[--vec 1,vec 1])` ASSUME_TAC THENL
     [UNDISCH_TAC `~(y IN IMAGE (g:real^3->real^3) (interval[--vec 1,vec 1]))` THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(h:real^3->real^3). pl_map_on (:real^3) h /\
       (!y. ~(y IN interval[--vec 1,vec 1]) ==> h y = y) /\
       (!y. y IN interval[--vec 1,vec 1] ==> h y IN interval[--vec 1,vec 1])
       ==> pl_map_on (:real^3) (\y:real^3. if y IN U then g(h(f y)) else y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[PL_MAP_ON_LOCAL] THEN
    X_GEN_TAC `y0:real^3` THEN REWRITE_TAC[IN_UNIV; INTER_UNIV] THEN
    ASM_CASES_TAC `(y0:real^3) IN U` THENL
     [EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `(g:real^3->real^3) o (h:real^3->real^3) o (f:real^3->real^3)` THEN
      CONJ_TAC THENL [SIMP_TAC[o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `IMAGE (f:real^3->real^3) U` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV] THEN
        UNDISCH_TAC `pl_homeomorphism (U,IMAGE f U) (f:real^3->real^3,g)` THEN
        SIMP_TAC[pl_homeomorphism];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `pl_homeomorphism (U,IMAGE f U) (f:real^3->real^3,g)` THEN
        SIMP_TAC[pl_homeomorphism];
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN ASM_CASES_TAC `(f:real^3->real^3) y IN interval[--vec 1,vec 1]` THENL
       [ASM_MESON_TAC[SUBSET]; ASM_SIMP_TAC[FUN_IN_IMAGE]];
      EXISTS_TAC `(:real^3) DIFF IMAGE (g:real^3->real^3) (interval[--vec 1,vec 1])` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
        REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM SET_TAC[];
        MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\y:real^3. y` THEN CONJ_TAC THENL
         [X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_DIFF; IN_UNIV] THEN DISCH_TAC THEN
          COND_CASES_TAC THEN REWRITE_TAC[] THEN
          SUBGOAL_THEN `~((f:real^3->real^3) y IN interval[--vec 1,vec 1])` ASSUME_TAC THENL
           [UNDISCH_TAC `~(y IN IMAGE (g:real^3->real^3) (interval[--vec 1,vec 1]))` THEN
            REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
            ASM_MESON_TAC[]];
          REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
          MATCH_MP_TAC LOCALLY_POLYHEDRAL_OPEN THEN
          REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN U
       ==> (g:real^3->real^3)((P:real^3->real^3)((f:real^3->real^3) y)) IN U /\
           f(g(P(f y))) = P(f y) /\
           g((P':real^3->real^3)(f y)) IN U /\
           f(g(P'(f y))) = P'(f y)`
  (LABEL_TAC "gu") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(f:real^3->real^3) y IN IMAGE f U` ASSUME_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!y:real^3. (if (if y IN U then (g:real^3->real^3)((P:real^3->real^3)((f:real^3->real^3) y))
                     else y) IN U
                 then g((P':real^3->real^3)(f (if y IN U then g(P(f y)) else y)))
                 else if y IN U then g(P(f y)) else y) = y) /\
    (!y:real^3. (if (if y IN U then (g:real^3->real^3)((P':real^3->real^3)((f:real^3->real^3) y))
                     else y) IN U
                 then g((P:real^3->real^3)(f (if y IN U then g(P'(f y)) else y)))
                 else if y IN U then g(P'(f y)) else y) = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN ASM_CASES_TAC `(y:real^3) IN U` THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "gu" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(y:real^3) IN U`)) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`\y:real^3. if y IN U then (g:real^3->real^3)((P:real^3->real^3)(f y)) else y`;
    `\y:real^3. if y IN U then (g:real^3->real^3)((P':real^3->real^3)(f y)) else y`;
    `IMAGE (g:real^3->real^3) (interval(--vec 1,vec 1))`] THEN
  SUBGOAL_THEN
   `pl_map_on (:real^3)
      (\y:real^3. if y IN U then (g:real^3->real^3)((P:real^3->real^3)(f y)) else y) /\
    pl_map_on (:real^3)
      (\y:real^3. if y IN U then (g:real^3->real^3)((P':real^3->real^3)(f y)) else y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN IMAGE (g:real^3->real^3) (interval(--vec 1,vec 1))
               ==> y IN U /\ (f:real^3->real^3) y IN interval(--vec 1,vec 1)`
  (LABEL_TAC "inW") THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN IMAGE (f:real^3->real^3) U` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`--vec 1:real^3`; `vec 1:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
      ASM SET_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. ~(y IN U /\ (f:real^3->real^3) y IN interval[--vec 1,vec 1])
                ==> (if y IN U then (g:real^3->real^3)((P:real^3->real^3)(f y)) else y) = y`
  (LABEL_TAC "fix") THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(P:real^3->real^3)((f:real^3->real^3) y) = f y` SUBST1_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[homeomorphism; IN_UNIV] THEN BETA_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^3` THEN
      EXISTS_TAC `if y IN U then (g:real^3->real^3)((P':real^3->real^3)(f y)) else y` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^3` THEN
      EXISTS_TAC `if y IN U then (g:real^3->real^3)((P:real^3->real^3)(f y)) else y` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`g:real^3->real^3`; `f:real^3->real^3`;
                   `IMAGE (f:real^3->real^3) U`; `U:real^3->bool`;
                   `interval(--vec 1:real^3,vec 1)`] HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN
        UNDISCH_TAC `pl_homeomorphism (U,IMAGE f U) (f:real^3->real^3,g)` THEN
        SIMP_TAC[pl_homeomorphism];
        MATCH_MP_TAC OPEN_SUBSET THEN REWRITE_TAC[OPEN_INTERVAL] THEN
        MP_TAC(ISPECL [`--vec 1:real^3`; `vec 1:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
        ASM SET_TAC[]];
      DISCH_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
      EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^3` THEN
    REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; REAL_ARITH_TAC];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((y:real^3) IN U)` (fun th -> REWRITE_TAC[th]) THEN ASM SET_TAC[];
    X_GEN_TAC `y:real^3` THEN
    ASM_CASES_TAC `(y:real^3) IN U /\ (f:real^3->real^3) y IN interval[--vec 1,vec 1]` THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "gu" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(y:real^3) IN U`)) THEN
      CONV_TAC SYM_CONV THEN
      USE_THEN "hX" MATCH_MP_TAC THEN ASM_SIMP_TAC[];
      USE_THEN "fix" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
        `~((y:real^3) IN U /\ (f:real^3->real^3) y IN interval[--vec 1,vec 1])`)])];
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^3) IN U /\ (f:real^3->real^3) y IN interval[--vec 1,vec 1]` THENL
     [ALL_TAC;
      USE_THEN "fix" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
        `~((y:real^3) IN U /\ (f:real^3->real^3) y IN interval[--vec 1,vec 1])`)]) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "inW" (MP_TAC o C MATCH_MP
        (ASSUME `(y:real^3) IN IMAGE (g:real^3->real^3) (interval(--vec 1,vec 1))`)) THEN
      MP_TAC(ISPECL [`--vec 1:real^3`; `vec 1:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
      ASM SET_TAC[]] THEN
    FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "gu" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(y:real^3) IN U`)) THEN
    FIRST_ASSUM(MP_TAC o SPEC `(f:real^3->real^3) y` o check (fun th ->
      is_forall (concl th) && is_exists (snd (dest_forall (concl th))))) THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(P:real^3->real^3)((f:real^3->real^3) y) IN interval[--vec 1,vec 1]`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(f:real^3->real^3)((g:real^3->real^3)((P:real^3->real^3)(f y))) IN
      interval[--vec 1,vec 1]`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `((g:real^3->real^3)((P:real^3->real^3)((f:real^3->real^3) y)) IN C <=>
       &0 <= s * (P(f y))$1) /\
      (g(P(f y)) IN A <=> (P(f y))$1 = &0) /\
      (y IN C <=> &0 <= s * (f y)$1) /\
      (y IN A <=> (f y)$1 = &0)`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "hC" (MP_TAC o C MATCH_MP (CONJ
        (ASSUME `(g:real^3->real^3)((P:real^3->real^3)((f:real^3->real^3) y)) IN U`)
        (ASSUME `(f:real^3->real^3)(g((P:real^3->real^3)(f y))) IN interval[--vec 1,vec 1]`))) THEN
      USE_THEN "hA" (MP_TAC o C MATCH_MP (CONJ
        (ASSUME `(g:real^3->real^3)((P:real^3->real^3)((f:real^3->real^3) y)) IN U`)
        (ASSUME `(f:real^3->real^3)(g((P:real^3->real^3)(f y))) IN interval[--vec 1,vec 1]`))) THEN
      USE_THEN "hC" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN U`)
        (ASSUME `(f:real^3->real^3) y IN interval[--vec 1,vec 1]`))) THEN
      USE_THEN "hA" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN U`)
        (ASSUME `(f:real^3->real^3) y IN interval[--vec 1,vec 1]`))) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= s * ((f:real^3->real^3) y)$1` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN C` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `s * ((P:real^3->real^3)((f:real^3->real^3) y))$1 = s * (f y)$1 + l / &2`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `s = &1 \/ s = -- &1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `&0 <= l` THEN UNDISCH_TAC `&0 <= s * ((f:real^3->real^3) y)$1` THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `((f:real^3->real^3) y)$1 = &0 /\ l = &0` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `((f:real^3->real^3) y)$1 + l * s / &2 = &0` THEN
      UNDISCH_TAC `&0 <= l` THEN UNDISCH_TAC `&0 <= s * ((f:real^3->real^3) y)$1` THEN
      UNDISCH_TAC `s = &1 \/ s = -- &1` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `~((f:real^3->real^3) y IN interval(--vec 1,vec 1))` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_iff (concl th) &&
        rand(concl th) = `(f:real^3->real^3) y IN interval(--vec 1,vec 1)`)) THEN
      ASM_REWRITE_TAC[REAL_LT_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(P:real^3->real^3)((f:real^3->real^3) y) = f y` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME `!p:real^3. ~(p IN interval(--vec 1,vec 1))
                                      ==> (P:real^3->real^3) p = p`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:real^3->real^3)((f:real^3->real^3) y) = y` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    USE_THEN "inW" (MP_TAC o C MATCH_MP
      (ASSUME `(y:real^3) IN IMAGE (g:real^3->real^3) (interval(--vec 1,vec 1))`)) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S3PU_PUSH_COMPOSE = prove
 (`!(kk:real^3->bool) C A X G.
     compact kk /\
     (!x. x IN kk
          ==> ?(Psi:real^3->real^3) Psi' W.
                pl_homeomorphism ((:real^3),(:real^3)) (Psi,Psi') /\
                open W /\ x IN W /\
                (!y. ~(y IN G) ==> Psi y = y) /\
                (!y. Psi y IN X <=> y IN X) /\
                (!y. y IN C ==> Psi y IN C /\
                                (Psi y IN A ==> y IN A /\ ~(y IN W) /\ Psi y = y)))
     ==> ?(Phi:real^3->real^3) Phi'.
           pl_homeomorphism ((:real^3),(:real^3)) (Phi,Phi') /\
           (!y. ~(y IN G) ==> Phi y = y) /\
           (!y. Phi y IN X <=> y IN X) /\
           (!y. y IN C ==> Phi y IN C /\ (Phi y IN A ==> ~(y IN kk) /\ Phi y = y))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])) THEN
  DISCH_THEN(X_CHOOSE_THEN `Psi:real^3->real^3->real^3`
    (X_CHOOSE_THEN `Psi':real^3->real^3->real^3`
      (X_CHOOSE_THEN `W:real^3->real^3->bool` (LABEL_TAC "loc")))) THEN
  SUBGOAL_THEN
   `?ff:real^3->bool. FINITE ff /\ ff SUBSET kk /\
                     kk SUBSET UNIONS (IMAGE (W:real^3->real^3->bool) ff)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `compact(kk:real^3->bool)` THEN REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN
    DISCH_THEN(MP_TAC o SPEC `IMAGE (W:real^3->real^3->bool) kk`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
      USE_THEN "loc" (fun th -> MESON_TAC[th]);
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`W:real^3->real^3->bool`; `kk:real^3->bool`;
                   `f':(real^3->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `ff:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!ss:real^3->bool. FINITE ss
      ==> ss SUBSET kk
          ==> ?(Phi:real^3->real^3) Phi'.
                pl_homeomorphism ((:real^3),(:real^3)) (Phi,Phi') /\
                (!y. ~(y IN G) ==> Phi y = y) /\
                (!y. Phi y IN X <=> y IN X) /\
                (!y. y IN C ==> Phi y IN C /\
                                (Phi y IN A
                                 ==> y IN A /\ (!x. x IN ss ==> ~(y IN W x)) /\
                                     Phi y = y))`
  MP_TAC THENL
   [MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
     [DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`\x:real^3. x`; `\x:real^3. x`] THEN
      REWRITE_TAC[NOT_IN_EMPTY; pl_homeomorphism; HOMEOMORPHISM_ID;
                  GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
      SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`x:real^3`; `ss:real^3->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
    USE_THEN "ih" (MP_TAC o C MP (ASSUME `(ss:real^3->bool) SUBSET kk`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->real^3` (X_CHOOSE_THEN `Phi':real^3->real^3`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "p1")
        (CONJUNCTS_THEN2 (LABEL_TAC "p2") (LABEL_TAC "p3")))))) THEN
    USE_THEN "loc" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN kk`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "q3")
        (CONJUNCTS_THEN2 (LABEL_TAC "q4") (LABEL_TAC "q5")))))) THEN
    MAP_EVERY EXISTS_TAC [`(Psi:real^3->real^3->real^3) x o (Phi:real^3->real^3)`;
                          `(Phi':real^3->real^3) o (Psi':real^3->real^3->real^3) x`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[o_THM; IN_INSERT] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "p1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~(y IN (G:real^3->bool))`)]) THEN
      USE_THEN "q3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^3` THEN USE_THEN "q4" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "p2" (fun th -> REWRITE_TAC[th]);
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      USE_THEN "p3" (MP_TAC o C MATCH_MP (ASSUME `(y:real^3) IN C`)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pa")) THEN
      USE_THEN "q5" (MP_TAC o C MATCH_MP (ASSUME `(Phi:real^3->real^3) y IN C`)) THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "qa")) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "qa" (MP_TAC o C MP
        (ASSUME `(Psi:real^3->real^3->real^3) x ((Phi:real^3->real^3) y) IN A`)) THEN
      STRIP_TAC THEN
      USE_THEN "pa" (MP_TAC o C MP (ASSUME `(Phi:real^3->real^3) y IN A`)) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(Phi:real^3->real^3) y = y` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN
        REWRITE_TAC[th]) THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `ff:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(kk:real^3->bool) SUBSET UNIONS (IMAGE (W:real^3->real^3->bool) ff)` THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* Part 3: the link of a vertex w of a finite simplicial complex d is a PL  *)
(* circle when every point of the open star of w has a plane chart in the  *)
(* polyhedron of d (MOI_S3TM_VERTEX_LINK_LOC in the closed star of w, with *)
(* dimension, purity and edge counts from the local arguments of           *)
(* MOI_S8TA_EMB2_DIM, MOI_S8TB_LOW_NO and MOI_S8TA_EDGE0/1/3).              *)
(* ========================================================================= *)

let MOI_S3PU_OPEN_STAR_RELINT = prove
 (`!(d:(real^N->bool)->bool) w s z.
     simplicial_complex d /\ s IN d /\ w IN s /\ z IN relative_interior s
     ==> z IN moi_sta_open_star d w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM; IN_UNIONS] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `s:real^N->bool` THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET t` (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
    MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `z:real^N`] THEN ASM_REWRITE_TAC[]]);;

(* A maximal simplex through w has dimension at least 2 when the points of *)
(* the open star of w have plane charts (MOI_S8TB_LOW_NO on the open star  *)
(* of the simplex, which lies in it).                                       *)

let MOI_S3PU_MAXIMAL = prove
 (`!(d:(real^N->bool)->bool) w t.
     simplicial_complex d /\ t IN d /\ w IN t /\
     (!u. u IN d /\ t SUBSET u ==> u = t) /\
     (!z. z IN moi_sta_open_star d w ==> moi_s28_locally_r2 (UNIONS d) z)
     ==> &2 <= aff_dim t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^N. z IN relative_interior t` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s28_locally_r2 (UNIONS d) (z:real^N)` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC MOI_S3PU_OPEN_STAR_RELINT THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`UNIONS d:real^N->bool`; `z:real^N`;
                 `{x:real^N | x IN UNIONS d /\ !u. u IN d /\ x IN u ==> t SUBSET u}`;
                 `t:real^N->bool`] MOI_S8TB_LOW_NO) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[MOI_SCF_SC_OPEN_STAR];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN CONJ_TAC THENL
     [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `z:real^N`] THEN
      ASM_REWRITE_TAC[]];
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)
      (LABEL_TAC "tu")) THEN
    SUBGOAL_THEN `t SUBSET (u:real^N->bool)` ASSUME_TAC THENL
     [USE_THEN "tu" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `u:real^N->bool = t` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      is_eq(snd(dest_imp(snd(dest_forall(concl th))))))) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `aff_dim(t:real^N->bool) < &2` THEN INT_ARITH_TAC]);;

let MOI_S3PU_VLINK = prove
 (`!(d:(real^N->bool)->bool) w.
     simplicial_complex d /\ {w} IN d /\
     (!z. z IN moi_sta_open_star d w ==> moi_s28_locally_r2 (UNIONS d) z)
     ==> pl_sphere 1 (UNIONS (simplicial_link d w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (d:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN UNIONS d` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`] MOI_S3TM_STAR) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `dw = {s:real^N->bool | ?t. t IN d /\ w IN t /\ s face_of t}` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!z:real^N. z IN moi_sta_open_star d w ==> moi_s28_locally_r2 (UNIONS dw) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `z:real^N`] MOI_S3TM_STAR_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN moi_sta_open_star d w` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_link dw (w:real^N) = simplicial_link d w` (SUBST1_TAC o SYM)
  THENL [EXPAND_TAC "dw" THEN MATCH_MP_TAC MOI_S3TM_LINK_STAR THEN ASM_REWRITE_TAC[];
         ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^N} IN dw` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s28_locally_r2 (UNIONS dw) (w:real^N)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN d /\ w IN t ==> aff_dim t <= &2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TA_EMB2_DIM THEN
    MAP_EVERY EXISTS_TAC [`dw:(real^N->bool)->bool`; `w:real^N`] THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN dw ==> aff_dim s <= &2` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN EXPAND_TAC "dw" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(t:real^N->bool)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC AFF_DIM_SUBSET THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^N->bool. t IN d /\ w IN t
        ==> ?t'. t' IN d /\ aff_dim t' = &2 /\ t SUBSET t'`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `!t:real^N->bool. t IN d /\ w IN t /\ aff_dim t < &2
          ==> ?u. u IN d /\ t SUBSET u /\ aff_dim t < aff_dim u`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM;
        TAUT `~(a /\ b /\ c) <=> a /\ b ==> ~c`; INT_NOT_LT]) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `t:real^N->bool`]
        MOI_S3PU_MAXIMAL) THEN
      ASM_REWRITE_TAC[GSYM INT_NOT_LT] THEN
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC(GSYM MOI_SCF_SUBSET_DIM_EQ) THEN
      EXISTS_TAC `d:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(INT_ARITH `a:int <= b /\ b <= a ==> a = b`) THEN
      ASM_SIMP_TAC[AFF_DIM_SUBSET];
      ALL_TAC] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `aff_dim(t:real^N->bool) = &2` THENL
     [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:real^N->bool`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INT_LT_LE] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `aff_dim(u:real^N->bool) = &2` THENL
     [EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INT_LT_LE] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]] THEN
      FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC(INT_ARITH `!a t u:int. a <= &2 /\ &0 <= t /\ t < u /\ u < a ==> a = &2`) THEN
    EXISTS_TAC `aff_dim(t:real^N->bool)` THEN EXISTS_TAC `aff_dim(u:real^N->bool)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      REWRITE_TAC[AFF_DIM_GE; INT_ARITH `&0:int <= x <=> -- &1 <= x /\ ~(x = -- &1)`] THEN
      REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN dw /\ ~(s = {})
                     ==> ?t. t IN dw /\ aff_dim t = &2 /\ s SUBSET t`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN EXPAND_TAC "dw" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t0:real^N->bool` o check (fun th ->
      is_forall(concl th) && is_exists(snd(dest_imp(snd(dest_forall(concl th))))))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_REFL] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX;
                                                 FACE_OF_REFL]];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:real^N. {a} IN simplicial_link dw w
     ==> CARD {t | t IN dw /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`dw:(real^N->bool)->bool`; `w:real^N`; `a:real^N`]
      MOI_S8TB_LINK_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ABBREV_TAC `e:real^N->bool = convex hull {w,a}` THEN
    SUBGOAL_THEN `?z:real^N. z IN relative_interior e` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
      SUBGOAL_THEN `convex(e:real^N->bool)` ASSUME_TAC THENL
       [EXPAND_TAC "e" THEN REWRITE_TAC[CONVEX_CONVEX_HULL]; ALL_TAC] THEN
      ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN EXPAND_TAC "e" THEN
      REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_s28_locally_r2 (UNIONS dw) (z:real^N)` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN MATCH_MP_TAC MOI_S3PU_OPEN_STAR_RELINT THEN
      EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; EXPAND_TAC "e" THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
      ALL_TAC] THEN
    ABBREV_TAC `ts = {t:real^N->bool | t IN dw /\ aff_dim t = &2 /\ e SUBSET t}` THEN
    SUBGOAL_THEN `FINITE (ts:(real^N->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "ts" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
      ASM_SIMP_TAC[MOI_SCF_SC_FINITE];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(CARD (ts:(real^N->bool)->bool) = 0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[CARD_EQ_0] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`dw:(real^N->bool)->bool`; `e:real^N->bool`; `z:real^N`]
        MOI_S8TA_EDGE0_NO) THEN
      ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
      UNDISCH_TAC `ts:(real^N->bool)->bool = {}` THEN EXPAND_TAC "ts" THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(CARD (ts:(real^N->bool)->bool) = 1)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(ts:(real^N->bool)->bool) HAS_SIZE 1` MP_TAC THENL
       [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
      CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
      DISCH_THEN(X_CHOOSE_TAC `t1:real^N->bool`) THEN
      SUBGOAL_THEN `(t1:real^N->bool) IN dw /\ aff_dim t1 = &2 /\ e SUBSET t1`
      STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `(t1:real^N->bool) IN ts` MP_TAC THENL
         [ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
        EXPAND_TAC "ts" THEN REWRITE_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`dw:(real^N->bool)->bool`; `e:real^N->bool`; `t1:real^N->bool`;
                     `z:real^N`] MOI_S8TA_EDGE1_NO_R2) THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `t':real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(t':real^N->bool) IN ts` MP_TAC THENL
       [EXPAND_TAC "ts" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ASM_REWRITE_TAC[IN_SING]];
      ALL_TAC] THEN
    SUBGOAL_THEN `CARD (ts:(real^N->bool)->bool) <= 2` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`3`; `ts:(real^N->bool)->bool`] CHOOSE_SUBSET_STRONG) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `2 < CARD(ts:(real^N->bool)->bool)` THEN
                      ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s3:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_SCF_HAS_SIZE_3]) THEN
      DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
        (X_CHOOSE_THEN `t3:real^N->bool` STRIP_ASSUME_TAC))) THEN
      SUBGOAL_THEN `(t1:real^N->bool) IN ts /\ t2 IN ts /\ t3 IN ts` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      EXPAND_TAC "ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`dw:(real^N->bool)->bool`; `e:real^N->bool`; `t1:real^N->bool`;
                     `t2:real^N->bool`; `t3:real^N->bool`; `z:real^N`] MOI_S8TA_EDGE3_NO) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~(CARD (ts:(real^N->bool)->bool) = 0)` THEN
    UNDISCH_TAC `~(CARD (ts:(real^N->bool)->bool) = 1)` THEN
    UNDISCH_TAC `CARD (ts:(real^N->bool)->bool) <= 2` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dw:(real^N->bool)->bool`; `w:real^N`] MOI_S3TM_VERTEX_LINK_LOC) THEN
  ASM_SIMP_TAC[] THEN ANTS_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S8TB_PUNCT THEN ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

(* The open star of a vertex w of a complex inside a convex set s with w in *)
(* the interior of s lies in the interior of s.                             *)

let MOI_S3PU_OPEN_STAR_INTERIOR = prove
 (`!(d:(real^N->bool)->bool) w s.
     simplicial_complex d /\ {w} IN d /\ convex s /\ UNIONS d SUBSET s /\
     w IN interior s
     ==> moi_sta_open_star d w SUBSET interior s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; moi_sta_open_star; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `z:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^N->bool) IN d` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN f` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  ASM_CASES_TAC `z:real^N = w` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^N->bool`; `z:real^N`; `w:real^N`] RELATIVE_INTERIOR_PROLONG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `w:real^N`; `w + r % (z - w):real^N`]
    IN_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    UNDISCH_TAC `UNIONS d SUBSET (s:real^N->bool)` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS] THEN DISCH_THEN MATCH_MP_TAC THEN
    EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `w:real^N = w + r % (z - w) <=> r % (z - w) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    UNDISCH_TAC `&1 < r` THEN REAL_ARITH_TAC;
    EXISTS_TAC `inv r:real` THEN
    SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL [UNDISCH_TAC `&1 < r` THEN REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_INV_LT_1] THEN
    REWRITE_TAC[VECTOR_ARITH `(&1 - u) % w + u % (w + r % (z - w)):real^N =
                              w + (u * r) % (z - w)`] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC]);;

(* ========================================================================= *)
(* Part 4: flat charts of locally polyhedral surfaces in real^3.  Near a    *)
(* point y of a closed set p that is locally polyhedral and locally R^2     *)
(* there is a PL chart onto an open set taking p to the plane z1 = 0.       *)
(* Route: a cube nbhd S of y, a triangulation of S with p INTER S and {y}  *)
(* as unions of simplices, the link of y (a PL 2-sphere) and the link of y  *)
(* in p (a PL circle, MOI_S3PU_VLINK), a PL homeomorphism of the link       *)
(* sphere onto the frontier of the unit cube taking the link circle to the *)
(* section by z1 = 0 (MOI_S4O_SPHERE_SPLIT, MOI_CEL_CELL_EXTENSION), and   *)
(* the cone map from y to vec 0 (MOI_CON_CONE_MAP) on the open star.        *)
(* ========================================================================= *)

(* Rays from an interior point of a bounded convex set meet its relative   *)
(* frontier exactly once.                                                    *)

let MOI_S3PU_RF_RAYS = prove
 (`!k:real^N->bool.
     bounded k /\ convex k /\ vec 0 IN interior k
     ==> !u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN relative_frontier k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(vec 0:real^N) IN relative_interior k` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET_RELATIVE_INTERIOR; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`k:real^N->bool`; `vec 0:real^N`; `u:real^N`]
      RAY_TO_RELATIVE_FRONTIER) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN ANTS_TAC THENL
     [SUBGOAL_THEN `affine hull k = (:real^N)` (fun th -> REWRITE_TAC[th; IN_UNIV]) THEN
      MATCH_MP_TAC AFFINE_HULL_NONEMPTY_INTERIOR THEN ASM SET_TAC[];
      MESON_TAC[]];
    MAP_EVERY X_GEN_TAC [`r1:real`; `r2:real`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:real^N->bool`; `r1 % u:real^N`; `r2 % u:real^N`; `r1 / r2`]
      MOI_CMB_RAY_FRONTIER_UNIQUE) THEN
    ASM_SIMP_TAC[REAL_LT_DIV; VECTOR_MUL_ASSOC; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
    ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_MUL_LID]]);;

let MOI_S3PU_RF_SPHERE = prove
 (`!k:real^N->bool.
     polytope k /\ vec 0 IN interior k
     ==> pl_sphere (dimindex(:N) - 1) (relative_frontier k)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CMB_STAR_SHAPED_PL_SPHERE_0 THEN
  ASM_SIMP_TAC[MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER] THEN CONJ_TAC THENL
   [REWRITE_TAC[relative_frontier; IN_DIFF] THEN
    ASM_MESON_TAC[INTERIOR_SUBSET_RELATIVE_INTERIOR; SUBSET];
    MATCH_MP_TAC MOI_S3PU_RF_RAYS THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_BOUNDED; POLYTOPE_IMP_CONVEX]]);;

(* Small cubes around a point of an open set. *)

let MOI_S3PU_CUBE_NBHD = prove
 (`!(y:real^3) w0.
     open w0 /\ y IN w0
     ==> ?e. &0 < e /\ interval[y - e % vec 1,y + e % vec 1] SUBSET w0 /\
             y IN interior(interval[y - e % vec 1,y + e % vec 1])`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3` o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r / &4` THEN ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y:real^3,r)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_INTERVAL; IN_BALL; dist] THEN
    X_GEN_TAC `z:real^3` THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
                VEC_COMPONENT; REAL_MUL_RID; DIMINDEX_3; FORALL_3] THEN
    STRIP_TAC THEN
    MP_TAC(ISPEC `y - z:real^3` NORM_LE_L1) THEN
    REWRITE_TAC[DIMINDEX_3; SUM_3; VECTOR_SUB_COMPONENT] THEN
    UNDISCH_TAC `&0 < r` THEN
    REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC;
    REWRITE_TAC[INTERIOR_INTERVAL; IN_INTERVAL] THEN
    REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT;
                VEC_COMPONENT; REAL_MUL_RID] THEN
    UNDISCH_TAC `&0 < r` THEN REAL_ARITH_TAC]);;

(* The simplices of a complex inside a set form a subcomplex. *)

let MOI_S3PU_SC_RESTRICT = prove
 (`!(K:(real^N->bool)->bool) q.
     simplicial_complex K ==> simplicial_complex {t | t IN K /\ t SUBSET q}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]);;

(* A triangulation of a polytope s in which a polyhedron q SUBSET s is a     *)
(* union of simplices and a point y of q is a vertex.                       *)

let MOI_S3PU_TRIANG = prove
 (`!(s:real^N->bool) q y.
     polytope s /\ pl_polyhedron q /\ q SUBSET s /\ y IN q
     ==> ?K. simplicial_complex K /\ UNIONS K = s /\ {y} IN K /\
             simplicial_complex {t | t IN K /\ t SUBSET q} /\
             UNIONS {t | t IN K /\ t SUBSET q} = q /\
             {y} IN {t | t IN K /\ t SUBSET q}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `cq:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `(s:real^N->bool) INSERT {y} INSERT cq` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT; POLYTOPE_SING]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `K:(real^N->bool)->bool` THEN
  REWRITE_TAC[FORALL_IN_INSERT; UNIONS_INSERT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "cqk"))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `fy:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `{y:real^N} IN K` ASSUME_TAC THENL
   [SUBGOAL_THEN `?t:real^N->bool. t IN fy /\ y IN t` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM IN_UNIONS] THEN ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
    SUBGOAL_THEN `t = {y:real^N}` (fun th ->
      UNDISCH_TAC `(t:real^N->bool) IN fy` THEN
      UNDISCH_TAC `fy SUBSET (K:(real^N->bool)->bool)` THEN
      REWRITE_TAC[th] THEN SET_TAC[]) THEN
    UNDISCH_TAC `UNIONS fy = {y:real^N}` THEN UNDISCH_TAC `(t:real^N->bool) IN fy` THEN
    UNDISCH_TAC `(y:real^N) IN t` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `UNIONS K = (s:real^N->bool) UNION {y} UNION UNIONS cq` THEN
    UNDISCH_TAC `UNIONS cq = (q:real^N->bool)` THEN
    UNDISCH_TAC `(q:real^N->bool) SUBSET s` THEN UNDISCH_TAC `(y:real^N) IN q` THEN
    SET_TAC[];
    MATCH_MP_TAC MOI_S3PU_SC_RESTRICT THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?k:real^N->bool. k IN cq /\ x IN k` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM IN_UNIONS] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "cqk" (MP_TAC o C MATCH_MP (ASSUME `(k:real^N->bool) IN cq`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `fk:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?t:real^N->bool. t IN fk /\ x IN t` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM IN_UNIONS] THEN
      UNDISCH_TAC `(x:real^N) IN k` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `UNIONS cq = (q:real^N->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(k:real^N->bool) = UNIONS fk` THEN UNDISCH_TAC `(t:real^N->bool) IN fk` THEN
    UNDISCH_TAC `(k:real^N->bool) IN cq` THEN SET_TAC[];
    ASM SET_TAC[]]);;

(* The model: the frontier of the unit cube is a PL 2-sphere; its section   *)
(* by the plane z1 = 0 is a PL circle whose cone from vec 0 is the section   *)
(* of the cube (via the square of real^2 and the linear map iota).          *)

let MOI_S3PU_SQUARE_FACTS = prove
 (`relative_frontier(interval[--vec 1:real^2,vec 1]) =
     interval[--vec 1,vec 1] DIFF interval(--vec 1,vec 1) /\
   relative_interior(interval[--vec 1:real^2,vec 1]) = interval(--vec 1,vec 1) /\
   (vec 0:real^2) IN interval(--vec 1,vec 1) /\
   pl_sphere 1 (relative_frontier(interval[--vec 1:real^2,vec 1]))`,
  SUBGOAL_THEN `(vec 0:real^2) IN interval(--vec 1,vec 1)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior(interval[--vec 1:real^2,vec 1]) = interval(--vec 1,vec 1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `interior(interval[--vec 1:real^2,vec 1])` THEN
    CONJ_TAC THENL [ALL_TAC; REWRITE_TAC[INTERIOR_INTERVAL]] THEN
    MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR THEN
    REWRITE_TAC[INTERIOR_INTERVAL; GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[relative_frontier; CLOSURE_INTERVAL] THEN
  MP_TAC(ISPEC `interval[--vec 1:real^2,vec 1]` MOI_S3PU_RF_SPHERE) THEN
  ASM_REWRITE_TAC[POLYTOPE_INTERVAL; INTERIOR_INTERVAL; DIMINDEX_2; relative_frontier;
                  CLOSURE_INTERVAL] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[]);;

(* The linear embedding iota of real^2 onto the plane z1 = 0 of real^3. *)

let MOI_S3PU_IOTA = prove
 (`linear (\a:real^2. vector[&0; a$1; a$2]:real^3) /\
   (!a b:real^2. (vector[&0; a$1; a$2]:real^3) = vector[&0; b$1; b$2] ==> a = b) /\
   (!s:real^2->bool. IMAGE (\a. vector[&0; a$1; a$2]:real^3) s =
                     {z:real^3 | z$1 = &0 /\ vector[z$2; z$3] IN s})`,
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN REAL_ARITH_TAC;
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; DIMINDEX_2; FORALL_2; VECTOR_3] THEN
    MESON_TAC[];
    GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `a:real^2` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[VECTOR_3] THEN
      SUBGOAL_THEN `vector[a$1; a$2]:real^2 = a` (fun th -> ASM_REWRITE_TAC[th]) THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
      STRIP_TAC THEN EXISTS_TAC `vector[(z:real^3)$2; z$3]:real^2` THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_2]]]);;

(* The model: the frontier of the unit cube is a PL 2-sphere, its section by *)
(* z1 = 0 a PL circle (the frontier of the square of real^2 under iota),    *)
(* whose cone from vec 0 is the section of the cube.                         *)

let MOI_S3PU_CUBE_MODEL = prove
 (`pl_sphere 2 (relative_frontier(interval[--vec 1:real^3,vec 1])) /\
   pl_sphere 1 {z:real^3 | z IN relative_frontier(interval[--vec 1,vec 1]) /\ z$1 = &0} /\
   {z:real^3 | z IN relative_frontier(interval[--vec 1,vec 1]) /\ z$1 = &0} SUBSET
     relative_frontier(interval[--vec 1,vec 1]) /\
   UNIONS {segment[vec 0,x] | x IN {z:real^3 | z IN relative_frontier(interval[--vec 1,vec 1]) /\
                                                z$1 = &0}} =
     {z:real^3 | z IN interval[--vec 1,vec 1] /\ z$1 = &0}`,
  MP_TAC MOI_S3PU_IOTA THEN
  ABBREV_TAC `iota = \a:real^2. vector[&0; a$1; a$2]:real^3` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{z:real^3 | z IN relative_frontier(interval[--vec 1,vec 1]) /\ z$1 = &0} =
    IMAGE (iota:real^2->real^3) (relative_frontier(interval[--vec 1,vec 1])) /\
    {z:real^3 | z IN interval[--vec 1,vec 1] /\ z$1 = &0} =
    IMAGE (iota:real^2->real^3) (interval[--vec 1,vec 1])`
  (CONJUNCTS_THEN SUBST1_TAC) THENL
   [ASM_REWRITE_TAC[MOI_S3PU_CUBE_RF; MOI_S3PU_SQUARE_FACTS] THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_INTERVAL; DIMINDEX_3; FORALL_3;
                DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `interval[--vec 1:real^3,vec 1]` MOI_S3PU_RF_SPHERE) THEN
    REWRITE_TAC[POLYTOPE_INTERVAL; MOI_S3PU_CUBE_FACTS; DIMINDEX_3] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    MATCH_MP_TAC(INST_TYPE [`:2`,`:M`] MOI_CMB_PL_SPHERE_TRANSFER) THEN
    EXISTS_TAC `relative_frontier(interval[--vec 1:real^2,vec 1])` THEN
    MAP_EVERY EXISTS_TAC [`iota:real^2->real^3`; `\z:real^3. vector[z$2; z$3]:real^2`] THEN
    REWRITE_TAC[el 3 (CONJUNCTS MOI_S3PU_SQUARE_FACTS); DIMINDEX_2; DIMINDEX_3; ARITH] THEN
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) &&
      is_eq(snd(dest_forall(concl th))))) THEN
    SUBGOAL_THEN `!x:real^2. vector[(iota:real^2->real^3) x$2; iota x$3]:real^2 = x`
    ASSUME_TAC THENL
     [EXPAND_TAC "iota" THEN REWRITE_TAC[VECTOR_3; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID];
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN
        REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
                    VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT]];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\x:real^2. (iota:real^2->real^3) x + vec 0` THEN
      CONJ_TAC THENL [REWRITE_TAC[VECTOR_ADD_RID]; ALL_TAC] THEN
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      SIMP_TAC[MOI_CEL_PL_POLYHEDRON_RELATIVE_FRONTIER; POLYTOPE_INTERVAL]];
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM; MOI_S3PU_CUBE_RF; MOI_S3PU_SQUARE_FACTS] THEN
    REWRITE_TAC[IN_DIFF; IN_INTERVAL; DIMINDEX_3; FORALL_3; DIMINDEX_2; FORALL_2; VECTOR_2;
                VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) &&
      is_eq(snd(dest_forall(concl th))))) THEN
    SUBGOAL_THEN `!x y. (iota:real^2->real^3) x = iota y ==> x = y` ASSUME_TAC THENL
     [EXPAND_TAC "iota" THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `relative_frontier(IMAGE (iota:real^2->real^3) (interval[--vec 1,vec 1])) =
      IMAGE iota (relative_frontier(interval[--vec 1,vec 1])) /\
      relative_interior(IMAGE (iota:real^2->real^3) (interval[--vec 1,vec 1])) =
      IMAGE iota (relative_interior(interval[--vec 1,vec 1]))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE;
        MATCH_MP_TAC RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) =
      `relative_frontier(IMAGE (iota:real^2->real^3) (interval[--vec 1,vec 1]))`)) THEN
    MATCH_MP_TAC MOI_CON_CONE_RF THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_LINEAR_IMAGE THEN ASM_REWRITE_TAC[CONVEX_INTERVAL];
      MATCH_MP_TAC COMPACT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
      REWRITE_TAC[IN_IMAGE; MOI_S3PU_SQUARE_FACTS] THEN EXISTS_TAC `vec 0:real^2` THEN
      REWRITE_TAC[MOI_S3PU_SQUARE_FACTS] THEN ASM_MESON_TAC[LINEAR_0];
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      REWRITE_TAC[MOI_S3PU_SQUARE_FACTS; GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN
      EXISTS_TAC `vec 1:real^2` THEN
      REWRITE_TAC[IN_INTERVAL; VECTOR_NEG_COMPONENT; VEC_COMPONENT; DIMINDEX_2; FORALL_2] THEN
      REAL_ARITH_TAC]]);;

(* PL cells are compact. *)

let MOI_S3PU_CELL_CLOSED = prove
 (`!n (d:real^N->bool) j. pl_cell_with_boundary n d j ==> compact d /\ closed d`,
  REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact(d:real^N->bool)` (fun th -> SIMP_TAC[th; COMPACT_IMP_CLOSED]) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o
    check (fun th -> is_eq(concl th) && rhs(concl th) = `d:real^N->bool`)) THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]);;

(* A PL homeomorphism of a PL 2-sphere onto another taking a given PL      *)
(* circle onto a given PL circle (2D Schoenflies on both sides).            *)

let MOI_S3PU_SPHERE_MAP = prove
 (`!(s:real^N->bool) j (s':real^M->bool) j'.
     pl_sphere 2 s /\ pl_sphere 1 j /\ j SUBSET s /\
     pl_sphere 2 s' /\ pl_sphere 1 j' /\ j' SUBSET s'
     ==> ?f g. pl_homeomorphism (s,s') (f,g) /\ IMAGE f j = j'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `j:real^N->bool`] MOI_S4O_SPHERE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^N->bool` (X_CHOOSE_THEN `d2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s':real^M->bool`; `j':real^M->bool`] MOI_S4O_SPHERE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1':real^M->bool` (X_CHOOSE_THEN `d2':real^M->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`j:real^N->bool`; `j':real^M->bool`] MOI_S8PL_SPHERE1_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^M` (X_CHOOSE_THEN `h':real^M->real^N`
    ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`2`; `d1:real^N->bool`; `j:real^N->bool`; `d1':real^M->bool`;
                 `j':real^M->bool`; `h:real^N->real^M`; `h':real^M->real^N`]
    MOI_CEL_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^N->real^M` (X_CHOOSE_THEN `g1:real^M->real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`2`; `d2:real^N->bool`; `j:real^N->bool`; `d2':real^M->bool`;
                 `j':real^M->bool`; `h:real^N->real^M`; `h':real^M->real^N`]
    MOI_CEL_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^N->real^M` (X_CHOOSE_THEN `g2:real^M->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (h:real^N->real^M) j = j'` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  MP_TAC(ISPECL [`d1:real^N->bool`; `d2:real^N->bool`; `d1':real^M->bool`;
                 `d2':real^M->bool`; `f1:real^N->real^M`; `g1:real^M->real^N`;
                 `f2:real^N->real^M`; `g2:real^M->real^N`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_S3PU_CELL_CLOSED]; ASM_MESON_TAC[MOI_S3PU_CELL_CLOSED];
      ASM_MESON_TAC[MOI_S3PU_CELL_CLOSED]; ASM_MESON_TAC[MOI_S3PU_CELL_CLOSED];
      ASM_SIMP_TAC[];
      SUBGOAL_THEN `IMAGE (f1:real^N->real^M) j = IMAGE h j` (fun th -> ASM_REWRITE_TAC[th]) THEN
      MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^N. if x IN d1 then (f1:real^N->real^M) x else f2 x`;
    `\y:real^M. if y IN d1' then (g1:real^M->real^N) y else g2 y`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(j:real^N->bool) SUBSET d1` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `j':real^M->bool`)) THEN
  MATCH_MP_TAC IMAGE_EQ THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN d1` (fun th -> REWRITE_TAC[th]) THENL
   [ASM SET_TAC[]; ASM_SIMP_TAC[]]);;
(* The open star of y in the subcomplex of the simplices inside q is the   *)
(* part in q of the open star of y in the whole complex (carriers).         *)

let MOI_S3PU_OPEN_STAR_SUB = prove
 (`!(K:(real^N->bool)->bool) q y.
     simplicial_complex K /\ UNIONS {t | t IN K /\ t SUBSET q} = q
     ==> moi_sta_open_star {t | t IN K /\ t SUBSET q} y = q INTER moi_sta_open_star K y`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_INTER] THEN X_GEN_TAC `z:real^N` THEN
  REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "st")) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN K /\ s SUBSET q /\ z IN s` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(z:real^N) IN UNIONS {t | t IN K /\ t SUBSET q}` MP_TAC THENL
     [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `z:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^N->bool) IN K` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->bool) SUBSET t` MP_TAC THENL
   [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `z:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(y:real^N) IN f ==> f SUBSET t ==> y IN t`) THEN
  USE_THEN "st" MATCH_MP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS];
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]]);;

let MOI_S3PU_LINK_MONO = prove
 (`!(K:(real^N->bool)->bool) K' y.
     K' SUBSET K ==> simplicial_link K' y SUBSET simplicial_link K y`,
  REWRITE_TAC[simplicial_link; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

(* The cone map takes the subcone over j SUBSET a onto the cone over f(j). *)

let MOI_S3PU_CONEMAP_SUBCONE = prove
 (`!(a:real^M->bool) u (v:real^N) f j.
     ~(u IN a) /\ (!x y. x IN a /\ y IN a /\ y IN segment[u,x] ==> y = x) /\ j SUBSET a
     ==> IMAGE (moi_con_conemap a u v f) (UNIONS {segment[u,x] | x IN j}) =
         UNIONS {segment[v,y] | y IN IMAGE f j}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `p:real^N` THEN
  REWRITE_TAC[MOI_CON_IN_CONE] THEN REWRITE_TAC[IN_IMAGE] THEN
  REWRITE_TAC[MOI_CON_IN_CONE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `q:real^M` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `x:real^M` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`(f:real^M->real^N) x`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_CON_CONEMAP_EQ THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `u + r % (x - u):real^M` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC MOI_CON_CONEMAP_EQ THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`x:real^M`; `r:real`] THEN ASM_REWRITE_TAC[]]]);;

(* The open star of a vertex y of a triangulation of a convex set S with y *)
(* in the interior of S is open and lies in the interior.                   *)

let MOI_S3PU_OPEN_STAR_OPEN3 = prove
 (`!(K:(real^N->bool)->bool) S y.
     simplicial_complex K /\ UNIONS K = S /\ convex S /\ {y} IN K /\ y IN interior S
     ==> open (moi_sta_open_star K y) /\ moi_sta_open_star K y SUBSET interior S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_sta_open_star K (y:real^N) SUBSET interior S` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3PU_OPEN_STAR_INTERIOR THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `y:real^N`] MOI_STA_OPEN_STAR_OPEN) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`euclidean:(real^N)topology`; `moi_sta_open_star K (y:real^N)`;
                 `interior S:real^N->bool`; `S:real^N->bool`] OPEN_IN_SUBSET_TRANS) THEN
  ASM_REWRITE_TAC[INTERIOR_SUBSET] THEN
  SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_INTERIOR]);;
(* The cone chart at a vertex y of a triangulation K of a convex set S with *)
(* y in the interior of S: when the link of y is a PL 2-sphere and the link  *)
(* of y in the subcomplex of the simplices inside q is a PL circle, the     *)
(* open star of y is PL homeomorphic to the open unit cube with y going to  *)
(* vec 0 and its points of q going onto the plane z1 = 0.                    *)

let MOI_S3PU_STAR_CHART3 = prove
 (`!(K:(real^3->bool)->bool) S q y.
     simplicial_complex K /\ UNIONS K = S /\ convex S /\ y IN interior S /\ {y} IN K /\
     UNIONS {t | t IN K /\ t SUBSET q} = q /\ {y} IN {t | t IN K /\ t SUBSET q} /\
     pl_sphere 2 (UNIONS (simplicial_link K y)) /\
     pl_sphere 1 (UNIONS (simplicial_link {t | t IN K /\ t SUBSET q} y))
     ==> ?(f:real^3->real^3) g.
           open (moi_sta_open_star K y) /\ moi_sta_open_star K y SUBSET interior S /\
           y IN moi_sta_open_star K y /\
           pl_homeomorphism (moi_sta_open_star K y,interval(--vec 1,vec 1)) (f,g) /\
           f y = vec 0 /\
           IMAGE f (q INTER moi_sta_open_star K y) =
             interval(--vec 1,vec 1) INTER {z:real^3 | z$1 = &0}`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `Kq = {t:real^3->bool | t IN K /\ t SUBSET q}` THEN
  ABBREV_TAC `Sg = UNIONS (simplicial_link K (y:real^3))` THEN
  ABBREV_TAC `J = UNIONS (simplicial_link Kq (y:real^3))` THEN
  ABBREV_TAC `u = moi_sta_open_star K (y:real^3)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (Kq:(real^3->bool)->bool) /\ Kq SUBSET K`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Kq" THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3PU_SC_RESTRICT THEN ASM_REWRITE_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^3->bool)->bool) /\
                lf_simplicial_complex (Kq:(real^3->bool)->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `S:real^3->bool`; `y:real^3`]
    MOI_S3PU_OPEN_STAR_OPEN3) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN u` ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN MATCH_MP_TAC MOI_S3PU_OPEN_STAR_RELINT THEN
    EXISTS_TAC `{y:real^3}` THEN ASM_REWRITE_TAC[IN_SING; RELATIVE_INTERIOR_SING];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `y:real^3`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(Sg:real^3->bool = {}) /\ ~(J:real^3->bool = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_NONEMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^3->bool) SUBSET Sg` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["J"; "Sg"] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    MATCH_MP_TAC MOI_S3PU_LINK_MONO THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC MOI_S3PU_CUBE_MODEL THEN
  ABBREV_TAC `J' = {z:real^3 | z IN relative_frontier(interval[--vec 1,vec 1]) /\ z$1 = &0}` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`Sg:real^3->bool`; `J:real^3->bool`;
                 `relative_frontier(interval[--vec 1:real^3,vec 1])`; `J':real^3->bool`]
    MOI_S3PU_SPHERE_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `F0:real^3->real^3` (X_CHOOSE_THEN `F1:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_polyhedron (Sg:real^3->bool) /\
                ~((vec 0:real^3) IN relative_frontier(interval[--vec 1,vec 1])) /\
                (!x w. x IN relative_frontier(interval[--vec 1:real^3,vec 1]) /\
                       w IN relative_frontier(interval[--vec 1,vec 1]) /\
                       w IN segment[vec 0,x] ==> w = x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON];
      REWRITE_TAC[MOI_S3PU_CUBE_FACTS; IN_DIFF];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_RF_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`interval[--vec 1:real^3,vec 1]`; `vec 0:real^3`] THEN
      ASM_REWRITE_TAC[CONVEX_INTERVAL] THEN REWRITE_TAC[MOI_S3PU_CUBE_FACTS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Sg:real^3->bool`; `relative_frontier(interval[--vec 1:real^3,vec 1])`;
                 `y:real^3`; `vec 0:real^3`; `F0:real^3->real^3`; `F1:real^3->real^3`]
    MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `UNIONS {segment[vec 0:real^3,x] | x IN relative_frontier(interval[--vec 1,vec 1])} =
                interval[--vec 1,vec 1]` SUBST1_TAC THENL
   [MATCH_MP_TAC MOI_CON_CONE_RF THEN REWRITE_TAC[MOI_S3PU_CUBE_FACTS]; ALL_TAC] THEN
  ABBREV_TAC `cm = moi_con_conemap (Sg:real^3->bool) y (vec 0:real^3) F0` THEN
  ABBREV_TAC `cm' = moi_con_conemap (relative_frontier(interval[--vec 1:real^3,vec 1]))
                      (vec 0) (y:real^3) F1` THEN
  ABBREV_TAC `St = UNIONS {segment[y:real^3,x] | x | x IN Sg}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "cmF")) THEN
  ABBREV_TAC `Stq = UNIONS {segment[y:real^3,x] | x | x IN J}` THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `y:real^3`] MOI_STA_OPEN_STAR_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  MP_TAC(ISPECL [`Kq:(real^3->bool)->bool`; `y:real^3`] MOI_STA_OPEN_STAR_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `q:real^3->bool`; `y:real^3`]
    MOI_S3PU_OPEN_STAR_SUB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Sg:real^3->bool) SUBSET St /\ (J:real^3->bool) SUBSET Stq /\
                (Stq:real^3->bool) SUBSET St` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["St"; "Stq"] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[ENDS_IN_SEGMENT];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[ENDS_IN_SEGMENT];
      MATCH_MP_TAC SUBSET_UNIONS THEN
      UNDISCH_TAC `(J:real^3->bool) SUBSET Sg` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x:real^3. x IN St ==> cm' (cm x) = x) /\
                IMAGE (cm:real^3->real^3) St = interval[--vec 1,vec 1]`
  (CONJUNCTS_THEN2 (LABEL_TAC "inj") ASSUME_TAC) THENL
   [UNDISCH_TAC `pl_homeomorphism (St,interval[--vec 1:real^3,vec 1])
                   (cm:real^3->real^3,cm')` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(cm:real^3->real^3) y = vec 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `?x0:real^3. x0 IN Sg` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
    MP_TAC(ISPECL [`Sg:real^3->bool`; `y:real^3`; `vec 0:real^3`;
                   `F0:real^3->real^3`; `x0:real^3`; `&0`] MOI_CON_CONEMAP_EQ) THEN
    ASM_REWRITE_TAC[REAL_LE_REFL; REAL_POS; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (cm:real^3->real^3) Sg = relative_frontier(interval[--vec 1,vec 1])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (F0:real^3->real^3) Sg` THEN CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN USE_THEN "cmF" ACCEPT_TAC;
      UNDISCH_TAC `pl_homeomorphism (Sg,relative_frontier(interval[--vec 1:real^3,vec 1]))
                     (F0:real^3->real^3,F1)` THEN
      SIMP_TAC[pl_homeomorphism; homeomorphism]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (cm:real^3->real^3) u = interval(--vec 1,vec 1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`cm:real^3->real^3`; `cm':real^3->real^3`; `St:real^3->bool`;
                   `interval[--vec 1:real^3,vec 1]`; `Sg:real^3->bool`] MOI_STA_IMAGE_DIFF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[MOI_S3PU_CUBE_FACTS] THEN
    MP_TAC(ISPECL [`--vec 1:real^3`; `vec 1:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (u,interval(--vec 1,vec 1)) (cm:real^3->real^3,cm')`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3SS_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`St:real^3->bool`; `interval[--vec 1:real^3,vec 1]`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `St DIFF Sg = (u:real^3->bool)` THEN SET_TAC[];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_OPEN THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`cm:real^3->real^3`; `cm':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `(q:real^3->bool) INTER u`)) THEN
  MP_TAC(ISPECL [`cm:real^3->real^3`; `cm':real^3->real^3`; `Stq:real^3->bool`;
                 `IMAGE (cm:real^3->real^3) Stq`; `J:real^3->bool`] MOI_STA_IMAGE_DIFF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    USE_THEN "inj" MATCH_MP_TAC THEN
    UNDISCH_TAC `(x:real^3) IN Stq` THEN UNDISCH_TAC `(Stq:real^3->bool) SUBSET St` THEN
    SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `IMAGE (cm:real^3->real^3) Stq =
                {z:real^3 | z IN interval[--vec 1,vec 1] /\ z$1 = &0} /\
                IMAGE (cm:real^3->real^3) J = J'` (CONJUNCTS_THEN SUBST1_TAC) THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`Sg:real^3->bool`; `y:real^3`; `vec 0:real^3`; `F0:real^3->real^3`;
                     `J:real^3->bool`] MOI_S3PU_CONEMAP_SUBCONE) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (F0:real^3->real^3) J` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_EQ THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
        USE_THEN "cmF" MATCH_MP_TAC THEN
        UNDISCH_TAC `(x:real^3) IN J` THEN UNDISCH_TAC `(J:real^3->bool) SUBSET Sg` THEN
        SET_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBST1_TAC(SYM(ASSUME
    `{z:real^3 | z IN relative_frontier(interval[--vec 1,vec 1]) /\ z$1 = &0} = J'`)) THEN
  MP_TAC(ISPECL [`--vec 1:real^3`; `vec 1:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
  REWRITE_TAC[EXTENSION; SUBSET; IN_DIFF; IN_INTER; IN_ELIM_THM; MOI_S3PU_CUBE_RF] THEN
  MESON_TAC[]);;
(* Flat charts: a closed set p, locally polyhedral and locally R^2 near y   *)
(* (inside an open w0), has a PL chart at y onto an open set taking p to    *)
(* the plane z1 = 0 (the form of pl_crossing_at for p alone).               *)

let MOI_S3PU_FLAT_CHART = prove
 (`!(p:real^3->bool) y w0.
     closed p /\ open w0 /\ y IN p /\ y IN w0 /\ locally_polyhedral (p INTER w0) /\
     (!x. x IN p INTER w0 ==> moi_s28_locally_r2 p x)
     ==> ?u (f:real^3->real^3) g.
           open u /\ y IN u /\ u SUBSET w0 /\ pl_homeomorphism (u,IMAGE f u) (f,g) /\
           open (IMAGE f u) /\ f y = vec 0 /\
           IMAGE f (p INTER u) = IMAGE f u INTER {z:real^3 | z$1 = &0}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "r2" o check (fun th -> is_forall(concl th))) THEN
  MP_TAC(ISPECL [`y:real^3`; `w0:real^3->bool`] MOI_S3PU_CUBE_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` MP_TAC) THEN
  ABBREV_TAC `S = interval[y - e % vec 1:real^3,y + e % vec 1]` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `polytope (S:real^3->bool) /\ convex S /\ compact S /\ (y:real^3) IN S`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[POLYTOPE_INTERVAL; CONVEX_INTERVAL; COMPACT_INTERVAL] THEN
    UNDISCH_TAC `(y:real^3) IN interior S` THEN EXPAND_TAC "S" THEN
    MP_TAC(ISPEC `interval[y - e % vec 1:real^3,y + e % vec 1]` INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q = (p:real^3->bool) INTER S` THEN
  SUBGOAL_THEN `pl_polyhedron (q:real^3->bool) /\ q SUBSET S /\ (y:real^3) IN q`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PTR_COMPACT_LOCALLY_POLYHEDRAL THEN CONJ_TAC THENL
       [EXPAND_TAC "q" THEN MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `q = (p INTER w0) INTER (S:real^3->bool)` SUBST1_TAC THENL
         [EXPAND_TAC "q" THEN UNDISCH_TAC `(S:real^3->bool) SUBSET w0` THEN SET_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC MOI_S3X2_LP_INTER THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
        MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN ASM_REWRITE_TAC[]];
      EXPAND_TAC "q" THEN SET_TAC[];
      EXPAND_TAC "q" THEN ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `q:real^3->bool`; `y:real^3`] MOI_S3PU_TRIANG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (simplicial_link K (y:real^3)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CMB_LOCAL_LINK_SPHERE THEN
    MAP_EVERY EXISTS_TAC [`S:real^3->bool`; `\x:real^3. x`] THEN
    REWRITE_TAC[DIMINDEX_3; ARITH] THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
      EXISTS_TAC `&1` THEN REWRITE_TAC[REAL_LT_01] THEN MESON_TAC[];
      REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN ASM_REWRITE_TAC[];
      MESON_TAC[];
      X_GEN_TAC `r:real` THEN DISCH_TAC THEN
      MP_TAC(ASSUME `(y:real^3) IN interior S`) THEN REWRITE_TAC[IN_INTERIOR] THEN
      DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min r r0` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN EXISTS_TAC `z:real^3` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ball(y:real^3,r0) SUBSET S` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (UNIONS (simplicial_link {t | t IN K /\ t SUBSET q} (y:real^3)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3PU_VLINK THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN interior S` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`{t | t IN K /\ t SUBSET q}:(real^3->bool)->bool`; `y:real^3`;
                     `S:real^3->bool`] MOI_S3PU_OPEN_STAR_INTERIOR) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^3` o GEN_REWRITE_RULE I [SUBSET]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN q` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN moi_sta_open_star {t | t IN K /\ t SUBSET q} y` THEN
      REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN p` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN q` THEN
      SUBST1_TAC(SYM(ASSUME `p INTER S:real^3->bool = q`)) THEN SIMP_TAC[IN_INTER];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`p:real^3->bool`; `p INTER interior S:real^3->bool`] THEN
    REPEAT CONJ_TAC THENL
     [USE_THEN "r2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
      UNDISCH_TAC `(z:real^3) IN interior S` THEN UNDISCH_TAC `(S:real^3->bool) SUBSET w0` THEN
      MP_TAC(ISPEC `S:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_INTERIOR];
      ASM_REWRITE_TAC[IN_INTER];
      SUBST1_TAC(SYM(ASSUME `p INTER S:real^3->bool = q`)) THEN
      MP_TAC(ISPEC `S:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      SUBST1_TAC(SYM(ASSUME `p INTER S:real^3->bool = q`)) THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `S:real^3->bool`; `q:real^3->bool`; `y:real^3`]
    MOI_S3PU_STAR_CHART3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`moi_sta_open_star K (y:real^3)`; `f:real^3->real^3`;
                        `g:real^3->real^3`] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (moi_sta_open_star K y) = interval(--vec 1,vec 1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (moi_sta_open_star K y,interval(--vec 1,vec 1))
                   (f:real^3->real^3,g)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL] THEN
  SUBGOAL_THEN `p INTER moi_sta_open_star K (y:real^3) = q INTER moi_sta_open_star K y`
  SUBST1_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `p INTER S:real^3->bool = q`)) THEN
    UNDISCH_TAC `moi_sta_open_star K (y:real^3) SUBSET interior S` THEN
    MP_TAC(ISPEC `S:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_sta_open_star K (y:real^3) SUBSET interior S` THEN
  UNDISCH_TAC `(S:real^3->bool) SUBSET w0` THEN
  MP_TAC(ISPEC `S:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[]);;
(* Normalizing charts: scale a chart at x (f x = vec 0, open image) so that *)
(* its image contains the box interval(--vec 2,vec 2); restrict a chart to  *)
(* an open subset, keeping the flattening of sets.                          *)

let MOI_S3PU_CHART_SCALE = prove
 (`!(U:real^3->bool) (f:real^3->real^3) g x.
     pl_homeomorphism (U,IMAGE f U) (f,g) /\ open (IMAGE f U) /\ x IN U /\ f x = vec 0
     ==> ?r (f':real^3->real^3) g'.
           &0 < r /\ (!y. f' y = r % f y) /\
           pl_homeomorphism (U,IMAGE f' U) (f',g') /\ open (IMAGE f' U) /\
           interval(--vec 2,vec 2) SUBSET IMAGE f' U`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?d. &0 < d /\ ball(vec 0:real^3,d) SUBSET IMAGE (f:real^3->real^3) U`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `r = &8 / d` THEN
  SUBGOAL_THEN `&0 < r /\ r * d = &8` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN
    ASM_SIMP_TAC[REAL_LT_DIV; REAL_OF_NUM_LT; ARITH; REAL_DIV_RMUL; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r:real`; `\y:real^3. r % (f:real^3->real^3) y`;
                        `\z:real^3. (g:real^3->real^3) (inv r % z)`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (\y:real^3. r % (f:real^3->real^3) y) U = IMAGE (\z. r % z) (IMAGE f U)`
  SUBST1_TAC THENL [REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(\y:real^3. r % (f:real^3->real^3) y) = (\z. r % z) o f /\
                  (\z:real^3. (g:real^3->real^3) (inv r % z)) = g o (\z. inv r % z)`
    (CONJUNCTS_THEN SUBST1_TAC) THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `IMAGE (f:real^3->real^3) U` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [REWRITE_TAC[homeomorphism; FORALL_IN_IMAGE; GSYM IMAGE_o; o_DEF; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID;
                   REAL_MUL_RID; REAL_MUL_LID; ETA_AX; LINEAR_CONTINUOUS_ON;
                   LINEAR_SCALING];
      MP_TAC(ISPECL [`IMAGE (f:real^3->real^3) U`; `\z:real^3. z`; `r:real`]
        PL_MAP_ON_CMUL) THEN
      REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN]];
    MATCH_MP_TAC OPEN_SCALING THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `IMAGE (\z:real^3. r % z) (ball(vec 0,d))` THEN
    CONJ_TAC THENL [ALL_TAC; MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]] THEN
    MP_TAC(ISPECL [`vec 0:real^3`; `d:real`]
      (MATCH_MP BALL_SCALING (ASSUME `&0 < r`))) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN X_GEN_TAC `z:real^3` THEN
    MP_TAC(ISPEC `z:real^3` NORM_LE_L1) THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; SUM_3; VECTOR_NEG_COMPONENT;
                VEC_COMPONENT] THEN
    REAL_ARITH_TAC]);;

let MOI_S3PU_CHART_RESTRICT = prove
 (`!(U:real^3->bool) (f:real^3->real^3) g O.
     open U /\ pl_homeomorphism (U,IMAGE f U) (f,g) /\ open (IMAGE f U) /\ open O
     ==> open (U INTER O) /\
         pl_homeomorphism (U INTER O,IMAGE f (U INTER O)) (f,g) /\
         open (IMAGE f (U INTER O)) /\
         (!P H. IMAGE f (P INTER U) = IMAGE f U INTER H
                ==> IMAGE f (P INTER (U INTER O)) = IMAGE f (U INTER O) INTER H)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `homeomorphism (U,IMAGE f U) (f:real^3->real^3,g)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN U ==> (g:real^3->real^3) (f y) = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
  ASM_SIMP_TAC[OPEN_INTER] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3SS_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `IMAGE (f:real^3->real^3) U`] THEN
    ASM_SIMP_TAC[INTER_SUBSET; LOCALLY_POLYHEDRAL_OPEN; OPEN_INTER];
    MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `IMAGE (f:real^3->real^3) U` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^3`; `U:real^3->bool`] THEN
    ASM_SIMP_TAC[OPEN_IN_OPEN_INTER];
    REPEAT GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `!y:real^3. y IN U ==> (g:real^3->real^3) (f y) = y` THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) (P INTER U) = IMAGE f U INTER H` THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* The statements of pieces 1-4 of the proof (the sides of a chart, LTD     *)
(* transport, the generic local push, the global push) and of the local     *)
(* push.                                                                    *)
(* ========================================================================= *)

(* These terms use only library notions and the definitions of              *)
(* pc_moi_stmt.ml (pl_homeomorphism) and pc_moi_s33_stmt.ml (moi_s33_ltd,   *)
(* moi_s33_ww).                                                             *)


(* Piece 1a.  Sides of a flattened set in a chart: if the chart takes P to  *)
(* the plane z1 = 0 on the box interval(--vec 2,vec 2), and x = g(vec 0) is *)
(* in the closures of two distinct components of N DIFF P (U SUBSET N),    *)
(* then the closure of the first one meets the unit cube of the chart in a *)
(* closed half-cube.                                                         *)

let T_S3PU_SIDE =
 `!(U:real^3->bool) (f:real^3->real^3) g (P:real^3->bool) (N:real^3->bool)
   (a1:real^3) (a2:real^3) (x:real^3).
    open U /\ homeomorphism (U,IMAGE f U) (f,g) /\
    interval(--vec 2,vec 2) SUBSET IMAGE f U /\ x IN U /\ f x = vec 0 /\ U SUBSET N /\
    (!y. y IN U /\ f y IN interval(--vec 2,vec 2) ==> (y IN P <=> (f y)$1 = &0)) /\
    ~(connected_component (N DIFF P) a1 = connected_component (N DIFF P) a2) /\
    x IN closure (connected_component (N DIFF P) a1) /\
    x IN closure (connected_component (N DIFF P) a2)
    ==> ?s. (s = &1 \/ s = -- &1) /\
            !y. y IN U /\ f y IN interval[--vec 1,vec 1]
                ==> (y IN closure (connected_component (N DIFF P) a1) <=>
                     &0 <= s * (f y)$1)`;;

(* Piece 1b.  A closed set X whose frontier is the plane z2 = 0 of the      *)
(* chart (or misses the chart box): on the unit cube, membership in X       *)
(* depends only on the second chart coordinate.                              *)

let T_S3PU_XSIDE =
 `!(U:real^3->bool) (f:real^3->real^3) g (X:real^3->bool).
    open U /\ homeomorphism (U,IMAGE f U) (f,g) /\
    interval(--vec 2,vec 2) SUBSET IMAGE f U /\ closed X /\
    ((!y. y IN U /\ f y IN interval(--vec 2,vec 2)
          ==> (y IN frontier X <=> (f y)$2 = &0)) \/
     (!y. y IN U /\ f y IN interval(--vec 2,vec 2) ==> ~(y IN frontier X)))
    ==> !y y'. y IN U /\ y' IN U /\ f y IN interval[--vec 1,vec 1] /\
               f y' IN interval[--vec 1,vec 1] /\ (f y)$2 = (f y')$2
               ==> (y IN X <=> y' IN X)`;;

(* Piece 2.  Transport of a disk of Sec 33 (moi_s33_ltd) by an ambient PL   *)
(* homeomorphism that is the identity off a subset u of W = moi_s33_ww and *)
(* preserves UNIONS x.                                                       *)

let T_S3PU_LTD_TRANSPORT =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (x:(real^3->bool)->bool) (d:real^3->bool) (Phi:real^3->real^3) Phi'
   (u:real^3->bool).
    moi_s33_ltd t l h x d /\ pl_homeomorphism ((:real^3),(:real^3)) (Phi,Phi') /\
    (!y. ~(y IN u) ==> Phi y = y) /\ (!y. Phi y IN UNIONS x <=> y IN UNIONS x) /\
    u SUBSET moi_s33_ww t l h
    ==> moi_s33_ltd t l h x (IMAGE Phi d)`;;


(* The statements of piece 3, of the local push and of piece 4 (they use    *)
(* MOI_S39_PUSH_BODY of pc_moi_s33_l9stmt.ml).                              *)


(* Piece 3.  A generic local push from a chart at x0 taking A to the plane  *)
(* z1 = 0 and frontier X to z2 = 0 (or missing it), where x0 lies in the    *)
(* closures of two distinct components of N DIFF A (U SUBSET N): scale the  *)
(* chart (MOI_S3PU_CHART_SCALE), sides by MOI_S3PU_SIDE and MOI_S3PU_XSIDE, *)
(* then MOI_S3PU_CHART_PUSH with C = the closure of the first component.     *)

let T_S3PU_G_PUSH =
 `!(U:real^3->bool) (f:real^3->real^3) g (x0:real^3) (A:real^3->bool)
   (X:real^3->bool) (G:real^3->bool) (N:real^3->bool) (a1:real^3) (a2:real^3).
    open U /\ pl_homeomorphism (U,IMAGE f U) (f,g) /\ open (IMAGE f U) /\
    x0 IN U /\ f x0 = vec 0 /\ U SUBSET G /\ U SUBSET N /\
    IMAGE f (A INTER U) = IMAGE f U INTER {z:real^3 | z$1 = &0} /\
    closed X /\
    (IMAGE f (frontier X INTER U) = IMAGE f U INTER {z:real^3 | z$2 = &0} \/
     frontier X INTER U = {}) /\
    ~(connected_component (N DIFF A) a1 = connected_component (N DIFF A) a2) /\
    x0 IN closure (connected_component (N DIFF A) a1) /\
    x0 IN closure (connected_component (N DIFF A) a2)
    ==> ?(Psi:real^3->real^3) Psi' W.
          pl_homeomorphism ((:real^3),(:real^3)) (Psi,Psi') /\ open W /\ x0 IN W /\
          (!y. ~(y IN G) ==> Psi y = y) /\ (!y. Psi y IN X <=> y IN X) /\
          (!y. y IN closure (connected_component (N DIFF A) a1)
               ==> Psi y IN closure (connected_component (N DIFF A) a1) /\
                   (Psi y IN A ==> y IN A /\ ~(y IN W) /\ Psi y = y))`;;

(* The local push at a point of z INTER PCS (proved in Part 6 from piece 3). *)

let T_S3PU_LOCAL_PUSH =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool)
   (x:(real^3->bool)->bool) (v:real^3) (u:real^3->bool) (y:real^3).
    moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ {v} IN l /\
    open u /\ u SUBSET moi_s33_ww t l h /\
    y IN u /\ y IN c v /\ y IN moi_s39_pcs l e
    ==> ?(Psi:real^3->real^3) Psi' W.
          pl_homeomorphism ((:real^3),(:real^3)) (Psi,Psi') /\ open W /\ y IN W /\
          (!p. ~(p IN u) ==> Psi p = p) /\
          (!p. Psi p IN UNIONS x <=> p IN UNIONS x) /\
          (!p. p IN c v
               ==> Psi p IN c v /\
                   (Psi p IN moi_s39_pcs l e
                    ==> p IN moi_s39_pcs l e /\ ~(p IN W) /\ Psi p = p))`;;

let T_S3PU_PCS_CLOSED =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool).
    moi_s33_hd t l h e c ==> closed (moi_s39_pcs l e)`;;

(* Piece 4.  S39_PUSH from the local pushes: kk = z INTER PCS is compact,   *)
(* MOI_S3PU_PUSH_COMPOSE (C = c v, A = PCS, X = UNIONS x, G = u) gives Phi, *)
(* MOI_S3PU_LTD_TRANSPORT gives the disk IMAGE Phi d, and its trace on PCS  *)
(* is (d DIFF u) INTER PCS.                                                  *)

let T_S3PU_FINAL =
  mk_imp(mk_conj(T_S3PU_LOCAL_PUSH,T_S3PU_PCS_CLOSED),MOI_S39_PUSH_BODY);;


(* ------------------------------------------------------------------------- *)
(* Piece 1: MOI_S3PU_SIDE and MOI_S3PU_XSIDE, the statements T_S3PU_SIDE    *)
(* and T_S3PU_XSIDE above; library only.                                    *)
(* Route: the open half boxes of the chart box, cut by a coordinate plane,  *)
(* are convex and open, so their images under the inverse chart are         *)
(* connected open sets.  1a: each of the two components whose closures      *)
(* contain x contains one image half (it meets the image of the box), the   *)
(* two halves differ, a point on the plane is a limit of points of the half *)
(* of the first component, and a point on the other side lies in an open    *)
(* set disjoint from the first component.  1b: a connected set missing the  *)
(* frontier of X lies in X or misses it.                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3PU_H1_CUBE = prove
 (`interval[--vec 1,vec 1] SUBSET interval(--vec 2,vec 2:real^3) /\
   vec 0 IN interval(--vec 2,vec 2:real^3)`,
  REWRITE_TAC[SUBSET; IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_NEG_COMPONENT;
              VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* The open half boxes. *)

let MOI_S3PU_H1_HALF = prove
 (`!s k. (s = &1 \/ s = -- &1) /\ 1 <= k /\ k <= 3
     ==> open (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$k}) /\
         convex (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$k}) /\
         ~(interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$k} = {})`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{z:real^3 | &0 < s * z$k} = {z | (s % basis k) dot z > &0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_LMUL; real_gt] THEN
    ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3];
    ALL_TAC] THEN
  SIMP_TAC[OPEN_INTER; OPEN_INTERVAL; OPEN_HALFSPACE_GT; CONVEX_INTER; CONVEX_INTERVAL;
           CONVEX_HALFSPACE_GT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM] THEN
  EXISTS_TAC `(s / &2) % basis k:real^3` THEN
  ASM_SIMP_TAC[DOT_LMUL; DOT_BASIS; DIMINDEX_3; IN_INTERVAL; VECTOR_MUL_COMPONENT;
               BASIS_COMPONENT; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th -> is_disj(concl th))) THEN
  REPEAT STRIP_TAC THEN TRY COND_CASES_TAC THEN REAL_ARITH_TAC);;

(* Images of open convex parts of the chart box under the inverse chart. *)

let MOI_S3PU_H1_CHART = prove
 (`!(U:real^3->bool) (f:real^3->real^3) g H.
     open U /\ homeomorphism (U,IMAGE f U) (f,g) /\ H SUBSET IMAGE f U /\
     open H /\ convex H
     ==> IMAGE g H = {y | y IN U /\ f y IN H} /\ open (IMAGE g H) /\
         connected (IMAGE g H) /\ (!z. z IN H ==> g z IN U /\ f (g z) = z)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!z. z IN H ==> (g:real^3->real^3) z IN U /\ f (g z) = z` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected (IMAGE (g:real^3->real^3) H)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[CONVEX_CONNECTED] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) H = {y | y IN U /\ f y IN H}` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[]);;

(* A point of the closed unit cube on the closed side s of the plane z1 = 0 *)
(* is a limit of points of the open half box on that side.                  *)

let MOI_S3PU_H1_APPROACH = prove
 (`!(g:real^3->real^3) s w.
     g continuous_on interval(--vec 2,vec 2) /\ (s = &1 \/ s = -- &1) /\
     w IN interval[--vec 1,vec 1] /\ &0 <= s * w$1
     ==> g w IN closure (IMAGE g (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$1}))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN interval(--vec 2,vec 2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3PU_H1_CUBE; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(g:real^3->real^3) continuous_on interval(--vec 2,vec 2)` THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(w + vector[s * min (d / &2) (&1 / &2); &0; &0]:real^3) IN
      interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$1} /\
    dist(w + vector[s * min (d / &2) (&1 / &2); &0; &0],w) < d`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN interval[--vec 1,vec 1]` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_3; FORALL_3;
                VECTOR_ADD_COMPONENT; VECTOR_3; VECTOR_NEG_COMPONENT; VEC_COMPONENT; dist;
                VECTOR_ARITH `(w + v) - w:real^3 = v`] THEN
    MP_TAC(ISPEC `vector[s * min (d / &2) (&1 / &2); &0; &0]:real^3` NORM_LE_L1) THEN
    REWRITE_TAC[DIMINDEX_3; SUM_3; VECTOR_3] THEN
    FIRST_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th -> is_disj(concl th))) THEN
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `(g:real^3->real^3)(w + vector[s * min (d / &2) (&1 / &2); &0; &0])` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN CONJ_TAC THENL
       [ASM SET_TAC[]; FIRST_ASSUM ACCEPT_TAC]]]);;

(* A connected set inside M meeting a component of M lies in it. *)

let MOI_S3PU_H1_COMPONENT = prove
 (`!(S:real^3->bool) M a.
     connected S /\ S SUBSET M /\ ~(S INTER connected_component M a = {})
     ==> S SUBSET connected_component M a`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC o
    REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CONNECTED_COMPONENT_EQ) THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]);;

(* A connected set missing the frontier of X lies in X or misses it. *)

let MOI_S3PU_H1_NOFRONT = prove
 (`!(S:real^3->bool) X.
     connected S /\ S INTER frontier X = {}
     ==> !y y'. y IN S /\ y' IN S ==> (y IN X <=> y' IN X)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `X:real^3->bool`] CONNECTED_INTER_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Piece 1a. *)

let MOI_S3PU_SIDE = prove
 (T_S3PU_SIDE,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(REWRITE_RULE[homeomorphism]
    (ASSUME `homeomorphism (U,IMAGE (f:real^3->real^3) U) (f,g)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^3->real^3) continuous_on interval(--vec 2,vec 2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. (s = &1 \/ s = -- &1)
        ==> IMAGE (g:real^3->real^3)
              (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$1}) =
              {y | y IN U /\ f y IN interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$1}} /\
            open (IMAGE g (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$1})) /\
            connected (IMAGE g (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$1})) /\
            ~(IMAGE g (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$1}) = {}) /\
            IMAGE g (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$1}) SUBSET
            N DIFF P`
  (LABEL_TAC "H") THENL
   [X_GEN_TAC `s:real` THEN DISCH_TAC THEN
    MP_TAC(SPECL [`s:real`; `1`] MOI_S3PU_H1_HALF) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                   `interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$1}`]
                  MOI_S3PU_H1_CHART) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER; IN_DIFF] THEN
    X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      FIRST_ASSUM(MP_TAC o C MATCH_MP (CONJ (ASSUME `(y:real^3) IN U`)
          (ASSUME `(f:real^3->real^3) y IN interval(--vec 2,vec 2)`))) THEN
      DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `&0 < s * ((f:real^3->real^3) y)$1` THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:real^3. x IN closure (connected_component (N DIFF P) a)
        ==> ?s. (s = &1 \/ s = -- &1) /\
                IMAGE (g:real^3->real^3)
                  (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$1})
                SUBSET connected_component (N DIFF P) a`
  (LABEL_TAC "side") THENL
   [X_GEN_TAC `a:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`U:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                   `interval(--vec 2,vec 2):real^3->bool`] MOI_S3PU_H1_CHART) THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL; CONVEX_INTERVAL] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `~(IMAGE (g:real^3->real^3) (interval(--vec 2,vec 2)) INTER
        connected_component (N DIFF P) a = {})`
    MP_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (interval(--vec 2,vec 2))`;
                     `connected_component (N DIFF P) (a:real^3)`]
                    OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3) IN s /\ x IN t ==> ~(s INTER t = {})`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; MOI_S3PU_H1_CUBE];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `(g:real^3->real^3) w IN U /\ (f:real^3->real^3) (g w) = w`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^3->real^3) ((g:real^3->real^3) w) IN interval(--vec 2,vec 2)`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((w:real^3)$1 = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^3) IN P` MP_TAC THENL
       [FIRST_ASSUM(MP_TAC o C MATCH_MP
          (CONJ (ASSUME `(g:real^3->real^3) w IN U`)
                (ASSUME `(f:real^3->real^3) ((g:real^3->real^3) w) IN
                         interval(--vec 2,vec 2)`))) THEN
        ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`N DIFF P:real^3->bool`; `a:real^3`] CONNECTED_COMPONENT_SUBSET) THEN
        UNDISCH_TAC `(z:real^3) IN connected_component (N DIFF P) a` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `?s. (s = &1 \/ s = -- &1) /\ &0 < s * (w:real^3)$1`
    (X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
     [ASM_CASES_TAC `&0 < (w:real^3)$1` THENL
       [EXISTS_TAC `&1` THEN ASM_REAL_ARITH_TAC;
        EXISTS_TAC `-- &1` THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "H" (MP_TAC o C MATCH_MP (ASSUME `s = &1 \/ s = -- &1`)) THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_S3PU_H1_COMPONENT THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `z:real^3` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `connected_component (N DIFF P) (a1:real^3) INTER
    connected_component (N DIFF P) a2 = {}`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[CONNECTED_COMPONENT_NONOVERLAP]; ALL_TAC] THEN
  USE_THEN "side" (MP_TAC o C MATCH_MP
    (ASSUME `x IN closure (connected_component (N DIFF P) (a1:real^3))`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` (CONJUNCTS_THEN2 (LABEL_TAC "s1") (LABEL_TAC "q1"))) THEN
  USE_THEN "side" (MP_TAC o C MATCH_MP
    (ASSUME `x IN closure (connected_component (N DIFF P) (a2:real^3))`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:real` (CONJUNCTS_THEN2 (LABEL_TAC "s2") (LABEL_TAC "q2"))) THEN
  SUBGOAL_THEN `s2 = --(s1:real)` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(s2 = (s1:real))` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      USE_THEN "H" (MP_TAC o C MATCH_MP (ASSUME `s1 = &1 \/ s1 = -- &1`)) THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      UNDISCH_TAC `connected_component (N DIFF P) (a1:real^3) INTER
                   connected_component (N DIFF P) a2 = {}` THEN
      USE_THEN "q1" MP_TAC THEN USE_THEN "q2" MP_TAC THEN SET_TAC[];
      USE_THEN "s1" MP_TAC THEN USE_THEN "s2" MP_TAC THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `s1:real` THEN USE_THEN "s1" (fun th -> REWRITE_TAC[th]) THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^3->real^3) y IN interval(--vec 2,vec 2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3PU_H1_CUBE; SUBSET]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `(y:real^3) IN IMAGE (g:real^3->real^3)
        (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s2 * z$1})`
    ASSUME_TAC THENL
     [USE_THEN "H" (MP_TAC o C MATCH_MP (ASSUME `s2 = &1 \/ s2 = -- &1`)) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`IMAGE (g:real^3->real^3) (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s2 * z$1})`;
      `connected_component (N DIFF P) (a1:real^3)`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    USE_THEN "H" (MP_TAC o C MATCH_MP (ASSUME `s2 = &1 \/ s2 = -- &1`)) THEN
    DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(CONJUNCT2 th)]) THEN
    MATCH_MP_TAC(TAUT `~p /\ q ==> ~(p <=> q)`) THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^3` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `connected_component (N DIFF P) (a1:real^3) INTER
                   connected_component (N DIFF P) a2 = {}` THEN
      USE_THEN "q2" MP_TAC THEN SET_TAC[]];
    DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t (y:real^3). y IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `closure (IMAGE (g:real^3->real^3)
                  (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s1 * z$1}))` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `y = (g:real^3->real^3) (f y)` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_S3PU_H1_APPROACH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_CLOSURE THEN USE_THEN "q1" ACCEPT_TAC]]);;

(* Piece 1b. *)

let MOI_S3PU_XSIDE = prove
 (T_S3PU_XSIDE,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fr"))))) THEN
  MP_TAC(REWRITE_RULE[homeomorphism]
    (ASSUME `homeomorphism (U,IMAGE (f:real^3->real^3) U) (f,g)`)) THEN
  STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `y':real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^3->real^3) y IN interval(--vec 2,vec 2) /\
                f y' IN interval(--vec 2,vec 2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_S3PU_H1_CUBE; SUBSET]; ALL_TAC] THEN
  USE_THEN "fr" (DISJ_CASES_THEN (LABEL_TAC "fr1")) THENL
   [ASM_CASES_TAC `((f:real^3->real^3) y)$2 = &0` THENL
     [SUBGOAL_THEN `(y:real^3) IN frontier X /\ (y':real^3) IN frontier X`
      STRIP_ASSUME_TAC THENL
       [USE_THEN "fr1" (fun th ->
          MP_TAC(MATCH_MP th (CONJ (ASSUME `(y:real^3) IN U`)
            (ASSUME `(f:real^3->real^3) y IN interval(--vec 2,vec 2)`))) THEN
          MP_TAC(MATCH_MP th (CONJ (ASSUME `(y':real^3) IN U`)
            (ASSUME `(f:real^3->real^3) y' IN interval(--vec 2,vec 2)`)))) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_MESON_TAC[FRONTIER_SUBSET_CLOSED; SUBSET];
      SUBGOAL_THEN `?s. (s = &1 \/ s = -- &1) /\ &0 < s * ((f:real^3->real^3) y)$2`
      (X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
       [ASM_CASES_TAC `&0 < ((f:real^3->real^3) y)$2` THENL
         [EXISTS_TAC `&1` THEN ASM_REAL_ARITH_TAC;
          EXISTS_TAC `-- &1` THEN ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(SPECL [`s:real`; `2`] MOI_S3PU_H1_HALF) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ARITH_TAC; STRIP_TAC] THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                     `interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$2}`]
                    MOI_S3PU_H1_CHART) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
      MP_TAC(ISPECL [`IMAGE (g:real^3->real^3)
                        (interval(--vec 2,vec 2) INTER {z:real^3 | &0 < s * z$2})`;
                     `X:real^3->bool`] MOI_S3PU_H1_NOFRONT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x:real^3. x IN s ==> ~(x IN t)`] THEN
        REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
        USE_THEN "fr1" (fun th ->
          MP_TAC(MATCH_MP th (CONJ (ASSUME `(v:real^3) IN U`)
            (ASSUME `(f:real^3->real^3) v IN interval(--vec 2,vec 2)`)))) THEN
        DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
        UNDISCH_TAC `&0 < s * ((f:real^3->real^3) v)$2` THEN
        ASM_REWRITE_TAC[REAL_MUL_RZERO; REAL_LT_REFL];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN
        UNDISCH_TAC `((f:real^3->real^3) y)$2 = (f y')$2` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]]];
    MP_TAC(ISPECL [`U:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                   `interval(--vec 2,vec 2):real^3->bool`] MOI_S3PU_H1_CHART) THEN
    ASM_REWRITE_TAC[OPEN_INTERVAL; CONVEX_INTERVAL] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (g:real^3->real^3) (interval(--vec 2,vec 2))`;
                   `X:real^3->bool`] MOI_S3PU_H1_NOFRONT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SET_RULE `s INTER t = {} <=> !x:real^3. x IN s ==> ~(x IN t)`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `v:real^3` THEN STRIP_TAC THEN
      USE_THEN "fr1" (fun th ->
        ACCEPT_TAC(MATCH_MP th (CONJ (ASSUME `(v:real^3) IN U`)
          (ASSUME `(f:real^3->real^3) v IN interval(--vec 2,vec 2)`))));
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]]]);;

(* ========================================================================= *)
(* Piece 2: MOI_S3PU_LTD_TRANSPORT, transport of a loop theorem disk of Sec *)
(* 33 by an ambient PL homeomorphism Phi that is the identity off u SUBSET  *)
(* W and preserves UNIONS x (the statement T_S3PU_LTD_TRANSPORT above).     *)
(* Witness k, Phi o f, g o Phi'; non-contractibility is pulled back by      *)
(* composing a contraction with Phi on the right and Phi' on the left.     *)
(* ========================================================================= *)

let MOI_S3PU_H2_FIXED_SET = prove
 (`!(Phi:real^3->real^3) Phi' (u:real^3->bool).
     homeomorphism ((:real^3),(:real^3)) (Phi,Phi') /\ (!y. ~(y IN u) ==> Phi y = y)
     ==> !y. y IN u ==> Phi y IN u`,
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN MESON_TAC[]);;

let MOI_S3PU_H2_FRONTIER = prove
 (`!(Phi:real^3->real^3) Phi' (X:real^3->bool).
     homeomorphism ((:real^3),(:real^3)) (Phi,Phi') /\ (!y. Phi y IN X <=> y IN X)
     ==> IMAGE Phi (frontier X) = frontier X /\ IMAGE Phi' (frontier X) = frontier X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (Phi:real^3->real^3) X = X` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism ((:real^3),(:real^3)) (Phi:real^3->real^3,Phi')` THEN
    REWRITE_TAC[homeomorphism; IN_UNIV; EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Phi:real^3->real^3) (frontier X) = frontier X` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Phi:real^3->real^3`; `Phi':real^3->real^3`; `(:real^3)`; `(:real^3)`;
                   `X:real^3->bool`] HOMEOMORPHISM_FRONTIER_OF) THEN
    ASM_REWRITE_TAC[SUBSET_UNIV; SUBTOPOLOGY_UNIV; EUCLIDEAN_FRONTIER_OF];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `homeomorphism ((:real^3),(:real^3)) (Phi:real^3->real^3,Phi')` THEN
  REWRITE_TAC[homeomorphism; IN_UNIV] THEN STRIP_TAC THEN ASM SET_TAC[]);;

let MOI_S3PU_LTD_TRANSPORT = prove
 (`!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (x:(real^3->bool)->bool) (d:real^3->bool) (Phi:real^3->real^3) Phi'
   (u:real^3->bool).
    moi_s33_ltd t l h x d /\ pl_homeomorphism ((:real^3),(:real^3)) (Phi,Phi') /\
    (!y. ~(y IN u) ==> Phi y = y) /\ (!y. Phi y IN UNIONS x <=> y IN UNIONS x) /\
    u SUBSET moi_s33_ww t l h
    ==> moi_s33_ltd t l h x (IMAGE Phi d)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_ltd] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC)))
    (CONJUNCTS_THEN2 (LABEL_TAC "PhiP") (CONJUNCTS_THEN2 (LABEL_TAC "fix")
      (CONJUNCTS_THEN2 (LABEL_TAC "inv") (LABEL_TAC "uW"))))) THEN
  USE_THEN "PhiP" (STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism] o check (fun th ->
    concl th = `pl_homeomorphism (k,d) (f:real^3->real^3,g)`)) THEN
  MP_TAC(ISPECL [`Phi:real^3->real^3`; `Phi':real^3->real^3`; `UNIONS x:real^3->bool`]
    MOI_S3PU_H2_FRONTIER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`Phi:real^3->real^3`; `Phi':real^3->real^3`; `u:real^3->bool`]
    MOI_S3PU_H2_FIXED_SET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "uu")] THEN
  SUBGOAL_THEN `(!y. (Phi':real^3->real^3) ((Phi:real^3->real^3) y) = y) /\
                (!y. Phi (Phi' y) = y) /\
                Phi continuous_on (:real^3) /\ Phi' continuous_on (:real^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism ((:real^3),(:real^3)) (Phi:real^3->real^3,Phi')` THEN
    SIMP_TAC[homeomorphism; IN_UNIV];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `(Phi:real^3->real^3) o (f:real^3->real^3)`;
                        `(g:real^3->real^3) o (Phi':real^3->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the PL homeomorphism *)
    MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `d:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`] THEN ASM_REWRITE_TAC[SUBSET_UNIV];
      MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV]];
    (* the disk stays in W *)
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^3) IN u` THENL
     [USE_THEN "uW" (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      USE_THEN "uu" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      USE_THEN "fix" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `~((y:real^3) IN u)`)]) THEN
      UNDISCH_TAC `(y:real^3) IN d` THEN
      UNDISCH_TAC `d SUBSET moi_s33_ww t l h` THEN SET_TAC[]];
    (* the trace on BX *)
    SUBGOAL_THEN `IMAGE (Phi:real^3->real^3) (d INTER frontier (UNIONS x)) =
                  IMAGE Phi d INTER IMAGE Phi (frontier (UNIONS x))` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_INTER_INJ THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_o] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    (* non-contractibility *)
    DISCH_THEN(X_CHOOSE_TAC `a:real^3`) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_exists(rand(concl th)))) THEN
    REWRITE_TAC[] THEN EXISTS_TAC `(Phi':real^3->real^3) a` THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
    MAP_EVERY EXISTS_TAC
     [`(Phi':real^3->real^3) o (\y:real^3. y) o (Phi:real^3->real^3)`;
      `(Phi':real^3->real^3) o (\y:real^3. (a:real^3)) o (Phi:real^3->real^3)`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_COMPOSE_CONTINUOUS_LEFT THEN
      EXISTS_TAC `frontier(UNIONS x):real^3->bool` THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC HOMOTOPIC_COMPOSE_CONTINUOUS_RIGHT THEN
        EXISTS_TAC `IMAGE ((Phi:real^3->real^3) o (f:real^3->real^3)) (relative_frontier k)` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
          ASM_REWRITE_TAC[SUBSET_UNIV];
          REWRITE_TAC[IMAGE_o; SUBSET_REFL]];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^3)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV];
        ASM_REWRITE_TAC[SUBSET_REFL]];
      ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM];
      REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Part 5: the pieces and the pseudo-cells of Sec 33 near a point.  The     *)
(* pseudo-cells are closed, so is their union PCS; a point of c v INTER PCS *)
(* lies on the pseudo-cell of an edge at v; the other pseudo-cells form a   *)
(* closed set missing it; the two pieces at the ends of an edge are the     *)
(* closures of two distinct components of N' DIFF PCS.                      *)
(* ========================================================================= *)

let MOI_S3PU_R2_SUPER = prove
 (`!(x:real^N->bool) x' y.
     moi_s28_locally_r2 x' y /\ open_in (subtopology euclidean x) x'
     ==> moi_s28_locally_r2 x y`,
  REWRITE_TAC[moi_s28_locally_r2] THEN MESON_TAC[OPEN_IN_TRANS]);;

let MOI_S3PU_PC_CLOSED = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c s.
     moi_s33_hd t l h e c /\ s IN l /\ aff_dim s = &1 ==> closed (e s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_s33_tube t l (h:real^3->real^3)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s33_hd]) THEN SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `s:real^3->bool`] MOI_S3X2_TUBE_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `a:real^3`; `b:real^3`] MOI_S3X2_HD_EDGE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let MOI_S3PU_HD_FINITE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c ==> FINITE l`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s33_hd]) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1(MATCH_MP MOI_S3FR_TUBE_BASIC (CONJUNCT1 th))]));;

let MOI_S3PU_PCS_CLOSED = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c ==> closed (moi_s39_pcs l e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3PU_HD_FINITE THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `h:real^3->real^3`;
                          `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s39_pcs] THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3PU_PC_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                          `h:real^3->real^3`; `c:real^3->real^3->bool`] THEN
    ASM_REWRITE_TAC[]]);;
(* A point of c v on the pseudo-cells lies on the pseudo-cell of an edge at *)
(* v (c v INTER c a = e(segment[v,a]) and distinct pseudo-cells are        *)
(* disjoint).                                                                *)

let MOI_S3PU_EDGE_AT = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c v y.
     moi_s33_hd t l h e c /\ {v} IN l /\ y IN c v /\ y IN moi_s39_pcs l e
     ==> ?w. ~(v = w) /\ segment[v,w] IN l /\ {w} IN l /\ y IN e(segment[v,w])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s33_hd]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "disj") (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "cvw")))))) THEN
  SUBGOAL_THEN `graph_in_complex t (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?s:real^3->bool. s IN l /\ aff_dim s = &1 /\ (y:real^3) IN e s`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN moi_s39_pcs l e` THEN
    REWRITE_TAC[moi_s39_pcs; IN_UNIONS; EXISTS_IN_GSPEC] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `s:real^3->bool`] MOI_S3X2_TUBE_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `{a:real^3} IN l /\ {b} IN l` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3D_EDGE_VERTEX THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `graph_in_complex t (l:(real^3->bool)->bool)` THEN
      SIMP_TAC[graph_in_complex];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->real^3->bool) a INTER c b = e(segment[a,b])` ASSUME_TAC THENL
   [USE_THEN "cvw" (MP_TAC o SPECL [`a:real^3`; `b:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `v:real^3 = a` THENL
   [EXISTS_TAC `b:real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `v:real^3 = b` THENL
   [EXISTS_TAC `a:real^3` THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN (c:real^3->real^3->bool) v INTER c a` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN e(segment[a:real^3,b])` THEN
    SUBST1_TAC(SYM(ASSUME `(c:real^3->real^3->bool) a INTER c b = e(segment[a,b])`)) THEN
    SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  USE_THEN "cvw" (MP_TAC o SPECL [`v:real^3`; `a:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN e(segment[v:real^3,a])` ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN (c:real^3->real^3->bool) v INTER c a` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "disj" (MP_TAC o SPECL [`segment[v:real^3,a]`; `segment[a:real^3,b]`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN REWRITE_TAC[SEGMENT_EQ] THEN
      UNDISCH_TAC `~(v:real^3 = a)` THEN UNDISCH_TAC `~(v:real^3 = b)` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN UNDISCH_TAC `(y:real^3) IN (c:real^3->real^3->bool) v INTER c a` THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY]]);;

(* The pseudo-cells other than the one of a given edge. *)

let MOI_S3PU_OTHERS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c v w.
     moi_s33_hd t l h e c /\ ~(v = w) /\ segment[v,w] IN l
     ==> closed (UNIONS {e s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])}) /\
         DISJOINT (e(segment[v,w]))
                  (UNIONS {e s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])}) /\
         moi_s39_pcs l e =
         e(segment[v,w]) UNION
         UNIONS {e s | s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3PU_HD_FINITE THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `h:real^3->real^3`;
                          `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s33_hd]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "disj") (K ALL_TAC)))) THEN
  SUBGOAL_THEN `aff_dim(segment[v:real^3,w]) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_SEGMENT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_S3PU_PC_CLOSED THEN
      MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                            `h:real^3->real^3`; `c:real^3->real^3->bool`] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[SET_RULE `!s t:real^3->bool. DISJOINT s t <=> !x. x IN s ==> ~(x IN t)`;
                IN_UNIONS; EXISTS_IN_GSPEC] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `DISJOINT (e(segment[v:real^3,w])) (e s:real^3->bool)` MP_TAC THENL
     [USE_THEN "disj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(s = segment[v:real^3,w])` THEN MESON_TAC[];
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[moi_s39_pcs] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    X_GEN_TAC `y:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `s:real^3->bool = segment[v,w]` THENL
       [DISJ1_TAC THEN UNDISCH_TAC `(y:real^3) IN e(s:real^3->bool)` THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC)) THENL
       [EXISTS_TAC `segment[v:real^3,w]` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[]]]]);;

(* The two pieces at the ends of an edge. *)

let MOI_S3PU_EDGE_SIDES = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c v w.
     moi_s33_hd t l h e c /\ {v} IN l /\ {w} IN l /\ ~(v = w) /\ segment[v,w] IN l
     ==> c v = closure (connected_component
                 (IMAGE h (derived_nbhd t l) DIFF moi_s39_pcs l e) (h v)) /\
         c w = closure (connected_component
                 (IMAGE h (derived_nbhd t l) DIFF moi_s39_pcs l e) (h w)) /\
         c v INTER c w = e(segment[v,w]) /\
         ~(connected_component (IMAGE h (derived_nbhd t l) DIFF moi_s39_pcs l e) (h v) =
           connected_component (IMAGE h (derived_nbhd t l) DIFF moi_s39_pcs l e) (h w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s33_hd]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (LABEL_TAC "cv")
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "cvw")))))) THEN
  SUBGOAL_THEN
   `(l:(real^3->bool)->bool) SUBSET t /\
    (!x y. x IN UNIONS t /\ y IN UNIONS t /\ (h:real^3->real^3) x = h y ==> x = y)`
  (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")) THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3FR_TUBE_BASIC) THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s39_pcs] THEN
  USE_THEN "cv" (MP_TAC o SPEC `v:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cvd") (LABEL_TAC "hv")) THEN
  USE_THEN "cv" (MP_TAC o SPEC `w:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cwd") (LABEL_TAC "hw")) THEN
  SUBGOAL_THEN `(c:real^3->real^3->bool) v INTER c w = e(segment[v,w])` (LABEL_TAC "vw")
  THENL
   [USE_THEN "cvw" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "cvd" ACCEPT_TAC; USE_THEN "cwd" ACCEPT_TAC; USE_THEN "vw" ACCEPT_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(c:real^3->real^3->bool) v = c w` ASSUME_TAC THENL
   [USE_THEN "cvd" SUBST1_TAC THEN USE_THEN "cwd" SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3) w = h v` ASSUME_TAC THENL
   [SUBGOAL_THEN `(h:real^3->real^3) w IN (c:real^3->real^3->bool) v INTER
                  IMAGE h {u | {u} IN l}` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `(c:real^3->real^3->bool) v = c w`)) THEN
      USE_THEN "hw" (fun th -> REWRITE_TAC[th; IN_SING]);
      USE_THEN "hv" (fun th -> REWRITE_TAC[th; IN_SING])];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN UNIONS t /\ (w:real^3) IN UNIONS t` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN CONJ_TAC THENL
     [EXISTS_TAC `{v:real^3}`; EXISTS_TAC `{w:real^3}`] THEN
    REWRITE_TAC[IN_SING] THEN
    UNDISCH_TAC `(l:(real^3->bool)->bool) SUBSET t` THEN
    UNDISCH_TAC `{v:real^3} IN l` THEN UNDISCH_TAC `{w:real^3} IN l` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(v:real^3 = w)` THEN REWRITE_TAC[] THEN
  USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Piece 3: MOI_S3PU_G_PUSH, the statement T_S3PU_G_PUSH: the generic local *)
(* push from a chart taking A to the plane z1 = 0 and frontier X to z2 = 0  *)
(* (or missing it).  Route: scale the chart (MOI_S3PU_CHART_SCALE), read A  *)
(* and frontier X off the first and second chart coordinates                *)
(* (MOI_S3PU_H3_FLAT), the sides by MOI_S3PU_SIDE and MOI_S3PU_XSIDE, then  *)
(* MOI_S3PU_CHART_PUSH with C the closure of the first component.           *)
(* ========================================================================= *)

(* A flattened set read off one coordinate of a scaled chart. *)

let MOI_S3PU_H3_FLAT = prove
 (`!(U:real^3->bool) (f:real^3->real^3) g (f':real^3->real^3) r (P:real^3->bool) k.
     homeomorphism (U,IMAGE f U) (f,g) /\ &0 < r /\ (!y. f' y = r % f y) /\
     IMAGE f (P INTER U) = IMAGE f U INTER {z:real^3 | z$k = &0}
     ==> !y. y IN U ==> (y IN P <=> (f' y)$k = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  ASM_REWRITE_TAC[VECTOR_MUL_COMPONENT; REAL_ENTIRE] THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN
  SUBGOAL_THEN `(f:real^3->real^3) y IN IMAGE f (P INTER U) <=>
                f y IN IMAGE f U INTER {z:real^3 | z$k = &0}`
  MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* The theorem MOI_S3PU_G_PUSH. *)

let MOI_S3PU_G_PUSH = prove
 (T_S3PU_G_PUSH,
  REPEAT GEN_TAC THEN DISCH_THEN(REPEAT_TCL CONJUNCTS_THEN ASSUME_TAC) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`; `x0:real^3`]
    MOI_S3PU_CHART_SCALE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `f':real^3->real^3`
    (X_CHOOSE_THEN `g':real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `homeomorphism (U,IMAGE f U) (f:real^3->real^3,g) /\
                homeomorphism (U,IMAGE f' U) (f':real^3->real^3,g')`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `(f':real^3->real^3) x0 = vec 0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_RZERO]; ALL_TAC] THEN
  SUBGOAL_THEN `interval[--vec 1,vec 1] SUBSET interval(--vec 2:real^3,vec 2)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERVAL; DIMINDEX_3; FORALL_3; VEC_COMPONENT;
                VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* A is the plane z1 = 0 of the scaled chart *)
  SUBGOAL_THEN `!y. y IN U ==> (y IN A <=> ((f':real^3->real^3) y)$1 = &0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3PU_H3_FLAT THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`; `r:real`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* frontier X is the plane z2 = 0, or misses the chart *)
  SUBGOAL_THEN
   `(!y. y IN U /\ (f':real^3->real^3) y IN interval(--vec 2,vec 2)
         ==> (y IN frontier X <=> (f' y)$2 = &0)) \/
    (!y. y IN U /\ (f':real^3->real^3) y IN interval(--vec 2,vec 2)
         ==> ~(y IN frontier X))`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
      can (find_term ((=) `frontier (X:real^3->bool)`)) (concl th))) THENL
     [DISJ1_TAC THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`U:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`;
                     `f':real^3->real^3`; `r:real`; `frontier X:real^3->bool`; `2:num`]
        MOI_S3PU_H3_FLAT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      DISJ2_TAC THEN UNDISCH_TAC `frontier X INTER U:real^3->bool = {}` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the scaling equation is no longer needed (it would unfold f' below) *)
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) &&
    is_eq(snd(dest_forall(concl th))) &&
    lhs(snd(dest_forall(concl th))) = `(f':real^3->real^3) y`)) THEN
  SUBGOAL_THEN
   `!y. y IN U /\ (f':real^3->real^3) y IN interval(--vec 2,vec 2)
        ==> (y IN A <=> (f' y)$1 = &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `A:real^3->bool`)) (concl th) &&
      not(is_conj(lhand(snd(dest_forall(concl th))))))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  (* the side of the first component *)
  MP_TAC(ISPECL [`U:real^3->bool`; `f':real^3->real^3`; `g':real^3->real^3`; `A:real^3->bool`;
                 `N:real^3->bool`; `a1:real^3`; `a2:real^3`; `x0:real^3`] MOI_S3PU_SIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  (* X depends only on the second chart coordinate *)
  MP_TAC(ISPECL [`U:real^3->bool`; `f':real^3->real^3`; `g':real^3->real^3`; `X:real^3->bool`]
    MOI_S3PU_XSIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* the hypotheses of the chart push on the unit cube *)
  SUBGOAL_THEN
   `interval[--vec 1,vec 1] SUBSET IMAGE (f':real^3->real^3) U /\
    (!y. y IN U /\ (f':real^3->real^3) y IN interval[--vec 1,vec 1]
         ==> (y IN A <=> (f' y)$1 = &0)) /\
    (!y y'. y IN U /\ y' IN U /\ (f':real^3->real^3) y IN interval[--vec 1,vec 1] /\
            f' y' IN interval[--vec 1,vec 1] /\
            (f' y)$2 = (f' y')$2 /\ (f' y)$3 = (f' y')$3
            ==> (y IN X <=> y' IN X))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `interval(--vec 2:real^3,vec 2)` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `A:real^3->bool`)) (concl th) &&
        not(is_conj(lhand(snd(dest_forall(concl th))))))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY X_GEN_TAC [`y:real^3`; `y':real^3`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `X:real^3->bool`)) (concl th) &&
        not(can (find_term ((=) `frontier (X:real^3->bool)`)) (concl th)))) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the push *)
  MP_TAC(ISPECL [`U:real^3->bool`; `f':real^3->real^3`; `g':real^3->real^3`; `x0:real^3`;
                 `closure (connected_component (N DIFF A) (a1:real^3))`; `A:real^3->bool`;
                 `X:real^3->bool`; `G:real^3->bool`; `s:real`] MOI_S3PU_CHART_PUSH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN ACCEPT_TAC]);;

(* ========================================================================= *)
(* Part 6: the local push at a point y of z INTER PCS.  y lies on the       *)
(* pseudo-cell E of an edge at v (MOI_S3PU_EDGE_AT); off the other          *)
(* pseudo-cells PCS is E.  At a trace point (y on frontier X) the crossing  *)
(* chart of moi_s33_x2 flattens E and frontier X; elsewhere a flat chart    *)
(* of E (MOI_S3PU_FLAT_CHART) inside an open set missing frontier X.  The   *)
(* chart is restricted into u and off the other pseudo-cells, and          *)
(* MOI_S3PU_G_PUSH (piece 3) does the rest with the two sides c v, c w.     *)
(* ========================================================================= *)

let MOI_S3PU_PCS_LOCAL = prove
 (`!(pcs:real^3->bool) E OT R m W u U.
     E UNION OT = pcs /\ u SUBSET W /\ E INTER W = (E DIFF R) DELETE m /\
     U SUBSET u INTER ((:real^3) DIFF OT)
     ==> pcs INTER U = (E DIFF R) INTER U /\ pcs INTER U = E INTER U`,
  SET_TAC[]);;

let MOI_S3PU_LOCAL_PUSH = prove
 (T_S3PU_LOCAL_PUSH,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s33_tube t l (h:real^3->real^3)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s33_hd]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s33_x2 t l h e (x:(real^3->bool)->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_s33_inv]) THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (moi_s33_ww t l (h:real^3->real^3)) /\
                moi_s33_ww t l h SUBSET IMAGE h (derived_nbhd t l)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_s33_ww] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_INTERIOR] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3FR_IMAGE_FACTS) THEN SIMP_TAC[];
      MP_TAC(ISPEC `IMAGE (h:real^3->real^3) (derived_nbhd t l)` INTERIOR_SUBSET) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS x:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_S3D_X_COMPACT THEN
    UNDISCH_TAC `moi_s33_x2 t l h e (x:(real^3->bool)->bool)` THEN
    SIMP_TAC[moi_s33_x2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `v:real^3`; `y:real^3`] MOI_S3PU_EDGE_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `v:real^3`; `w:real^3`] MOI_S3X2_HD_EDGE) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM moi_s33_ww] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `v:real^3`; `w:real^3`] MOI_S3PU_OTHERS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  ABBREV_TAC `OT = UNIONS {(e:(real^3->bool)->real^3->bool) s |
                           s IN l /\ aff_dim s = &1 /\ ~(s = segment[v,w])}` THEN
  ABBREV_TAC `O = (u:real^3->bool) INTER ((:real^3) DIFF OT)` THEN
  SUBGOAL_THEN `open (O:real^3->bool) /\ (y:real^3) IN O` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed];
      REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (e(segment[v:real^3,w])) (OT:real^3->bool)` THEN
      UNDISCH_TAC `(y:real^3) IN e(segment[v:real^3,w])` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?U (f:real^3->real^3) g.
      open U /\ pl_homeomorphism (U,IMAGE f U) (f,g) /\ open (IMAGE f U) /\
      y IN U /\ f y = vec 0 /\ U SUBSET O /\
      IMAGE f (moi_s39_pcs l e INTER U) = IMAGE f U INTER {z:real^3 | z$1 = &0} /\
      (IMAGE f (frontier (UNIONS x) INTER U) = IMAGE f U INTER {z:real^3 | z$2 = &0} \/
       frontier (UNIONS x) INTER U = {})`
  MP_TAC THENL
   [ASM_CASES_TAC `(y:real^3) IN frontier (UNIONS x)` THENL
     [SUBGOAL_THEN
       `pl_crossing_at (e(segment[v:real^3,w]) DIFF moi_s33_rim t l h v w)
                       (frontier (UNIONS x)) y`
      MP_TAC THENL
       [UNDISCH_TAC `moi_s33_x2 t l h e (x:(real^3->bool)->bool)` THEN
        REWRITE_TAC[moi_s33_x2] THEN
        DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[IN_INTER];
        ALL_TAC] THEN
      REWRITE_TAC[pl_crossing_at] THEN
      DISCH_THEN(X_CHOOSE_THEN `U0:real^3->bool` (X_CHOOSE_THEN `f0:real^3->real^3`
        (X_CHOOSE_THEN `g0:real^3->real^3` STRIP_ASSUME_TAC))) THEN
      MP_TAC(ISPECL [`U0:real^3->bool`; `f0:real^3->real^3`; `g0:real^3->real^3`;
                     `O:real^3->bool`] MOI_S3PU_CHART_RESTRICT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rflat")))) THEN
      MAP_EVERY EXISTS_TAC [`U0 INTER O:real^3->bool`; `f0:real^3->real^3`;
                            `g0:real^3->real^3`] THEN
      ASM_REWRITE_TAC[IN_INTER; INTER_SUBSET] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`moi_s39_pcs l e:real^3->bool`; `e(segment[v:real^3,w]):real^3->bool`;
                       `OT:real^3->bool`; `moi_s33_rim t l h v w`;
                       `(h:real^3->real^3)(midpoint(v,w))`; `moi_s33_ww t l h`;
                       `u:real^3->bool`; `U0 INTER O:real^3->bool`] MOI_S3PU_PCS_LOCAL) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN EXPAND_TAC "O" THEN SET_TAC[];
          DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
        USE_THEN "rflat" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISJ1_TAC THEN USE_THEN "rflat" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ABBREV_TAC `w0 = (O:real^3->bool) INTER ((:real^3) DIFF frontier (UNIONS x))` THEN
      SUBGOAL_THEN `open (w0:real^3->bool) /\ (y:real^3) IN w0 /\ w0 SUBSET moi_s33_ww t l h`
      STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "w0" THEN REPEAT CONJ_TAC THENL
         [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[GSYM closed; FRONTIER_CLOSED];
          ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV];
          UNDISCH_TAC `(u:real^3->bool) SUBSET moi_s33_ww t l h` THEN EXPAND_TAC "O" THEN
          SET_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`e(segment[v:real^3,w]):real^3->bool`; `y:real^3`; `w0:real^3->bool`]
        MOI_S3PU_FLAT_CHART) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN
         `e(segment[v:real^3,w]) INTER w0 =
          ((e(segment[v,w]) DIFF moi_s33_rim t l h v w) DELETE
           (h:real^3->real^3)(midpoint(v,w))) INTER w0`
        SUBST1_TAC THENL
         [UNDISCH_TAC `(w0:real^3->bool) SUBSET moi_s33_ww t l h` THEN
          UNDISCH_TAC `e(segment[v:real^3,w]) INTER moi_s33_ww t l h =
                       (e(segment[v,w]) DIFF moi_s33_rim t l h v w) DELETE
                       (h:real^3->real^3)(midpoint(v,w))` THEN
          SET_TAC[];
          ALL_TAC] THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MOI_S3X2_LP_INTER THEN CONJ_TAC THENL
           [ASM_REWRITE_TAC[]; MATCH_MP_TAC LOCALLY_POLYHEDRAL_OPEN THEN ASM_REWRITE_TAC[]];
          X_GEN_TAC `q:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
          MATCH_MP_TAC MOI_S3PU_R2_SUPER THEN
          EXISTS_TAC `(e(segment[v:real^3,w]) DIFF moi_s33_rim t l h v w) DELETE
                      (h:real^3->real^3)(midpoint(v,w))` THEN
          CONJ_TAC THENL
           [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
              can (find_term ((=) `moi_s28_locally_r2:(real^3->bool)->real^3->bool`))
                (concl th))) THEN
            ASM_REWRITE_TAC[];
            SUBST1_TAC(SYM(ASSUME
             `e(segment[v:real^3,w]) INTER moi_s33_ww t l h =
              (e(segment[v,w]) DIFF moi_s33_rim t l h v w) DELETE
              (h:real^3->real^3)(midpoint(v,w))`)) THEN
            MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[]]];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
        (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
      MAP_EVERY EXISTS_TAC [`U:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
      SUBGOAL_THEN `(U:real^3->bool) SUBSET O` ASSUME_TAC THENL
       [UNDISCH_TAC `(U:real^3->bool) SUBSET w0` THEN EXPAND_TAC "w0" THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`moi_s39_pcs l e:real^3->bool`; `e(segment[v:real^3,w]):real^3->bool`;
                       `OT:real^3->bool`; `moi_s33_rim t l h v w`;
                       `(h:real^3->real^3)(midpoint(v,w))`; `moi_s33_ww t l h`;
                       `u:real^3->bool`; `U:real^3->bool`] MOI_S3PU_PCS_LOCAL) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[];
          DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
        DISJ2_TAC THEN UNDISCH_TAC `(U:real^3->bool) SUBSET w0` THEN EXPAND_TAC "w0" THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` (MAP_EVERY ASSUME_TAC o CONJUNCTS)))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `v:real^3`; `w:real^3`] MOI_S3PU_EDGE_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cvq") (CONJUNCTS_THEN2 (LABEL_TAC "cwq")
    (CONJUNCTS_THEN2 (LABEL_TAC "cvw") (LABEL_TAC "qne")))) THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`; `y:real^3`;
                 `moi_s39_pcs l e:real^3->bool`; `UNIONS x:real^3->bool`; `u:real^3->bool`;
                 `IMAGE (h:real^3->real^3) (derived_nbhd t l)`; `(h:real^3->real^3) v`;
                 `(h:real^3->real^3) w`] MOI_S3PU_G_PUSH) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(U:real^3->bool) SUBSET O` THEN EXPAND_TAC "O" THEN SET_TAC[];
      UNDISCH_TAC `(U:real^3->bool) SUBSET O` THEN EXPAND_TAC "O" THEN
      UNDISCH_TAC `(u:real^3->bool) SUBSET moi_s33_ww t l h` THEN
      UNDISCH_TAC `moi_s33_ww t l h SUBSET IMAGE (h:real^3->real^3) (derived_nbhd t l)` THEN
      SET_TAC[];
      USE_THEN "cvq" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
      USE_THEN "cwq" (SUBST1_TAC o SYM) THEN
      USE_THEN "cvw" (fun th -> MP_TAC th) THEN
      UNDISCH_TAC `(y:real^3) IN e(segment[v:real^3,w])` THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "cvq" (fun th -> REWRITE_TAC[SYM th]));;

(* ========================================================================= *)
(* Piece 4: MOI_S3PU_FINAL : |- T_S3PU_FINAL, i.e. the local pushes         *)
(* (T_S3PU_LOCAL_PUSH) and the closedness of the pseudo-cells               *)
(* (T_S3PU_PCS_CLOSED) give MOI_S39_PUSH_BODY.  kk = z INTER PCS is         *)
(* compact; MOI_S3PU_PUSH_COMPOSE over the local pushes at the points of kk *)
(* (C = c v, A = PCS, X = UNIONS x, G = u) gives Phi; the new               *)
(* disk is IMAGE Phi d (MOI_S3PU_LTD_TRANSPORT), whose trace on PCS is      *)
(* (d DIFF u) INTER PCS.                                                    *)
(* ========================================================================= *)

let MOI_S3PU_FINAL = prove
 (T_S3PU_FINAL,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "LP") (LABEL_TAC "PC")) THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hd") (CONJUNCTS_THEN2 (LABEL_TAC "inv")
    (CONJUNCTS_THEN2 (LABEL_TAC "v") (CONJUNCTS_THEN2 (LABEL_TAC "ltd")
    (CONJUNCTS_THEN2 (LABEL_TAC "ou") (CONJUNCTS_THEN2 (LABEL_TAC "uW")
    (CONJUNCTS_THEN2 (LABEL_TAC "cz") (CONJUNCTS_THEN2 (LABEL_TAC "zu")
    (CONJUNCTS_THEN2 (LABEL_TAC "du") (LABEL_TAC "dz")))))))))) THEN
  (* the compact set kk of points to push off *)
  SUBGOAL_THEN `compact (z INTER moi_s39_pcs l e:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_INTER_CLOSED THEN USE_THEN "cz" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "PC" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `h:real^3->real^3`;
                          `c:real^3->real^3->bool`] THEN
    USE_THEN "hd" ACCEPT_TAC;
    ALL_TAC] THEN
  (* the composed push *)
  MP_TAC(ISPECL [`z INTER moi_s39_pcs l e:real^3->bool`; `(c:real^3->real^3->bool) v`;
                 `moi_s39_pcs l e:real^3->bool`; `UNIONS x:real^3->bool`; `u:real^3->bool`]
                MOI_S3PU_PUSH_COMPOSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    USE_THEN "LP" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `h:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "zu" (MP_TAC o REWRITE_RULE[SUBSET; IN_INTER]) THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Phi:real^3->real^3` (X_CHOOSE_THEN `Phi':real^3->real^3`
    (CONJUNCTS_THEN2 (LABEL_TAC "PhiP") (CONJUNCTS_THEN2 (LABEL_TAC "fix")
    (CONJUNCTS_THEN2 (LABEL_TAC "invX") (LABEL_TAC "cv")))))) THEN
  EXISTS_TAC `IMAGE (Phi:real^3->real^3) d` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3PU_LTD_TRANSPORT THEN
    MAP_EVERY EXISTS_TAC [`Phi':real^3->real^3`; `u:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    USE_THEN "fix" MP_TAC THEN USE_THEN "cv" MP_TAC THEN
    USE_THEN "du" MP_TAC THEN USE_THEN "dz" MP_TAC THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Part 7: the main theorem S39_PUSH : |- MOI_S39_PUSH_BODY, from the       *)
(* local pushes (Part 6) and the closedness of PCS (Part 5) by              *)
(* MOI_S3PU_FINAL (piece 4).                                                *)
(* ========================================================================= *)

let S39_PUSH = prove
 (MOI_S39_PUSH_BODY,
  ACCEPT_TAC(MP MOI_S3PU_FINAL (CONJ MOI_S3PU_LOCAL_PUSH MOI_S3PU_PCS_CLOSED)));;

