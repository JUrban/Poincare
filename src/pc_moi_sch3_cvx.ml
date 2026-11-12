(* ========================================================================= *)
(* pc_moi_sch3_cvx: main theorem LEVEL_CONVEXIFY = MOI_SCH3_LEVEL_CONVEXIFY  *)
(* (pc_moi_sch3_stmt.ml; Moise GTM 47, Lemma 1 of the proof of 17.12,        *)
(* p.123, first paragraph): a PL 2-cell in a level plane meeting s exactly   *)
(* in its boundary is carried onto a 2-simplex by a level-preserving PLH of  *)
(* real^3 that is the identity off w and off a thin slab.  Route:            *)
(* AMB2_VERTEX in the plane (after an isometric change of coordinates),      *)
(* then the conewise extension of the planar PLH to a bipyramid over a       *)
(* convex polygon with apexes on the normal line, extended by the identity.  *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_sch3_free.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Planar facts: the boundary of a PL 2-cell is a PL circle; in the plane a  *)
(* PL 2-cell is its boundary curve together with the inside; the plane step  *)
(* (AMB2_VERTEX carries the whole cell onto the triangle); a polytope        *)
(* between a compact set and a convex open superset.                         *)
(* ------------------------------------------------------------------------- *)

let MOI_SCX_CELL_SPHERE = prove
 (`!(d:real^N->bool) j. pl_cell_with_boundary 2 d j ==> pl_sphere 1 j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (j:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SS2_FSA_OF_CELL; MOI_SS2_FSA_POLYHEDRON]; ALL_TAC] THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^N->bool) j` THEN
  REWRITE_TAC[pl_cell_with_boundary; pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCD_PLH_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `d:real^N->bool`] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
  ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]);;

let MOI_SCX_TRI_FILL = prove
 (`!t:real^2->bool.
     &2 simplex t ==> relative_frontier t UNION inside (relative_frontier t) = t`,
  GEN_TAC THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^2` (X_CHOOSE_THEN `b:real^2`
    (X_CHOOSE_THEN `c:real^2` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP MOI_PL2_FRONTIER_TRIANGLE th)]) THEN
  REWRITE_TAC[FRONTIER_OF_TRIANGLE; MOI_PL2_TRIANGLE_CLOSED_INSIDE]);;

let MOI_SCX_FILL2 = prove
 (`!d j:real^2->bool. pl_cell_with_boundary 2 d j ==> d = j UNION inside j`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SCX_CELL_SPHERE) THEN
  SUBGOAL_THEN
   `frontier (d:real^2->bool) = j /\ j SUBSET d /\ compact d /\
    connected (d DIFF j) /\ ~(d DIFF j = {})`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
      (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PL2_FRONTIER_PL_BALL_2 THEN
    EXISTS_TAC `g:real^2->real^2` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior (d:real^2->bool) = d DIFF j` ASSUME_TAC THENL
   [MP_TAC(ISPEC `d:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `frontier (d:real^2->bool) = j` THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (inside (j:real^2->bool)) /\ inside j INTER j = {}`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP PL_SPHERE_1_POLYGON) THEN
    DISCH_THEN(X_CHOOSE_THEN `pp:(real^2)list` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`polygonal_path (pp:(real^2)list)`; `j:real^2->bool`]
      MOI_SFR_JORDAN_REGION) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d DIFF j SUBSET inside (j:real^2->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; inside; IN_ELIM_THM; IN_DIFF] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `d:real^2->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    ABBREV_TAC `cc = connected_component ((:real^2) DIFF j) (x:real^2)` THEN
    SUBGOAL_THEN `(x:real^2) IN cc /\ connected cc /\ cc SUBSET (:real^2) DIFF j`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "cc" THEN
      REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT; CONNECTED_COMPONENT_SUBSET] THEN
      REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((cc:real^2->bool) INTER frontier d = {})` MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_INTER_FRONTIER THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `d DIFF j = inside (j:real^2->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `connected (inside (j:real^2->bool))` THEN
    REWRITE_TAC[CONNECTED_CLOPEN] THEN
    DISCH_THEN(MP_TAC o SPEC `d DIFF j:real^2->bool`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `interior (d:real^2->bool) = d DIFF j`)) THEN
        REWRITE_TAC[OPEN_INTERIOR];
        REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `d:real^2->bool` THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_SCX_PLANE = prove
 (`!d j (w:real^2->bool) p.
     pl_cell_with_boundary 2 d j /\ open w /\ d SUBSET w /\ p IN j
     ==> ?t f g. &2 simplex t /\ pl_homeomorphism ((:real^2),(:real^2)) (f,g) /\
                 (!x. ~(x IN w) ==> f x = x) /\
                 IMAGE f d = t /\ IMAGE f j = relative_frontier t /\
                 {f p} face_of t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SCX_CELL_SPHERE) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SCX_FILL2) THEN
  MP_TAC(ISPECL [`j:real^2->bool`; `w:real^2->bool`; `p:real^2`] AMB2_VERTEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
    (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`t:real^2->bool`; `f:real^2->real^2`; `g:real^2->real^2`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `d:real^2->bool`)) THEN
  REWRITE_TAC[IMAGE_UNION] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o MATCH_MP MOI_SA2_PLH_UNIV) THEN
  DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP MOI_SCD_INSIDE_HOMEOMORPHISM th]) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCX_TRI_FILL THEN ASM_REWRITE_TAC[]);;

let MOI_SCX_POLYTOPE_BETWEEN = prove
 (`!(k:real^2->bool) w.
     compact k /\ convex w /\ open w /\ k SUBSET w
     ==> ?b. polytope b /\ k SUBSET interior b /\ b SUBSET w`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `kk = convex hull (k:real^2->bool)` THEN
  SUBGOAL_THEN `compact (kk:real^2->bool) /\ k SUBSET kk /\ kk SUBSET w`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "kk" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONVEX_HULL THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[HULL_SUBSET];
      MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kk:real^2->bool`; `(:real^2) DIFF w`] SEPARATE_COMPACT_CLOSED) THEN
  ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep"))) THEN
  MP_TAC(ISPEC `kk:real^2->bool` COMPACT_IMP_TOTALLY_BOUNDED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e / &4`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?sf. !x:real^2. FINITE (sf x:real^2->bool) /\
                    interval[x - (e / &4) % vec 1,x + (e / &4) % vec 1] =
                    convex hull (sf x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[CLOSED_INTERVAL_AS_CONVEX_HULL];
    ALL_TAC] THEN
  EXISTS_TAC `convex hull (UNIONS (IMAGE (sf:real^2->real^2->bool) ff))` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    ASM_SIMP_TAC[FINITE_UNIONS; FINITE_IMAGE; FORALL_IN_IMAGE];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `kk:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS (IMAGE (\x. ball(x,e / &4)) (ff:real^2->bool))` THEN
    ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior(interval[x - (e / &4) % vec 1:real^2,x + (e / &4) % vec 1])` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[INTERIOR_INTERVAL; SUBSET; IN_BALL; IN_INTERVAL; DIMINDEX_2;
                  FORALL_2; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
                  VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`x - y:real^2`; `1`] COMPONENT_LE_NORM) THEN
      MP_TAC(ISPECL [`x - y:real^2`; `2`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[DIMINDEX_2; ARITH; VECTOR_SUB_COMPONENT; GSYM dist] THEN
      ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]];
    MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^2) IN kk` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interval[x - (e / &4) % vec 1:real^2,x + (e / &4) % vec 1]` THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[HULL_SUBSET];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      REMOVE_THEN "sep" (MP_TAC o SPECL [`x:real^2`; `y:real^2`]) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `x - y:real^2` NORM_LE_L1) THEN
      REWRITE_TAC[DIMINDEX_2; SUM_2; VECTOR_SUB_COMPONENT; GSYM dist] THEN
      UNDISCH_TAC
       `(y:real^2) IN interval[x - (e / &4) % vec 1,x + (e / &4) % vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_SUB_COMPONENT;
                  VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
      ASM_REAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Standard coordinates: the level plane x$3 = 0 of real^3 and real^2.      *)
(* ------------------------------------------------------------------------- *)

let moi_scx_e = new_definition
 `moi_scx_e (u:real^2) = vector[u$1; u$2; &0]:real^3`;;

let moi_scx_pr = new_definition
 `moi_scx_pr (x:real^3) = vector[x$1; x$2]:real^2`;;

let MOI_SCX_EP = prove
 (`linear moi_scx_e /\ linear moi_scx_pr /\
   (!u. moi_scx_pr (moi_scx_e u) = u) /\
   (!u. (moi_scx_e u)$3 = &0) /\
   (!u. (moi_scx_e u)$1 = u$1 /\ (moi_scx_e u)$2 = u$2) /\
   (!x. (moi_scx_pr x)$1 = x$1 /\ (moi_scx_pr x)$2 = x$2) /\
   (!x. x$3 = &0 ==> moi_scx_e (moi_scx_pr x) = x) /\
   (!u v. moi_scx_e u = moi_scx_e v <=> u = v)`,
  REWRITE_TAC[linear; moi_scx_e; moi_scx_pr; CART_EQ; DIMINDEX_2; DIMINDEX_3;
              FORALL_2; FORALL_3; VECTOR_2; VECTOR_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_SCX_PL_LINEAR = prove
 (`!(s:real^M->bool) (l:real^M->real^N).
     locally_polyhedral s /\ linear l ==> pl_map_on s l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `\x:real^M. (l:real^M->real^N) x + vec 0` THEN
  ASM_SIMP_TAC[PL_MAP_ON_AFFINE; VECTOR_ADD_RID]);;

let MOI_SCX_LP_LEVEL = prove
 (`!t. locally_polyhedral {x:real^3 | x$3 = t}`,
  GEN_TAC THEN MATCH_MP_TAC MOI_SA2_LP_POLYHEDRON THEN
  SUBGOAL_THEN `{x:real^3 | x$3 = t} = {x | basis 3 dot x = t}` SUBST1_TAC THENL
   [SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]; REWRITE_TAC[POLYHEDRON_HYPERPLANE]]);;

let MOI_SCX_LP_UNIV = prove
 (`locally_polyhedral (:real^N)`,
  MATCH_MP_TAC MOI_SA2_LP_POLYHEDRON THEN REWRITE_TAC[POLYHEDRON_UNIV]);;

let MOI_SCX_PLANE_PLH = prove
 (`pl_homeomorphism ({x:real^3 | x$3 = &0},(:real^2)) (moi_scx_pr,moi_scx_e)`,
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN REPEAT CONJ_TAC THENL
   [SIMP_TAC[IN_ELIM_THM; MOI_SCX_EP];
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `u:real^2` THEN EXISTS_TAC `moi_scx_e u` THEN REWRITE_TAC[MOI_SCX_EP];
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_SCX_EP];
    REWRITE_TAC[MOI_SCX_EP];
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_UNIV; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[MOI_SCX_EP];
      DISCH_TAC THEN EXISTS_TAC `moi_scx_pr x` THEN ASM_SIMP_TAC[MOI_SCX_EP]];
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_SCX_EP];
    MATCH_MP_TAC MOI_SCX_PL_LINEAR THEN REWRITE_TAC[MOI_SCX_LP_LEVEL; MOI_SCX_EP];
    MATCH_MP_TAC MOI_SCX_PL_LINEAR THEN REWRITE_TAC[MOI_SCX_LP_UNIV; MOI_SCX_EP]]);;

let MOI_SCX_TO_PLANE = prove
 (`!d j:real^3->bool.
     pl_cell_with_boundary 2 d j /\ d SUBSET {x | x$3 = &0}
     ==> pl_cell_with_boundary 2 (IMAGE moi_scx_pr d) (IMAGE moi_scx_pr j)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_SS2_CELL_EQ_FSA_2] THEN
  MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
  MAP_EVERY EXISTS_TAC [`{x:real^3 | x$3 = &0}`; `(:real^2)`; `moi_scx_e`] THEN
  ASM_REWRITE_TAC[MOI_SCX_PLANE_PLH; GSYM MOI_SS2_CELL_EQ_FSA]);;

(* ------------------------------------------------------------------------- *)
(* Cones and the bipyramid over a level polygon.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_SCX_FIX_IMAGE = prove
 (`!(f:real^2->real^2) g u s.
     pl_homeomorphism ((:real^2),(:real^2)) (f,g) /\
     (!x. ~(x IN u) ==> f x = x) /\ u SUBSET s
     ==> IMAGE f s = s /\ IMAGE g s = s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_PLH_UNIV) THEN
  MP_TAC(ISPECL [`f:real^2->real^2`; `g:real^2->real^2`; `u:real^2->bool`;
                 `u:real^2->bool`] MOI_SA2_FIX_OFF) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`g:real^2->real^2`; `f:real^2->real^2`; `u:real^2->bool`;
                 `u:real^2->bool`] MOI_SA2_FIX_OFF) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (f:real^2->real^2) s SUBSET s /\ IMAGE (g:real^2->real^2) s SUBSET s`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^2) IN u` THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_SCX_COMP = prove
 (`!(m:real^3) c.
     (m + c % basis 3)$1 = m$1 /\ (m + c % basis 3)$2 = m$2 /\
     (m + c % basis 3)$3 = m$3 + c`,
  SIMP_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; BASIS_COMPONENT;
           DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC);;

let MOI_SCX_CONE_PT = prove
 (`!(a:real^N->bool) ap p.
     p IN UNIONS {segment[ap,x] | x IN a} <=>
     ?x r. x IN a /\ &0 <= r /\ r <= &1 /\ p = ap + r % (x - ap)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`x:real^N`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `r:real`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `segment[ap:real^N,x]` THEN CONJ_TAC THENL
     [EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `r:real` THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]]);;

let MOI_SCX_APEX = prove
 (`!(a:real^3->bool) m c.
     (!x. x IN a ==> x$3 = &0) /\ m$3 = &0 /\ ~(c = &0)
     ==> ~((m + c % basis 3) IN a) /\
         (!x y. x IN a /\ y IN a /\ y IN segment[m + c % basis 3,x] ==> y = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `m + c % basis 3:real^3`) THEN
    ASM_REWRITE_TAC[MOI_SCX_COMP; REAL_ADD_LID];
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(x:real^3)$3 = &0 /\ (y:real^3)$3 = &0` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `r = &1` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `y = (&1 - r) % (m + c % basis 3) + r % (x:real^3)` THEN
      DISCH_THEN(MP_TAC o BETA_RULE o AP_TERM `\v:real^3. v$3`) THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; MOI_SCX_COMP] THEN
      REWRITE_TAC[REAL_ADD_LID; REAL_MUL_RZERO; REAL_ADD_RID] THEN
      DISCH_THEN(MP_TAC o SYM) THEN ASM_REWRITE_TAC[REAL_ENTIRE] THEN
      REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC]]);;

let MOI_SCX_BIPYR_STEP = prove
 (`!(a:real^N->bool) m d y al be ga.
     convex a /\ m IN a /\ y IN a /\ &0 <= al /\ &0 <= be /\ &0 <= ga /\
     al + be + ga = &1 /\ be <= al
     ==> al % (m + d) + be % (m - d) + ga % y IN UNIONS {segment[m + d,x] | x IN a}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_SCX_CONE_PT] THEN
  ASM_CASES_TAC `&2 * be + ga = &0` THENL
   [SUBGOAL_THEN `be = &0 /\ ga = &0 /\ al = &1` STRIP_ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`m:real^N`; `&0`] THEN ASM_REWRITE_TAC[REAL_POS] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `la = &2 * be + ga` THEN
  SUBGOAL_THEN `&0 < la` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `inv la % ((&2 * be) % m + ga % y):real^N` THEN
  EXISTS_TAC `la:real` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    UNDISCH_TAC `convex (a:real^N->bool)` THEN REWRITE_TAC[convex] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE; REAL_POS] THEN
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    SUBGOAL_THEN `al = &1 - be - ga` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "la" THEN VECTOR_ARITH_TAC]);;

let MOI_SCX_BIPYR = prove
 (`!(a:real^N->bool) m d.
     convex a /\ m IN a
     ==> convex hull ((m + d) INSERT (m - d) INSERT a) =
         UNIONS {segment[m + d,x] | x IN a} UNION
         UNIONS {segment[m - d,x] | x IN a}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [SUBGOAL_THEN `~(a:real^N->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONVEX_HULL_INSERT; NOT_INSERT_EMPTY] THEN
    ASM_SIMP_TAC[HULL_P] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real`
      (X_CHOOSE_THEN `b:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `u':real` (X_CHOOSE_THEN `v':real`
          (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC))) ASSUME_TAC))))))) THEN
    SUBGOAL_THEN
     `x = u % (m + d) + (v * u') % (m - d) + (v * v') % (y:real^N)`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC]; ALL_TAC] THEN
    SUBGOAL_THEN `u + v * u' + v * v' = &1` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM REAL_ADD_LDISTRIB; REAL_MUL_RID]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= v * u' /\ &0 <= v * v'` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_MUL]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN
    ASM_CASES_TAC `v * u' <= u` THENL
     [DISJ1_TAC THEN MATCH_MP_TAC MOI_SCX_BIPYR_STEP THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN
      SUBGOAL_THEN
       `u % (m + d) + (v * u') % (m - d) + (v * v') % (y:real^N) =
        (v * u') % (m + --d) + u % (m - --d) + (v * v') % y`
      SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `m - d:real^N = m + --d` SUBST1_TAC THENL
       [VECTOR_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC MOI_SCX_BIPYR_STEP THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL] THEN CONJ_TAC THEN
    MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]]);;

let MOI_SCX_CONE_INTER = prove
 (`!(a:real^3->bool) m c.
     (!x. x IN a ==> x$3 = &0) /\ m$3 = &0 /\ &0 < c
     ==> UNIONS {segment[m + c % basis 3,x] | x IN a} INTER
         UNIONS {segment[m + --c % basis 3,x] | x IN a} = a`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; MOI_SCX_CONE_PT] THEN X_GEN_TAC `p:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))
      (X_CHOOSE_THEN `y:real^3` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(x:real^3)$3 = &0 /\ (y:real^3)$3 = &0` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3)$3 = (&1 - r) * c` ASSUME_TAC THENL
     [UNDISCH_TAC `p = (m + c % basis 3) + r % (x - (m + c % basis 3):real^3)` THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                      VECTOR_SUB_COMPONENT; MOI_SCX_COMP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3)$3 = (&1 - s) * --c` ASSUME_TAC THENL
     [UNDISCH_TAC `p = (m + --c % basis 3) + s % (y - (m + --c % basis 3):real^3)` THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                      VECTOR_SUB_COMPONENT; MOI_SCX_COMP] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `r = &1` SUBST_ALL_TAC THENL
     [SUBGOAL_THEN `&0 <= (&1 - r) * c /\ &0 <= (&1 - s) * c` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LE_MUL; REAL_SUB_LE; REAL_LT_IMP_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `(&1 - r) * c = &0` MP_TAC THENL
       [UNDISCH_TAC `(p:real^3)$3 = (&1 - r) * c` THEN
        UNDISCH_TAC `(p:real^3)$3 = (&1 - s) * --c` THEN
        UNDISCH_TAC `&0 <= (&1 - r) * c` THEN UNDISCH_TAC `&0 <= (&1 - s) * c` THEN
        REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_ENTIRE; REAL_LT_IMP_NZ] THEN REAL_ARITH_TAC];
      UNDISCH_TAC `p = (m + c % basis 3) + &1 % (x - (m + c % basis 3):real^3)` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[VECTOR_ARITH `a + &1 % (x - a) = x:real^3`] THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; IN_INTER; MOI_SCX_CONE_PT] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN CONJ_TAC THEN
    MAP_EVERY EXISTS_TAC [`x:real^3`; `&1`] THEN
    ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Cone coordinates in the slab and interior points of the bipyramid.        *)
(* ------------------------------------------------------------------------- *)

let MOI_SCX_B3 = prove
 (`(basis 3:real^3)$1 = &0 /\ (basis 3:real^3)$2 = &0 /\ (basis 3:real^3)$3 = &1`,
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH]);;

let MOI_SCX_DIV_NEG = prove
 (`!t e. t / --e = --t / e`,
  REWRITE_TAC[real_div; REAL_INV_NEG; REAL_MUL_RNEG; REAL_MUL_LNEG]);;

let MOI_SCX_SLAB_SCALAR = prove
 (`!eps c t. &0 < eps /\ (c = eps \/ c = --eps) /\ --eps < t /\ t < eps
             ==> &0 < &1 - t / c`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (DISJ_CASES_THEN SUBST1_TAC) STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[MOI_SCX_DIV_NEG; REAL_SUB_LT] THEN
  ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN ASM_REAL_ARITH_TAC);;

let MOI_SCX_CONE_MEM = prove
 (`!(bb:real^2->bool) b0 c x.
     ~(c = &0) /\ &0 <= x$3 / c /\ x$3 / c < &1 /\
     b0 + inv(&1 - x$3 / c) % (moi_scx_pr x - b0) IN bb
     ==> x IN UNIONS {segment[moi_scx_e b0 + c % basis 3,y] |
                      y IN IMAGE moi_scx_e bb}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_SCX_CONE_PT] THEN
  ABBREV_TAC `la = &1 - (x:real^3)$3 / c` THEN
  SUBGOAL_THEN `&0 < la /\ la <= &1` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `moi_scx_e (b0 + inv la % (moi_scx_pr x - b0))` THEN
  EXISTS_TAC `la:real` THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE; REAL_LT_IMP_LE] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; MOI_SCX_COMP; MOI_SCX_EP;
              MOI_SCX_B3] THEN
  MAP_EVERY UNDISCH_TAC [`&0 < la`; `&1 - (x:real^3)$3 / c = la`; `~(c = &0)`] THEN
  CONV_TAC REAL_FIELD);;

let MOI_SCX_CONE_COORDS = prove
 (`!b0 c y r.
     moi_scx_pr ((moi_scx_e b0 + c % basis 3) +
                 r % (moi_scx_e y - (moi_scx_e b0 + c % basis 3))) =
     b0 + r % (y - b0) /\
     ((moi_scx_e b0 + c % basis 3) +
      r % (moi_scx_e y - (moi_scx_e b0 + c % basis 3)))$3 = (&1 - r) * c`,
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT; VECTOR_SUB_COMPONENT; MOI_SCX_COMP; MOI_SCX_EP;
              MOI_SCX_B3] THEN
  REAL_ARITH_TAC);;

let MOI_SCX_SLAB_OPEN = prove
 (`!eps. open {x:real^3 | --eps < x$3 /\ x$3 < eps}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{x:real^3 | --eps < x$3 /\ x$3 < eps} =
                {x | x$3 > --eps} INTER {x | x$3 < eps}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_gt];
    MATCH_MP_TAC OPEN_INTER THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_LT; OPEN_HALFSPACE_COMPONENT_GT]]);;

let MOI_SCX_PSI_CONT = prove
 (`!(b0:real^2) eps c.
     &0 < eps /\ (c = eps \/ c = --eps)
     ==> (\x:real^3. b0 + inv(&1 - x$3 / c) % (moi_scx_pr x - b0)) continuous_on
         {x | --eps < x$3 /\ x$3 < eps}`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `(lift o (\x:real^3. inv(&1 - x$3 / c))) =
      (lift o inv o (\x:real^3. &1 - x$3 / c))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_INV THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `(lift o (\x:real^3. &1 - x$3 / c)) =
        (\x. lift(&1) - inv c % lift(x$3))`
      SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM; real_div] THEN GEN_TAC THEN
        ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[LIFT_SUB; LIFT_CMUL];
        ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN
      REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`eps:real`; `c:real`; `(x:real^3)$3`] MOI_SCX_SLAB_SCALAR) THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST; ETA_AX] THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_SCX_EP]]);;

let MOI_SCX_INTERIOR = prove
 (`!(bb:real^2->bool) b0 eps c y r.
     convex bb /\ b0 IN interior bb /\ &0 < eps /\ (c = eps \/ c = --eps) /\
     y IN interior bb /\ &0 < r /\ r <= &1
     ==> (moi_scx_e b0 + c % basis 3) +
         r % (moi_scx_e y - (moi_scx_e b0 + c % basis 3)) IN
         interior (UNIONS {segment[moi_scx_e b0 + eps % basis 3,z] |
                           z IN IMAGE moi_scx_e bb} UNION
                   UNIONS {segment[moi_scx_e b0 + --eps % basis 3,z] |
                           z IN IMAGE moi_scx_e bb})`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  ABBREV_TAC `x0 = (moi_scx_e b0 + c % basis 3) +
                   r % (moi_scx_e y - (moi_scx_e b0 + c % basis 3))` THEN
  SUBGOAL_THEN `moi_scx_pr x0 = b0 + r % (y - b0) /\ (x0:real^3)$3 = (&1 - r) * c`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "x0" THEN REWRITE_TAC[MOI_SCX_CONE_COORDS]; ALL_TAC] THEN
  SUBGOAL_THEN `~(c = &0) /\ abs c = eps` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[interior; IN_ELIM_THM] THEN
  EXISTS_TAC
   `{x:real^3 | x IN {x | --eps < x$3 /\ x$3 < eps} /\
                b0 + inv(&1 - x$3 / eps) % (moi_scx_pr x - b0) IN interior bb} INTER
    {x:real^3 | x IN {x | --eps < x$3 /\ x$3 < eps} /\
                b0 + inv(&1 - x$3 / --eps) % (moi_scx_pr x - b0) IN interior bb}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_INTER THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
    REWRITE_TAC[MOI_SCX_SLAB_OPEN; OPEN_INTERIOR] THEN
    MATCH_MP_TAC MOI_SCX_PSI_CONT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `--eps < (&1 - r) * c /\ (&1 - r) * c < eps` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `&0 < r * eps /\ r * eps <= eps` STRIP_ASSUME_TAC THENL
       [ASM_SIMP_TAC[REAL_LT_MUL] THEN
        MATCH_MP_TAC(REAL_ARITH `r * eps <= &1 * eps ==> r * eps <= eps`) THEN
        MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
        ALL_TAC] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `!d. (d = c \/ d = --c)
          ==> b0 + inv(&1 - ((&1 - r) * c) / d) % ((b0 + r % (y - b0)) - b0) IN
              interior (bb:real^2->bool)`
    MP_TAC THENL
     [GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THENL
      [SUBGOAL_THEN `&1 - ((&1 - r) * c) / c = r` SUBST1_TAC THENL
        [UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
       REWRITE_TAC[VECTOR_ARITH `(b0 + r % (y - b0)) - b0:real^2 = r % (y - b0)`] THEN
       ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
       ASM_REWRITE_TAC[VECTOR_ARITH `b0 + y - b0:real^2 = y`];
       SUBGOAL_THEN `&1 - ((&1 - r) * c) / --c = &2 - r` SUBST1_TAC THENL
        [UNDISCH_TAC `~(c = &0)` THEN CONV_TAC REAL_FIELD; ALL_TAC] THEN
       SUBGOAL_THEN
        `b0 + inv(&2 - r) % ((b0 + r % (y - b0)) - b0) =
         (&1 - r / (&2 - r)) % b0 + (r / (&2 - r)) % (y:real^2)`
       SUBST1_TAC THENL
        [REWRITE_TAC[VECTOR_ARITH `(b0 + r % (y - b0)) - b0:real^2 = r % (y - b0)`] THEN
         REWRITE_TAC[VECTOR_MUL_ASSOC; real_div; VECTOR_SUB_LDISTRIB] THEN
         REWRITE_TAC[VECTOR_SUB_RDISTRIB; VECTOR_MUL_LID] THEN
         REWRITE_TAC[REAL_MUL_SYM] THEN VECTOR_ARITH_TAC;
         ALL_TAC] THEN
       MP_TAC(MATCH_MP CONVEX_INTERIOR (ASSUME `convex (bb:real^2->bool)`)) THEN
       REWRITE_TAC[convex] THEN DISCH_THEN MATCH_MP_TAC THEN
       ASM_REWRITE_TAC[] THEN
       SUBGOAL_THEN `&0 < &2 - r` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
       SUBGOAL_THEN `&0 <= r / (&2 - r) /\ r / (&2 - r) <= &1` STRIP_ASSUME_TAC THENL
        [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
         ASM_REAL_ARITH_TAC;
         ALL_TAC] THEN
       ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
    REWRITE_TAC[REAL_NEG_NEG];
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; IN_UNION] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    ASM_CASES_TAC `&0 <= (x:real^3)$3` THENL
     [DISJ1_TAC THEN MATCH_MP_TAC MOI_SCX_CONE_MEM THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LT_LDIV_EQ;
                   REAL_MUL_LID] THEN
      ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET];
      DISJ2_TAC THEN MATCH_MP_TAC MOI_SCX_CONE_MEM THEN
      ASM_REWRITE_TAC[MOI_SCX_DIV_NEG; REAL_NEG_EQ_0] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ; REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LT_LDIV_EQ;
                   REAL_MUL_LID] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `b0 + inv (&1 - (x:real^3)$3 / --eps) % (moi_scx_pr x - b0) IN
                   interior bb` THEN
      REWRITE_TAC[MOI_SCX_DIV_NEG] THEN ASM_MESON_TAC[SUBSET; INTERIOR_SUBSET]]]);;

(* ------------------------------------------------------------------------- *)
(* The level-preserving double-cone extension of a planar PLH fixed off the  *)
(* interior of a convex polygon.                                             *)
(* ------------------------------------------------------------------------- *)

let MOI_SCX_IMAGE_LIFT = prove
 (`!(h:real^2->real^2) s.
     IMAGE (moi_scx_e o h o moi_scx_pr) (IMAGE moi_scx_e s) =
     IMAGE moi_scx_e (IMAGE h s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM; o_THM; MOI_SCX_EP]);;

let MOI_SCX_LIFT_PLH = prove
 (`!(bb:real^2->bool) f2 g2.
     polytope bb /\ pl_homeomorphism ((:real^2),(:real^2)) (f2,g2) /\
     IMAGE f2 bb = bb /\ IMAGE g2 bb = bb
     ==> pl_homeomorphism (IMAGE moi_scx_e bb,IMAGE moi_scx_e bb)
           (moi_scx_e o f2 o moi_scx_pr,moi_scx_e o g2 o moi_scx_pr)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SA2_PLH_UNIV) THEN
  SUBGOAL_THEN
   `pl_map_on (:real^2) (f2:real^2->real^2) /\ pl_map_on (:real^2) (g2:real^2->real^2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(f2:real^2->real^2) continuous_on (:real^2) /\
    (g2:real^2->real^2) continuous_on (:real^2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON]; ALL_TAC] THEN
  SUBGOAL_THEN `locally_polyhedral (IMAGE moi_scx_e bb)` ASSUME_TAC THENL
   [MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN
    MATCH_MP_TAC POLYTOPE_LINEAR_IMAGE THEN ASM_REWRITE_TAC[MOI_SCX_EP];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^2->real^2. pl_map_on (:real^2) h
        ==> pl_map_on (IMAGE moi_scx_e bb) (moi_scx_e o h o moi_scx_pr)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `(:real^2)` THEN
    SIMP_TAC[MOI_SCX_PL_LINEAR; MOI_SCX_LP_UNIV; MOI_SCX_EP; SUBSET_UNIV] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^2)` THEN
    ASM_SIMP_TAC[MOI_SCX_PL_LINEAR; MOI_SCX_EP; SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!h:real^2->real^2. h continuous_on (:real^2)
        ==> (moi_scx_e o h o moi_scx_pr) continuous_on (IMAGE moi_scx_e bb)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_SCX_EP] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; MOI_SCX_EP] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  ASM_SIMP_TAC[MOI_SCX_IMAGE_LIFT] THEN
  REWRITE_TAC[FORALL_IN_IMAGE; o_THM; MOI_SCX_EP] THEN ASM_REWRITE_TAC[]);;

let MOI_SCX_CONEMAP_FACTS = prove
 (`!(bb:real^2->bool) b0 (f2:real^2->real^2) c x.
     ~(c = &0) /\
     x IN UNIONS {segment[moi_scx_e b0 + c % basis 3,z] | z IN IMAGE moi_scx_e bb}
     ==> ?u r. u IN bb /\ &0 <= r /\ r <= &1 /\
               x = (moi_scx_e b0 + c % basis 3) +
                   r % (moi_scx_e u - (moi_scx_e b0 + c % basis 3)) /\
               moi_con_conemap (IMAGE moi_scx_e bb) (moi_scx_e b0 + c % basis 3)
                 (moi_scx_e b0 + c % basis 3) (moi_scx_e o f2 o moi_scx_pr) x =
               (moi_scx_e b0 + c % basis 3) +
               r % (moi_scx_e (f2 u) - (moi_scx_e b0 + c % basis 3))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_SCX_CONE_PT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^3`
    (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `(z:real^3) IN IMAGE moi_scx_e bb` THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^2` (CONJUNCTS_THEN2 SUBST_ALL_TAC ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`u:real^2`; `r:real`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`IMAGE moi_scx_e bb`; `moi_scx_e b0`; `c:real`] MOI_SCX_APEX) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE; MOI_SCX_EP] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE moi_scx_e bb`; `moi_scx_e b0 + c % basis 3`;
                 `moi_scx_e b0 + c % basis 3`; `moi_scx_e o f2 o moi_scx_pr`;
                 `moi_scx_e u`; `r:real`] MOI_CON_CONEMAP_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM; MOI_SCX_EP]]);;

let MOI_SCX_CONE_POLYTOPE = prove
 (`!(aa:real^3->bool) a b.
     polytope aa ==> polytope (convex hull (a INSERT b INSERT aa))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[polytope] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(a:real^3) INSERT b INSERT s` THEN
  ASM_REWRITE_TAC[FINITE_INSERT] THEN
  ONCE_REWRITE_TAC[SET_RULE `(a:real^3) INSERT b INSERT s = {a,b} UNION s`] THEN
  REWRITE_TAC[GSYM HULL_UNION_RIGHT]);;

let MOI_SCX_DCONE = prove
 (`!(bb:real^2->bool) b0 (f2:real^2->real^2) g2 eps.
     polytope bb /\ b0 IN interior bb /\
     pl_homeomorphism ((:real^2),(:real^2)) (f2,g2) /\
     (!x. ~(x IN interior bb) ==> f2 x = x) /\ &0 < eps
     ==> ?f g. pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
               (!x. (f x)$3 = x$3) /\
               (!x. ~(x IN convex hull ((moi_scx_e b0 + eps % basis 3) INSERT
                                        (moi_scx_e b0 + --eps % basis 3) INSERT
                                        IMAGE moi_scx_e bb)) ==> f x = x) /\
               (!u. u IN bb ==> f (moi_scx_e u) = moi_scx_e (f2 u))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex (bb:real^2->bool) /\ (b0:real^2) IN bb /\ ~(bb = {}) /\
                ~(eps = &0) /\ ~(--eps = &0)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; REAL_LT_IMP_NZ; REAL_NEG_EQ_0] THEN
    MP_TAC(ISPEC `bb:real^2->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(b0:real^2) IN interior bb` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`f2:real^2->real^2`; `g2:real^2->real^2`;
                 `interior bb:real^2->bool`; `bb:real^2->bool`] MOI_SCX_FIX_IMAGE) THEN
  ASM_REWRITE_TAC[INTERIOR_SUBSET] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`bb:real^2->bool`; `f2:real^2->real^2`; `g2:real^2->real^2`]
    MOI_SCX_LIFT_PLH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `convex (IMAGE moi_scx_e bb) /\ compact (IMAGE moi_scx_e bb) /\
    polytope (IMAGE moi_scx_e bb) /\ moi_scx_e b0 IN IMAGE moi_scx_e bb /\
    ~(IMAGE moi_scx_e bb = {}) /\
    (!x. x IN IMAGE moi_scx_e bb ==> x$3 = &0) /\ (moi_scx_e b0)$3 = &0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONVEX_LINEAR_IMAGE; COMPACT_LINEAR_IMAGE; POLYTOPE_LINEAR_IMAGE;
                 POLYTOPE_IMP_COMPACT; MOI_SCX_EP; FUN_IN_IMAGE; FORALL_IN_IMAGE;
                 IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (IMAGE moi_scx_e bb)` ASSUME_TAC THENL
   [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the cone sets are closed and meet in the base *)
  SUBGOAL_THEN
   `!c. closed (UNIONS {segment[moi_scx_e b0 + c % basis 3,x] |
                        x IN IMAGE moi_scx_e bb})`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`IMAGE moi_scx_e bb`; `moi_scx_e b0 + c % basis 3`]
      CONVEX_HULL_INSERT_SEGMENTS) THEN
    REWRITE_TAC[MATCH_MP HULL_P (ASSUME `convex (IMAGE moi_scx_e bb)`)] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
    MATCH_MP_TAC COMPACT_INSERT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE moi_scx_e bb`; `moi_scx_e b0`; `eps:real`]
    MOI_SCX_CONE_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* visibility, the two cone maps *)
  MP_TAC(ISPECL [`IMAGE moi_scx_e bb`; `moi_scx_e b0`; `eps:real`] MOI_SCX_APEX) THEN
  MP_TAC(ISPECL [`IMAGE moi_scx_e bb`; `moi_scx_e b0`; `--eps:real`] MOI_SCX_APEX) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE moi_scx_e bb`; `IMAGE moi_scx_e bb`;
                 `moi_scx_e b0 + eps % basis 3`; `moi_scx_e b0 + eps % basis 3`;
                 `moi_scx_e o f2 o moi_scx_pr`; `moi_scx_e o g2 o moi_scx_pr`]
                MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "eu")) THEN
  MP_TAC(ISPECL [`IMAGE moi_scx_e bb`; `IMAGE moi_scx_e bb`;
                 `moi_scx_e b0 + --eps % basis 3`; `moi_scx_e b0 + --eps % basis 3`;
                 `moi_scx_e o f2 o moi_scx_pr`; `moi_scx_e o g2 o moi_scx_pr`]
                MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ed")) THEN
  ABBREV_TAC `cu = UNIONS {segment[moi_scx_e b0 + eps % basis 3,x] |
                           x IN IMAGE moi_scx_e bb}` THEN
  ABBREV_TAC `cd = UNIONS {segment[moi_scx_e b0 + --eps % basis 3,x] |
                           x IN IMAGE moi_scx_e bb}` THEN
  ABBREV_TAC `fu = moi_con_conemap (IMAGE moi_scx_e bb) (moi_scx_e b0 + eps % basis 3)
                     (moi_scx_e b0 + eps % basis 3) (moi_scx_e o f2 o moi_scx_pr)` THEN
  ABBREV_TAC `gu = moi_con_conemap (IMAGE moi_scx_e bb) (moi_scx_e b0 + eps % basis 3)
                     (moi_scx_e b0 + eps % basis 3) (moi_scx_e o g2 o moi_scx_pr)` THEN
  ABBREV_TAC `fd = moi_con_conemap (IMAGE moi_scx_e bb) (moi_scx_e b0 + --eps % basis 3)
                     (moi_scx_e b0 + --eps % basis 3) (moi_scx_e o f2 o moi_scx_pr)` THEN
  ABBREV_TAC `gd = moi_con_conemap (IMAGE moi_scx_e bb) (moi_scx_e b0 + --eps % basis 3)
                     (moi_scx_e b0 + --eps % basis 3) (moi_scx_e o g2 o moi_scx_pr)` THEN
  SUBGOAL_THEN `closed (cu:real^3->bool) /\ closed (cd:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["cu"; "cd"] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the glued map on the bipyramid *)
  MP_TAC(ISPECL [`cu:real^3->bool`; `cd:real^3->bool`; `cu:real^3->bool`;
                 `cd:real^3->bool`; `fu:real^3->real^3`; `gu:real^3->real^3`;
                 `fd:real^3->real^3`; `gd:real^3->real^3`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "eu" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^3) IN IMAGE moi_scx_e bb`)]) THEN
      USE_THEN "ed" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(x:real^3) IN IMAGE moi_scx_e bb`)]);
      MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `IMAGE (moi_scx_e o f2 o moi_scx_pr) (IMAGE moi_scx_e bb)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `!f g (s:real^3->bool). (!x. x IN s ==> f x = (g:real^3->real^3) x)
                                 ==> IMAGE f s = IMAGE g s`) THEN
        USE_THEN "eu" ACCEPT_TAC;
        ASM_REWRITE_TAC[MOI_SCX_IMAGE_LIFT]]];
    ALL_TAC] THEN
  ABBREV_TAC `f0 = \x:real^3. if x IN cu then fu x else (fd:real^3->real^3) x` THEN
  ABBREV_TAC `g0 = \y:real^3. if y IN cu then gu y else (gd:real^3->real^3) y` THEN
  DISCH_TAC THEN
  (* the bipyramid is a polytope equal to cu UNION cd *)
  SUBGOAL_THEN
   `convex hull ((moi_scx_e b0 + eps % basis 3) INSERT
                 (moi_scx_e b0 + --eps % basis 3) INSERT IMAGE moi_scx_e bb) =
    cu UNION cd`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`IMAGE moi_scx_e bb`; `moi_scx_e b0`; `eps % basis 3:real^3`]
      MOI_SCX_BIPYR) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `m - e % b:real^3 = m + --e % b`];
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope (cu UNION cd:real^3->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `cu UNION cd:real^3->bool`)) THEN
    MATCH_MP_TAC MOI_SCX_CONE_POLYTOPE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the cone maps preserve levels and fix the frontier *)
  SUBGOAL_THEN
   `!c. (c = eps \/ c = --eps)
        ==> !x. x IN UNIONS {segment[moi_scx_e b0 + c % basis 3,z] |
                             z IN IMAGE moi_scx_e bb}
                ==> (moi_con_conemap (IMAGE moi_scx_e bb) (moi_scx_e b0 + c % basis 3)
                      (moi_scx_e b0 + c % basis 3) (moi_scx_e o f2 o moi_scx_pr) x)$3 =
                    x$3 /\
                    (~(moi_con_conemap (IMAGE moi_scx_e bb)
                        (moi_scx_e b0 + c % basis 3) (moi_scx_e b0 + c % basis 3)
                        (moi_scx_e o f2 o moi_scx_pr) x = x)
                     ==> x IN interior (cu UNION cd))`
  MP_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(c = &0)` ASSUME_TAC THENL
     [FIRST_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (is_disj o concl)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`bb:real^2->bool`; `b0:real^2`; `f2:real^2->real^2`; `c:real`;
                   `x:real^3`] MOI_SCX_CONEMAP_FACTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^2` (X_CHOOSE_THEN `r:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          SUBST1_TAC)))))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `x:real^3`)) THEN
    REWRITE_TAC[MOI_SCX_CONE_COORDS] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((f2:real^2->real^2) u = u) /\ ~(r = &0)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC
       `~((moi_scx_e b0 + c % basis 3) +
          r % (moi_scx_e ((f2:real^2->real^2) u) - (moi_scx_e b0 + c % basis 3)) =
          (moi_scx_e b0 + c % basis 3) +
          r % (moi_scx_e u - (moi_scx_e b0 + c % basis 3)))` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^2) IN interior bb` ASSUME_TAC THENL
     [UNDISCH_TAC `~((f2:real^2->real^2) u = u)` THEN
      UNDISCH_TAC `!x:real^2. ~(x IN interior bb) ==> (f2:real^2->real^2) x = x` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`bb:real^2->bool`; `b0:real^2`; `eps:real`; `c:real`;
                   `u:real^2`; `r:real`] MOI_SCX_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `eps:real` th) THEN
                       MP_TAC(SPEC `--eps:real` th)) THEN
  REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(LABEL_TAC "ld") THEN DISCH_THEN(LABEL_TAC "lu") THEN
  (* extension by the identity *)
  MP_TAC(ISPECL [`cu UNION cd:real^3->bool`; `f0:real^3->real^3`; `g0:real^3->real^3`]
    MOI_SA2_PLH_EXTEND_ID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    EXPAND_TAC "f0" THEN REWRITE_TAC[] THEN COND_CASES_TAC THENL
     [USE_THEN "lu" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN cu`)) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[];
      SUBGOAL_THEN `(x:real^3) IN cd` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN cu UNION cd` THEN ASM_REWRITE_TAC[IN_UNION];
        ALL_TAC] THEN
      USE_THEN "ld" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN cd`)) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^3. if x IN cu UNION cd then (f0:real^3->real^3) x else x`;
    `\x:real^3. if x IN cu UNION cd then (g0:real^3->real^3) x else x`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REWRITE_TAC[] THEN EXPAND_TAC "f0" THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THENL
     [USE_THEN "lu" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN cu`)) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[];
      SUBGOAL_THEN `(x:real^3) IN cd` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN cu UNION cd` THEN ASM_REWRITE_TAC[IN_UNION];
        ALL_TAC] THEN
      USE_THEN "ld" (MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN cd`)) THEN ASM_REWRITE_TAC[] THEN
      MESON_TAC[]];
    SIMP_TAC[];
    X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
    SUBGOAL_THEN `moi_scx_e u IN IMAGE moi_scx_e bb` ASSUME_TAC THENL
     [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_scx_e u IN cu` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_scx_e u IN IMAGE moi_scx_e bb` THEN
      UNDISCH_TAC `(cu:real^3->bool) INTER cd = IMAGE moi_scx_e bb` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_UNION] THEN EXPAND_TAC "f0" THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "eu" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `moi_scx_e u IN IMAGE moi_scx_e bb`)]) THEN
    REWRITE_TAC[o_THM; MOI_SCX_EP]]);;

(* ------------------------------------------------------------------------- *)
(* LEVEL_CONVEXIFY in standard position (level x$3 = 0).                     *)
(* ------------------------------------------------------------------------- *)

let MOI_SCX_IMAGE_CONG = prove
 (`!(f:A->B) g s. (!x. x IN s ==> f x = g x) ==> IMAGE f s = IMAGE g s`,
  SET_TAC[]);;

let MOI_SCX_EP_INV = prove
 (`!x:real^3. x$3 = &0 ==> moi_scx_e (moi_scx_pr x) = x`,
  MESON_TAC[MOI_SCX_EP]);;

let MOI_SCX_EP_IMAGE = prove
 (`!s. s SUBSET {x:real^3 | x$3 = &0} ==> IMAGE moi_scx_e (IMAGE moi_scx_pr s) = s`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN GEN_REWRITE_TAC RAND_CONV [GSYM IMAGE_ID] THEN
  MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN ASM_SIMP_TAC[o_THM; MOI_SCX_EP_INV]);;

let MOI_SCX_SLAB_CONVEX = prove
 (`!e. convex {x:real^3 | --e <= x$3 /\ x$3 <= e}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{x:real^3 | --e <= x$3 /\ x$3 <= e} =
                {x | x$3 >= --e} INTER {x | x$3 <= e}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; real_ge];
    MATCH_MP_TAC CONVEX_INTER THEN
    REWRITE_TAC[CONVEX_HALFSPACE_COMPONENT_GE; CONVEX_HALFSPACE_COMPONENT_LE]]);;

let MOI_SCX_STD = prove
 (`!d j (w:real^3->bool) p del.
     pl_cell_with_boundary 2 d j /\ d SUBSET {x | x$3 = &0} /\
     convex w /\ open w /\ d SUBSET w /\ p IN j /\ &0 < del
     ==> ?f g t. pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\
                 (!x. (f x)$3 = x$3) /\
                 (!x. ~(x IN w) \/ del <= abs(x$3) ==> f x = x) /\
                 &2 simplex t /\ IMAGE f d = t /\
                 IMAGE f j = relative_frontier t /\ {f p} face_of t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d /\ compact d` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `ff:real^3->real^3`
      (X_CHOOSE_THEN `gg:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN d /\ p$3 = &0 /\ p IN w` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`d:real^3->bool`; `j:real^3->bool`] MOI_SCX_TO_PLANE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE moi_scx_e (IMAGE moi_scx_pr d) = d /\
                IMAGE moi_scx_e (IMAGE moi_scx_pr j) = j` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_SCX_EP_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE moi_scx_pr d) /\
                IMAGE moi_scx_pr j SUBSET IMAGE moi_scx_pr d /\
                moi_scx_pr p IN IMAGE moi_scx_pr j` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_LINEAR_IMAGE; MOI_SCX_EP; IMAGE_SUBSET; FUN_IN_IMAGE];
    ALL_TAC] THEN
  ABBREV_TAC `d2 = IMAGE moi_scx_pr d` THEN ABBREV_TAC `j2 = IMAGE moi_scx_pr j` THEN
  SUBGOAL_THEN `convex {u:real^2 | moi_scx_e u IN w} /\
                open {u:real^2 | moi_scx_e u IN w} /\
                d2 SUBSET {u:real^2 | moi_scx_e u IN w}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_LINEAR_PREIMAGE THEN ASM_REWRITE_TAC[MOI_SCX_EP];
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; MOI_SCX_EP];
      EXPAND_TAC "d2" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3)$3 = &0` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[MOI_SCX_EP_INV] THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d2:real^2->bool`; `{u:real^2 | moi_scx_e u IN w}`]
    MOI_SCX_POLYTOPE_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `bb:real^2->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`d2:real^2->bool`; `j2:real^2->bool`; `interior bb:real^2->bool`;
                 `moi_scx_pr p`] MOI_SCX_PLANE) THEN
  ASM_REWRITE_TAC[OPEN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `t2:real^2->bool` (X_CHOOSE_THEN `f2:real^2->real^2`
    (X_CHOOSE_THEN `g2:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `moi_scx_pr p IN interior bb /\ d2 SUBSET bb` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `bb:real^2->bool` INTERIOR_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC [`moi_scx_pr p IN j2`; `(j2:real^2->bool) SUBSET d2`;
                           `(d2:real^2->bool) SUBSET interior bb`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(p:real^3,r) SUBSET w` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open (w:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `eps = min (r / &2) (del / &2)` THEN
  SUBGOAL_THEN `&0 < eps /\ eps < r /\ eps < del` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`bb:real^2->bool`; `moi_scx_pr p`; `f2:real^2->real^2`;
                 `g2:real^2->real^2`; `eps:real`] MOI_SCX_DCONE) THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_SCX_EP_INV] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:real^3->real^3` (X_CHOOSE_THEN `gg:real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "off") (LABEL_TAC "val")))))) THEN
  MAP_EVERY EXISTS_TAC [`ff:real^3->real^3`; `gg:real^3->real^3`;
                        `IMAGE moi_scx_e t2`] THEN
  ASM_REWRITE_TAC[] THEN
  (* the bipyramid lies in w and in the slab of half-width eps *)
  SUBGOAL_THEN
   `convex hull ((p + eps % basis 3) INSERT (p + --eps % basis 3) INSERT
                 IMAGE moi_scx_e bb) SUBSET
    w INTER {x:real^3 | --eps <= x$3 /\ x$3 <= eps}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_SIMP_TAC[CONVEX_INTER; MOI_SCX_SLAB_CONVEX] THEN
    SUBGOAL_THEN `!c. abs c < r ==> (p + c % basis 3:real^3) IN w` ASSUME_TAC THENL
     [GEN_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `ball(p:real^3,r) SUBSET w` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
      DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[dist; VECTOR_ARITH `p - (p + v) = --v:real^3`; NORM_NEG; NORM_MUL] THEN
      SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[INSERT_SUBSET; SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[MOI_SCX_COMP; MOI_SCX_EP; REAL_ADD_LID] THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN USE_THEN "off" MATCH_MP_TAC THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN w /\ --eps <= x$3 /\ x$3 <= eps` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((x:real^3) IN w) \/ del <= abs(x$3)` THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[SIMPLEX_LINEAR_IMAGE_EQ; MOI_SCX_EP];
    SUBGOAL_THEN `IMAGE (ff:real^3->real^3) d = IMAGE ff (IMAGE moi_scx_e d2)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE moi_scx_e t2 = IMAGE moi_scx_e (IMAGE (f2:real^2->real^2) d2)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
    USE_THEN "val" MATCH_MP_TAC THEN ASM SET_TAC[];
    SUBGOAL_THEN `IMAGE (ff:real^3->real^3) j = IMAGE ff (IMAGE moi_scx_e j2)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SIMP_TAC[RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE; MOI_SCX_EP] THEN
    SUBGOAL_THEN `IMAGE moi_scx_e (relative_frontier t2) =
                  IMAGE moi_scx_e (IMAGE (f2:real^2->real^2) j2)`
    SUBST1_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC MOI_SCX_IMAGE_CONG THEN
    REWRITE_TAC[o_THM] THEN X_GEN_TAC `u:real^2` THEN DISCH_TAC THEN
    USE_THEN "val" MATCH_MP_TAC THEN ASM SET_TAC[];
    SUBGOAL_THEN `(ff:real^3->real^3) p = moi_scx_e (f2 (moi_scx_pr p))` SUBST1_TAC THENL
     [GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM(MATCH_MP MOI_SCX_EP_INV
        (ASSUME `(p:real^3)$3 = &0`))] THEN
      USE_THEN "val" MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{moi_scx_e ((f2:real^2->real^2) (moi_scx_pr p))} =
                  IMAGE moi_scx_e {f2 (moi_scx_pr p)}` SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
    ASM_SIMP_TAC[FACE_OF_LINEAR_IMAGE; MOI_SCX_EP]]);;

(* ------------------------------------------------------------------------- *)
(* Isometric coordinates adapted to the level a dot x = h, and the main     *)
(* theorem LEVEL_CONVEXIFY.                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_SCX_FRAME = prove
 (`!(a:real^3) h.
     ~(a = vec 0)
     ==> ?l l' q. linear l /\ linear l' /\ (!x. l' (l x) = x) /\ (!y. l (l' y) = y) /\
                  (!y:real^3. a dot (q + l y) = h + norm a * y$3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `norm(inv(norm a) % (a:real^3)) = norm(basis 3:real^3)` MP_TAC THENL
   [SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH; NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; NORM_EQ_0];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (ONCE_REWRITE_RULE[EQ_SYM_EQ]
    ORTHOGONAL_TRANSFORMATION_EXISTS)) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^3->real^3` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP ORTHOGONAL_TRANSFORMATION_INVERSE) THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^3->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`l:real^3->real^3`; `l':real^3->real^3`;
                        `(h / ((a:real^3) dot a)) % a`] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[orthogonal_transformation]) THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[DOT_RADD; DOT_RMUL] THEN
  SUBGOAL_THEN `~((a:real^3) dot a = &0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[DOT_EQ_0]; ALL_TAC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(a:real^3) = norm a % (l:real^3->real^3) (basis 3)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `inv (norm (a:real^3)) % a = (l:real^3->real^3) (basis 3)`)) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; NORM_EQ_0; VECTOR_MUL_LID];
    ALL_TAC] THEN
  REWRITE_TAC[DOT_LMUL] THEN AP_TERM_TAC THEN
  ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3; ARITH]);;

let MOI_SCX_AFFINE_IMAGE = prove
 (`!(l:real^3->real^3) q t.
     IMAGE (\x. q + l x) t = IMAGE (\x. q + x) (IMAGE l t)`,
  REWRITE_TAC[GSYM IMAGE_o; o_DEF]);;

let MOI_SCX_AFFINE_FACE = prove
 (`!(l:real^3->real^3) q c s.
     linear l /\ (!x y. l x = l y ==> x = y)
     ==> (IMAGE (\x. q + l x) c face_of IMAGE (\x. q + l x) s <=> c face_of s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MOI_SCX_AFFINE_IMAGE] THEN
  REWRITE_TAC[FACE_OF_TRANSLATION_EQ] THEN
  MATCH_MP_TAC FACE_OF_LINEAR_IMAGE THEN ASM_REWRITE_TAC[]);;

let MOI_SCX_AFFINE_SIMPLEX = prove
 (`!(l:real^3->real^3) q s n.
     linear l /\ (!x y. l x = l y ==> x = y)
     ==> (n simplex (IMAGE (\x. q + l x) s) <=> n simplex s)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MOI_SCX_AFFINE_IMAGE] THEN
  REWRITE_TAC[SIMPLEX_TRANSLATION_EQ] THEN
  MATCH_MP_TAC SIMPLEX_LINEAR_IMAGE_EQ THEN ASM_REWRITE_TAC[]);;

let LEVEL_CONVEXIFY = prove
 (MOI_SCH3_LEVEL_CONVEXIFY,
  MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `a:real^3`; `h:real`; `j:real^3->bool`;
                       `d:real^3->bool`; `pt:real^3`; `w:real^3->bool`; `del:real`] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`a:real^3`; `h:real`] MOI_SCX_FRAME) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^3->real^3` (X_CHOOSE_THEN `l':real^3->real^3`
    (X_CHOOSE_THEN `q0:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `!x y. (l:real^3->real^3) x = l y ==> x = y` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(a:real^3)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x:real^3. q0 + l (l' (x - q0)) = x) /\ (!y:real^3. l' ((q0 + l y) - q0) = y) /\
    (!x:real^3. a dot x = h + norm a * (l' (x - q0))$3)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `(q0 + v) - q0:real^3 = v`] THEN
    CONJ_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(l':real^3->real^3) (x - q0)` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `norm(a:real^3)`)) (concl th))) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `q0 + x - q0:real^3 = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism ((:real^3),(:real^3))
                  ((\y. q0 + (l:real^3->real^3) y),(\x. l' (x - q0)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SS2_AFFINE_PLH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* d lies in w *)
  SUBGOAL_THEN `(d:real^3->bool) SUBSET w /\ (j:real^3->bool) SUBSET d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull (j:real^3->bool)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PLANE_CELL_HULL THEN REWRITE_TAC[moi_sch3_plane_cell] THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY EXISTS_TAC [`a:real^3`; `h:real`] THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HULL_MINIMAL THEN ASM SET_TAC[]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the base point of the vertex *)
  SUBGOAL_THEN `?p0:real^3. p0 IN j /\ (pt IN j ==> p0 = pt)` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(pt:real^3) IN j` THENL
     [EXISTS_TAC `pt:real^3` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`1`; `j:real^3->bool`] MOI_SCD_PL_SPHERE_NONEMPTY) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC MOI_SCX_CELL_SPHERE THEN EXISTS_TAC `d:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY]]];
    ALL_TAC] THEN
  (* the standard-position problem *)
  MP_TAC(ISPECL [`IMAGE (\x. (l':real^3->real^3) (x - q0)) d`;
                 `IMAGE (\x. (l':real^3->real^3) (x - q0)) j`;
                 `{y:real^3 | q0 + (l:real^3->real^3) y IN w}`;
                 `(l':real^3->real^3) (p0 - q0)`; `del / norm(a:real^3)`]
    MOI_SCX_STD) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_SS2_CELL_EQ_FSA] THEN MATCH_MP_TAC MOI_SS2_FSA_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`(:real^3)`; `(:real^3)`; `\y. q0 + (l:real^3->real^3) y`] THEN
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
      ASM_REWRITE_TAC[SUBSET_UNIV; GSYM MOI_SS2_CELL_EQ_FSA];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(a:real^3) dot x = h` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[REAL_ARITH `h + n * t = h <=> n * t = &0`; REAL_ENTIRE] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      REWRITE_TAC[convex; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`y1:real^3`; `y2:real^3`; `u:real`; `v:real`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `q0 + (l:real^3->real^3) (u % y1 + v % y2) =
                    u % (q0 + l y1) + v % (q0 + l y2)` SUBST1_TAC THENL
       [REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear (l:real^3->real^3)`);
                    MATCH_MP LINEAR_CMUL (ASSUME `linear (l:real^3->real^3)`)] THEN
        REWRITE_TAC[VECTOR_ADD_LDISTRIB] THEN
        SUBGOAL_THEN `q0:real^3 = (u + v) % q0` (fun th ->
          GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [th]) THENL
         [ASM_REWRITE_TAC[VECTOR_MUL_LID]; ALL_TAC] THEN
        VECTOR_ARITH_TAC;
        UNDISCH_TAC `convex (w:real^3->bool)` THEN REWRITE_TAC[convex] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
      GEN_TAC THEN MATCH_MP_TAC CONTINUOUS_ADD THEN
      ASM_SIMP_TAC[CONTINUOUS_CONST; LINEAR_CONTINUOUS_AT; ETA_AX];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM SET_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `p0:real^3` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_LT_DIV]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':real^3->real^3` (X_CHOOSE_THEN `g':real^3->real^3`
    (X_CHOOSE_THEN `t':real^3->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`(:real^3)`; `(:real^3)`; `(:real^3)`;
                 `\x. (l':real^3->real^3) (x - q0)`; `\y. q0 + (l:real^3->real^3) y`;
                 `f':real^3->real^3`; `g':real^3->real^3`] PL_HOMEOMORPHISM_COMPOSE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`(:real^3)`; `(:real^3)`; `(:real^3)`;
                 `(f':real^3->real^3) o (\x. (l':real^3->real^3) (x - q0))`;
                 `(\y. q0 + (l:real^3->real^3) y) o (g':real^3->real^3)`;
                 `\y. q0 + (l:real^3->real^3) y`; `\x. (l':real^3->real^3) (x - q0)`]
    PL_HOMEOMORPHISM_COMPOSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `(\y. q0 + (l:real^3->real^3) y) o
              (f':real^3->real^3) o (\x. (l':real^3->real^3) (x - q0))` THEN
  EXISTS_TAC `((\y. q0 + (l:real^3->real^3) y) o (g':real^3->real^3)) o
              (\x. (l':real^3->real^3) (x - q0))` THEN
  EXISTS_TAC `IMAGE (\y. q0 + (l:real^3->real^3) y) t'` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[o_THM] THEN
    REWRITE_TAC[REAL_ARITH `(h + n * t) - h = n * t`; REAL_ABS_MUL; REAL_ABS_NORM] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(f':real^3->real^3) ((l':real^3->real^3) (x - q0)) = l' (x - q0)`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [DISJ1_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN
        UNDISCH_TAC `del <= norm(a:real^3) * abs((l':real^3->real^3) (x - q0)$3)` THEN
        GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [REAL_MUL_SYM] THEN REWRITE_TAC[]];
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`l:real^3->real^3`; `q0:real^3`; `t':real^3->bool`; `&2:int`]
      MOI_SCX_AFFINE_SIMPLEX) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`l:real^3->real^3`; `q0:real^3`; `t':real^3->bool`]
      MOI_SS2_AFFINE_IMAGES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    SUBGOAL_THEN `p0:real^3 = pt` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN
     `{q0 + (l:real^3->real^3) ((f':real^3->real^3) (l' (pt - q0)))} =
      IMAGE (\y. q0 + l y) {f' (l' (pt - q0))}` SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
    MP_TAC(ISPECL [`l:real^3->real^3`; `q0:real^3`;
                   `{(f':real^3->real^3) ((l':real^3->real^3) (pt - q0))}`;
                   `t':real^3->bool`]
      MOI_SCX_AFFINE_FACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN ACCEPT_TAC]);;

