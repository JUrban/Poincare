(* ========================================================================= *)
(* pc_moi_s35_ext: the Sec 35 unit s35_ext (part a), main theorem           *)
(* ONE_DISK_EXT = MOI_S35_ONE_DISK_EXT (pc_moi_s35_stmt.ml, section 7.4): a *)
(* PL homeomorphism of one boundary disk of a PL 3-ball onto a boundary     *)
(* disk of another extends to the balls taking a second boundary disk onto  *)
(* a second boundary disk.  Method: the frontier of the ball minus both     *)
(* open disks is an annulus (plane annulus theorem MOI_S5C_ANN2 of          *)
(* pc_moi_s35_minc after a disk chart); the sphere map is g0 on the first   *)
(* disk, an annulus chart with prescribed outer map (MOI_S5C_ANN_OUTER) and *)
(* a cell extension on the second disk; it extends to the balls             *)
(* (MOI_SCD_COR_EXTEND_BALL).  Moise GTM 47, p.251.                         *)
(* ========================================================================= *)

needs "src/pc_moi_s35_minc.ml";;
needs "src/pc_moi_sch3_s2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Cells: the boundary of a PL cell is unique, a PL homeomorphism of     *)
(* cells maps boundary onto boundary, and the frontier of a PL 3-ball in    *)
(* real^3 is a PL 2-sphere.                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S5E_CELL_BOUNDARY_UNIQUE = prove
 (`!n (s:real^N->bool) b1 b2.
     pl_cell_with_boundary n s b1 /\ pl_cell_with_boundary n s b2 ==> b1 = b2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k1:real^N->bool` (X_CHOOSE_THEN `f1:real^N->real^N`
     (X_CHOOSE_THEN `g1:real^N->real^N` STRIP_ASSUME_TAC)))
   (X_CHOOSE_THEN `k2:real^N->bool` (X_CHOOSE_THEN `f2:real^N->real^N`
     (X_CHOOSE_THEN `g2:real^N->real^N` STRIP_ASSUME_TAC)))) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `homeomorphism (k1:real^N->bool,k2)
                 ((g2:real^N->real^N) o f1,(g1:real^N->real^N) o (f2:real^N->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `s:real^N->bool` THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pl_homeomorphism]) THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k1:real^N->bool`; `k2:real^N->bool`;
                 `(g2:real^N->real^N) o (f1:real^N->real^N)`;
                 `(g1:real^N->real^N) o (f2:real^N->real^N)`]
    MOI_FM3_HOMEO_RELATIVE_FRONTIER) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism]) THEN
  MATCH_MP_TAC(SET_RULE
   `(!y. y IN s ==> (f2:real^N->real^N) ((g2:real^N->real^N) y) = y) /\ t SUBSET s
    ==> t = IMAGE f2 (IMAGE g2 t)`) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `relative_frontier (k1:real^N->bool) SUBSET k1` MP_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_S5E_PLH_CELL_BOUNDARY = prove
 (`!(d:real^3->bool) j (e:real^3->bool) i (g:real^3->real^3) g'.
     pl_cell_with_boundary 2 d j /\ pl_cell_with_boundary 2 e i /\
     pl_homeomorphism (d,e) (g,g')
     ==> IMAGE g j = i`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S5E_CELL_BOUNDARY_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`2`; `e:real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S5C_CELL_PLH THEN
  MAP_EVERY EXISTS_TAC [`d:real^3->bool`; `g':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 (e:real^3->bool) i` THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN MESON_TAC[]);;

let MOI_S5E_BALL_FRONTIER_SPHERE = prove
 (`!u:real^3->bool. pl_ball 3 u ==> pl_sphere 2 (frontier u)`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCD_BALL_BOUNDARY_PLH THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. A PL 2-sphere minus two disjoint open boundary-disks is an annulus     *)
(* (the complement of the first disk is a disk, DISK_COMPLEMENT; in a plane *)
(* chart of it the second disk lies inside the square, MOI_S5C_ANN2).        *)
(* ------------------------------------------------------------------------- *)

let MOI_S5E_SQ2_CELL = prove
 (`pl_cell_with_boundary 2 (interval[--vector[&2;&2]:real^2,vector[&2;&2]])
     (relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) /\
   interval[--vector[&2;&2]:real^2,vector[&2;&2]] =
   relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) UNION
   inside(relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])) /\
   interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
   relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) =
   inside(relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`,
  MP_TAC(SPEC `&2` MOI_S5C_SQ_JORDAN) THEN REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5C_POLYTOPE_CELL THEN
    REWRITE_TAC[POLYTOPE_INTERVAL; INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
    REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) =
    interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&2;&2],vector[&2;&2])`
  SUBST1_TAC THENL
   [W(MP_TAC o PART_MATCH (lhand o rand) RELATIVE_FRONTIER_NONEMPTY_INTERIOR o
      lhand o snd) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INTERIOR_INTERVAL; INTERVAL_NE_EMPTY] THEN
      REWRITE_TAC[DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
      REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[FRONTIER_CLOSED_INTERVAL]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM INTERIOR_INTERVAL] THEN
  MP_TAC(ISPEC `interval[--vector[&2;&2]:real^2,vector[&2;&2]]` INTERIOR_SUBSET) THEN
  SET_TAC[]);;

(* The boundary of a 2-cell is a PL circle (as MOI_SCX_CELL_SPHERE of       *)
(* pc_moi_sch3_cvx, which is outside this load closure).                     *)

let MOI_S5E_CELL_SPHERE1 = prove
 (`!(d:real^N->bool) j. pl_cell_with_boundary 2 d j ==> pl_sphere 1 j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5C_PLH_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `d:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; SIMPLEX_IMP_CLOSED];
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `1` THEN
    MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 + 1 = 2`]]);;

(* PL homeomorphisms between cells preserving boundaries (as MOI_S5H_CELL_PLH *)
(* of pc_moi_s35_charts, which is outside this load closure).                 *)

let MOI_S5E_CELL_PLH = prove
 (`!n (s:real^M->bool) bs (t:real^N->bool) bt.
     pl_cell_with_boundary n s bs /\ pl_cell_with_boundary n t bt
     ==> ?f g. pl_homeomorphism (s,t) (f,g) /\ IMAGE f bs = bt`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k1:real^M->bool` (X_CHOOSE_THEN `f1:real^M->real^M`
     (X_CHOOSE_THEN `g1:real^M->real^M` STRIP_ASSUME_TAC)))
   (X_CHOOSE_THEN `k2:real^N->bool` (X_CHOOSE_THEN `f2:real^N->real^N`
     (X_CHOOSE_THEN `g2:real^N->real^N` STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`k1:real^M->bool`; `k2:real^N->bool`; `&n:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^M->real^N` (X_CHOOSE_THEN `q:real^N->real^M`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `(f2:real^N->real^N) o (p:real^M->real^N) o (g1:real^M->real^M)` THEN
  EXISTS_TAC `((f1:real^M->real^M) o (q:real^N->real^M)) o (g2:real^N->real^N)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k2:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k1:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `IMAGE (g1:real^M->real^M) (IMAGE f1 (relative_frontier k1)) =
                relative_frontier k1` SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(!z:real^M. z IN s ==> (g:real^M->real^M)((f:real^M->real^M) z) = z)
                           ==> IMAGE g (IMAGE f s) = s`) THEN
    X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    UNDISCH_TAC `pl_homeomorphism (k1:real^M->bool,s:real^M->bool)
                    ((f1:real^M->real^M),(g1:real^M->real^M))` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(z:real^M) IN relative_frontier k1` THEN
    REWRITE_TAC[relative_frontier; IN_DIFF] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; CLOSURE_CLOSED];
    UNDISCH_TAC `pl_homeomorphism (relative_frontier k1:real^M->bool,
                                   relative_frontier k2:real^N->bool)
                    ((p:real^M->real^N),(q:real^N->real^M))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism]]);;

let MOI_S5E_BIJ_DIFF = prove
 (`!(f:real^3->real^2) g d t p q.
     (!x. x IN d ==> g (f x) = x) /\ (!y. y IN t ==> f (g y) = y) /\
     IMAGE f d = t /\ IMAGE g t = d /\ p SUBSET d /\ q SUBSET p
     ==> IMAGE g (t DIFF (IMAGE f p DIFF IMAGE f q)) = d DIFF (p DIFF q)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t DIFF (IMAGE (f:real^3->real^2) p DIFF IMAGE f q) =
                IMAGE f (d DIFF (p DIFF q))` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM IMAGE_o] THEN
  MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (h:real^3->real^3) x = x)
                         ==> IMAGE h s = s`) THEN
  REWRITE_TAC[o_THM; IN_DIFF] THEN ASM_MESON_TAC[]);;

let MOI_S5E_SPHERE_ANNULUS = prove
 (`!(s:real^3->bool) d0 j0 d1 j1.
     pl_sphere 2 s /\ pl_cell_with_boundary 2 d0 j0 /\ pl_cell_with_boundary 2 d1 j1 /\
     d0 SUBSET s /\ d1 SUBSET s /\ DISJOINT d0 d1
     ==> pl_annulus_with_ends ((s DIFF (d0 UNION d1)) UNION j0 UNION j1) j1 j0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(j0:real^3->bool) SUBSET d0 /\ (j1:real^3->bool) SUBSET d1 /\
                compact d0 /\ compact d1 /\ compact j0 /\ compact j1`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S5C_CELL_COMPACT; MOI_S5C_CELL_COMPACT2]; ALL_TAC] THEN
  ABBREV_TAC `d = (s DIFF d0) UNION (j0:real^3->bool)` THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (d:real^3->bool) j0` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN MATCH_MP_TAC DISK_COMPLEMENT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d1:real^3->bool) SUBSET d DIFF j0` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(d1:real^3->bool) SUBSET d` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(j0:real^3->bool) SUBSET d` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN SET_TAC[]; ALL_TAC] THEN
  (* a plane chart of d taking j0 onto the square circle *)
  MP_TAC(SPEC `&2` MOI_S5C_SQ_JORDAN) THEN REWRITE_TAC[REAL_ARITH `&0 < &2`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`2`; `d:real^3->bool`; `j0:real^3->bool`;
                 `interval[--vector[&2;&2]:real^2,vector[&2;&2]]`;
                 `relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])`]
    MOI_S5E_CELL_PLH) THEN
  ASM_REWRITE_TAC[MOI_S5E_SQ2_CELL] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^2` (X_CHOOSE_THEN `psi':real^2->real^3`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `q2 = interval[--vector[&2;&2]:real^2,vector[&2;&2]]` THEN
  MP_TAC MOI_S5E_SQ2_CELL THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
    concl th = `pl_homeomorphism (d:real^3->bool,q2:real^2->bool)
                  ((psi:real^3->real^2),(psi':real^2->real^3))`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    concl th = `homeomorphism (d:real^3->bool,q2:real^2->bool)
                  ((psi:real^3->real^2),(psi':real^2->real^3))`)) THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (IMAGE (psi:real^3->real^2) d1) (IMAGE psi j1)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5C_CELL_PLH THEN
    MAP_EVERY EXISTS_TAC [`d1:real^3->bool`; `psi':real^2->real^3`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S5C_PLH_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`d:real^3->bool`; `q2:real^2->bool`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC MOI_S5C_CELL_POLYHEDRON THEN
      MAP_EVERY EXISTS_TAC [`2`; `j1:real^3->bool`] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `pl_cell_with_boundary 2 (q2:real^2->bool) (relative_frontier q2)` THEN
      REWRITE_TAC[pl_cell_with_boundary] THEN MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `x = IMAGE (psi:real^3->real^2) d1` THEN
  ABBREV_TAC `k = IMAGE (psi:real^3->real^2) j1` THEN
  SUBGOAL_THEN `(x:real^2->bool) SUBSET q2 DIFF relative_frontier q2` ASSUME_TAC THENL
   [EXPAND_TAC "x" THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (psi:real^3->real^2) j0 = relative_frontier q2`)) THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN d /\ ~(y IN j0)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(d1:real^3->bool) SUBSET d DIFF j0` THEN
      UNDISCH_TAC `(y:real^3) IN d1` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (psi:real^3->real^2) d = q2` THEN
      UNDISCH_TAC `(y:real^3) IN d` THEN SET_TAC[];
      REWRITE_TAC[IN_IMAGE; NOT_EXISTS_THM] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `y:real^3 = z` (fun th ->
        UNDISCH_TAC `~((y:real^3) IN j0)` THEN REWRITE_TAC[th] THEN ASM_REWRITE_TAC[]) THEN
      MP_TAC(MATCH_MP (ASSUME
        `!x. x IN d ==> (psi':real^2->real^3) ((psi:real^3->real^2) x) = x`)
        (ASSUME `(y:real^3) IN d`)) THEN
      SUBGOAL_THEN `(z:real^3) IN d` ASSUME_TAC THENL
       [UNDISCH_TAC `(j0:real^3->bool) SUBSET d` THEN
        UNDISCH_TAC `(z:real^3) IN j0` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(MATCH_MP (ASSUME
        `!x. x IN d ==> (psi':real^2->real^3) ((psi:real^3->real^2) x) = x`)
        (ASSUME `(z:real^3) IN d`)) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^2->bool) SUBSET inside(relative_frontier q2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `x:real^2->bool` THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["x"; "k"] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(x:real^2->bool) SUBSET q2 DIFF relative_frontier q2` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside k = (x:real^2->bool) DIFF k` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`x:real^2->bool`; `k:real^2->bool`] MOI_S5C_PLANE_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`x:real^2->bool`; `k:real^2->bool`] MOI_S5C_PLANE_FILL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `relative_frontier q2:real^2->bool`] MOI_S5C_ANN2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S5E_CELL_SPHERE1 THEN
    EXISTS_TAC `x:real^2->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(relative_frontier q2 UNION inside(relative_frontier q2)) DIFF inside k =
                q2 DIFF ((x:real^2->bool) DIFF k)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `pl_homeomorphism (q2 DIFF ((x:real^2->bool) DIFF k),
                                  IMAGE (psi':real^2->real^3) (q2 DIFF (x DIFF k)))
                                 (psi',psi)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5C_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`q2:real^2->bool`; `d:real^3->bool`] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_S5C_ANN_POLYHEDRON THEN
    MAP_EVERY EXISTS_TAC [`k:real^2->bool`; `relative_frontier q2:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q2 DIFF ((x:real^2->bool) DIFF k)`; `k:real^2->bool`;
                 `relative_frontier q2:real^2->bool`;
                 `IMAGE (psi':real^2->real^3) (q2 DIFF (x DIFF k))`;
                 `psi':real^2->real^3`; `psi:real^3->real^2`] MOI_S5C_ANN_TRANSFER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `IMAGE (psi':real^2->real^3) (q2 DIFF (x DIFF k)) =
    (s DIFF (d0 UNION d1)) UNION j0 UNION j1 /\
    IMAGE psi' k = j1 /\ IMAGE psi' (relative_frontier q2) = j0`
  (fun th -> REWRITE_TAC[th]) THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY EXPAND_TAC ["x"; "k"] THEN
    MP_TAC(ISPECL [`psi:real^3->real^2`; `psi':real^2->real^3`; `d:real^3->bool`;
                   `q2:real^2->bool`; `d1:real^3->bool`; `j1:real^3->bool`]
      MOI_S5E_BIJ_DIFF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "d" THEN
    ASM SET_TAC[];
    EXPAND_TAC "k" THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (h:real^3->real^3) x = x)
                           ==> IMAGE h s = s`) THEN
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (psi:real^3->real^2) j0 = relative_frontier q2`)) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (h:real^3->real^3) x = x)
                           ==> IMAGE h s = s`) THEN
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. The sphere map (g0 on the first disk, an annulus chart with prescribed *)
(* outer map, a cell extension on the second disk) and ONE_DISK_EXT.         *)
(* ------------------------------------------------------------------------- *)

let MOI_S5E_GLUE3 = prove
 (`!(a:real^3->bool) b c a' b' c' ja jc ja' jc' (f:real^3->real^3) f' g g' h h'.
     pl_homeomorphism (a,a') (f,f') /\ pl_homeomorphism (b,b') (g,g') /\
     pl_homeomorphism (c,c') (h,h') /\
     closed a /\ closed b /\ closed c /\ closed a' /\ closed b' /\ closed c' /\
     a INTER b = ja /\ b INTER c = jc /\ a INTER c = {} /\
     a' INTER b' = ja' /\ b' INTER c' = jc' /\ a' INTER c' = {} /\
     (!x. x IN ja ==> f x = g x) /\ (!x. x IN jc ==> g x = h x) /\
     IMAGE f ja = ja' /\ IMAGE g jc = jc'
     ==> ?k k'. pl_homeomorphism (a UNION b UNION c,a' UNION b' UNION c') (k,k') /\
                (!x. x IN a ==> k x = f x) /\ (!x. x IN c ==> k x = h x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `b:real^3->bool`; `a':real^3->bool`; `b':real^3->bool`;
                 `f:real^3->real^3`; `f':real^3->real^3`; `g:real^3->real^3`;
                 `g':real^3->real^3`] MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`a UNION b:real^3->bool`; `c:real^3->bool`; `a' UNION b':real^3->bool`;
                 `c':real^3->bool`;
                 `\x:real^3. if x IN a then (f:real^3->real^3) x else g x`;
                 `\y:real^3. if y IN a' then (f':real^3->real^3) y else g' y`;
                 `h:real^3->real^3`; `h':real^3->real^3`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ASM_SIMP_TAC[CLOSED_UNION] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER; IN_UNION] THEN STRIP_TAC THENL
       [UNDISCH_TAC `a INTER c:real^3->bool = {}` THEN ASM SET_TAC[];
        SUBGOAL_THEN `~((x:real^3) IN a)` (fun th -> REWRITE_TAC[th]) THENL
         [UNDISCH_TAC `a INTER c:real^3->bool = {}` THEN ASM SET_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]];
      SUBGOAL_THEN `(a UNION b) INTER c:real^3->bool = jc /\
                    (a' UNION b') INTER c':real^3->bool = jc'`
        STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (g:real^3->real^3) jc = jc'`)) THEN
      MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (u:real^3->real^3) x = v x)
                             ==> IMAGE u s = IMAGE v s`) THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((x:real^3) IN a)` (fun th -> REWRITE_TAC[th]) THEN
      UNDISCH_TAC `a INTER c:real^3->bool = {}` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o BETA_RULE) THEN
  EXISTS_TAC `\x:real^3. if x IN a UNION b
                         then (if x IN a then (f:real^3->real^3) x else g x)
                         else (h:real^3->real^3) x` THEN
  EXISTS_TAC `\y:real^3. if y IN a' UNION b'
                         then (if y IN a' then (f':real^3->real^3) y else g' y)
                         else (h':real^3->real^3) y` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `c':real^3->bool`)) (concl th) &&
      can (find_term ((=) `h':real^3->real^3`)) (concl th))) THEN
    REWRITE_TAC[UNION_ASSOC] THEN DISCH_THEN ACCEPT_TAC;
    ALL_TAC] THEN
  CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_REWRITE_TAC[IN_UNION] THEN
  SUBGOAL_THEN `~((x:real^3) IN a)` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `a INTER c:real^3->bool = {}` THEN ASM SET_TAC[]; ALL_TAC] THEN
  COND_CASES_TAC THEN REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM SET_TAC[]);;

let MOI_S5E_SPHERE_MAP = prove
 (`!(s:real^3->bool) s' d0 j0 d1 j1 e0 i0 e1 i1 (g0:real^3->real^3) g0'.
     pl_sphere 2 s /\ pl_sphere 2 s' /\
     pl_cell_with_boundary 2 d0 j0 /\ pl_cell_with_boundary 2 d1 j1 /\
     d0 SUBSET s /\ d1 SUBSET s /\ DISJOINT d0 d1 /\
     pl_cell_with_boundary 2 e0 i0 /\ pl_cell_with_boundary 2 e1 i1 /\
     e0 SUBSET s' /\ e1 SUBSET s' /\ DISJOINT e0 e1 /\
     pl_homeomorphism (d0,e0) (g0,g0')
     ==> ?h h'. pl_homeomorphism (s,s') (h,h') /\
                (!x. x IN d0 ==> h x = g0 x) /\ IMAGE h d1 = e1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(j0:real^3->bool) SUBSET d0 /\ (j1:real^3->bool) SUBSET d1 /\
                (i0:real^3->bool) SUBSET e0 /\ (i1:real^3->bool) SUBSET e1 /\
                compact d0 /\ compact d1 /\ compact e0 /\ compact e1 /\
                compact j0 /\ compact j1 /\ compact i0 /\ compact i1`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S5C_CELL_COMPACT; MOI_S5C_CELL_COMPACT2]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g0:real^3->real^3) j0 = i0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5E_PLH_CELL_BOUNDARY THEN
    MAP_EVERY EXISTS_TAC [`d0:real^3->bool`; `e0:real^3->bool`; `g0':real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `au = ((s:real^3->bool) DIFF (d0 UNION d1)) UNION j0 UNION j1` THEN
  ABBREV_TAC `aw = ((s':real^3->bool) DIFF (e0 UNION e1)) UNION i0 UNION i1` THEN
  SUBGOAL_THEN `pl_annulus_with_ends (au:real^3->bool) j1 j0 /\
                pl_annulus_with_ends (aw:real^3->bool) i1 i0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["au"; "aw"] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_S5E_SPHERE_ANNULUS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j1:real^3->bool) SUBSET au /\ (j0:real^3->bool) SUBSET au`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "au" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(d0:real^3->bool) INTER au = j0 /\ au INTER d1 = j1 /\
                (e0:real^3->bool) INTER aw = i0 /\ aw INTER e1 = i1 /\
                d0 UNION au UNION d1 = s /\ e0 UNION aw UNION e1 = s'`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["au"; "aw"] THEN
    MAP_EVERY UNDISCH_TAC [`(j0:real^3->bool) SUBSET d0`; `(j1:real^3->bool) SUBSET d1`;
      `(i0:real^3->bool) SUBSET e0`; `(i1:real^3->bool) SUBSET e1`;
      `(d0:real^3->bool) SUBSET s`; `(d1:real^3->bool) SUBSET s`;
      `(e0:real^3->bool) SUBSET s'`; `(e1:real^3->bool) SUBSET s'`;
      `DISJOINT (d0:real^3->bool) d1`; `DISJOINT (e0:real^3->bool) e1`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (au:real^3->bool) /\ compact (aw:real^3->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_S5C_ANN_COMPACT]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_annulus_with_ends] o check (fun th ->
    concl th = `pl_annulus_with_ends (au:real^3->bool) j1 j0`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `fu:real^2->real^3` (X_CHOOSE_THEN `fu':real^3->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (ASSUME_TAC o SYM))))) THEN
  ABBREV_TAC `q1 = relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
  ABBREV_TAC `q2 = relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])` THEN
  ABBREV_TAC `m = interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1])` THEN
  SUBGOAL_THEN `(q1:real^2->bool) SUBSET m /\ (q2:real^2->bool) SUBSET m /\
                locally_polyhedral (q1:real^2->bool) /\ locally_polyhedral (q2:real^2->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q1"; "q2"; "m"] THEN
    REWRITE_TAC[SUBSET; MOI_S5C_IN_RF1; MOI_S5C_IN_RF2; MOI_S5C_IN_SQANN] THEN
    REPEAT CONJ_TAC THEN TRY(GEN_TAC THEN REAL_ARITH_TAC) THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_S5C_SQ_RF_POLYHEDRON THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `locally_polyhedral (j0:real^3->bool) /\ locally_polyhedral (j1:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_SCD_PL_SPHERE_POLYHEDRON THEN EXISTS_TAC `1` THEN
    MATCH_MP_TAC MOI_S5E_CELL_SPHERE1 THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (q2:real^2->bool,i0)
                  ((g0:real^3->real^3) o (fu:real^2->real^3),
                   (fu':real^3->real^2) o (g0':real^3->real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `j0:real^3->bool` THEN
    CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (fu:real^2->real^3) q2 = j0`)) THEN
      MATCH_MP_TAC MOI_S5C_PLH_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`m:real^2->bool`; `au:real^3->bool`] THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (g0:real^3->real^3) j0 = i0`)) THEN
      MATCH_MP_TAC MOI_S5C_PLH_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`d0:real^3->bool`; `e0:real^3->bool`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`aw:real^3->bool`; `i1:real^3->bool`; `i0:real^3->bool`;
                 `(g0:real^3->real^3) o (fu:real^2->real^3)`;
                 `(fu':real^3->real^2) o (g0':real^3->real^3)`] MOI_S5C_ANN_OUTER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fw:real^2->real^3` (X_CHOOSE_THEN `fw':real^3->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (ASSUME_TAC o SYM)))))) THEN
  SUBGOAL_THEN `pl_homeomorphism (au:real^3->bool,aw)
                  ((fw:real^2->real^3) o (fu':real^3->real^2),
                   (fu:real^2->real^3) o (fw':real^3->real^2))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `m:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[pl_homeomorphism; homeomorphism] o
    check (fun th -> concl th = `pl_homeomorphism (m:real^2->bool,au:real^3->bool)
                                   ((fu:real^2->real^3),(fu':real^3->real^2))`)) THEN
  SUBGOAL_THEN `!x. x IN j0 ==> ((fw:real^2->real^3) o (fu':real^3->real^2)) x =
                                (g0:real^3->real^3) x` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?y:real^2. y IN q2 /\ (x:real^3) = (fu:real^2->real^3) y` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN j0` THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `IMAGE (fu:real^2->real^3) q2 = j0`)) THEN
      REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(fu':real^3->real^2) ((fu:real^2->real^3) y) = y` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `fu':real^3->real^2`)) (concl th) &&
        can (find_term ((=) `m:real^2->bool`)) (concl th))) THEN
      UNDISCH_TAC `(q2:real^2->bool) SUBSET m` THEN
      UNDISCH_TAC `(y:real^2) IN q2` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^2` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `fw:real^2->real^3`)) (concl th) &&
      can (find_term ((=) `q2:real^2->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[o_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((fw:real^2->real^3) o (fu':real^3->real^2)) j1 = i1` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (fu:real^2->real^3) q1 = j1`)) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (fw:real^2->real^3) q1 = i1`)) THEN
    REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(SET_RULE `(!y:real^2. y IN s ==> (g:real^3->real^2) ((f:real^2->real^3) y) = y)
                           ==> IMAGE g (IMAGE f s) = s`) THEN
    X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `fu':real^3->real^2`)) (concl th) &&
      can (find_term ((=) `m:real^2->bool`)) (concl th))) THEN
    UNDISCH_TAC `(q1:real^2->bool) SUBSET m` THEN
    UNDISCH_TAC `(y:real^2) IN q1` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `d1:real^3->bool`; `j1:real^3->bool`; `e1:real^3->bool`;
                 `i1:real^3->bool`; `(fw:real^2->real^3) o (fu':real^3->real^2)`;
                 `(fu:real^2->real^3) o (fw':real^3->real^2)`] MOI_S5C_CELL_EXT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE ((fw:real^2->real^3) o (fu':real^3->real^2)) j1 = i1`)) THEN
    MATCH_MP_TAC MOI_S5C_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`au:real^3->bool`; `aw:real^3->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kap:real^3->real^3` (X_CHOOSE_THEN `kap':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`d0:real^3->bool`; `au:real^3->bool`; `d1:real^3->bool`;
                 `e0:real^3->bool`; `aw:real^3->bool`; `e1:real^3->bool`;
                 `j0:real^3->bool`; `j1:real^3->bool`; `i0:real^3->bool`;
                 `i1:real^3->bool`; `g0:real^3->real^3`; `g0':real^3->real^3`;
                 `(fw:real^2->real^3) o (fu':real^3->real^2)`;
                 `(fu:real^2->real^3) o (fw':real^3->real^2)`;
                 `kap:real^3->real^3`; `kap':real^3->real^3`] MOI_S5E_GLUE3) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM_REWRITE_TAC[GSYM DISJOINT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->real^3` (X_CHOOSE_THEN `k':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->real^3`; `k':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (kap:real^3->real^3) d1` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(!x:real^3. x IN s ==> (u:real^3->real^3) x = v x)
                           ==> IMAGE u s = IMAGE v s`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    UNDISCH_TAC `pl_homeomorphism (d1:real^3->bool,e1:real^3->bool)
                   ((kap:real^3->real^3),(kap':real^3->real^3))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism]]);;

let ONE_DISK_EXT = prove
 (MOI_S35_ONE_DISK_EXT,
  MAP_EVERY X_GEN_TAC [`u:real^3->bool`; `w:real^3->bool`; `d0:real^3->bool`;
                       `j0:real^3->bool`; `d1:real^3->bool`; `j1:real^3->bool`;
                       `e0:real^3->bool`; `i0:real^3->bool`; `e1:real^3->bool`;
                       `i1:real^3->bool`; `g0:real^3->real^3`; `g0':real^3->real^3`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`frontier u:real^3->bool`; `frontier w:real^3->bool`;
                 `d0:real^3->bool`; `j0:real^3->bool`; `d1:real^3->bool`;
                 `j1:real^3->bool`; `e0:real^3->bool`; `i0:real^3->bool`;
                 `e1:real^3->bool`; `i1:real^3->bool`; `g0:real^3->real^3`;
                 `g0':real^3->real^3`] MOI_S5E_SPHERE_MAP) THEN
  ASM_SIMP_TAC[MOI_S5E_BALL_FRONTIER_SPHERE] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `w:real^3->bool`; `h:real^3->real^3`;
                 `h':real^3->real^3`] MOI_SCD_COR_EXTEND_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `f':real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN frontier u` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (h:real^3->real^3) d1 = e1`)) THEN
    MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> (f:real^3->real^3) x = h x) ==> IMAGE f s = IMAGE h s`) THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN frontier u` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]]]);;

