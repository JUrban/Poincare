(* ========================================================================= *)
(* pc_moi_p305: MOI_PROD_305_THM : |- MOI_PROD_305 (pc_moi_core_stmt.ml),    *)
(* Moise 30.5 (GTM 47 p.216), from 30.4 and the PL Schoenflies theorem in    *)
(* real^3.                                                                   *)
(* ========================================================================= *)

needs "src/pc_moi_core_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Topological facts: PL 2-spheres are topological spheres; boundary points  *)
(* of a homeomorphic copy stay out of the interior (invariance of domain);   *)
(* ends of a spherical shell; complements of interiors of 3-cells.           *)
(* ------------------------------------------------------------------------- *)

let MOI_P35_PL_SPHERE_HOMEO = prove
 (`!b:real^3->bool. pl_sphere 2 b ==> b homeomorphic sphere(vec 0:real^3,&1)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`b:real^3->bool`; `relative_frontier(k:real^3->bool)`;
                       `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_TRANS) THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^3,&1) = relative_frontier(cball(vec 0,&1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[RELATIVE_FRONTIER_CBALL] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
  REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL; DIMINDEX_3] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]);;

let MOI_P35_HOMEO_INTERIOR = prove
 (`!(s:real^N->bool) (x:real^N->bool) h k p.
     homeomorphism (s,x) (h,k) /\ p IN s /\ h p IN interior x
     ==> p IN interior s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_INTERIOR]) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open (IMAGE (k:real^N->real^N) (ball(h(p:real^N),e)))` ASSUME_TAC
  THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_BALL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (k:real^N->real^N) (ball(h(p:real^N),e)) SUBSET interior s`
  MP_TAC THENL
   [MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^N) p`) THEN
  ASM_SIMP_TAC[CENTRE_IN_BALL]);;

let MOI_P35_SHELL_ENDS = prove
 (`!p:real^3. norm p = &1 \/ norm p = &2
              ==> ~(p IN interior {y:real^3 | &1 <= norm y /\ norm y <= &2})`,
  GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[IN_INTERIOR; SUBSET; IN_BALL; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC) THENL
   [ABBREV_TAC `m = min (e / &2) (&1 / &2)` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - m) % (p:real^3)`) THEN
    REWRITE_TAC[dist; NORM_MUL; VECTOR_ARITH `p - a % p:real^3 = (&1 - a) % p`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    FIRST_X_ASSUM(MP_TAC o SPEC `(&1 + e / &4) % (p:real^3)`) THEN
    REWRITE_TAC[dist; NORM_MUL; VECTOR_ARITH `p - a % p:real^3 = (&1 - a) % p`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_P35_SHELL_COMPACT = prove
 (`compact {y:real^3 | &1 <= norm y /\ norm y <= &2}`,
  SUBGOAL_THEN `{y:real^3 | &1 <= norm y /\ norm y <= &2} =
                cball(vec 0,&2) DIFF ball(vec 0,&1)` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_CBALL_0; IN_BALL_0] THEN
    REAL_ARITH_TAC;
    SIMP_TAC[COMPACT_DIFF; COMPACT_CBALL; OPEN_BALL]]);;

let MOI_P35_SHELL_FACTS = prove
 (`!x b0 b1:real^3->bool.
     spherical_shell x b0 b1
     ==> compact x /\ connected b0 /\ ~(b0 = {}) /\ connected b1 /\ ~(b1 = {}) /\
         b0 SUBSET x /\ b1 SUBSET x /\
         b0 INTER interior x = {} /\ b1 INTER interior x = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[spherical_shell; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`h:real^3->real^3`; `k:real^3->real^3`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `sphere(vec 0:real^3,&1) SUBSET {y:real^3 | &1 <= norm y /\ norm y <= &2} /\
    sphere(vec 0:real^3,&2) SUBSET {y:real^3 | &1 <= norm y /\ norm y <= &2}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_SPHERE_0; IN_ELIM_THM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^3->real^3) continuous_on {y:real^3 | &1 <= norm y /\ norm y <= &2} /\
                IMAGE h {y:real^3 | &1 <= norm y /\ norm y <= &2} = x`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:3)` ASSUME_TAC THENL
   [REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [EXPAND_TAC "x" THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[MOI_P35_SHELL_COMPACT];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONNECTED_SPHERE] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_SIMP_TAC[CONNECTED_SPHERE] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[IMAGE_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    EXPAND_TAC "x" THEN ASM_SIMP_TAC[IMAGE_SUBSET];
    EXPAND_TAC "x" THEN ASM_SIMP_TAC[IMAGE_SUBSET];
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    MP_TAC(ISPECL [`{y:real^3 | &1 <= norm y /\ norm y <= &2}`; `x:real^3->bool`;
                   `h:real^3->real^3`; `k:real^3->real^3`; `q:real^3`]
      MOI_P35_HOMEO_INTERIOR) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> F`) THEN
    MATCH_MP_TAC MOI_P35_SHELL_ENDS THEN
    UNDISCH_TAC `(q:real^3) IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0] THEN MESON_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_IMAGE] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    MP_TAC(ISPECL [`{y:real^3 | &1 <= norm y /\ norm y <= &2}`; `x:real^3->bool`;
                   `h:real^3->real^3`; `k:real^3->real^3`; `q:real^3`]
      MOI_P35_HOMEO_INTERIOR) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p ==> F`) THEN
    MATCH_MP_TAC MOI_P35_SHELL_ENDS THEN
    UNDISCH_TAC `(q:real^3) IN sphere(vec 0,&2)` THEN
    REWRITE_TAC[IN_SPHERE_0] THEN MESON_TAC[]]);;

let MOI_P35_CELL_FACTS = prove
 (`!c:real^3->bool.
     c homeomorphic cball(vec 0:real^3,&1)
     ==> compact c /\ connected c /\ ~(c = {}) /\
         connected ((:real^3) DIFF interior c)`,
  GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_CBALL];
    ASM_MESON_TAC[HOMEOMORPHIC_CONNECTEDNESS; CONNECTED_CBALL];
    DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o ONCE_REWRITE_RULE[HOMEOMORPHIC_SYM]) THEN
    REWRITE_TAC[HOMEOMORPHIC_EMPTY; CBALL_EQ_EMPTY] THEN REAL_ARITH_TAC;
    REWRITE_TAC[GSYM CLOSURE_COMPLEMENT] THEN MATCH_MP_TAC CONNECTED_CLOSURE THEN
    MATCH_MP_TAC(ISPECL [`c:real^3->bool`; `cball(vec 0:real^3,&1)`]
      CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
    ASM_REWRITE_TAC[CONVEX_CBALL; COMPACT_CBALL; DIMINDEX_3] THEN ARITH_TAC]);;

let MOI_P35_CONNECTED_IN_ONE = prove
 (`!s e1 e2:real^N->bool.
     connected s /\ open e1 /\ open e2 /\ e1 INTER e2 = {} /\ s SUBSET e1 UNION e2
     ==> s SUBSET e1 \/ s SUBSET e2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* MOI_PROD_305 (Moise 30.5, p.216): the PL 2-sphere b of 30.4 between the   *)
(* frontiers bounds, by the PL Schoenflies theorem, the PL 3-ball            *)
(* b UNION inside b; it contains c1 in its interior (b separates the two     *)
(* frontiers, and the complement of the interior of c2 is connected and      *)
(* unbounded, hence outside b) and lies in the interior of c2.               *)
(* ------------------------------------------------------------------------- *)

let MOI_PROD_305_THM = prove
 (`MOISE_304_STATEMENT /\ PL_SCHOENFLIES_3_STATEMENT ==> MOISE_305_STATEMENT`,
  REWRITE_TAC[MOISE_304_STATEMENT; PL_SCHOENFLIES_3_STATEMENT;
              MOISE_305_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "A304") (LABEL_TAC "SCH")) THEN
  MAP_EVERY X_GEN_TAC [`c1:real^3->bool`; `c2:real^3->bool`] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_P35_SHELL_FACTS) THEN
  MP_TAC(ISPEC `c1:real^3->bool` MOI_P35_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c2:real^3->bool` MOI_P35_CELL_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REMOVE_THEN "A304" (MP_TAC o SPECL
   [`closure((c2:real^3->bool) DIFF c1)`; `frontier(c1:real^3->bool)`;
    `frontier(c2:real^3->bool)`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "SCH" (MP_TAC o SPEC `b:real^3->bool`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `(b:real^3->bool) UNION inside b` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `b:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_P35_PL_SPHERE_HOMEO; DIMINDEX_3] THEN ARITH_TAC;
    STRIP_TAC] THEN
  SUBGOAL_THEN `closed(c1:real^3->bool) /\ closed(c2:real^3->bool)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `frontier(c1:real^3->bool) = c1 DIFF interior c1 /\
    frontier(c2:real^3->bool) = c2 DIFF interior c2`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^3->bool) SUBSET interior c2` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior(closure((c2:real^3->bool) DIFF c1))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c1:real^3->bool) INTER b = {}` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `interior(c1:real^3->bool) INTER closure(c2 DIFF c1) = {}` MP_TAC THENL
     [SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_INTERIOR] THEN
      MP_TAC(ISPEC `c1:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `closure((c2:real^3->bool) DIFF c1)` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `frontier(c1:real^3->bool) INTER
                 interior(closure(c2 DIFF c1)) = {}` THEN
    UNDISCH_TAC `frontier(c1:real^3->bool) = c1 DIFF interior c1` THEN
    UNDISCH_TAC `(b:real^3->bool) SUBSET interior(closure(c2 DIFF c1))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(:real^3) DIFF interior c2 SUBSET outside b` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^3) DIFF interior c2`; `inside(b:real^3->bool)`;
                   `outside(b:real^3->bool)`] MOI_P35_CONNECTED_IN_ONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    MP_TAC(INST_TYPE [`:3`,`:N`] NOT_BOUNDED_UNIV) THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> F`) THEN
    SUBGOAL_THEN `(:real^3) = interior c2 UNION ((:real^3) DIFF interior c2)`
    SUBST1_TAC THENL [SET_TAC[]; REWRITE_TAC[BOUNDED_UNION]] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `c2:real^3->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; INTERIOR_SUBSET];
      ASM_MESON_TAC[BOUNDED_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier(c1:real^3->bool) SUBSET inside b` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`frontier(c1:real^3->bool)`; `inside(b:real^3->bool)`;
                   `outside(b:real^3->bool)`] MOI_P35_CONNECTED_IN_ONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [euclidean_separates]) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`outside(b:real^3->bool)`; `u:real^3->bool`;
                   `v:real^3->bool`] MOI_P35_CONNECTED_IN_ONE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `frontier(c2:real^3->bool) SUBSET outside b` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c1:real^3->bool) SUBSET inside b` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c1:real^3->bool`; `inside(b:real^3->bool)`;
                   `outside(b:real^3->bool)`] MOI_P35_CONNECTED_IN_ONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `frontier(c1:real^3->bool) SUBSET c1` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `inside(b:real^3->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[UNION_SUBSET] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

