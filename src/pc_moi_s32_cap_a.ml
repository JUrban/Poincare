(* ========================================================================= *)
(* pc_moi_s32_cap_a: Moise GTM 47, 32.4, first half (p.228).  Main theorem  *)
(* CAP_SETUP |- MOI_S32_CAP_SETUP of the statement file pc_moi_s3032_stmt:  *)
(* for a pseudo-cell (e,j,p) and d > 0 a PL 3-ball c around p in ball(p,d), *)
(* off j, whose frontier crosses (e DIFF j) DELETE p in finitely many       *)
(* disjoint PL circles, with c INTER e inside a small disk dz of e DIFF j.  *)
(* Route: a cube around p moved into general position (GP_SURFACES_3) with  *)
(* a lf combinatorial triangulation of e in a cubical shell around p (a     *)
(* compact polyhedral piece, LF_TRIANGULATION_OPEN_SUBSET, the              *)
(* SURFACE_TRIANG antecedent), MOI_S4L_CROSSING_CIRCLES.                    *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s34_cellnbb.ml";;
needs "src/pc_moi_tube3.ml";;
needs "src/pc_moi_chain.ml";;
needs "src/pc_moi_pl1m.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* Part 1: the pseudo-cell data and the small disk dz around p.              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3C1_PCELL = prove
 (`!(e:real^3->bool) j p.
     pseudo_cell e j p
     ==> closed e /\ compact j /\ j SUBSET e /\ p IN e /\ ~(p IN j) /\
         locally_polyhedral ((e DIFF j) DELETE p) /\
         open_in (subtopology euclidean e) (e DIFF j) /\
         ?h k. homeomorphism (ball(vec 0:real^2,&1),e DIFF j) (h,k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pseudo_cell] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (e:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_CLOSURE]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (j:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_COMPACTNESS; COMPACT_SPHERE]; ALL_TAC] THEN
  UNDISCH_TAC `(p:real^3) IN e DIFF j` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `e DIFF j = (e:real^3->bool) INTER ((:real^3) DIFF j)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[GSYM closed] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    UNDISCH_TAC `(e DIFF j:real^3->bool) homeomorphic ball(vec 0:real^2,&1)` THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic]]);;

let MOI_S3C1_DISK = prove
 (`!(e:real^3->bool) j p (h:real^2->real^3) k d.
     homeomorphism (ball(vec 0:real^2,&1),e DIFF j) (h,k) /\
     open_in (subtopology euclidean e) (e DIFF j) /\ p IN e DIFF j /\ &0 < d
     ==> ?dz (fz:real^2->real^3) gz.
           homeomorphism (cball(vec 0:real^2,&1),dz) (fz,gz) /\ fz(vec 0) = p /\
           dz SUBSET (e DIFF j) INTER ball(p,d) /\
           open_in (subtopology euclidean e) (IMAGE fz (ball(vec 0,&1)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ABBREV_TAC `q = (k:real^3->real^2) p` THEN
  SUBGOAL_THEN `(q:real^2) IN ball(vec 0,&1) /\ (h:real^2->real^3) q = p` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN ASM SET_TAC[]; ALL_TAC] THEN
  (* continuity of h at q *)
  UNDISCH_TAC `(h:real^2->real^3) continuous_on ball(vec 0,&1)` THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `q:real^2`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rho = min r0 (&1 - norm(q:real^2)) / &2` THEN
  SUBGOAL_THEN `&0 < rho /\ rho < r0 /\ cball(q:real^2,rho) SUBSET ball(vec 0,&1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^2) IN ball(vec 0,&1)` THEN
    REWRITE_TAC[IN_BALL_0; SUBSET; IN_CBALL; IN_BALL_0] THEN DISCH_TAC THEN
    EXPAND_TAC "rho" THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `z:real^2` THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`z:real^2`; `q:real^2`] NORM_TRIANGLE_SUB) THEN
    MP_TAC(ISPECL [`q:real^2`; `z:real^2`] NORM_SUB) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (\x:real^2. rho % x + q) (cball(vec 0,&1)) = cball(q,rho) /\
                IMAGE (\x:real^2. rho % x + q) (ball(vec 0,&1)) = ball(q,rho)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[IMAGE_AFFINITY_CBALL; IMAGE_AFFINITY_BALL; REAL_LT_IMP_NZ; REAL_LE_01] THEN
    ASM_SIMP_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID; REAL_MUL_RID; REAL_ARITH
      `&0 < x ==> abs x = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphism (cball(vec 0:real^2,&1),cball(q,rho))
      ((\x. rho % x + q),(\y. inv rho % (y - q)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[HOMEOMORPHISM] THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      SIMP_TAC[CONTINUOUS_ON_CMUL; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_ID; CONTINUOUS_ON_CONST];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_CBALL; IN_CBALL_0; dist] THEN
      X_GEN_TAC `y:real^2` THEN DISCH_TAC THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`] THEN
      ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[GSYM real_div; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      REPEAT STRIP_TAC THEN
      REWRITE_TAC[VECTOR_ARITH `(a + q) - q:real^2 = a`; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
      REPEAT STRIP_TAC THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (cball(q:real^2,rho),IMAGE (h:real^2->real^3) (cball(q,rho)))
                              (h,k)` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^2,&1)`; `e DIFF j:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (h:real^2->real^3) (cball(q,rho))`;
                        `(h:real^2->real^3) o (\x:real^2. rho % x + q)`;
                        `(\y:real^2. inv rho % (y - q)) o (k:real^3->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `cball(q:real^2,rho)` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[o_THM; VECTOR_MUL_RZERO; VECTOR_ADD_LID];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `z:real^2` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^2) IN ball(vec 0,&1)` ASSUME_TAC THENL
     [UNDISCH_TAC `cball(q:real^2,rho) SUBSET ball(vec 0,&1)` THEN
      UNDISCH_TAC `(z:real^2) IN cball(q,rho)` THEN SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `IMAGE (h:real^2->real^3) (ball(vec 0,&1)) = e DIFF j` THEN
      UNDISCH_TAC `(z:real^2) IN ball(vec 0,&1)` THEN SET_TAC[];
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^2) IN cball(q,rho)` THEN REWRITE_TAC[IN_CBALL] THEN
      MP_TAC(ISPECL [`z:real^2`; `q:real^2`] DIST_SYM) THEN ASM_REAL_ARITH_TAC];
    REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `e DIFF j:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->real^2`; `ball(vec 0:real^2,&1)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN
    REWRITE_TAC[OPEN_BALL] THEN
    MP_TAC(ISPECL [`q:real^2`; `rho:real`] BALL_SUBSET_CBALL) THEN
    UNDISCH_TAC `cball(q:real^2,rho) SUBSET ball(vec 0,&1)` THEN SET_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* Part 2: cubes around p (sup-norm balls), their distance bound, the        *)
(* cube as a PL 3-ball, the open cubical shell W = int Q(r2) DIFF Q(r1).    *)
(* ------------------------------------------------------------------------- *)

let moi_s3c1_cube = new_definition
 `moi_s3c1_cube (p:real^3) (t:real) = interval[p - t % vec 1,p + t % vec 1]`;;

let MOI_S3C1_IN_CUBE = prove
 (`!(p:real^3) t x.
     x IN moi_s3c1_cube p t <=> !i. 1 <= i /\ i <= 3 ==> abs(x$i - p$i) <= t`,
  REWRITE_TAC[moi_s3c1_cube; IN_INTERVAL; DIMINDEX_3; VECTOR_SUB_COMPONENT;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `p - t <= x /\ x <= p + t <=> abs(x - p) <= t`]);;

let MOI_S3C1_IN_OCUBE = prove
 (`!(p:real^3) t x.
     x IN interval(p - t % vec 1,p + t % vec 1) <=>
     !i. 1 <= i /\ i <= 3 ==> abs(x$i - p$i) < t`,
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; VECTOR_SUB_COMPONENT;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
  REWRITE_TAC[REAL_ARITH `p - t < x /\ x < p + t <=> abs(x - p) < t`]);;

let MOI_S3C1_CUBE_DIST = prove
 (`!(p:real^3) t x. x IN moi_s3c1_cube p t ==> dist(p,x) <= &3 * t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_S3C1_IN_CUBE; dist] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `p - x:real^3` NORM_LE_L1) THEN
  REWRITE_TAC[DIMINDEX_3; SUM_3; VECTOR_SUB_COMPONENT] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
    MP_TAC(SPEC `3` th)) THEN
  CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC);;

let MOI_S3C1_CUBE_BALL = prove
 (`!(p:real^3) t. &0 < t ==> pl_ball 3 (moi_s3c1_cube p t)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_s3c1_cube] THEN MATCH_MP_TAC MOI_TB3_BOX_BALL THEN
  REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
              VEC_COMPONENT] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_S3C1_FRONTIER_IN_SHELL = prove
 (`!(p:real^3) r1 r r2.
     r1 < r /\ r < r2
     ==> frontier (moi_s3c1_cube p r) SUBSET
         interval(p - r2 % vec 1,p + r2 % vec 1) DIFF moi_s3c1_cube p r1`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_s3c1_cube; FRONTIER_CLOSED_INTERVAL] THEN REWRITE_TAC[GSYM moi_s3c1_cube] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; MOI_S3C1_IN_CUBE; MOI_S3C1_IN_OCUBE] THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;


(* ------------------------------------------------------------------------- *)
(* Part 3: a locally finite combinatorial triangulation of e in the         *)
(* open cubical shell W around p.  A compact locally polyhedral set is a    *)
(* finite union of polytopes; e INTER (closed shell) is one; its part in W  *)
(* is open in it (LF_TRIANGULATION_OPEN_SUBSET); plane charts from the disk *)
(* structure of e DIFF j; the SURFACE_TRIANG hypothesis then gives CM2.     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3C1_COMPACT_LP = prove
 (`!s:real^N->bool.
     compact s /\ locally_polyhedral s
     ==> ?c. FINITE c /\ (!k. k IN c ==> polytope k) /\ UNIONS c = s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] o
    GEN_REWRITE_RULE I [locally_polyhedral]) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->(real^N->bool)->bool`
    (X_CHOOSE_TAC `U:real^N->real^N->bool`)) THEN
  FIRST_ASSUM(MP_TAC o SPEC `IMAGE (U:real^N->real^N->bool) s` o
    MATCH_MP COMPACT_IMP_HEINE_BOREL) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[TAUT `a /\ b /\ c <=> b /\ a /\ c`] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `fs:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `UNIONS (IMAGE (C:real^N->(real^N->bool)->bool) fs)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM SET_TAC[];
    REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_UNIONS; FORALL_IN_IMAGE] THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM SET_TAC[]]]);;

let MOI_S3C1_HALFSPACES = prove
 (`!i b. 1 <= i /\ i <= 3
         ==> polyhedron {y:real^3 | y$i <= b} /\ polyhedron {y:real^3 | b <= y$i}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. y$i = basis i dot y` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[DOT_BASIS; DIMINDEX_3]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[POLYHEDRON_HALFSPACE_LE];
    REWRITE_TAC[GSYM real_ge; POLYHEDRON_HALFSPACE_GE]]);;

let MOI_S3C1_SHELL_LP = prove
 (`!(X:real^3->bool) p r1 r2.
     locally_polyhedral X
     ==> locally_polyhedral
           (X INTER (moi_s3c1_cube p r2 DIFF interval(p - r1 % vec 1,p + r1 % vec 1)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_polyhedral] THEN DISCH_TAC THEN
  X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^3->bool)->bool` (X_CHOOSE_THEN `u:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC
   `{k INTER moi_s3c1_cube p r2 INTER {y:real^3 | y$i <= p$i - r1} | k IN c /\ i IN 1..3} UNION
    {k INTER moi_s3c1_cube p r2 INTER {y:real^3 | p$i + r1 <= y$i} | k IN c /\ i IN 1..3}` THEN
  EXISTS_TAC `u:real^3->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    ASM_REWRITE_TAC[FINITE_NUMSEG];
    REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_UNIONS; IN_UNION; IN_ELIM_THM;
                MOI_S3C1_IN_OCUBE; NOT_FORALL_THM; NOT_IMP] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
    SUBGOAL_THEN `?k. k IN c /\ (y:real^3) IN k` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(X:real^3->bool) INTER u SUBSET UNIONS c` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^3)$i <= (p:real^3)$i - r1` THENL
     [EXISTS_TAC `k INTER moi_s3c1_cube p r2 INTER {y':real^3 | y'$i <= p$i - r1}` THEN
      CONJ_TAC THENL
       [DISJ1_TAC THEN MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `i:num`] THEN
        ASM_REWRITE_TAC[IN_NUMSEG];
        ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM]];
      EXISTS_TAC `k INTER moi_s3c1_cube p r2 INTER {y':real^3 | p$i + r1 <= y'$i}` THEN
      CONJ_TAC THENL
       [DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `i:num`] THEN
        ASM_REWRITE_TAC[IN_NUMSEG];
        ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM_REAL_ARITH_TAC]];
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `k':real^3->bool` THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `i:num`
      (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST1_TAC)))) THEN
    (SUBGOAL_THEN `polytope (k:real^3->bool) /\ k SUBSET X` STRIP_ASSUME_TAC THENL
      [ASM_SIMP_TAC[]; ALL_TAC] THEN
     UNDISCH_TAC `i IN 1..3` THEN REWRITE_TAC[IN_NUMSEG] THEN STRIP_TAC THEN
     CONJ_TAC THENL
      [MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN ASM_REWRITE_TAC[] THEN
       MATCH_MP_TAC POLYHEDRON_INTER THEN CONJ_TAC THENL
        [MATCH_MP_TAC POLYTOPE_IMP_POLYHEDRON THEN
         REWRITE_TAC[moi_s3c1_cube; POLYTOPE_INTERVAL];
         ASM_SIMP_TAC[MOI_S3C1_HALFSPACES]];
       REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_ELIM_THM; MOI_S3C1_IN_OCUBE] THEN
       X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
        [ASM SET_TAC[];
         REWRITE_TAC[NOT_FORALL_THM; NOT_IMP] THEN EXISTS_TAC `i:num` THEN
         ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]])]);;

(* Plane charts at the points of e INTER V for an open V missing j. *)

let MOI_S3C1_CHARTS = prove
 (`!(e:real^3->bool) j (h:real^2->real^3) k V y.
     homeomorphism (ball(vec 0:real^2,&1),e DIFF j) (h,k) /\ open V /\ DISJOINT V j /\
     y IN e INTER V
     ==> moi_s28_locally_r2 (e INTER V) y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s28_locally_r2] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (e DIFF j)) (e INTER (V:real^3->bool))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `e INTER V = (e DIFF j) INTER (V:real^3->bool)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (k:real^3->real^2) (e INTER V))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:real^3->real^2`; `h:real^2->real^3`; `e DIFF j:real^3->bool`;
                   `ball(vec 0:real^2,&1)`; `e INTER V:real^3->bool`]
                  HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SIMP_TAC[OPEN_IN_OPEN_EQ; OPEN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `?rho. &0 < rho /\
                      ball((k:real^3->real^2) y,rho) SUBSET IMAGE k (e INTER V)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open (IMAGE (k:real^3->real^2) (e INTER V))` THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(y:real^3) IN e INTER V` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball((k:real^3->real^2) y,rho) SUBSET ball(vec 0,&1) /\
                IMAGE (h:real^2->real^3) (ball((k:real^3->real^2) y,rho)) SUBSET e INTER V /\
                e INTER V SUBSET e DIFF j`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ball((k:real^3->real^2) y,rho) SUBSET IMAGE k (e INTER V)` THEN
      UNDISCH_TAC `IMAGE (k:real^3->real^2) (e DIFF j) = ball(vec 0,&1)` THEN
      UNDISCH_TAC `DISJOINT (V:real^3->bool) j` THEN SET_TAC[];
      UNDISCH_TAC `ball((k:real^3->real^2) y,rho) SUBSET IMAGE k (e INTER V)` THEN
      UNDISCH_TAC `!y. y IN e DIFF j ==> (h:real^2->real^3) ((k:real^3->real^2) y) = y` THEN
      UNDISCH_TAC `DISJOINT (V:real^3->bool) j` THEN SET_TAC[];
      UNDISCH_TAC `DISJOINT (V:real^3->bool) j` THEN SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (h:real^2->real^3) (ball((k:real^3->real^2) y,rho))` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `e DIFF j:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->real^2`; `ball(vec 0:real^2,&1)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_OPEN_IN_TRANS THEN
    ASM_REWRITE_TAC[OPEN_BALL];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(k:real^3->real^2) y` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL] THEN CONV_TAC SYM_CONV THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN UNDISCH_TAC `(y:real^3) IN e INTER V` THEN
    UNDISCH_TAC `DISJOINT (V:real^3->bool) j` THEN SET_TAC[];
    MATCH_MP_TAC(ISPECL [`IMAGE (h:real^2->real^3) (ball((k:real^3->real^2) y,rho))`;
                         `ball((k:real^3->real^2) y,rho)`; `(:real^2)`] HOMEOMORPHIC_TRANS) THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_BALL_UNIV] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`h:real^2->real^3`; `k:real^3->real^2`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`ball(vec 0:real^2,&1)`; `e DIFF j:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* The lf combinatorial triangulation of e INTER W (W the open shell). *)

let MOI_S3C1_SHELL_TRI = prove
 (`!(e:real^3->bool) j p (h:real^2->real^3) k r1 r2.
     (!c:(real^3->bool)->bool.
        lf_simplicial_complex c /\
        (!y. y IN UNIONS c
             ==> moi_s28_locally_r2 (UNIONS c) y \/ moi_s28_locally_half (UNIONS c) y)
        ==> combinatorial_manifold_with_boundary 2 c /\
            surface_boundary c = {y | y IN UNIONS c /\ ~moi_s28_locally_r2 (UNIONS c) y} /\
            (surface_boundary c = {} ==> combinatorial_manifold 2 c)) /\
     closed e /\ j SUBSET e /\ ~(p IN j) /\ locally_polyhedral ((e DIFF j) DELETE p) /\
     homeomorphism (ball(vec 0:real^2,&1),e DIFF j) (h,k) /\
     &0 < r1 /\ r1 < r2 /\ DISJOINT (moi_s3c1_cube p r2) j
     ==> ?t. lf_simplicial_complex t /\ combinatorial_manifold 2 t /\
             UNIONS t =
             e INTER (interval(p - r2 % vec 1,p + r2 % vec 1) DIFF moi_s3c1_cube p r1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "tri") STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `A = moi_s3c1_cube p r2 DIFF interval(p - r1 % vec 1,p + r1 % vec 1)` THEN
  ABBREV_TAC `W = interval(p - r2 % vec 1,p + r2 % vec 1) DIFF moi_s3c1_cube (p:real^3) r1` THEN
  SUBGOAL_THEN `(W:real^3->bool) SUBSET A /\ open W /\ compact (A:real^3->bool) /\
                DISJOINT A j /\ ~((p:real^3) IN A)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["A"; "W"] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`p - r2 % vec 1:real^3`; `p + r2 % vec 1:real^3`]
        INTERVAL_OPEN_SUBSET_CLOSED) THEN
      MP_TAC(ISPECL [`p - r1 % vec 1:real^3`; `p + r1 % vec 1:real^3`]
        INTERVAL_OPEN_SUBSET_CLOSED) THEN
      REWRITE_TAC[moi_s3c1_cube] THEN SET_TAC[];
      MATCH_MP_TAC OPEN_DIFF THEN
      REWRITE_TAC[OPEN_INTERVAL; moi_s3c1_cube; CLOSED_INTERVAL];
      MATCH_MP_TAC COMPACT_DIFF THEN
      REWRITE_TAC[OPEN_INTERVAL; moi_s3c1_cube; COMPACT_INTERVAL];
      UNDISCH_TAC `DISJOINT (moi_s3c1_cube p r2) (j:real^3->bool)` THEN SET_TAC[];
      REWRITE_TAC[IN_DIFF; MOI_S3C1_IN_OCUBE; REAL_SUB_REFL; REAL_ABS_0] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((e DIFF j) DELETE p) INTER A = e INTER (A:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (A:real^3->bool) j` THEN UNDISCH_TAC `~((p:real^3) IN A)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(e DIFF j) DELETE (p:real^3)`; `p:real^3`; `r1:real`; `r2:real`]
    MOI_S3C1_SHELL_LP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `compact (e INTER (A:real^3->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `e INTER (A:real^3->bool)` MOI_S3C1_COMPACT_LP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `c1:(real^3->bool)->bool` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c0:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c0:(real^3->bool)->bool`; `e INTER (W:real^3->bool)`]
    LF_TRIANGULATION_OPEN_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `e INTER (W:real^3->bool) = (e INTER A) INTER W` SUBST1_TAC THENL
     [UNDISCH_TAC `(W:real^3->bool) SUBSET A` THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!y. y IN e INTER (W:real^3->bool) ==> moi_s28_locally_r2 (e INTER W) y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3C1_CHARTS THEN
    MAP_EVERY EXISTS_TAC [`j:real^3->bool`; `h:real^2->real^3`; `k:real^3->real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (A:real^3->bool) j` THEN UNDISCH_TAC `(W:real^3->bool) SUBSET A` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN UNIONS t
               ==> moi_s28_locally_r2 (UNIONS t) y \/ moi_s28_locally_half (UNIONS t) y`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  USE_THEN "tri" (MP_TAC o C MATCH_MP (CONJ
    (ASSUME `lf_simplicial_complex (t:(real^3->bool)->bool)`)
    (ASSUME `!y:real^3. y IN UNIONS t
               ==> moi_s28_locally_r2 (UNIONS t) y \/ moi_s28_locally_half (UNIONS t) y`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC MATCH_MP_TAC)) THEN
  ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 4: PL homeomorphisms of real^3 that are the identity off a set      *)
(* k map k into itself, PL 3-balls onto PL 3-balls, interiors and frontiers *)
(* onto interiors and frontiers.                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3C1_OFF_FIX = prove
 (`!(f:real^3->real^3) g k.
     (!x. g(f x) = x) /\ (!x. ~(x IN k) ==> f x = x)
     ==> !x. x IN k ==> f x IN k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(f:real^3->real^3) (f x) = f x` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->real^3) x = x` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `g:real^3->real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_S3C1_PLH_BALL = prove
 (`!(f:real^3->real^3) g b.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g) /\ pl_ball 3 b
     ==> pl_ball 3 (IMAGE f b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4Z_PL_BALL_CELL) THEN
  UNDISCH_TAC `pl_ball 3 (b:real^3->bool)` THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (X_CHOOSE_THEN `f0:real^3->real^3`
    (X_CHOOSE_THEN `g0:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `(f:real^3->real^3) o (f0:real^3->real^3)`;
                        `(g0:real^3->real^3) o (g:real^3->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `b:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FGB_PLH_UNIV_RESTRICT THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

let MOI_S3C1_PLH_INT_FRONTIER = prove
 (`!(f:real^3->real^3) g u.
     pl_homeomorphism ((:real^3),(:real^3)) (f,g)
     ==> interior (IMAGE f u) = IMAGE f (interior u) /\
         frontier (IMAGE f u) = IMAGE f (frontier u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `(:real^3)`; `(:real^3)`;
                 `u:real^3->bool`] HOMEOMORPHISM_INTERIOR_OF) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `(:real^3)`; `(:real^3)`;
                 `u:real^3->bool`] HOMEOMORPHISM_FRONTIER_OF) THEN
  ASM_REWRITE_TAC[SUBSET_UNIV; SUBTOPOLOGY_UNIV; EUCLIDEAN_INTERIOR_OF;
                  EUCLIDEAN_FRONTIER_OF] THEN
  SIMP_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* Part 5: CAP_SETUP.  Radii r1 < r < r2 with 3 r2 below d, the disk        *)
(* margin delta and the distance dj to j; t the lf triangulation of e in   *)
(* the open shell W, s a triangulation of the cube frontier; GP_SURFACES_3 *)
(* on W moves the cube frontier into crossing position by a PL             *)
(* homeomorphism f that is the identity off a compact subset of W; c = f Q; *)
(* ff the components of frontier c INTER e (MOI_S4L_CROSSING_CIRCLES).      *)
(* ------------------------------------------------------------------------- *)

let CAP_SETUP = prove
 (MOI_S32_CAP_SETUP,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "gp") (LABEL_TAC "tri")) THEN
  MAP_EVERY X_GEN_TAC [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `d:real`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3C1_PCELL) THEN
  (* the disk *)
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `h:real^2->real^3`;
                 `k:real^3->real^2`; `d:real`] MOI_S3C1_DISK) THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `dz:real^3->bool` (X_CHOOSE_THEN `fz:real^2->real^3`
    (X_CHOOSE_THEN `gz:real^3->real^2` STRIP_ASSUME_TAC))) THEN
  (* the margin of the disk *)
  SUBGOAL_THEN `?delta. &0 < delta /\
                        !x. x IN e /\ dist(p,x) < delta
                            ==> x IN IMAGE (fz:real^2->real^3) (ball(vec 0,&1))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean e)
                   (IMAGE (fz:real^2->real^3) (ball(vec 0,&1)))` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o1:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `o1:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ANTS_TAC THENL
     [SUBGOAL_THEN `(p:real^3) IN IMAGE (fz:real^2->real^3) (ball(vec 0,&1))` MP_TAC THENL
       [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN
        ASM_REWRITE_TAC[CENTRE_IN_BALL; REAL_LT_01];
        ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `delta:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    UNDISCH_TAC `ball(p:real^3,delta) SUBSET o1` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the distance to j *)
  SUBGOAL_THEN `?dj. &0 < dj /\ !x. x IN j ==> dj <= dist(p:real^3,x)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^3) DIFF j` OPEN_CONTAINS_BALL) THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `dj:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    UNDISCH_TAC `ball(p:real^3,dj) SUBSET (:real^3) DIFF j` THEN
    REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* radii *)
  ABBREV_TAC `r2 = min (min d delta) dj / &4` THEN
  ABBREV_TAC `r1 = r2 / &3` THEN ABBREV_TAC `r = &2 * r2 / &3` THEN
  SUBGOAL_THEN `&0 < r1 /\ r1 < r /\ r < r2 /\ &3 * r2 < d /\ &3 * r2 < delta /\
                &3 * r2 < dj`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["r"; "r1"; "r2"] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN moi_s3c1_cube p r2 ==> dist(p,x) < min d (min delta dj)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S3C1_CUBE_DIST) THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (moi_s3c1_cube p r2) (j:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `dist(p:real^3,x) < min d (min delta dj) /\ dj <= dist(p,x)` MP_TAC THENL
     [ASM_SIMP_TAC[]; REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `W = interval(p - r2 % vec 1,p + r2 % vec 1) DIFF moi_s3c1_cube (p:real^3) r1` THEN
  SUBGOAL_THEN `open (W:real^3->bool) /\ W SUBSET moi_s3c1_cube p r2 /\
                ~((p:real^3) IN W) /\ DISJOINT W j /\
                frontier (moi_s3c1_cube p r) SUBSET W`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_INTERVAL; moi_s3c1_cube; CLOSED_INTERVAL];
      MP_TAC(ISPECL [`p - r2 % vec 1:real^3`; `p + r2 % vec 1:real^3`]
        INTERVAL_OPEN_SUBSET_CLOSED) THEN REWRITE_TAC[moi_s3c1_cube] THEN SET_TAC[];
      REWRITE_TAC[IN_DIFF; MOI_S3C1_IN_CUBE; REAL_SUB_REFL; REAL_ABS_0] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MP_TAC(ISPECL [`p - r2 % vec 1:real^3`; `p + r2 % vec 1:real^3`]
        INTERVAL_OPEN_SUBSET_CLOSED) THEN
      UNDISCH_TAC `DISJOINT (moi_s3c1_cube p r2) (j:real^3->bool)` THEN
      REWRITE_TAC[moi_s3c1_cube] THEN SET_TAC[];
      MATCH_MP_TAC MOI_S3C1_FRONTIER_IN_SHELL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ &0 < r2` STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  (* the shell triangulation t of e INTER W *)
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `h:real^2->real^3`;
                 `k:real^3->real^2`; `r1:real`; `r2:real`] MOI_S3C1_SHELL_TRI) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIONS t = e INTER (W:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  (* the triangulation s of the frontier of the cube Q = moi_s3c1_cube p r *)
  MP_TAC(ISPECL [`moi_s3c1_cube (p:real^3) r`; `{}:(real^3->bool)->bool`] MOI_S4Z_BALL_TRI) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY] THEN MATCH_MP_TAC MOI_S3C1_CUBE_BALL THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:(real^3->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))))) THEN
  (* general position inside W *)
  USE_THEN "gp" (MP_TAC o SPECL [`s:(real^3->bool)->bool`; `t:(real^3->bool)->bool`;
                                  `W:real^3->bool`; `&1`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET; REAL_LT_01] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `k0:real^3->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "cross")))))) THEN
  REMOVE_THEN "gp" (K ALL_TAC) THEN REMOVE_THEN "tri" (K ALL_TAC) THEN
  (* f moves only points of k0, a subset of W *)
  SUBGOAL_THEN `!x:real^3. (g:real^3->real^3) (f x) = x` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism ((:real^3),(:real^3)) (f:real^3->real^3,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN k0 ==> (f:real^3->real^3) x IN k0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3C1_OFF_FIX THEN EXISTS_TAC `g:real^3->real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(!x:real^3. x IN W ==> (f:real^3->real^3) x IN W) /\
                (!x:real^3. x IN moi_s3c1_cube p r2 ==> f x IN moi_s3c1_cube p r2) /\
                f p = p`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `(x:real^3) IN k0` THENL
       [MAP_EVERY UNDISCH_TAC [`(x:real^3) IN k0`; `k0 SUBSET (W:real^3->bool)`;
                               `!x:real^3. x IN k0 ==> (f:real^3->real^3) x IN k0`] THEN
        SET_TAC[];
        ASM_SIMP_TAC[]];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `(x:real^3) IN k0` THENL
       [MAP_EVERY UNDISCH_TAC [`(x:real^3) IN k0`; `k0 SUBSET (W:real^3->bool)`;
                               `W SUBSET moi_s3c1_cube (p:real^3) r2`;
                               `!x:real^3. x IN k0 ==> (f:real^3->real^3) x IN k0`] THEN
        SET_TAC[];
        ASM_SIMP_TAC[]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY UNDISCH_TAC [`~((p:real^3) IN W)`; `k0 SUBSET (W:real^3->bool)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s3c1_cube (p:real^3) r SUBSET moi_s3c1_cube p r2` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_S3C1_IN_CUBE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (moi_s3c1_cube p r) SUBSET moi_s3c1_cube p r2`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN moi_s3c1_cube p r2` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* interior and frontier of c = IMAGE f Q *)
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `moi_s3c1_cube (p:real^3) r`]
    MOI_S3C1_PLH_INT_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^3) IN IMAGE (f:real^3->real^3) (interior (moi_s3c1_cube p r))`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `p:real^3` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_s3c1_cube; INTERIOR_CLOSED_INTERVAL; MOI_S3C1_IN_OCUBE] THEN
    ASM_REWRITE_TAC[REAL_SUB_REFL; REAL_ABS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r)) SUBSET W`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  (* the crossings, first relative to e INTER W, then to (e DIFF j) DELETE p *)
  SUBGOAL_THEN
   `!x. x IN IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r)) INTER e
        ==> pl_crossing_at (IMAGE f (frontier (moi_s3c1_cube p r))) (e INTER W) x`
  ASSUME_TAC THENL
   [REMOVE_THEN "cross" MP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r)) INTER e`;
      `IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r)) SUBSET W`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r)) INTER ((e DIFF j) DELETE p) =
    IMAGE f (frontier (moi_s3c1_cube p r)) INTER e`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r)) SUBSET W`;
      `DISJOINT (W:real^3->bool) j`; `~((p:real^3) IN W)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r)) INTER e
        ==> pl_crossing_at (IMAGE f (frontier (moi_s3c1_cube p r))) ((e DIFF j) DELETE p) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FGB_CROSSING_LOCAL THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r))`;
                          `e INTER (W:real^3->bool)`; `W:real^3->bool`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(x:real^3) IN IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r)) INTER e`;
        `IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r)) SUBSET W`] THEN
      SET_TAC[];
      REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC [`DISJOINT (W:real^3->bool) j`; `~((p:real^3) IN W)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* compactness, then the circles *)
  SUBGOAL_THEN `compact (IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r)) INTER e)`
  ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `moi_s3c1_cube (p:real^3) r2` THEN
      CONJ_TAC THENL [REWRITE_TAC[moi_s3c1_cube; BOUNDED_INTERVAL]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r)) SUBSET W`;
        `W SUBSET moi_s3c1_cube (p:real^3) r2`] THEN
      SET_TAC[];
      MATCH_MP_TAC CLOSED_INTER THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM(ASSUME `frontier (IMAGE (f:real^3->real^3) (moi_s3c1_cube p r)) =
                               IMAGE f (frontier (moi_s3c1_cube p r))`)] THEN
      REWRITE_TAC[FRONTIER_CLOSED]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r))`;
                 `(e DIFF j) DELETE (p:real^3)`] MOI_S4L_CROSSING_CIRCLES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the witnesses *)
  MAP_EVERY EXISTS_TAC
   [`IMAGE (f:real^3->real^3) (moi_s3c1_cube p r)`; `dz:real^3->bool`;
    `fz:real^2->real^3`; `gz:real^3->real^2`;
    `components (IMAGE (f:real^3->real^3) (frontier (moi_s3c1_cube p r)) INTER e)`] THEN
  ASM_REWRITE_TAC[PAIRWISE_DISJOINT_COMPONENTS; GSYM UNIONS_COMPONENTS] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3C1_PLH_BALL THEN EXISTS_TAC `g:real^3->real^3` THEN
    ASM_SIMP_TAC[MOI_S3C1_CUBE_BALL];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `moi_s3c1_cube (p:real^3) r2` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `x < min d (min delta dj) ==> x < d`) THEN ASM_SIMP_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^3->real^3) (moi_s3c1_cube p r) SUBSET moi_s3c1_cube p r2`;
      `DISJOINT (moi_s3c1_cube p r2) (j:real^3->bool)`] THEN
    SET_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN moi_s3c1_cube p r2` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(y:real^3) IN IMAGE (f:real^3->real^3) (moi_s3c1_cube p r)`;
        `IMAGE (f:real^3->real^3) (moi_s3c1_cube p r) SUBSET moi_s3c1_cube p r2`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `fz:real^2->real^3`)) (concl th) &&
      can (find_term ((=) `delta:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REAL_ARITH `x < min d (min delta dj) ==> x < delta`) THEN ASM_SIMP_TAC[]]);;

