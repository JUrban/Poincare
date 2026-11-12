(* ========================================================================= *)
(* pc_moi_s31_link: the meridian lemma of Moise Sec 31 (GTM 47, p.222).     *)
(* Main theorem NULL_POLYGON_2 : |- MOI_S31_NULL_POLYGON_2                  *)
(* (pc_moi_s3032_stmt2.ml).  A polygon in the boundary torus of a PL solid  *)
(* torus, null-homotopic in the solid torus and bounding a PL disk that     *)
(* misses a pi_1-carrier of the interior, bounds a disk in the boundary     *)
(* torus.  Route: if it were essential, a loop of the carrier nonzero in    *)
(* H_1 of the solid torus would be cut by Mayer-Vietoris (MV_POLY) along    *)
(* the torus minus a 3-ball neighbourhood of the disk (BALL_2) into a cycle *)
(* of the torus minus the polygon, whose loops are null in the solid torus. *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt2.ml";;
needs "src/pc_moi_s288_cov.ml";;
needs "src/pc_moi_s34_h1.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_fnd_dn.ml";;
needs "src/pc_moi_fnd_h1.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1. Solid tori, cells and complements of interiors.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3LK_SOLID_TORUS = prove
 (`!s:real^3->bool.
     pl_solid_torus s
     ==> pl_polyhedron s /\ path_connected s /\ compact s /\ closed s /\
         torus_surface (frontier s) /\ frontier s SUBSET s /\
         ~trivial_group(homology_group(&1,subtopology euclidean s))`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(SPEC `s:real^3->bool` MOI_S4U_PL_SOLID_TORUS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
   [UNDISCH_TAC `pl_solid_torus (s:real^3->bool)` THEN
    REWRITE_TAC[pl_solid_torus; GSYM moi_fps_ann; GSYM moi_fps_m] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^(2,1)finite_sum->real^3`
      (X_CHOOSE_THEN `g:real^3->real^(2,1)finite_sum` MP_TAC)) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `s:real^3->bool`)) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[MOI_FPS_M_PL_POLYHEDRON];
    MP_TAC(ISPEC `s:real^3->bool` (CONJUNCT1 PL_SOLID_TORUS_BASIC)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:real^3->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    UNDISCH_TAC `spine (j:real^3->bool) s` THEN REWRITE_TAC[spine; homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^(2,2)finite_sum->real^3` (X_CHOOSE_THEN
      `g:real^3->real^(2,2)finite_sum` (X_CHOOSE_THEN `p:real^2` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `s:real^3->bool`)) THEN
    MATCH_MP_TAC PATH_CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PATH_CONNECTED_PCROSS THEN
    SIMP_TAC[CONVEX_IMP_PATH_CONNECTED; CONVEX_CBALL] THEN
    MATCH_MP_TAC PATH_CONNECTED_SPHERE THEN REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC]);;

let MOI_S3LK_CELL = prove
 (`!n (d:real^N->bool) b.
     pl_cell_with_boundary n d b
     ==> pl_ball n d /\ pl_polyhedron d /\ compact d /\ b SUBSET d`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `pl_ball n (d:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_cell_with_boundary n (d:real^N->bool) b` THEN
    REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_cell_with_boundary n (d:real^N->bool) b` THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `pl_homeomorphism (k,d) (f:real^N->real^N,g)` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `polytope (k:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `&n:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `d:real^N->bool`)) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    MP_TAC(ISPEC `k:real^N->bool` RELATIVE_FRONTIER_SUBSET) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED; CLOSURE_CLOSED]]);;

let MOI_S3LK_CPLX_POLYTOPE = prove
 (`!(t:(real^N->bool)->bool) c.
     simplicial_complex t /\ c IN t
     ==> polytope c /\ convex c /\ closed c /\ compact c`,
  REWRITE_TAC[simplicial_complex] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `polytope (c:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (c:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_CLOSED; POLYTOPE_IMP_COMPACT]]);;

let MOI_S3LK_SIMPLEX_OFF = prove
 (`!(t:(real^N->bool)->bool) l c.
     simplicial_complex t /\ simplicial_subcomplex l t /\ c IN t /\ ~(c SUBSET UNIONS l)
     ==> DISJOINT c (interior (UNIONS l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `polytope (c:real^N->bool) /\ convex c /\ closed c` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `c:real^N->bool`] MOI_S3LK_CPLX_POLYTOPE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (relative_interior c) (UNIONS l:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(r:real^N->bool) IN t` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(c INTER r:real^N->bool) face_of c` ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplicial_complex] o check (fun th ->
        concl th = `simplicial_complex (t:(real^N->bool)->bool)`)) THEN
      DISCH_THEN(MP_TAC o SPECL [`c:real^N->bool`; `r:real^N->bool`] o
        CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `c INTER r:real^N->bool = c` THENL
     [UNDISCH_TAC `~(c SUBSET UNIONS (l:(real^N->bool)->bool))` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `r:real^N->bool` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; UNDISCH_TAC `(r:real^N->bool) IN l` THEN SET_TAC[]];
      MP_TAC(ISPECL [`c INTER r:real^N->bool`; `c:real^N->bool`]
        FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `c:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(x:real^N) IN relative_interior c` THEN UNDISCH_TAC `(x:real^N) IN r` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN interior (UNIONS l)` THEN REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN closure (relative_interior c)` MP_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS l` MP_TAC THENL
   [UNDISCH_TAC `ball(x:real^N,e) SUBSET UNIONS l` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `DISJOINT (relative_interior c) (UNIONS l:real^N->bool)` THEN
    UNDISCH_TAC `(y:real^N) IN relative_interior c` THEN SET_TAC[]]);;

let MOI_S3LK_COMPL_UNIONS = prove
 (`!(t:(real^N->bool)->bool) l.
     simplicial_complex t /\ simplicial_subcomplex l t /\
     UNIONS l SUBSET interior (UNIONS t)
     ==> UNIONS t DIFF interior (UNIONS l) = UNIONS {c | c IN t /\ ~(c SUBSET UNIONS l)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_DIFF] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `c:real^N->bool`]
      MOI_S3LK_SIMPLEX_OFF) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `c0:real^N->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM]) THEN
  SUBGOAL_THEN `!c:real^N->bool. c IN t /\ (x:real^N) IN c ==> c SUBSET UNIONS l`
  (LABEL_TAC "claim") THENL
   [X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `c:real^N->bool` o check (fun th ->
      is_forall(concl th) && is_disj(snd(dest_forall(concl th))))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS {c | c IN t /\ ~((x:real^N) IN c)})` MP_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; SET_TAC[]];
      ASM_MESON_TAC[MOI_S3LK_CPLX_POLYTOPE]];
    ALL_TAC] THEN
  REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ANTS_TAC THENL [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN interior (UNIONS t)` MP_TAC THENL
   [ASM_MESON_TAC[SUBSET; IN_UNIONS]; ALL_TAC] THEN
  REWRITE_TAC[IN_INTERIOR] THEN DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~((x:real^N) IN interior (UNIONS l))` THEN REWRITE_TAC[IN_INTERIOR] THEN
  EXISTS_TAC `min e1 e2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REWRITE_TAC[SUBSET; IN_BALL; REAL_LT_MIN] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS t` MP_TAC THENL
   [UNDISCH_TAC `ball(x:real^N,e2) SUBSET UNIONS t` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(x:real^N) IN c` THENL
   [USE_THEN "claim" (MP_TAC o SPEC `c:real^N->bool`) THEN
    REWRITE_TAC[SUBSET; ASSUME `(c:real^N->bool) IN t`; ASSUME `(x:real^N) IN c`] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[IN_UNIONS];
    ALL_TAC] THEN
  UNDISCH_TAC `ball(x:real^N,e1) SUBSET (:real^N) DIFF UNIONS {c | c IN t /\ ~(x IN c)}` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN EXISTS_TAC `c:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3LK_COMPL_POLY = prove
 (`!q s:real^N->bool.
     pl_polyhedron q /\ pl_polyhedron s /\ s SUBSET interior q
     ==> pl_polyhedron (q DIFF interior s) /\ closed (q DIFF interior s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`q:real^N->bool`; `s:real^N->bool`] MOI_S4J_PAIR_TRIANGULATION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `q:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` (X_CHOOSE_THEN
    `l:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_S3LK_COMPL_UNIONS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{c | c IN t /\ ~(c SUBSET (s:real^N->bool))}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; SET_TAC[]];
      ASM_MESON_TAC[MOI_S3LK_CPLX_POLYTOPE]];
    MATCH_MP_TAC CLOSED_DIFF THEN
    ASM_SIMP_TAC[OPEN_INTERIOR; PL_POLYHEDRON_IMP_COMPACT; COMPACT_IMP_CLOSED]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2. A small PL 3-ball neighbourhood of a PL disk (BALL_2).           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3LK_ITER_FINITE = prove
 (`!(c:(real^N->bool)->bool) n.
     FINITE c ==> FINITE (ITER n barycentric_subdivision c)`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  ASM_MESON_TAC[MOI_BAR_SUBDIVISION_FINITE]);;

let MOI_S3LK_REL_INTERIOR = prove
 (`!q n x:real^N.
     x IN (subtopology euclidean q) interior_of n /\ x IN interior q
     ==> x IN interior n`,
  REPEAT GEN_TAC THEN REWRITE_TAC[interior_of; IN_ELIM_THM; OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N->bool` MP_TAC) ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_INTERIOR] THEN
  SUBGOAL_THEN `(x:real^N) IN w INTER interior q` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (w INTER interior q:real^N->bool)` MP_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR]; ALL_TAC] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `q:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]);;

let MOI_S3LK_NBHD = prove
 (mk_imp(moi_n3 MOI_FND_DERIVED_NBHD_BALL_2,
  `!(q:real^3->bool) d gg v.
     polytope q /\ pl_cell_with_boundary 2 d gg /\ d SUBSET interior q /\
     open v /\ d SUBSET v
     ==> ?n. pl_ball 3 n /\ n SUBSET interior q /\ n SUBSET v /\ d SUBSET interior n`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3LK_CELL) THEN
  MP_TAC(ISPECL [`q:real^3->bool`; `d:real^3->bool`] MOI_S4J_PAIR_TRIANGULATION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON] THEN
    MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(real^3->bool)->bool` (X_CHOOSE_THEN
    `l0:(real^3->bool)->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `lf_simplicial_complex (t0:(real^3->bool)->bool) /\ FINITE t0`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FMB_SC_LF] THEN ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `l0:(real^3->bool)->bool`;
                 `(q:real^3->bool) INTER (v INTER interior q)`] DERIVED_NBHD_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR];
      MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `m:num`)] THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `l0:(real^3->bool)->bool`; `m:num`]
    MOI_FDN_ITER_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `t = ITER m barycentric_subdivision (t0:(real^3->bool)->bool)` THEN
  ABBREV_TAC `l = ITER m barycentric_subdivision (l0:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool) /\ l SUBSET t` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
      CONJ_TAC THENL
       [EXPAND_TAC "t" THEN MATCH_MP_TAC MOI_S3LK_ITER_FINITE THEN ASM_REWRITE_TAC[];
        ASM_MESON_TAC[simplicial_subcomplex]];
      ASM_MESON_TAC[simplicial_subcomplex]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. {w} IN l ==> pl_sphere 2 (UNIONS (simplicial_link t w))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FMB_INTERIOR_VERTEX_SPHERE THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^3) IN UNIONS l` MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^3}` THEN ASM_REWRITE_TAC[IN_SING];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`] o
    check (fun th -> is_forall(concl th) && can (find_term (fun t -> is_const t &&
      fst(dest_const t) = "derived_frontier")) (concl th))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN EXISTS_TAC `2` THEN
    ASM_REWRITE_TAC[LE_REFL];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `derived_nbhd (t:(real^3->bool)->bool) l` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_S3LK_CELL o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_cell_with_boundary"))
        (concl th) && not (is_forall (concl th)) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "derived_nbhd")) (concl th))) THEN
    SIMP_TAC[];
    UNDISCH_TAC `derived_nbhd (t:(real^3->bool)->bool) l SUBSET q INTER (v INTER interior q)` THEN
    SET_TAC[];
    UNDISCH_TAC `derived_nbhd (t:(real^3->bool)->bool) l SUBSET q INTER (v INTER interior q)` THEN
    SET_TAC[];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S3LK_REL_INTERIOR THEN EXISTS_TAC `q:real^3->bool` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> can (find_term (fun t -> is_const t &&
        fst(dest_const t) = "interior_of")) (concl th))) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(d:real^3->bool) SUBSET interior q` THEN
      UNDISCH_TAC `(x:real^3) IN d` THEN SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 3. Mayer-Vietoris consequences: H_1 of a box minus the interior of  *)
(* a PL 3-ball is trivial; classes that agree in a trivial H_1 of the       *)
(* union.                                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3LK_MV_TRIVIAL = prove
 (mk_imp(moi_n3 MOI_S31_MV_POLY,
  `!(a:real^3->bool) b x y.
     pl_polyhedron a /\ pl_polyhedron b /\
     trivial_group (homology_group(&1,subtopology euclidean (a UNION b))) /\
     x IN group_carrier(homology_group(&1,subtopology euclidean a)) /\
     y IN group_carrier(homology_group(&1,subtopology euclidean b))
     ==> ?z. z IN group_carrier(homology_group(&1,subtopology euclidean (a INTER b))) /\
             hom_induced (&1) (subtopology euclidean (a INTER b),{})
                         (subtopology euclidean a,{}) (\x. x) z = x /\
             hom_induced (&1) (subtopology euclidean (a INTER b),{})
                         (subtopology euclidean b,{}) (\x. x) z = y`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3->bool`; `b:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [TRIVIAL_GROUP_ALT] o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "trivial_group")) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_TAC `e:((num->real)->real^3)frag->bool`) THEN
  MATCH_MP_TAC(SET_RULE `!s. x IN s /\ y IN s /\ s SUBSET {e:A} ==> x = y`) THEN
  EXISTS_TAC `group_carrier(homology_group(&1,subtopology euclidean
                (a UNION b:real^3->bool)))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S4J_HOM_IN THENL
   [EXISTS_TAC `homology_group(&1,subtopology euclidean (a:real^3->bool))`;
    EXISTS_TAC `homology_group(&1,subtopology euclidean (b:real^3->bool))`] THEN
  ASM_REWRITE_TAC[GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY]);;

let MOI_S3LK_H1_BALL_COMPL = prove
 (mk_imp(moi_n3 MOI_S31_MV_POLY,
  `!(q:real^3->bool) n.
     polytope q /\ pl_ball 3 n /\ n SUBSET interior q
     ==> trivial_group (homology_group(&1,subtopology euclidean (q DIFF interior n)))`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4J_BALL3_FACTS) THEN
  MP_TAC(ISPECL [`q:real^3->bool`; `n:real^3->bool`] MOI_S3LK_COMPL_POLY) THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q DIFF interior n) UNION n = q /\
                (q DIFF interior n) INTER n = frontier (n:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `n:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN
      MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `n:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(n:real^3->bool) SUBSET interior q` THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[TRIVIAL_GROUP_ALT] THEN
  EXISTS_TAC `group_id(homology_group(&1,subtopology euclidean (q DIFF interior n:real^3->bool)))` THEN
  REWRITE_TAC[SUBSET; IN_SING] THEN X_GEN_TAC `c:((num->real)->real^3)frag->bool` THEN
  DISCH_TAC THEN
  MP_TAC(SPECL [`q DIFF interior n:real^3->bool`; `n:real^3->bool`; `c:((num->real)->real^3)frag->bool`;
                `group_id(homology_group(&1,subtopology euclidean (n:real^3->bool)))`]
    (MATCH_MP MOI_S3LK_MV_TRIVIAL (ASSUME (moi_n3 MOI_S31_MV_POLY)))) THEN
  ASM_REWRITE_TAC[GROUP_ID] THEN ANTS_TAC THENL
   [MATCH_MP_TAC MOI_S4J_H1_CONTRACTIBLE THEN MATCH_MP_TAC CONVEX_IMP_CONTRACTIBLE THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:((num->real)->real^3)frag->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `c:((num->real)->real^3)frag->bool`)) THEN
  SUBGOAL_THEN `z = group_id(homology_group(&1,subtopology euclidean (frontier n:real^3->bool)))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `trivial_group (homology_group(&1,subtopology euclidean
                   (frontier n:real^3->bool)))` THEN
    REWRITE_TAC[trivial_group] THEN
    UNDISCH_TAC `z IN group_carrier(homology_group(&1,subtopology euclidean
                   (frontier n:real^3->bool)))` THEN SET_TAC[];
    MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (frontier n:real^3->bool)`;
                   `subtopology euclidean (q DIFF interior n:real^3->bool)`; `\x:real^3. x`]
      GROUP_HOMOMORPHISM_HOM_INDUCED_EMPTY) THEN
    SIMP_TAC[group_homomorphism]]);;

(* ------------------------------------------------------------------------- *)
(* Part 4. Loops of the torus off an essential polygon that is              *)
(* null-homotopic in the solid torus are null in H_1 of the solid torus.    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3LK_NULL_LOOP = prove
 (`!(g:real^3->bool) s z h:real^1->real^3.
     homotopic_with (\f. T) (subtopology euclidean g,subtopology euclidean s)
                    (\x. x) (\x. z) /\
     path h /\ pathfinish h = pathstart h /\ path_image h SUBSET g
     ==> homologous_rel (1,subtopology euclidean s,{})
           (frag_of (path_simplex (h o lift))) =
         group_id (homology_group(&1,subtopology euclidean s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `homotopic_loops s h ((\x:real^3. z) o (h:real^1->real^3))` ASSUME_TAC THENL
   [REWRITE_TAC[homotopic_loops] THEN
    SUBGOAL_THEN `h = (\x:real^3. x) o (h:real^1->real^3)` (fun th ->
      GEN_REWRITE_TAC LAND_CONV [th]) THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_RIGHT THEN
    EXISTS_TAC `\f:real^3->real^3. T` THEN
    EXISTS_TAC `subtopology euclidean (g:real^3->bool)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; CONTINUOUS_MAP_EUCLIDEAN;
                  TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; GSYM path; GSYM path_image] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[pathstart; pathfinish; o_THM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_FH1_LOOP_CLASS_HOMOTOPIC) THEN
  REWRITE_TAC[o_ASSOC] THEN
  SUBGOAL_THEN `((\x:real^3. (z:real^3)) o (h:real^1->real^3)) o lift = (\t:real. z)` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FH1_CONST_LOOP_CLASS THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMOTOPIC_WITH_IMP_CONTINUOUS_MAPS) THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  SUBGOAL_THEN `~(g:real^3->bool = {})` MP_TAC THENL
   [MP_TAC(ISPEC `h:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN ASM SET_TAC[];
    SET_TAC[]]);;

let MOI_S3LK_TRACE_NULL = prove
 (`!(s:real^3->bool) gg x z.
     torus_surface (frontier s) /\ frontier s SUBSET s /\ gg SUBSET frontier s /\
     gg homeomorphic sphere(vec 0:real^2,&1) /\
     (?k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET gg /\
          ~homotopic_loops (frontier s) k (linepath(pathstart k,pathstart k))) /\
     homotopic_with (\f. T) (subtopology euclidean gg,subtopology euclidean s)
                    (\x. x) (\x. z) /\
     x SUBSET frontier s DIFF gg
     ==> group_image (homology_group(&1,subtopology euclidean x),
                      homology_group(&1,subtopology euclidean s))
                     (hom_induced (&1) (subtopology euclidean x,{})
                                       (subtopology euclidean s,{}) (\x. x))
         SUBSET {group_id (homology_group(&1,subtopology euclidean s))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4U_H1_IMAGE_LOOPS THEN REWRITE_TAC[TRIVIAL_SUBGROUP_OF] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `h:real^1->real^3` THEN STRIP_TAC THEN REWRITE_TAC[IN_SING] THEN
  MP_TAC(ISPECL [`frontier s:real^3->bool`; `gg:real^3->bool`; `h:real^1->real^3`]
    MOI_S4U_CURVE_LOOPS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `k:real^1->real^3` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `h':real^1->real^3` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `homotopic_loops s (h:real^1->real^3) h'` MP_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_LOOPS_SUBSET THEN EXISTS_TAC `frontier s:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o MATCH_MP MOI_FH1_LOOP_CLASS_HOMOTOPIC)] THEN
  MATCH_MP_TAC MOI_S3LK_NULL_LOOP THEN
  MAP_EVERY EXISTS_TAC [`gg:real^3->bool`; `z:real^3`] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 5. A loop of the carrier that is nonzero in H_1 of the solid torus. *)
(* ------------------------------------------------------------------------- *)

let MOI_S3LK_GAMMA = prove
 (`!(s:real^3->bool) zm.
     pl_solid_torus s /\ zm SUBSET s /\ loops_carried zm s
     ==> ?g. path g /\ pathfinish g = pathstart g /\ path_image g SUBSET zm /\
             ~(homologous_rel (1,subtopology euclidean s,{}) (frag_of (path_simplex (g o lift))) =
               group_id (homology_group(&1,subtopology euclidean s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3LK_SOLID_TORUS) THEN
  UNDISCH_TAC `~trivial_group(homology_group(&1,subtopology euclidean (s:real^3->bool)))` THEN
  REWRITE_TAC[trivial_group] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?u. u IN group_carrier(homology_group(&1,subtopology euclidean (s:real^3->bool))) /\
                    ~(u = group_id(homology_group(&1,subtopology euclidean s)))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a s:A->bool. a IN s /\ ~(s = {a}) ==> ?u. u IN s /\ ~(u = a)`) THEN
    ASM_REWRITE_TAC[GROUP_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^3. a IN s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `torus_surface (frontier s:real^3->bool)` THEN REWRITE_TAC[torus_surface] THEN
    ASM_CASES_TAC `frontier s:real^3->bool = {}` THENL
     [ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; PCROSS_EQ_EMPTY; SPHERE_EQ_EMPTY] THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `frontier s SUBSET (s:real^3->bool)` THEN
      UNDISCH_TAC `~(frontier s:real^3->bool = {})` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `a:real^3`; `u:((num->real)->real^3)frag->bool`]
    MOI_FH1_H1_LOOP_REPRESENTATIVE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^1->real^3` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `loops_carried (zm:real^3->bool) s` THEN REWRITE_TAC[loops_carried] THEN
  DISCH_THEN(MP_TAC o SPEC `d:real^1->real^3`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^1->real^3` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o MATCH_MP MOI_FH1_LOOP_CLASS_HOMOTOPIC o check (fun th ->
    can (find_term (fun t -> is_const t && fst(dest_const t) = "homotopic_loops")) (concl th))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `u:((num->real)->real^3)frag->bool`)) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Part 6. The meridian lemma (NULL_POLYGON_2).                             *)
(* ------------------------------------------------------------------------- *)

(* The case of an essential polygon is contradictory.  The hypotheses that  *)
(* carry the argument: DISJOINT d zm lets the 3-ball neighbourhood N of d   *)
(* miss the loop gam of the carrier (so gam lies in a = sb - int N), and the *)
(* null-homotopy of gg in sb kills the image of H_1(T - int N) in H_1(sb)   *)
(* (MOI_S3LK_TRACE_NULL), while gam is nonzero there (MOI_S3LK_GAMMA).       *)

let MOI_S3LK_ESSENTIAL_FALSE = prove
 (mk_imp(list_mk_conj [moi_n3 MOI_S31_MV_POLY; moi_n3 MOI_FND_DERIVED_NBHD_BALL_2],
  `!(sb:real^3->bool) gg d zm z k.
     pl_solid_torus sb /\ pl_sphere 1 gg /\ gg SUBSET frontier sb /\
     pl_cell_with_boundary 2 d gg /\ DISJOINT d zm /\ zm SUBSET interior sb /\
     loops_carried zm sb /\
     homotopic_with (\f. T) (subtopology euclidean gg,subtopology euclidean sb)
                    (\x. x) (\x. z) /\
     path k /\ pathfinish k = pathstart k /\ path_image k SUBSET gg /\
     ~homotopic_loops (frontier sb) k (linepath(pathstart k,pathstart k))
     ==> F`),
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3LK_SOLID_TORUS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3LK_CELL) THEN
  (* the loop of the carrier *)
  MP_TAC(ISPECL [`sb:real^3->bool`; `zm:real^3->bool`] MOI_S3LK_GAMMA) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `sb:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `gam:real^1->real^3` STRIP_ASSUME_TAC)] THEN
  (* the box *)
  SUBGOAL_THEN `compact (path_image (gam:real^1->real^3))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_PATH_IMAGE]; ALL_TAC] THEN
  MP_TAC(ISPEC `sb UNION d UNION path_image (gam:real^1->real^3)`
    BOUNDED_SUBSET_OPEN_INTERVAL_SYMMETRIC) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `w:real^3`) THEN
  ABBREV_TAC `q = interval[--w,w:real^3]` THEN
  SUBGOAL_THEN `polytope (q:real^3->bool) /\ pl_polyhedron q /\ interior q = interval(--w,w)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    REWRITE_TAC[POLYTOPE_INTERVAL; INTERIOR_CLOSED_INTERVAL] THEN
    SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  (* the 3-ball neighbourhood of d missing gam *)
  MP_TAC(SPECL [`q:real^3->bool`; `d:real^3->bool`; `gg:real^3->bool`;
                `interval(--w,w) DIFF path_image (gam:real^1->real^3)`]
    (MATCH_MP MOI_S3LK_NBHD (ASSUME (moi_n3 MOI_FND_DERIVED_NBHD_BALL_2)))) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `sb UNION d UNION path_image (gam:real^1->real^3) SUBSET interval(--w,w)` THEN
      SET_TAC[];
      MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[OPEN_INTERVAL; COMPACT_IMP_CLOSED];
      MAP_EVERY UNDISCH_TAC
       [`sb UNION d UNION path_image (gam:real^1->real^3) SUBSET interval(--w,w)`;
        `DISJOINT (d:real^3->bool) zm`; `path_image (gam:real^1->real^3) SUBSET zm`] THEN
      SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `n:real^3->bool` STRIP_ASSUME_TAC)] THEN
  (* H_1 of the box minus the ball is trivial *)
  MP_TAC(SPECL [`q:real^3->bool`; `n:real^3->bool`]
    (MATCH_MP MOI_S3LK_H1_BALL_COMPL (ASSUME (moi_n3 MOI_S31_MV_POLY)))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4J_BALL3_FACTS) THEN
  (* the two pieces *)
  SUBGOAL_THEN `sb SUBSET interior (q:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sb UNION d UNION path_image (gam:real^1->real^3) SUBSET interval(--w,w)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^3->bool`; `n:real^3->bool`] MOI_S3LK_COMPL_POLY) THEN
  MP_TAC(ISPECL [`q:real^3->bool`; `sb:real^3->bool`] MOI_S3LK_COMPL_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `a = (sb:real^3->bool) INTER (q DIFF interior n)` THEN
  ABBREV_TAC `b = (q DIFF interior sb) INTER (q DIFF interior (n:real^3->bool))` THEN
  SUBGOAL_THEN `pl_polyhedron (a:real^3->bool) /\ pl_polyhedron (b:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN CONJ_TAC THEN
    MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3->bool) UNION b = q DIFF interior n /\
                a INTER b = frontier sb DIFF interior n`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["a"; "b"] THEN
    SUBGOAL_THEN `frontier sb = sb DIFF interior (sb:real^3->bool)` MP_TAC THENL
     [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED]; ALL_TAC] THEN
    MP_TAC(ISPEC `sb:real^3->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `q:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `sb SUBSET interior (q:real^3->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* gam lies in a *)
  SUBGOAL_THEN `path_image (gam:real^1->real^3) SUBSET a` ASSUME_TAC THENL
   [EXPAND_TAC "a" THEN
    MAP_EVERY UNDISCH_TAC
     [`(n:real^3->bool) SUBSET interval(--w,w) DIFF path_image (gam:real^1->real^3)`;
      `sb UNION d UNION path_image (gam:real^1->real^3) SUBSET interval(--w,w)`;
      `path_image (gam:real^1->real^3) SUBSET zm`; `(zm:real^3->bool) SUBSET interior sb`] THEN
    MP_TAC(ISPEC `sb:real^3->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `n:real^3->bool` INTERIOR_SUBSET) THEN
    EXPAND_TAC "q" THEN MP_TAC(ISPECL [`--w:real^3`; `w:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `ca = homologous_rel (1,subtopology euclidean a,{})
                     (frag_of (path_simplex ((gam:real^1->real^3) o lift)))` THEN
  SUBGOAL_THEN `ca IN group_carrier(homology_group(&1,subtopology euclidean (a:real^3->bool)))`
  ASSUME_TAC THENL
   [EXPAND_TAC "ca" THEN MATCH_MP_TAC MOI_FH1_LOOP_CLASS_IN_CARRIER THEN
    ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN; o_THM; LIFT_NUM] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`a:real^3->bool`; `b:real^3->bool`; `ca:((num->real)->real^3)frag->bool`;
                `group_id(homology_group(&1,subtopology euclidean (b:real^3->bool)))`]
    (MATCH_MP MOI_S3LK_MV_TRIVIAL (ASSUME (moi_n3 MOI_S31_MV_POLY)))) THEN
  ASM_REWRITE_TAC[GROUP_ID] THEN
  DISCH_THEN(X_CHOOSE_THEN `zz:((num->real)->real^3)frag->bool` STRIP_ASSUME_TAC) THEN
  (* push to sb in two ways *)
  ABBREV_TAC `xx = frontier sb DIFF interior (n:real^3->bool)` THEN
  SUBGOAL_THEN `xx SUBSET (a:real^3->bool) /\ a SUBSET sb` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(a:real^3->bool) INTER b = xx` THEN SET_TAC[];
      EXPAND_TAC "a" THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `hom_induced (&1) (subtopology euclidean xx,{}) (subtopology euclidean sb,{})
                (\x:real^3. x) zz =
    homologous_rel (1,subtopology euclidean sb,{})
      (frag_of (path_simplex ((gam:real^1->real^3) o lift)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&1:int`; `subtopology euclidean (xx:real^3->bool)`;
                   `subtopology euclidean (a:real^3->bool)`;
                   `subtopology euclidean (sb:real^3->bool)`;
                   `\x:real^3. x`; `\x:real^3. x`] HOM_INDUCED_COMPOSE_EMPTY) THEN
    ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION] THEN
    SUBGOAL_THEN `(\x:real^3. x) o (\x:real^3. x) = (\x. x)` SUBST1_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM(ASSUME `homologous_rel (1,subtopology euclidean a,{})
                     (frag_of (path_simplex ((gam:real^1->real^3) o lift))) = ca`)] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) MOI_FH1_HOM_INDUCED_LOOP o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[ATOP_CONTINUOUS_MAP_INCLUSION] THEN
      ASM_REWRITE_TAC[GSYM PATH_EUCLIDEAN; o_THM; LIFT_NUM] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
      REWRITE_TAC[FUN_EQ_THM; o_THM]];
    ALL_TAC] THEN
  MP_TAC(SPECL [`sb:real^3->bool`; `gg:real^3->bool`; `xx:real^3->bool`; `z:real^3`]
    MOI_S3LK_TRACE_NULL) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_S4U_PL_SPHERE1_CIRCLE] THEN CONJ_TAC THENL
     [EXISTS_TAC `k:real^1->real^3` THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "xx" THEN
      MAP_EVERY UNDISCH_TAC
       [`(gg:real^3->bool) SUBSET d`; `(d:real^3->bool) SUBSET interior n`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; group_image; FORALL_IN_IMAGE; IN_SING] THEN
  DISCH_THEN(MP_TAC o SPEC `zz:((num->real)->real^3)frag->bool`) THEN
  ASM_REWRITE_TAC[]);;

let NULL_POLYGON_2 = prove
 (MOI_S31_NULL_POLYGON_2,
  DISCH_THEN(fun th ->
    let ths = CONJUNCTS th in
    ASSUME_TAC (el 0 ths) THEN ASSUME_TAC (el 2 ths)) THEN
  MAP_EVERY X_GEN_TAC [`sb:real^3->bool`; `gg:real^3->bool`; `d:real^3->bool`;
                       `zm:real^3->bool`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC
   `?k. path k /\ pathfinish k = pathstart k /\ path_image k SUBSET gg /\
        ~homotopic_loops (frontier sb) k (linepath(pathstart k,pathstart (k:real^1->real^3)))`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `k:real^1->real^3` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MATCH_MP_TAC(MATCH_MP MOI_S3LK_ESSENTIAL_FALSE
      (CONJ (ASSUME (moi_n3 MOI_S31_MV_POLY))
            (ASSUME (moi_n3 MOI_FND_DERIVED_NBHD_BALL_2)))) THEN
    MAP_EVERY EXISTS_TAC [`sb:real^3->bool`; `gg:real^3->bool`; `d:real^3->bool`;
                          `zm:real^3->bool`; `z:real^3`; `k:real^1->real^3`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S8C_INESSENTIAL_DISK THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN MESON_TAC[]]);;

