(* ========================================================================= *)
(* pc_moi_fnd_split: the splitting operation at a disk in real^3 (Moise,    *)
(* Geometric Topology in Dimensions 2 and 3, GTM 47, 28.19-28.20, p.209).    *)
(* Main theorem (statement terms of pc_moi_fnd_stmt, pc_moi_fnd_stmt3 and    *)
(* pc_moi_fnd_stmt4):                                                        *)
(*   SPLIT_SURFACE_DISK_3 = mk_imp(MOI_FND_DERIVED_NBHD_BALL_2 /\            *)
(*                                 MOI_FND_SPLIT_TRACE_ANNULUS,              *)
(*                                 MOI_FND_SPLIT_DISK_R3)                    *)
(* Route: triangulate a 3-simplex S containing d and M = UNIONS m with d, M  *)
(* as subcomplexes; N = derived_nbhd t ld is a 3-cell (BALL_2), its          *)
(* frontier F a 2-sphere; the trace a = N INTER M is an annulus with ends    *)
(* j1, j2 = F INTER M (the antecedent SPLIT_TRACE_ANNULUS); j1, j2 bound     *)
(* disjoint disks d1, d2 in F (SPHERE_SPLIT, DISK_COMPLEMENT); m' glues the  *)
(* closure of M - a to d1, d2 (MOI_S26_SURF_GLUE, SURF_GLUE in               *)
(* pc_moi_s26_surf); the polygon lemma DERIVED_NBHD_POLYGON_2 is from        *)
(* pc_moi_fnd_nb2f; the x-clause uses closure(|x| - N) or |x| UNION N.       *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt3.ml";;
needs "src/pc_moi_fnd_stmt4.ml";;
needs "src/pc_moi_s2628_stmt.ml";;
needs "src/pc_moi_fnd_nb2.ml";;
needs "src/pc_moi_fnd_rnb2.ml";;
needs "src/pc_moi_s28_trib.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_fnd_dn.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_fnd_euler.ml";;
needs "src/pc_moi_fnd_nb2f.ml";;
needs "src/pc_moi_s26_surf.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Step S1: a triangulated box around d and M.                              *)
(* ========================================================================= *)

(* The simplices of a refinement lying in the union of a refined family.     *)

let MOI_FSP_SUBPOLY = prove
 (`!(t:(real^N->bool)->bool) c.
     simplicial_complex t /\ (!k. k IN c ==> ?f. f SUBSET t /\ k = UNIONS f)
     ==> simplicial_subcomplex {s | s IN t /\ s SUBSET UNIONS c} t /\
         UNIONS {s | s IN t /\ s SUBSET UNIONS c} = UNIONS c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:real^N->bool`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (t:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`f:real^N->bool`; `s:real^N->bool`] o
        CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^N) IN f` THEN SET_TAC[]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real^N) IN k` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      UNDISCH_TAC `(k:real^N->bool) IN c` THEN UNDISCH_TAC `k = UNIONS (f:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `(s:real^N->bool) IN f` THEN SET_TAC[]]]);;

(* A polyhedron with two subpolyhedra is triangulated with both as           *)
(* subcomplexes.                                                             *)

let MOI_FSP_TRIANGULATE3 = prove
 (`!(p:real^N->bool) q1 q2.
     pl_polyhedron p /\ pl_polyhedron q1 /\ pl_polyhedron q2 /\
     q1 SUBSET p /\ q2 SUBSET p
     ==> ?t l1 l2. simplicial_complex t /\ UNIONS t = p /\
                   simplicial_subcomplex l1 t /\ UNIONS l1 = q1 /\
                   simplicial_subcomplex l2 t /\ UNIONS l2 = q2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `cp:(real^N->bool)->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `c1:(real^N->bool)->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `c2:(real^N->bool)->bool` STRIP_ASSUME_TAC)
        STRIP_ASSUME_TAC))) THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq (concl th) && is_var (lhs (concl th))))) THEN
  MP_TAC(ISPEC `cp UNION c1 UNION c2:(real^N->bool)->bool` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_UNION; IN_UNION] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ref")))) THEN
  MAP_EVERY EXISTS_TAC
   [`t:(real^N->bool)->bool`;
    `{s:real^N->bool | s IN t /\ s SUBSET UNIONS c1}`;
    `{s:real^N->bool | s IN t /\ s SUBSET UNIONS c2}`] THEN
  SUBGOAL_THEN
   `!c:(real^N->bool)->bool.
      (!k. k IN c ==> k IN cp UNION c1 UNION c2)
      ==> simplicial_subcomplex {s | s IN t /\ s SUBSET UNIONS c} t /\
          UNIONS {s | s IN t /\ s SUBSET UNIONS c} = UNIONS c`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FSP_SUBPOLY THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_THEN "ref" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[IN_UNION] THEN REWRITE_TAC[UNIONS_UNION] THEN ASM SET_TAC[]);;

(* PL cells are compact polyhedra.                                           *)

let MOI_FSP_CELL_POLYHEDRON = prove
 (`!n (d:real^N->bool) j.
     pl_cell_with_boundary n d j ==> pl_polyhedron d /\ compact d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o CONJUNCT1 o CONJUNCT2 o
              GEN_REWRITE_RULE I [homeomorphism]) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{k:real^N->bool}` THEN
    REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; homeomorphism]]);;

(* A box around a bounded nonempty set; the box is a PL 3-cell bounded by    *)
(* its frontier.                                                             *)

let MOI_FSP_BOX = prove
 (`!X:real^3->bool.
     bounded X /\ ~(X = {})
     ==> ?a b. (!i. 1 <= i /\ i <= 3 ==> a$i < b$i) /\ X SUBSET interval(a,b)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_TAC `b:real^3`) o
    MATCH_MP BOUNDED_SUBSET_OPEN_INTERVAL) THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM DIMINDEX_3; GSYM(CONJUNCT2 INTERVAL_NE_EMPTY)] THEN ASM SET_TAC[]);;

let MOI_FSP_BOX_FACTS = prove
 (`!a b:real^3.
     (!i. 1 <= i /\ i <= 3 ==> a$i < b$i)
     ==> pl_polyhedron (interval[a,b]) /\
         interior (interval[a,b]) = interval(a,b) /\
         interval(a,b) SUBSET interval[a,b] /\
         relative_frontier (interval[a,b]) = interval[a,b] DIFF interval(a,b) /\
         pl_cell_with_boundary 3 (interval[a,b]) (interval[a,b] DIFF interval(a,b))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(interior (interval[a:real^3,b]) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_3] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier (interval[a:real^3,b]) = interval[a,b] DIFF interval(a,b)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; FRONTIER_CLOSED_INTERVAL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_OPEN_SUBSET_CLOSED] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{interval[a:real^3,b]}` THEN
    REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN MESON_TAC[POLYTOPE_INTERVAL];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl)) THEN
    MATCH_MP_TAC MOI_S4A_POLY_CELL_3 THEN REWRITE_TAC[POLYTOPE_INTERVAL] THEN
    REWRITE_TAC[GSYM DIMINDEX_3] THEN MATCH_MP_TAC AFF_DIM_NONEMPTY_INTERIOR THEN
    ASM_REWRITE_TAC[]]);;

(* Iterated subdivisions of finite complexes are finite.                     *)

let MOI_FSP_ITER_FINITE = prove
 (`!(t:(real^N->bool)->bool) n.
     FINITE t ==> FINITE (ITER n barycentric_subdivision t)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[ITER; MOI_BAR_SUBDIVISION_FINITE]);;

(* S1: a triangulated box t with d and M as subcomplexes, the vertices of d *)
(* interior, the surface subcomplex combinatorial, N(d) inside v and the box. *)

let MOI_FSP_SETUP = prove
 (`!(m:(real^3->bool)->bool) d j v.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\ open v /\ d SUBSET v
     ==> ?a b t ld lm.
           (!i. 1 <= i /\ i <= 3 ==> a$i < b$i) /\
           d UNION UNIONS m SUBSET interval(a,b) /\
           FINITE t /\ simplicial_complex t /\ lf_simplicial_complex t /\
           UNIONS t = interval[a,b] /\
           combinatorial_manifold_with_boundary 3 t /\
           complex_boundary t = interval[a,b] DIFF interval(a,b) /\
           simplicial_subcomplex ld t /\ UNIONS ld = d /\
           simplicial_subcomplex lm t /\ UNIONS lm = UNIONS m /\
           FINITE lm /\ combinatorial_manifold 2 lm /\
           (!w. {w} IN ld ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
           derived_nbhd t ld SUBSET v INTER interval(a,b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (d:real^3->bool) /\ compact d` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSP_CELL_POLYHEDRON]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (UNIONS m:real^3->bool) /\ compact (UNIONS m)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `!s:real^3->bool. s IN m ==> polytope s` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `?n. n simplex (s:real^3->bool)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[combinatorial_manifold; lf_simplicial_complex]; ALL_TAC] THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `m:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[POLYTOPE_IMP_COMPACT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(d:real^3->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^3->bool) j` THEN
    REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_MESON_TAC[SIMPLEX_EMPTY; INT_ARITH `~(&2:int = -- &1)`];
    ALL_TAC] THEN
  MP_TAC(ISPEC `d UNION UNIONS m:real^3->bool` MOI_FSP_BOX) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[BOUNDED_UNION; COMPACT_IMP_BOUNDED] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`] MOI_FSP_BOX_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`interval[a:real^3,b]`; `d:real^3->bool`; `UNIONS m:real^3->bool`]
                MOI_FSP_TRIANGULATE3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(real^3->bool)->bool` (X_CHOOSE_THEN `ld0:(real^3->bool)->bool`
    (X_CHOOSE_THEN `lm0:(real^3->bool)->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `lf_simplicial_complex (t0:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_SC_LF THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `ld0:(real^3->bool)->bool`;
                 `interval[a:real^3,b] INTER (v INTER interval(a,b))`]
                DERIVED_NBHD_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERVAL];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MAP_EVERY EXISTS_TAC
   [`a:real^3`; `b:real^3`; `ITER n barycentric_subdivision (t0:(real^3->bool)->bool)`;
    `ITER n barycentric_subdivision (ld0:(real^3->bool)->bool)`;
    `ITER n barycentric_subdivision (lm0:(real^3->bool)->bool)`] THEN
  ABBREV_TAC `t = ITER n barycentric_subdivision (t0:(real^3->bool)->bool)` THEN
  ABBREV_TAC `ld = ITER n barycentric_subdivision (ld0:(real^3->bool)->bool)` THEN
  ABBREV_TAC `lm = ITER n barycentric_subdivision (lm0:(real^3->bool)->bool)` THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `ld0:(real^3->bool)->bool`; `n:num`]
                MOI_FDN_ITER_SUBCOMPLEX) THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `lm0:(real^3->bool)->bool`; `n:num`]
                MOI_FDN_ITER_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC MOI_FSP_ITER_FINITE THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `interval[a:real^3,b] DIFF interval(a,b)`]
                PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (lm:(real^3->bool)->bool) /\ simplicial_complex lm`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
      ASM_MESON_TAC[simplicial_subcomplex];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                   `\x:real^3. x`; `\x:real^3. x`] MOI_FRB_SURF_INVARIANT) THEN
    ASM_REWRITE_TAC[HOMEOMORPHISM_ID] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[combinatorial_manifold; combinatorial_manifold_with_boundary];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3. {w} IN ld ==> pl_sphere 2 (UNIONS (simplicial_link t w))`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `t:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN
    SUBGOAL_THEN `{w:real^3} IN t /\ (w:real^3) IN d` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
        UNDISCH_TAC `UNIONS ld = (d:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^3}` THEN ASM_REWRITE_TAC[IN_SING]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(TAUT `p ==> (p <=> q) ==> q`) THEN
    REWRITE_TAC[IN_DIFF] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `derived_nbhd t ld SUBSET v INTER interval(a:real^3,b)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Step S6: two disjoint circles in a PL 2-sphere bound disjoint disks      *)
(* (SPHERE_SPLIT of pc_moi_sch3_s2).                                         *)
(* ========================================================================= *)

(* Basic facts on PL cells and PL circles.                                    *)

let MOI_FSP_CELL_BASIC = prove
 (`!n (d:real^N->bool) j.
     pl_cell_with_boundary n d j ==> j SUBSET d /\ connected d /\ compact d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]]);;

let MOI_FSP_SPHERE1_NONEMPTY = prove
 (`!j:real^N->bool. pl_sphere 1 j ==> ~(j = {})`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism; homeomorphism] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `IMAGE (f:real^N->real^N) (relative_frontier k) = j` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IMAGE_EQ_EMPTY; RELATIVE_FRONTIER_EQ_EMPTY] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `aff_dim (k:real^N->bool) = &2` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPEC `k:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `bounded (k:real^N->bool)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `aff_dim (k:real^N->bool) = &2` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
    INT_ARITH_TAC;
    UNDISCH_TAC `aff_dim (k:real^N->bool) = &2` THEN ASM_REWRITE_TAC[AFF_DIM_SING] THEN
    INT_ARITH_TAC]);;

(* A connected subset of s minus the common boundary of the two halves of s *)
(* lies in one half.                                                         *)

let MOI_FSP_HALF_SIDE = prove
 (`!(s:real^N->bool) d1 d2 j c.
     d1 UNION d2 = s /\ d1 INTER d2 = j /\ closed d1 /\ closed d2 /\
     connected c /\ c SUBSET s /\ c INTER j = {}
     ==> c SUBSET d1 \/ c SUBSET d2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `c:real^N->bool = {}` THENL [ASM_REWRITE_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s DIFF j:real^N->bool`; `d1 DIFF j:real^N->bool`; `c:real^N->bool`]
                CONNECTED_SUBSET_CLOPEN) THEN
  ASM_CASES_TAC `c INTER (d1 DIFF j:real^N->bool) = {}` THENL
   [DISCH_THEN(K ALL_TAC) THEN DISJ2_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `d1 DIFF j:real^N->bool = (s DIFF j) INTER d1` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `d1 DIFF j:real^N->bool = (s DIFF j) DIFF ((s DIFF j) INTER d2)`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    DISCH_TAC THEN DISJ1_TAC THEN ASM SET_TAC[]]);;

(* Two disjoint polygons j1, j2 in a PL 2-sphere f bound disjoint disks d1, *)
(* d2 in f, each missing the other polygon.                                  *)

let MOI_FSP_TWO_DISKS = prove
 (`!(f:real^3->bool) j1 j2.
     pl_sphere 2 f /\ pl_sphere 1 j1 /\ pl_sphere 1 j2 /\
     j1 SUBSET f /\ j2 SUBSET f /\ j1 INTER j2 = {} /\ connected j1 /\ connected j2
     ==> ?d1 d2. pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
                 d1 SUBSET f /\ d2 SUBSET f /\ d1 INTER d2 = {} /\
                 d1 INTER j2 = {} /\ d2 INTER j1 = {}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^3->bool`; `j1:real^3->bool`] SPHERE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^3->bool` (X_CHOOSE_THEN `b1:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`f:real^3->bool`; `j2:real^3->bool`] SPHERE_SPLIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a2:real^3->bool` (X_CHOOSE_THEN `b2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `compact (a1:real^3->bool) /\ compact (b1:real^3->bool) /\
                compact (a2:real^3->bool) /\ compact (b2:real^3->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FSP_CELL_POLYHEDRON]; ALL_TAC] THEN
  SUBGOAL_THEN `(j2:real^3->bool) SUBSET a1 \/ j2 SUBSET b1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSP_HALF_SIDE THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->bool`; `j1:real^3->bool`] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j1:real^3->bool) SUBSET a2 \/ j1 SUBSET b2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSP_HALF_SIDE THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->bool`; `j2:real^3->bool`] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d1 e1. pl_cell_with_boundary 2 d1 (j1:real^3->bool) /\
            pl_cell_with_boundary 2 e1 j1 /\ d1 UNION e1 = f /\ d1 INTER e1 = j1 /\
            compact d1 /\ compact e1 /\ j2 SUBSET e1`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
      is_disj (concl th) && free_in `j2:real^3->bool` (concl th) &&
      free_in `a1:real^3->bool` (concl th))) THENL
     [MAP_EVERY EXISTS_TAC [`b1:real^3->bool`; `a1:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`a1:real^3->bool`; `b1:real^3->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d2 e2. pl_cell_with_boundary 2 d2 (j2:real^3->bool) /\
            pl_cell_with_boundary 2 e2 j2 /\ d2 UNION e2 = f /\ d2 INTER e2 = j2 /\
            compact d2 /\ compact e2 /\ j1 SUBSET e2`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th ->
      is_disj (concl th) && free_in `j1:real^3->bool` (concl th) &&
      free_in `a2:real^3->bool` (concl th))) THENL
     [MAP_EVERY EXISTS_TAC [`b2:real^3->bool`; `a2:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`a2:real^3->bool`; `b2:real^3->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`d1:real^3->bool`; `d2:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(d1:real^3->bool) INTER j2 = {} /\ (d2:real^3->bool) INTER j1 = {}`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(d2:real^3->bool) SUBSET e1` MP_TAC THENL
   [SUBGOAL_THEN `connected (d2:real^3->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FSP_CELL_BASIC]; ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^3->bool`; `d1:real^3->bool`; `e1:real^3->bool`; `j1:real^3->bool`;
                   `d2:real^3->bool`] MOI_FSP_HALF_SIDE) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(j2:real^3->bool) SUBSET d2` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FSP_CELL_BASIC]; ALL_TAC] THEN
    SUBGOAL_THEN `~(j2:real^3->bool = {})` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FSP_SPHERE1_NONEMPTY]; ALL_TAC] THEN
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* Horizontal and vertical segments in the plane.                             *)

let MOI_FSP_SEG_H = prove
 (`!x1 x2 y (z:real^2).
     x1 < x2
     ==> (z IN segment[vector[x1;y],vector[x2;y]] <=>
          z$2 = y /\ x1 <= z$1 /\ z$1 <= x2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN_SEGMENT; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= u * (x2 - x1) ==> x1 <= (&1 - u) * x1 + u * x2`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
        `&0 <= (&1 - u) * (x2 - x1) ==> (&1 - u) * x1 + u * x2 <= x2`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    STRIP_TAC THEN EXISTS_TAC `((z:real^2)$1 - x1) / (x2 - x1)` THEN
    SUBGOAL_THEN `&0 < x2 - x1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < x2 - x1` THEN CONV_TAC REAL_FIELD;
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]]);;

let MOI_FSP_SEG_V = prove
 (`!x y1 y2 (z:real^2).
     y1 < y2
     ==> (z IN segment[vector[x;y1],vector[x;y2]] <=>
          z$1 = x /\ y1 <= z$2 /\ z$2 <= y2)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[IN_SEGMENT; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH `&0 <= u * (y2 - y1) ==> y1 <= (&1 - u) * y1 + u * y2`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC(REAL_ARITH
        `&0 <= (&1 - u) * (y2 - y1) ==> (&1 - u) * y1 + u * y2 <= y2`) THEN
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
    STRIP_TAC THEN EXISTS_TAC `((z:real^2)$2 - y1) / (y2 - y1)` THEN
    SUBGOAL_THEN `&0 < y2 - y1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_SUB_LE; REAL_LT_IMP_LE] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < y2 - y1` THEN CONV_TAC REAL_FIELD]]);;

(* The boundary of a square is a PL circle, the union of two arcs from one   *)
(* corner to the opposite one; in particular it is connected.               *)

let MOI_FSP_SQ_SPHERE = prove
 (`!r. &0 < r
       ==> pl_sphere 1 (relative_frontier (interval[--vector[r;r]:real^2,vector[r;r]])) /\
           connected (relative_frontier (interval[--vector[r;r]:real^2,vector[r;r]]))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `relative_frontier (interval[--vector[r;r]:real^2,vector[r;r]]) =
    path_image (linepath(vector[--r;--r],vector[r;--r]) ++ linepath(vector[r;--r],vector[r;r]))
    UNION
    path_image (linepath(vector[--r;--r],vector[--r;r]) ++ linepath(vector[--r;r],vector[r;r]))`
  SUBST1_TAC THENL
   [SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    ASM_SIMP_TAC[MOI_FN2_RF_SQUARE] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `z:real^2` THEN REWRITE_TAC[IN_UNION] THEN
    ASM_SIMP_TAC[MOI_FSP_SEG_H; MOI_FSP_SEG_V; REAL_ARITH `&0 < r ==> --r < r`] THEN
    REWRITE_TAC[IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `h1 = linepath(vector[--r;--r]:real^2,vector[r;--r]) ++
                   linepath(vector[r;--r],vector[r;r])` THEN
  ABBREV_TAC `h2 = linepath(vector[--r;--r]:real^2,vector[--r;r]) ++
                   linepath(vector[--r;r],vector[r;r])` THEN
  SUBGOAL_THEN `~(vector[--r;--r]:real^2 = vector[r;--r]) /\
                ~(vector[r;--r]:real^2 = vector[r;r]) /\
                ~(vector[--r;--r]:real^2 = vector[--r;r]) /\
                ~(vector[--r;r]:real^2 = vector[r;r])` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `arc (h1:real^1->real^2) /\ arc (h2:real^1->real^2)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h1"; "h2"] THEN CONJ_TAC THEN MATCH_MP_TAC ARC_JOIN THEN
    ASM_SIMP_TAC[ARC_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_SING] THEN X_GEN_TAC `z:real^2` THEN
    ASM_SIMP_TAC[MOI_FSP_SEG_H; MOI_FSP_SEG_V; REAL_ARITH `&0 < r ==> --r < r`] THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pathstart (h1:real^1->real^2) = vector[--r;--r] /\
                pathfinish h1 = vector[r;r] /\
                pathstart (h2:real^1->real^2) = vector[--r;--r] /\
                pathfinish h2 = vector[r;r]` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["h1"; "h2"] THEN
    REWRITE_TAC[PATHSTART_JOIN; PATHFINISH_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLV_ARCS_SPHERE THEN ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "h1" THEN MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
      SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
      EXPAND_TAC "h2" THEN MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
      SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
      MAP_EVERY EXPAND_TAC ["h1"; "h2"] THEN
      SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATH_IMAGE_LINEPATH] THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^2` THEN
      REWRITE_TAC[IN_INTER; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_SIMP_TAC[MOI_FSP_SEG_H; MOI_FSP_SEG_V; REAL_ARITH `&0 < r ==> --r < r`] THEN
      REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2] THEN ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC CONNECTED_UNION THEN
    ASM_SIMP_TAC[CONNECTED_PATH_IMAGE; ARC_IMP_PATH] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `vector[--r;--r]:real^2` THEN
    ASM_MESON_TAC[PATHSTART_IN_PATH_IMAGE]]);;

(* The ends of a PL annulus: disjoint connected compact subsets of it.        *)

let MOI_FSP_ANN_ENDS = prove
 (`!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1
     ==> j0 SUBSET a /\ j1 SUBSET a /\ j0 INTER j1 = {} /\
         connected j0 /\ connected j1 /\ compact j0 /\ compact j1 /\ compact a`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)))) THEN
  SUBGOAL_THEN
   `relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) SUBSET
    interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
    interval(--vector[&1;&1]:real^2,vector[&1;&1]) /\
    relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]) SUBSET
    interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
    interval(--vector[&1;&1]:real^2,vector[&1;&1]) /\
    relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) INTER
    relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]) = {} /\
    compact (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
    compact (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])) /\
    compact (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
             interval(--vector[&1;&1]:real^2,vector[&1;&1])) /\
    connected (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
    connected (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `&1` MOI_FSP_SQ_SPHERE) THEN MP_TAC(SPEC `&2` MOI_FSP_SQ_SPHERE) THEN
    REWRITE_TAC[REAL_ARITH `&0 < &1 /\ &0 < &2`] THEN
    REPEAT(DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[MOI_FN2_RF_SQUARE; REAL_ARITH `&0 < &1 /\ &0 < &2`] THEN
    SIMP_TAC[COMPACT_DIFF; COMPACT_INTERVAL; OPEN_INTERVAL] THEN
    REWRITE_TAC[SUBSET; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_DIFF; IN_INTERVAL;
                DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `A = interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                  interval(--vector[&1;&1]:real^2,vector[&1;&1])` THEN
  ABBREV_TAC `r1 = relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
  ABBREV_TAC `r2 = relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])` THEN
  SUBGOAL_THEN `homeomorphism (A,a) (f:real^2->real^N,g)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM_MESON_TAC[COMPACT_CONTINUOUS_IMAGE]]);;

(* ========================================================================= *)
(* Triangulated disks, the identity PL homeomorphism, and two               *)
(* disjoint closed connected sets as the components of their union.         *)
(* ========================================================================= *)

(* The surface boundary of the faces of a 2-simplex is its relative frontier. *)

let MOI_FSP_FACE_SB = prove
 (`!k:real^N->bool.
     &2 simplex k ==> surface_boundary {f | f face_of k} = relative_frontier k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim (k:real^N->bool) = &2 /\ convex k /\ polyhedron k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYHEDRON]; ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON] THEN
  REWRITE_TAC[surface_boundary; IN_ELIM_THM] THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; facet_of] THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC INT_REDUCE_CONV THEN
  ASM_CASES_TAC `(s:real^N->bool) face_of k` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `aff_dim (s:real^N->bool) = &1` THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim (s:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{r:real^N->bool | r face_of k /\ aff_dim r = &2 /\ s SUBSET r} = {k}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
     [STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`r:real^N->bool`; `k:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN ASM_SIMP_TAC[FACE_OF_REFL] THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
    REWRITE_TAC[CARD_SING]]);;

(* The identity is a PL homeomorphism of a polyhedron onto itself.            *)

let MOI_FSP_PLH_ID = prove
 (`!s:real^N->bool. pl_polyhedron s ==> pl_homeomorphism (s,s) ((\x. x),(\x. x))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

(* A triangulated PL 2-cell: a finite combinatorial surface with boundary   *)
(* the boundary circle, chi = 1.                                             *)

let MOI_FSP_DISK_COMPLEX = prove
 (`!(d:real^N->bool) j.
     pl_cell_with_boundary 2 d j
     ==> ?c. FINITE c /\ simplicial_complex c /\ combinatorial_manifold_with_boundary 2 c /\
             UNIONS c = d /\ surface_boundary c = j /\ complex_euler c = &1 /\
             (!s. s IN c ==> aff_dim s <= &2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSP_CELL_POLYHEDRON) THEN
  MP_TAC(ISPECL [`d:real^N->bool`; `d:real^N->bool`; `d:real^N->bool`]
                MOI_FSP_TRIANGULATE3) THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^N->bool) j` THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `simplicial_complex {e:real^N->bool | e face_of k} /\
                UNIONS {e:real^N->bool | e face_of k} = k /\
                FINITE {e:real^N->bool | e face_of k}` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`&2:int`; `k:real^N->bool`] MOI_FMB_FACE_COMPLEX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{e:real^N->bool | e face_of k}`; `c:(real^N->bool)->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_FRB_SURF_INVARIANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FRB_FACE_COMPLEX_CMWB2 THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FSP_FACE_SB] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FRB_BALL2_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[pl_ball] THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

(* Two disjoint nonempty closed connected sets are the components of their   *)
(* union.                                                                    *)

let MOI_FSP_TWO_COMPONENTS = prove
 (`!(j1:real^N->bool) j2.
     closed j1 /\ closed j2 /\ connected j1 /\ connected j2 /\
     ~(j1 = {}) /\ ~(j2 = {}) /\ j1 INTER j2 = {}
     ==> components (j1 UNION j2) = {j1,j2}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_UNIQUE THEN
  REWRITE_TAC[UNIONS_2; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`j1 UNION j2:real^N->bool`; `j1:real^N->bool`; `c:real^N->bool`]
                  CONNECTED_SUBSET_CLOPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        SUBGOAL_THEN `j1:real^N->bool = (j1 UNION j2) DIFF j2`
          (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      SIMP_TAC[]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`j1 UNION j2:real^N->bool`; `j2:real^N->bool`; `c:real^N->bool`]
                  CONNECTED_SUBSET_CLOPEN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        SUBGOAL_THEN `j2:real^N->bool = (j1 UNION j2) DIFF j1`
          (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      SIMP_TAC[]]]);;

(* ========================================================================= *)
(* Steps S2, S3: small facts on cells and annuli, the box context, the      *)
(* derived neighbourhood N of d as a PL 3-cell, and the trace of N on M.    *)
(* ========================================================================= *)

(* The boundary of a 2-cell is a PL circle; a cell is a ball.                *)

let MOI_FSP_CELL_SPHERE1 = prove
 (`!(d:real^N->bool) j. pl_cell_with_boundary 2 d j ==> pl_sphere 1 j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
    is_eq (concl th) && is_var (lhs (concl th)))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FMB_PLH_RESTRICT THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `d:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    MP_TAC(ISPECL [`k:real^N->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[]]);;

let MOI_FSP_CELL_BALL = prove
 (`!n (d:real^N->bool) j. pl_cell_with_boundary n d j ==> pl_ball n d`,
  REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[]);;

(* The ends of a PL annulus are nonempty.                                     *)

let MOI_FSP_ANN_NONEMPTY = prove
 (`!(a:real^N->bool) j0 j1.
     pl_annulus_with_ends a j0 j1 ==> ~(j0 = {}) /\ ~(j1 = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)))) THEN
  REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
  SIMP_TAC[MOI_FN2_RF_SQUARE; REAL_ARITH `&0 < &1 /\ &0 < &2`] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              VECTOR_2; VECTOR_NEG_COMPONENT] THEN
  CONJ_TAC THENL
   [EXISTS_TAC `vector[&1;&1]:real^2`; EXISTS_TAC `vector[&2;&2]:real^2`] THEN
  REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC);;

(* The frontier of a closed subset a of a closed set s, relative to s.        *)

let MOI_FSP_SUBTOP_FRONTIER = prove
 (`!(a:real^N->bool) s.
     closed a /\ closed s /\ a SUBSET s
     ==> (subtopology euclidean s) frontier_of a = a INTER closure (s DIFF a)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[FRONTIER_OF_CLOSURES; CLOSURE_OF_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
              EUCLIDEAN_CLOSURE_OF] THEN
  SUBGOAL_THEN `(s:real^N->bool) INTER a = a /\ s INTER (s DIFF a) = s DIFF a`
  (fun th -> REWRITE_TAC[th]) THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
  SUBGOAL_THEN `closure (s DIFF a) SUBSET (s:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_FSP_SB_SUBSET = prove
 (`!c:(real^N->bool)->bool. surface_boundary c SUBSET UNIONS c`,
  REWRITE_TAC[surface_boundary; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

(* The box context of S1, as a predicate.                                    *)

let moi_fsp_box = new_definition
 `moi_fsp_box (m:(real^3->bool)->bool) (d:real^3->bool) (v:real^3->bool)
              (a:real^3) (b:real^3) (t:(real^3->bool)->bool)
              (ld:(real^3->bool)->bool) (lm:(real^3->bool)->bool) <=>
    (!i. 1 <= i /\ i <= 3 ==> a$i < b$i) /\
    d UNION UNIONS m SUBSET interval(a,b) /\
    FINITE t /\ simplicial_complex t /\ lf_simplicial_complex t /\
    UNIONS t = interval[a,b] /\
    combinatorial_manifold_with_boundary 3 t /\
    complex_boundary t = interval[a,b] DIFF interval(a,b) /\
    simplicial_subcomplex ld t /\ UNIONS ld = d /\
    simplicial_subcomplex lm t /\ UNIONS lm = UNIONS m /\
    FINITE lm /\ combinatorial_manifold 2 lm /\
    (!w. {w} IN ld ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
    derived_nbhd t ld SUBSET v INTER interval(a,b)`;;

let MOI_FSP_SETUP_BOX = prove
 (`!(m:(real^3->bool)->bool) d j v.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\ open v /\ d SUBSET v
     ==> ?a b t ld lm. moi_fsp_box m d v a b t ld lm`,
  REWRITE_TAC[moi_fsp_box] THEN MATCH_ACCEPT_TAC MOI_FSP_SETUP);;

(* S2: N = derived_nbhd t ld is a PL 3-cell bounded by F = derived_frontier *)
(* t ld, its complex a combinatorial 3-manifold with boundary F.             *)

let MOI_FSP_N_FACTS = prove
 (`!(m:(real^3->bool)->bool) d j v a b t ld lm.
     pl_cell_with_boundary 2 d j /\ moi_fsp_box m d v a b t ld lm
     ==> FINITE ld /\ FINITE (derived_nbhd_complex t ld) /\
         lf_simplicial_complex (derived_nbhd_complex t ld) /\
         simplicial_subcomplex (derived_nbhd_complex t ld)
           (barycentric_subdivision (barycentric_subdivision t)) /\
         UNIONS (derived_nbhd_complex t ld) = derived_nbhd t ld /\
         pl_cell_with_boundary 3 (derived_nbhd t ld) (derived_frontier t ld) /\
         combinatorial_manifold_with_boundary 3 (derived_nbhd_complex t ld) /\
         complex_boundary (derived_nbhd_complex t ld) = derived_frontier t ld /\
         pl_sphere 2 (derived_frontier t ld) /\
         compact (derived_nbhd t ld) /\
         derived_frontier t ld SUBSET derived_nbhd t ld /\
         d INTER derived_frontier t ld = {} /\
         d SUBSET derived_nbhd t ld /\
         derived_nbhd t ld SUBSET v INTER interval(a,b)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsp_box] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (ld:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_cell_with_boundary 3 (derived_nbhd t ld) (derived_frontier t ld:real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(INST_TYPE [`:3`,`:N`] DERIVED_NBHD_BALL_2) THEN
    ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN EXISTS_TAC `2` THEN
    REWRITE_TAC[LE_REFL] THEN ASM_MESON_TAC[MOI_FSP_CELL_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`derived_nbhd_complex (t:(real^3->bool)->bool) ld`;
                 `derived_frontier (t:(real^3->bool)->bool) ld`]
                PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `derived_frontier t ld SUBSET derived_nbhd t (ld:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[derived_frontier] THEN MATCH_MP_TAC FRONTIER_OF_SUBSET_CLOSED_IN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `d SUBSET derived_nbhd t (ld:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(subtopology euclidean (UNIONS t)) interior_of
                (derived_nbhd t (ld:(real^3->bool)->bool))` THEN
    REWRITE_TAC[INTERIOR_OF_SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `d SUBSET (subtopology euclidean (interval[a:real^3,b])) interior_of
                 (derived_nbhd t (ld:(real^3->bool)->bool))` THEN
  ASM_REWRITE_TAC[derived_frontier; frontier_of] THEN SET_TAC[]);;

(* S3: the trace of N on M is the annulus a with ends j1, j2 (the antecedent *)
(* MOI_FND_SPLIT_TRACE_ANNULUS), it is the 2D derived neighbourhood of j in *)
(* M, and the ends are PL circles (POLYGON_2 for the trace).                 *)

let MOI_FSP_TRACE = prove
 (mk_imp(mk_conj(inst [`:3`,`:N`] MOI_FND_DERIVED_NBHD_POLYGON_2,
                 MOI_FND_SPLIT_TRACE_ANNULUS),
  `!(m:(real^3->bool)->bool) d j v a b t ld lm.
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     moi_fsp_box m d v a b t ld lm
     ==> ?j1 j2.
           pl_annulus_with_ends (derived_nbhd t ld INTER UNIONS m) j1 j2 /\
           derived_frontier t ld INTER UNIONS m = j1 UNION j2 /\
           j SUBSET (derived_nbhd t ld INTER UNIONS m) DIFF (j1 UNION j2) /\
           pl_sphere 1 j1 /\ pl_sphere 1 j2 /\ j1 INTER j2 = {} /\
           connected j1 /\ connected j2 /\ compact j1 /\ compact j2 /\
           ~(j1 = {}) /\ ~(j2 = {}) /\
           UNIONS (ld INTER lm) = j /\ simplicial_subcomplex (ld INTER lm) lm /\
           pl_sphere 1 j /\
           derived_nbhd t ld INTER UNIONS m = derived_nbhd lm (ld INTER lm) /\
           derived_frontier t ld INTER UNIONS m = derived_frontier lm (ld INTER lm)`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "POL") (LABEL_TAC "TRA")) THEN
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsp_box] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 1 (j:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSP_CELL_SPHERE1]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_subcomplex (ld INTER lm) (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex ld (t:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `simplicial_subcomplex lm (t:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_subcomplex; IN_INTER] THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "TRA" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                                  `lm:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `UNIONS lm = UNIONS (m:(real^3->bool)->bool)`;
              ASSUME `UNIONS ld = (d:real^3->bool)`;
              ASSUME `d INTER UNIONS m = (j:real^3->bool)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `j1:real^3->bool` (X_CHOOSE_THEN `j2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`j1:real^3->bool`; `j2:real^3->bool`] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSP_ANN_ENDS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSP_ANN_NONEMPTY) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `UNIONS lm = UNIONS (m:(real^3->bool)->bool)`;
              ASSUME `UNIONS ld = (d:real^3->bool)`;
              ASSUME `d INTER UNIONS m = (j:real^3->bool)`;
              ASSUME `derived_frontier t ld INTER UNIONS m = (j1 UNION j2:real^3->bool)`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `pl_sphere 1 (j1:real^3->bool) /\ pl_sphere 1 (j2:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "POL" (MP_TAC o SPECL [`lm:(real^3->bool)->bool`;
                                    `ld INTER lm:(real^3->bool)->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o el 7 o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `components (j1 UNION j2:real^3->bool) = {j1,j2}` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_FSP_TWO_COMPONENTS THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Steps S6, S7: the new surface m' and its Euler characteristic, and       *)
(* the surface part B of the split.  m' is glued (MOI_S26_SURF_GLUE_BODY)   *)
(* from the closed complement CC of the annulus in M and the two disks;    *)
(* chi(CC) = chi(m) because CC glued to the annulus complex (chi 0) is a   *)
(* triangulation of M.                                                     *)
(* ========================================================================= *)

let MOI_FSP_MPRIME = prove
 (mk_imp(mk_conj(inst [`:3`,`:N`] MOI_FND_DERIVED_NBHD_POLYGON_2,
                 inst [`:3`,`:N`] MOI_S26_SURF_GLUE_BODY),
  `!(m:(real^3->bool)->bool) lm l j1 j2 d1 d2.
     FINITE m /\ combinatorial_manifold 2 m /\
     FINITE lm /\ combinatorial_manifold 2 lm /\ UNIONS lm = UNIONS m /\
     simplicial_subcomplex l lm /\ pl_sphere 1 (UNIONS l) /\
     derived_frontier lm l = j1 UNION j2 /\
     pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
     d1 INTER d2 = {} /\ d1 INTER UNIONS m = j1 /\ d2 INTER UNIONS m = j2
     ==> ?m':(real^3->bool)->bool.
           FINITE m' /\ combinatorial_manifold 2 m' /\
           UNIONS m' = (UNIONS m DIFF derived_nbhd lm l) UNION d1 UNION d2 /\
           complex_euler m' = complex_euler m + &2`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "POL") (LABEL_TAC "GLUE")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (lm:(real^3->bool)->bool) /\
                lf_simplicial_complex (m:(real^3->bool)->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `lm:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (UNIONS m:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[MOI_FM3_LF_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `derived_nbhd lm l INTER closure (UNIONS m DIFF derived_nbhd lm l) =
    (j1 UNION j2:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `derived_frontier lm l = (j1 UNION j2:real^3->bool)` THEN
    REWRITE_TAC[derived_frontier] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_FSP_SUBTOP_FRONTIER THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closure (UNIONS m DIFF derived_nbhd lm l) SUBSET (UNIONS m:real^3->bool) /\
    UNIONS m DIFF derived_nbhd lm l SUBSET closure (UNIONS m DIFF derived_nbhd lm l)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[CLOSURE_SUBSET] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "POL" (MP_TAC o SPECL [`lm:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let ths = CONJUNCTS th in
    MAP_EVERY (fun i -> MP_TAC (el i ths)) [0;1;2;4;10;11;12]) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `cc = {s | s IN barycentric_subdivision (barycentric_subdivision lm) /\
              s SUBSET closure (UNIONS m DIFF derived_nbhd lm l:real^3->bool)}` THEN
  REPEAT(DISCH_THEN ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (cc:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "cc" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j1:real^3->bool) SUBSET d1 /\ (j2:real^3->bool) SUBSET d2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `d1:real^3->bool`; `j1:real^3->bool`] MOI_FSP_CELL_BASIC) THEN
    MP_TAC(ISPECL [`2`; `d2:real^3->bool`; `j2:real^3->bool`] MOI_FSP_CELL_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `j1:real^3->bool`] MOI_FSP_DISK_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`d2:real^3->bool`; `j2:real^3->bool`] MOI_FSP_DISK_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "GLUE" (MP_TAC o SPECL [`c1:(real^3->bool)->bool`; `c2:(real^3->bool)->bool`;
                                   `{}:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[EMPTY_SUBSET; INTER_EMPTY]; ALL_TAC] THEN
  ASM_REWRITE_TAC[DIFF_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `c12:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "GLUE" (MP_TAC o SPECL [`cc:(real^3->bool)->bool`; `c12:(real^3->bool)->bool`;
                                   `j1 UNION j2:real^3->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT CONJ_TAC THENL
     [MESON_TAC[IN_COMPONENTS_SUBSET];
      MESON_TAC[IN_COMPONENTS_SUBSET];
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
        [`closure (UNIONS m DIFF derived_nbhd lm l) SUBSET (UNIONS m:real^3->bool)`;
         `UNIONS m DIFF derived_nbhd lm l SUBSET
          closure (UNIONS m DIFF derived_nbhd lm (l:(real^3->bool)->bool))`;
         `derived_nbhd lm l INTER closure (UNIONS m DIFF derived_nbhd lm l) =
          (j1 UNION j2:real^3->bool)`;
         `derived_nbhd lm l SUBSET UNIONS (m:(real^3->bool)->bool)`;
         `(j1:real^3->bool) SUBSET d1`; `(j2:real^3->bool) SUBSET d2`;
         `d1 INTER UNIONS m = (j1:real^3->bool)`; `d2 INTER UNIONS m = (j2:real^3->bool)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DIFF_EQ_EMPTY; UNION_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "GLUE" (MP_TAC o SPECL [`cc:(real^3->bool)->bool`;
                                   `derived_nbhd_complex lm (l:(real^3->bool)->bool)`;
                                   `j1 UNION j2:real^3->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN REPEAT CONJ_TAC THENL
     [MESON_TAC[IN_COMPONENTS_SUBSET];
      MESON_TAC[IN_COMPONENTS_SUBSET];
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
        [`closure (UNIONS m DIFF derived_nbhd lm l) SUBSET (UNIONS m:real^3->bool)`;
         `UNIONS m DIFF derived_nbhd lm l SUBSET
          closure (UNIONS m DIFF derived_nbhd lm (l:(real^3->bool)->bool))`;
         `derived_nbhd lm l INTER closure (UNIONS m DIFF derived_nbhd lm l) =
          (j1 UNION j2:real^3->bool)`;
         `derived_nbhd lm l SUBSET UNIONS (m:(real^3->bool)->bool)`;
         `(j1:real^3->bool) SUBSET d1`; `(j2:real^3->bool) SUBSET d2`;
         `d1 INTER UNIONS m = (j1:real^3->bool)`; `d2 INTER UNIONS m = (j2:real^3->bool)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[DIFF_EQ_EMPTY; UNION_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIONS g = UNIONS (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MAP_EVERY (fun t -> MP_TAC(ASSUME t))
      [`closure (UNIONS m DIFF derived_nbhd lm l) SUBSET (UNIONS m:real^3->bool)`;
       `UNIONS m DIFF derived_nbhd lm l SUBSET
        closure (UNIONS m DIFF derived_nbhd lm (l:(real^3->bool)->bool))`;
       `derived_nbhd lm l INTER closure (UNIONS m DIFF derived_nbhd lm l) =
        (j1 UNION j2:real^3->bool)`;
       `derived_nbhd lm l SUBSET UNIONS (m:(real^3->bool)->bool)`;
       `(j1:real^3->bool) SUBSET d1`; `(j2:real^3->bool) SUBSET d2`;
       `d1 INTER UNIONS m = (j1:real^3->bool)`; `d2 INTER UNIONS m = (j2:real^3->bool)`] THEN
    SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `complex_euler (g:(real^3->bool)->bool) = complex_euler (m:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC COMPLEX_EULER_PL_INVARIANT THEN
    MAP_EVERY EXISTS_TAC [`\x:real^3. x`; `\x:real^3. x`] THEN
    SUBGOAL_THEN `lf_simplicial_complex (g:(real^3->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `UNIONS g = UNIONS (m:(real^3->bool)->bool)`] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_CM_DIM THEN
      EXISTS_TAC `g:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_CM_DIM THEN
      EXISTS_TAC `m:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FSP_PLH_ID THEN REWRITE_TAC[pl_polyhedron] THEN
      EXISTS_TAC `m:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FM3_LF_POLYTOPE THEN
      EXISTS_TAC `m:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `e:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
      [`closure (UNIONS m DIFF derived_nbhd lm l) SUBSET (UNIONS m:real^3->bool)`;
       `UNIONS m DIFF derived_nbhd lm l SUBSET
        closure (UNIONS m DIFF derived_nbhd lm (l:(real^3->bool)->bool))`;
       `derived_nbhd lm l INTER closure (UNIONS m DIFF derived_nbhd lm l) =
        (j1 UNION j2:real^3->bool)`;
       `derived_nbhd lm l SUBSET UNIONS (m:(real^3->bool)->bool)`;
       `(j1:real^3->bool) SUBSET d1`; `(j2:real^3->bool) SUBSET d2`;
       `d1 INTER UNIONS m = (j1:real^3->bool)`; `d2 INTER UNIONS m = (j2:real^3->bool)`] THEN
    SET_TAC[];
    UNDISCH_TAC `complex_euler (g:(real^3->bool)->bool) = complex_euler (m:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC]);;

(* The ends and the two disks found in parts S3 and S6, as a predicate.        *)

let moi_fsp_ends = new_definition
 `moi_fsp_ends (m:(real^3->bool)->bool) (j:real^3->bool) (t:(real^3->bool)->bool)
               (ld:(real^3->bool)->bool) (j1:real^3->bool) j2 d1 d2 <=>
    pl_annulus_with_ends (derived_nbhd t ld INTER UNIONS m) j1 j2 /\
    derived_frontier t ld INTER UNIONS m = j1 UNION j2 /\
    j SUBSET (derived_nbhd t ld INTER UNIONS m) DIFF (j1 UNION j2) /\
    pl_sphere 1 j1 /\ pl_sphere 1 j2 /\ j1 INTER j2 = {} /\
    pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
    d1 SUBSET derived_frontier t ld /\ d2 SUBSET derived_frontier t ld /\
    d1 INTER d2 = {} /\ d1 INTER j2 = {} /\ d2 INTER j1 = {}`;;

(* Part B: everything in MOI_FND_SPLIT_DISK_R3 except the x-clause, for the  *)
(* box context, with the ends and disks recorded for part C.                 *)

let MOI_FSP_PART_B = prove
 (mk_imp(list_mk_conj[inst [`:3`,`:N`] MOI_FND_DERIVED_NBHD_POLYGON_2;
                      MOI_FND_SPLIT_TRACE_ANNULUS;
                      inst [`:3`,`:N`] MOI_S26_SURF_GLUE_BODY],
  `!(m:(real^3->bool)->bool) d j v a b t ld lm.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     moi_fsp_box m d v a b t ld lm
     ==> ?j1 j2 d1 d2 (m':(real^3->bool)->bool).
           moi_fsp_ends m j t ld j1 j2 d1 d2 /\
           pl_annulus_with_ends (derived_nbhd t ld INTER UNIONS m) j1 j2 /\
           derived_nbhd t ld INTER UNIONS m SUBSET UNIONS m INTER v /\
           j SUBSET (derived_nbhd t ld INTER UNIONS m) DIFF (j1 UNION j2) /\
           pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
           d1 SUBSET v /\ d2 SUBSET v /\ DISJOINT d1 d2 /\
           DISJOINT d (d1 UNION d2) /\
           d1 INTER UNIONS m = j1 /\ d2 INTER UNIONS m = j2 /\
           FINITE m' /\ combinatorial_manifold 2 m' /\
           UNIONS m' = (UNIONS m DIFF (derived_nbhd t ld INTER UNIONS m)) UNION d1 UNION d2 /\
           complex_euler m' = complex_euler m + &2`),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "POL")
    (CONJUNCTS_THEN2 (LABEL_TAC "TRA") (LABEL_TAC "GLUE"))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_N_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "POL" (fun pol -> USE_THEN "TRA" (fun tra ->
    MP_TAC(SPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                  `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                  `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`]
                 (MP MOI_FSP_TRACE (CONJ pol tra))))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j1:real^3->bool` (X_CHOOSE_THEN `j2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(j1:real^3->bool) SUBSET derived_frontier t ld /\
                (j2:real^3->bool) SUBSET derived_frontier t ld`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `derived_frontier t ld INTER UNIONS m = (j1 UNION j2:real^3->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`derived_frontier t (ld:(real^3->bool)->bool)`; `j1:real^3->bool`;
                 `j2:real^3->bool`] MOI_FSP_TWO_DISKS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(j1:real^3->bool) SUBSET d1 /\ (j2:real^3->bool) SUBSET d2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `d1:real^3->bool`; `j1:real^3->bool`] MOI_FSP_CELL_BASIC) THEN
    MP_TAC(ISPECL [`2`; `d2:real^3->bool`; `j2:real^3->bool`] MOI_FSP_CELL_BASIC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d1 INTER UNIONS m = (j1:real^3->bool) /\ d2 INTER UNIONS m = (j2:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`derived_frontier t ld INTER UNIONS m = (j1 UNION j2:real^3->bool)`;
      `(d1:real^3->bool) SUBSET derived_frontier t ld`;
      `(d2:real^3->bool) SUBSET derived_frontier t ld`;
      `(d1:real^3->bool) INTER j2 = {}`; `(d2:real^3->bool) INTER j1 = {}`;
      `(j1:real^3->bool) SUBSET d1`; `(j2:real^3->bool) SUBSET d2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "POL" (fun pol -> USE_THEN "GLUE" (fun glue ->
    MP_TAC(SPECL [`m:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                  `ld INTER lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                  `d1:real^3->bool`; `d2:real^3->bool`]
                 (MP MOI_FSP_MPRIME (CONJ pol glue))))) THEN
  ANTS_TAC THENL
   [UNDISCH_TAC `moi_fsp_box m d v a b t ld (lm:(real^3->bool)->bool)` THEN
    REWRITE_TAC[moi_fsp_box] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `derived_frontier t ld INTER UNIONS m =
                 derived_frontier lm (ld INTER lm:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN REFL_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `derived_nbhd t ld INTER UNIONS m =
               derived_nbhd lm (ld INTER lm:(real^3->bool)->bool)` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  DISCH_THEN(X_CHOOSE_THEN `mm:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`;
                        `d2:real^3->bool`; `mm:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[moi_fsp_ends; DISJOINT] THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t))
   [`derived_nbhd t ld SUBSET v INTER interval(a:real^3,b)`;
    `derived_frontier t ld SUBSET derived_nbhd t (ld:(real^3->bool)->bool)`;
    `d INTER derived_frontier t (ld:(real^3->bool)->bool) = {}`;
    `(d1:real^3->bool) SUBSET derived_frontier t ld`;
    `(d2:real^3->bool) SUBSET derived_frontier t ld`] THEN
  SET_TAC[]);;

(* ========================================================================= *)
(* Complements of subcomplexes.  For a finite complex K and a                *)
(* subcomplex A, the simplices of K inside the closure of UNIONS K minus     *)
(* UNIONS A form a subcomplex whose vertex links are the closed complements  *)
(* of the links; if K and A are combinatorial 3-manifolds with boundary, so  *)
(* is this complement, given the links at the common boundary vertices.      *)
(* ========================================================================= *)

let MOI_FSP_COMP_UNIONS = prove
 (`!(K:(real^N->bool)->bool) A.
     FINITE K /\ lf_simplicial_complex K /\ simplicial_subcomplex A K
     ==> closure (UNIONS K DIFF UNIONS A) = UNIONS {r | r IN K /\ ~(r IN A)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
      ASM_MESON_TAC[MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED]];
    REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `r:real^N->bool` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `convex (r:real^N->bool) /\ closed r` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_CONVEX; MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
    SUBGOAL_THEN `r = closure (relative_interior (r:real^N->bool))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN REWRITE_TAC[SUBSET; IN_DIFF] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      DISCH_TAC THEN UNDISCH_TAC `~((r:real^N->bool) IN A)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
      MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `z:real^N`] THEN
      ASM_SIMP_TAC[MOI_FRN_LF_BAR_COMPLEX]]]);;

(* A nonempty simplex of the complement is a face of a simplex outside A.     *)

let MOI_FSP_COMP_FACE = prove
 (`!(K:(real^N->bool)->bool) A s.
     FINITE K /\ lf_simplicial_complex K /\ simplicial_subcomplex A K /\
     s IN K /\ s SUBSET closure (UNIONS K DIFF UNIONS A) /\ ~(s = {})
     ==> ?r. r IN K /\ ~(r IN A) /\ s face_of r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex (s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
  ASM_CASES_TAC `(s:real^N->bool) IN A` THENL
   [ALL_TAC;
    EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[FACE_OF_REFL]] THEN
  SUBGOAL_THEN `~(relative_interior (s:real^N->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN
  SUBGOAL_THEN `(z:real^N) IN UNIONS {r | r IN K /\ ~(r IN A)}` MP_TAC THENL
   [ASM_SIMP_TAC[GSYM MOI_FSP_COMP_UNIONS] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s INTER r) face_of (s:real^N->bool) /\ (s INTER r) face_of r`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `s INTER r = (s:real^N->bool)` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s INTER r:real^N->bool`; `s:real^N->bool`]
                FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(z:real^N) IN relative_interior s` THEN
  UNDISCH_TAC `(z:real^N) IN r` THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]);;

(* A simplex of c inside the join of v with a link simplex s', not containing *)
(* v, lies in s'.                                                             *)

let MOI_FSP_JOIN_FACE = prove
 (`!(c:(real^N->bool)->bool) v s s'.
     lf_simplicial_complex c /\ {v} IN c /\ s' IN simplicial_link c v /\
     s IN c /\ s SUBSET convex hull (v INSERT s') /\ ~(v IN s)
     ==> s SUBSET s'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
                MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s':real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LINK_IN]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (s':real^N->bool) /\ compact s'` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_CONVEX; MOI_FM3_LF_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) face_of convex hull (v INSERT s')` MP_TAC THENL
   [SUBGOAL_THEN `(s INTER convex hull (v INSERT s')) face_of
                  convex hull (v INSERT (s':real^N->bool))` MP_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_INTER]; ALL_TAC] THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET convex hull (v INSERT s')` THEN
    SIMP_TAC[SET_RULE `!s h:real^N->bool. s SUBSET h ==> s INTER h = s`];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`v INSERT (s':real^N->bool)`; `s:real^N->bool`]
                FACE_OF_CONVEX_HULL_SUBSET) THEN
  ASM_SIMP_TAC[COMPACT_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET s'` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `u:real^N->bool`] HULL_SUBSET) THEN
    UNDISCH_TAC `(u:real^N->bool) SUBSET v INSERT s'` THEN
    UNDISCH_TAC `~((v:real^N) IN s)` THEN
    UNDISCH_TAC `s = convex hull (u:real^N->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull (s':real^N->bool)` THEN
  ASM_SIMP_TAC[HULL_MONO] THEN ASM_MESON_TAC[CONVEX_HULL_EQ; SUBSET_REFL]);;

(* A link simplex is a face of its join with the vertex.                      *)

let MOI_FSP_LINK_FACE_JOIN = prove
 (`!(c:(real^N->bool)->bool) v s.
     lf_simplicial_complex c /\ {v} IN c /\ s IN simplicial_link c v
     ==> s face_of convex hull (v INSERT s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
                MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LINK_IN]; ALL_TAC] THEN
  SUBGOAL_THEN `(s INTER convex hull (v INSERT s)) face_of
                convex hull (v INSERT (s:real^N->bool))` MP_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_INTER]; ALL_TAC] THEN
  UNDISCH_TAC `(s:real^N->bool) SUBSET convex hull (v INSERT s)` THEN
  SIMP_TAC[SET_RULE `!s h:real^N->bool. s SUBSET h ==> s INTER h = s`]);;

(* The link of a vertex in the complement complex is the closed complement   *)
(* of its link in A inside its link in K.                                    *)

let MOI_FSP_LINK_SUB = prove
 (`!(K:(real^N->bool)->bool) A w.
     lf_simplicial_complex K /\ simplicial_subcomplex A K /\ {w} IN K
     ==> FINITE (simplicial_link K w) /\ lf_simplicial_complex (simplicial_link K w) /\
         simplicial_subcomplex (simplicial_link A w) (simplicial_link K w)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`] MOI_FM3_LINK_SC) THEN
    ASM_SIMP_TAC[simplicial_complex];
    MATCH_MP_TAC MOI_FMB_SC_LF THEN MATCH_MP_TAC MOI_FM3_LINK_SC THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[simplicial_subcomplex; SUBSET; simplicial_link; IN_ELIM_THM] THEN
    UNDISCH_TAC `simplicial_subcomplex A (K:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:real^N->bool`] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
      EXISTS_TAC `t:real^N->bool` THEN ASM_MESON_TAC[FACE_OF_TRANS]]]);;

let MOI_FSP_VERTEX_SUB = prove
 (`!(K:(real^N->bool)->bool) A w t.
     lf_simplicial_complex K /\ simplicial_subcomplex A K /\ {w} IN K /\
     t IN A /\ w IN t
     ==> {w} IN A`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^N->bool) IN K` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `({w} INTER t) face_of (t:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^N} INTER t = {w}` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[simplicial_subcomplex]);;

let MOI_FSP_COMP_LINK = prove
 (`!(K:(real^N->bool)->bool) A w.
     FINITE K /\ lf_simplicial_complex K /\ simplicial_subcomplex A K /\ {w} IN K
     ==> UNIONS (simplicial_link
                  {s | s IN K /\ s SUBSET closure (UNIONS K DIFF UNIONS A)} w) =
         closure (UNIONS (simplicial_link K w) DIFF UNIONS (simplicial_link A w))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `C = {s | s IN K /\ s SUBSET closure (UNIONS K DIFF UNIONS (A:(real^N->bool)->bool))}` THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `A:(real^N->bool)->bool`; `w:real^N`]
                MOI_FSP_LINK_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FSP_COMP_UNIONS] THEN
  SUBGOAL_THEN `lf_simplicial_complex (A:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SUBCOMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!r:real^N->bool. r IN K /\ ~(r IN A) ==> r IN C`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_SIMP_TAC[MOI_FSP_COMP_UNIONS] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FM3_LINK_IN) THEN
    SUBGOAL_THEN `(t:real^N->bool) IN K /\ t SUBSET closure (UNIONS K DIFF UNIONS A) /\
                  (s:real^N->bool) IN K`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^N->bool) IN C` THEN UNDISCH_TAC `(s:real^N->bool) IN C` THEN
      EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `A:(real^N->bool)->bool`; `t:real^N->bool`]
                  MOI_FSP_COMP_FACE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(w:real^N) IN r` ASSUME_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`; `r:real^N->bool`]
                  MOI_FM3_LINK_OPP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s':real^N->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSP_JOIN_FACE THEN
      MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `w:real^N`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(s:real^N->bool) SUBSET r` MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; FACE_OF_TRANS]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN u ==> x SUBSET UNIONS u`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((r:real^N->bool) IN A)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `r:real^N->bool`)) THEN
      SUBGOAL_THEN `{w:real^N} IN A` ASSUME_TAC THENL
       [UNDISCH_TAC `(s':real^N->bool) IN simplicial_link A w` THEN
        REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
        DISCH_THEN(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
        MATCH_MP_TAC MOI_FSP_VERTEX_SUB THEN
        MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `t':real^N->bool`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`A:(real^N->bool)->bool`; `w:real^N`; `s':real^N->bool`]
                    MOI_FM3_LINK_JOIN) THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s':real^N->bool` THEN
    STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN u ==> x SUBSET UNIONS u`) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`; `s':real^N->bool`]
                  MOI_FM3_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`; `s':real^N->bool`]
                  MOI_FSP_LINK_FACE_JOIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(convex hull (w INSERT s':real^N->bool) IN A)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((s':real^N->bool) IN simplicial_link A w)` THEN
      REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `convex hull (w INSERT s':real^N->bool)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex hull (w INSERT s':real^N->bool) IN C` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `convex hull (w INSERT s':real^N->bool) IN C` THEN
      EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[MOI_FM3_LINK_IN]; ASM SET_TAC[]];
      EXISTS_TAC `convex hull (w INSERT s':real^N->bool)` THEN ASM_REWRITE_TAC[]]]);;

(* A PL 2-cell is the closure of its interior.                               *)

let MOI_FSP_CELL_CLOSURE = prove
 (`!(e:real^N->bool) jj. pl_cell_with_boundary 2 e jj ==> closure (e DIFF jj) = e`,
  REPEAT GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [SET_TAC[]; ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (k,e) (f:real^N->real^N,g)` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ closed k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `closure (relative_interior k) = (k:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) (closure (relative_interior k)) SUBSET
                closure (IMAGE f (relative_interior k))` MP_TAC THENL
   [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The complement of a combinatorial 3-manifold with boundary A inside       *)
(* another one K is one, given the links at vertices on both boundaries.     *)

let MOI_FSP_COMP_CMWB = prove
 (`!(K:(real^3->bool)->bool) A.
     FINITE K /\ combinatorial_manifold_with_boundary 3 K /\
     simplicial_subcomplex A K /\ combinatorial_manifold_with_boundary 3 A /\
     (!w. {w} IN K /\ w IN complex_boundary A /\ w IN complex_boundary K /\
          w IN closure (UNIONS K DIFF UNIONS A)
          ==> pl_ball 2 (UNIONS (simplicial_link
                {s | s IN K /\ s SUBSET closure (UNIONS K DIFF UNIONS A)} w)))
     ==> combinatorial_manifold_with_boundary 3
           {s | s IN K /\ s SUBSET closure (UNIONS K DIFF UNIONS A)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^3->bool)->bool) /\
                lf_simplicial_complex (A:(real^3->bool)->bool) /\ FINITE A`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary; FINITE_SUBSET; simplicial_subcomplex];
    ALL_TAC] THEN
  ABBREV_TAC `C = {s | s IN K /\ s SUBSET closure (UNIONS K DIFF UNIONS (A:(real^3->bool)->bool))}` THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBCOMPLEX THEN EXISTS_TAC `K:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN CONJ_TAC THENL
     [SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FM3_LF_FACE];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^3->bool` THEN
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `{w:real^3} IN K /\ w IN closure (UNIONS K DIFF UNIONS A)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{w:real^3} IN C` THEN EXPAND_TAC "C" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (simplicial_link C (w:real^3)) =
                closure (UNIONS (simplicial_link K w) DIFF UNIONS (simplicial_link A w))`
  ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC MOI_FSP_COMP_LINK THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(w:real^3) IN UNIONS A` THENL
   [ALL_TAC;
    SUBGOAL_THEN `simplicial_link A (w:real^3) = {}` ASSUME_TAC THENL
     [REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; simplicial_link; IN_ELIM_THM] THEN
      UNDISCH_TAC `~((w:real^3) IN UNIONS A)` THEN REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[UNIONS_0; DIFF_EMPTY] THEN
    SUBGOAL_THEN `closed (UNIONS (simplicial_link K (w:real^3)))` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN
      MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `A:(real^3->bool)->bool`; `w:real^3`]
                    MOI_FSP_LINK_SUB) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (K:(real^3->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[]] THEN
  SUBGOAL_THEN `(w:real^3) IN complex_boundary A` ASSUME_TAC THENL
   [MP_TAC(ISPEC `A:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN closure ((:real^3) DIFF UNIONS A)` MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s t. (x:real^3) IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `closure (UNIONS K DIFF UNIONS (A:(real^3->bool)->bool))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_COMPLEMENT; IN_DIFF; IN_UNIV] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(w:real^3) IN complex_boundary K` THENL
   [DISJ2_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{w:real^3} IN A` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN UNIONS A` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FSP_VERTEX_SUB THEN
    MAP_EVERY EXISTS_TAC [`K:(real^3->bool)->bool`; `t:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `K:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `A:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `simplicial_link A (w:real^3)` MOI_FM3_DISK_PL) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[MOI_FM3_LINK_SC]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 (UNIONS (simplicial_link A (w:real^3)))
                  (IMAGE (f:real^3->real^3) (relative_frontier k))`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (simplicial_link A (w:real^3)) SUBSET UNIONS (simplicial_link K w)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^3->bool)->bool`; `A:(real^3->bool)->bool`; `w:real^3`]
                  MOI_FSP_LINK_SUB) THEN
    ASM_REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (simplicial_link K (w:real^3))`;
                 `UNIONS (simplicial_link A (w:real^3))`;
                 `IMAGE (f:real^3->real^3) (relative_frontier k)`]
                DISK_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^3->real^3) (relative_frontier k) SUBSET
                UNIONS (simplicial_link A w)` ASSUME_TAC THENL
   [ACCEPT_TAC(CONJUNCT1(SPEC_ALL(MATCH_MP MOI_FSP_CELL_BASIC (ASSUME
      `pl_cell_with_boundary 2 (UNIONS (simplicial_link A (w:real^3)))
                  (IMAGE (f:real^3->real^3) (relative_frontier k))`))));
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closure (UNIONS (simplicial_link K (w:real^3)) DIFF UNIONS (simplicial_link A w)) =
    (UNIONS (simplicial_link K w) DIFF UNIONS (simplicial_link A w)) UNION
    IMAGE (f:real^3->real^3) (relative_frontier k)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `closure (((UNIONS (simplicial_link K (w:real^3)) DIFF
                           UNIONS (simplicial_link A w)) UNION
                          IMAGE (f:real^3->real^3) (relative_frontier k)) DIFF
                         IMAGE f (relative_frontier k))` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_frontier k) SUBSET
                                    UNIONS (simplicial_link A w)` THEN SET_TAC[];
      MATCH_MP_TAC MOI_FSP_CELL_CLOSURE THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_FSP_CELL_BALL THEN
    EXISTS_TAC `IMAGE (f:real^3->real^3) (relative_frontier k)` THEN ASM_REWRITE_TAC[]]);;

let MOI_FSP_COMP_UNIONS2 = prove
 (`!(K:(real^N->bool)->bool) A.
     FINITE K /\ lf_simplicial_complex K /\ simplicial_subcomplex A K
     ==> UNIONS {s | s IN K /\ s SUBSET closure (UNIONS K DIFF UNIONS A)} =
         closure (UNIONS K DIFF UNIONS A)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FSP_COMP_UNIONS] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

let MOI_FSP_COMP_SUBCX = prove
 (`!(K:(real^N->bool)->bool) A.
     lf_simplicial_complex K
     ==> simplicial_subcomplex {s | s IN K /\ s SUBSET closure (UNIONS K DIFF UNIONS A)} K`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_subcomplex; IN_ELIM_THM] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_FACE];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]);;

(* ========================================================================= *)
(* A compact 3-manifold X whose frontier is M (the x of the                 *)
(* x-clause) lies inside the box and is triangulated by the simplices of t  *)
(* inside it; the disk d lies in X or meets it only in its rim.  A finite   *)
(* combinatorial 3-manifold with boundary in real^3 is the closure of its   *)
(* interior.                                                                *)
(* ========================================================================= *)

let MOI_FSP_X_IN_BOX = prove
 (`!(X:real^3->bool) a b M.
     bounded X /\ frontier X = M /\ M SUBSET interval(a,b)
     ==> X SUBSET interval(a,b)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`(:real^3) DIFF interval(a:real^3,b)`; `X:real^3->bool`]
                CONNECTED_INTER_FRONTIER) THEN
  REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPLEMENT_BOUNDED_CONVEX THEN
    REWRITE_TAC[DIMINDEX_3; BOUNDED_INTERVAL; CONVEX_INTERVAL] THEN ARITH_TAC;
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `p:real^3` THEN ASM SET_TAC[];
    SUBGOAL_THEN `~((:real^3) SUBSET X UNION interval(a,b))` MP_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `bounded (X UNION interval(a:real^3,b))` MP_TAC THENL
       [ASM_REWRITE_TAC[BOUNDED_UNION; BOUNDED_INTERVAL]; ALL_TAC] THEN
      SUBGOAL_THEN `X UNION interval(a:real^3,b) = (:real^3)` SUBST1_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[NOT_BOUNDED_UNIV]];
      SET_TAC[]];
    ASM SET_TAC[]]);;

let MOI_FSP_X_SUBCX = prove
 (`!(t:(real^N->bool)->bool) lm (X:real^N->bool).
     lf_simplicial_complex t /\ simplicial_subcomplex lm t /\
     closed X /\ X SUBSET UNIONS t /\ frontier X = UNIONS lm
     ==> simplicial_subcomplex {s | s IN t /\ s SUBSET X} t /\
         UNIONS {s | s IN t /\ s SUBSET X} = X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; IN_ELIM_THM] THEN CONJ_TAC THENL
     [SET_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FM3_LF_FACE];
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `p:real^N`] MOI_FM3_CARRIER_VERTEX) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `r:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]] THEN
  SUBGOAL_THEN `convex (r:real^N->bool) /\ closed r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_CONVEX; MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  ASM_CASES_TAC `relative_interior (r:real^N->bool) INTER UNIONS lm = {}` THENL
   [SUBGOAL_THEN `relative_interior (r:real^N->bool) SUBSET X` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`relative_interior (r:real^N->bool)`; `X:real^N->bool`]
                    CONNECTED_INTER_FRONTIER) THEN
      ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR];
        ASM SET_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `r = closure (relative_interior (r:real^N->bool))` SUBST1_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(r:real^N->bool) IN lm` ASSUME_TAC THENL
     [UNDISCH_TAC `~(relative_interior (r:real^N->bool) INTER UNIONS lm = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `z:real^N`] THEN
      ASM_SIMP_TAC[MOI_FRN_LF_BAR_COMPLEX];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS lm:real^N->bool` THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `frontier (X:real^N->bool)`)) THEN
      ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED]]]);;

(* The triangulation of X by t: a combinatorial 3-manifold with boundary M.  *)

let MOI_FSP_XCX = prove
 (`!(t:(real^3->bool)->bool) lm x.
     FINITE t /\ lf_simplicial_complex t /\ simplicial_subcomplex lm t /\
     FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
     frontier (UNIONS x) = UNIONS lm /\ UNIONS x SUBSET UNIONS t
     ==> simplicial_subcomplex {s | s IN t /\ s SUBSET UNIONS x} t /\
         UNIONS {s | s IN t /\ s SUBSET UNIONS x} = UNIONS x /\
         FINITE {s | s IN t /\ s SUBSET UNIONS x} /\
         combinatorial_manifold_with_boundary 3 {s | s IN t /\ s SUBSET UNIONS x} /\
         complex_boundary {s | s IN t /\ s SUBSET UNIONS x} = UNIONS lm`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (x:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS x:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[MOI_FM3_LF_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `UNIONS x:real^3->bool`] MOI_FSP_X_SUBCX) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `xt = {s | s IN t /\ s SUBSET UNIONS (x:(real^3->bool)->bool)}` THEN
  SUBGOAL_THEN `FINITE (xt:(real^3->bool)->bool) /\ lf_simplicial_complex xt`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
      ASM_MESON_TAC[simplicial_subcomplex];
      ASM_MESON_TAC[MOI_FDN_LF_SUBCOMPLEX]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`x:(real^3->bool)->bool`; `xt:(real^3->bool)->bool`;
                 `\y:real^3. y`; `\y:real^3. y`] COMBINATORIAL_WB_PL_INVARIANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSP_PLH_ID THEN
    REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `x:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FM3_LF_POLYTOPE THEN
    EXISTS_TAC `x:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_ID] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `complex_boundary (xt:(real^3->bool)->bool)`)) THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_SIMP_TAC[]);;

(* The two cases of the x-clause.                                             *)

let MOI_FSP_X_CASES = prove
 (`!(d:real^N->bool) j X M.
     pl_cell_with_boundary 2 d j /\ d INTER M = j /\ closed X /\ frontier X = M
     ==> d SUBSET X \/ d INTER X = j`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
  SUBGOAL_THEN `(M:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `frontier (X:real^N->bool)`)) THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED];
    ALL_TAC] THEN
  ASM_CASES_TAC `(d DIFF j) INTER (X:real^N->bool) = {}` THENL
   [DISJ2_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISJ1_TAC THEN
  SUBGOAL_THEN `d DIFF j SUBSET (X:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d DIFF j:real^N->bool`; `X:real^N->bool`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP MOI_FSP_CELL_CLOSURE) THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]);;

(* A finite combinatorial 3-manifold with boundary in real^3 is the closure *)
(* of its interior.                                                          *)

let MOI_FSP_REG_CLOSED = prove
 (`!c:(real^3->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> closure (interior (UNIONS c)) = UNIONS c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS c:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_MESON_TAC[MOI_FM3_LF_COMPACT];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[INTERIOR_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(p:real^3) IN complex_boundary c` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    MATCH_MP_TAC MOI_FM3_NOT_CB_INTERIOR THEN ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `(p:real^3) IN complex_boundary c` THEN
  REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r:real^3->bool. r IN c /\ aff_dim r = &3 /\ s SUBSET r` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!k:(real^3->bool)->bool. ~(k = {}) /\ (!r. r IN k ==> P r)
                           ==> ?r. P r`) THEN
    EXISTS_TAC `{r:real^3->bool | r IN c /\ aff_dim r = &3 /\ s SUBSET r}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_TAC THEN UNDISCH_TAC
     `CARD {r:real^3->bool | r IN c /\ aff_dim r = &3 /\ s SUBSET r} = 1` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (r:real^3->bool) /\ closed r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_CONVEX; MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior (r:real^3->bool) = interior r` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR THEN
    ASM_SIMP_TAC[GSYM AFF_DIM_NONEMPTY_INTERIOR_EQ; DIMINDEX_3] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN closure (relative_interior r)` MP_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `!s t:real^3->bool. s SUBSET t ==> x IN s ==> x IN t`) THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]);;

(* The frontier of the closed complement of a regular closed set Z in a set  *)
(* Q, when Z contains the boundary of Q and the complement stays inside.     *)

let MOI_FSP_FRONTIER_COMP = prove
 (`!(Z:real^N->bool) Q.
     closed Z /\ closure (interior Z) = Z /\ Q DIFF interior Q SUBSET Z /\
     closure (Q DIFF Z) SUBSET interior Q
     ==> frontier (closure (Q DIFF Z)) = frontier Z INTER interior Q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `open (Q DIFF Z:real^N->bool) /\ Q DIFF Z SUBSET interior Q`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `Q DIFF Z = interior Q DIFF (Z:real^N->bool)` SUBST1_TAC THENL
     [MP_TAC(ISPEC `Q:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_DIFF; OPEN_INTERIOR] THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `O = Q DIFF (Z:real^N->bool)` THEN
  REWRITE_TAC[frontier; CLOSURE_CLOSURE] THEN ASM_SIMP_TAC[CLOSURE_CLOSED] THEN
  SUBGOAL_THEN `interior Z INTER closure O = {}:real^N->bool` ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_INTERIOR] THEN
    MP_TAC(ISPEC `Z:real^N->bool` INTERIOR_SUBSET) THEN EXPAND_TAC "O" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `O SUBSET interior (closure O:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[CLOSURE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `interior Q INTER closure ((:real^N) DIFF Z) SUBSET closure O`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure (interior Q INTER ((:real^N) DIFF Z))` THEN
    SIMP_TAC[OPEN_INTER_CLOSURE_SUBSET; OPEN_INTERIOR] THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN EXPAND_TAC "O" THEN
    MP_TAC(ISPEC `Q:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior (closure O) INTER interior Z = {}:real^N->bool` ASSUME_TAC THENL
   [MP_TAC(ISPEC `closure O:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior (closure O) INTER Z = {}:real^N->bool` ASSUME_TAC THENL
   [SUBGOAL_THEN `Z = closure (interior (Z:real^N->bool))` (fun th -> ONCE_REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_INTERIOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure O SUBSET closure ((:real^N) DIFF Z)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_CLOSURE THEN EXPAND_TAC "O" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `interior Z = (:real^N) DIFF closure ((:real^N) DIFF Z)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INTERIOR_COMPLEMENT] THEN AP_TERM_TAC THEN SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `p:real^N` THEN
  REWRITE_TAC[IN_DIFF; IN_INTER] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^N) IN interior Q` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(p:real^N) IN Z` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~((p:real^N) IN interior (closure O))` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!s t. (x:real^N) IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `O:real^N->bool` THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "O" THEN
      MP_TAC(ISPEC `Q:real^N->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    STRIP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        is_binary "SUBSET" (concl th) &&
        lhand(concl th) = `interior Q INTER closure ((:real^N) DIFF Z)`)) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
      ASM SET_TAC[]]]);;

(* The frontier of the closed complement of a regular closed set inside the *)
(* open box.                                                                 *)

let MOI_FSP_FRONTIER_COMPL_BOX = prove
 (`!(X:real^N->bool) Q.
     closed Q /\ closed X /\ closure (interior X) = X /\ X SUBSET interior Q
     ==> closure (Q DIFF X) = Q DIFF interior X /\
         frontier (closure (Q DIFF X)) = (Q DIFF interior Q) UNION frontier X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `closure (Q DIFF X) = Q DIFF interior (X:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN
      ASM_SIMP_TAC[CLOSED_DIFF; OPEN_INTERIOR] THEN
      MP_TAC(ISPEC `X:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^N` THEN REWRITE_TAC[IN_DIFF] THEN
    STRIP_TAC THEN ASM_CASES_TAC `(p:real^N) IN X` THENL
     [ALL_TAC; MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN ASM SET_TAC[]] THEN
    SUBGOAL_THEN `(p:real^N) IN interior Q INTER closure ((:real^N) DIFF X)` MP_TAC THENL
     [REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[CLOSURE_COMPLEMENT; IN_DIFF; IN_UNIV] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s t. s SUBSET t ==> (x:real^N) IN s ==> x IN t`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure (interior Q INTER ((:real^N) DIFF X))` THEN
    SIMP_TAC[OPEN_INTER_CLOSURE_SUBSET; OPEN_INTERIOR] THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN MP_TAC(ISPEC `Q:real^N->bool` INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[frontier] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED; CLOSED_DIFF; OPEN_INTERIOR] THEN
  SUBGOAL_THEN `interior (Q DIFF interior X) = interior Q DIFF (X:real^N->bool)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `interior (Q INTER ((:real^N) DIFF interior X))` THEN CONJ_TAC THENL
     [AP_TERM_TAC THEN SET_TAC[];
      REWRITE_TAC[INTERIOR_INTER; INTERIOR_COMPLEMENT] THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `X:real^N->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `Q:real^N->bool` INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `interior X:real^N->bool` INTERIOR_SUBSET) THEN
  SUBGOAL_THEN `interior X SUBSET interior (Q:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN MP_TAC(ISPEC `Q:real^N->bool` INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(X:real^N->bool) SUBSET interior Q` THEN SET_TAC[]);;

(* ========================================================================= *)
(* Tools for the corners of the cut.  PL 1-balls are PL arcs; the            *)
(* link of a boundary vertex of a combinatorial surface with boundary is a  *)
(* PL arc; links of intersections of subcomplexes; and the 2D cut: removing *)
(* from a disk E in a 2-sphere a disk D meeting the boundary of E in an     *)
(* arc of its own boundary leaves (the closure of) a disk.                  *)
(* ========================================================================= *)

(* The second barycentric subdivision of a subcomplex.                       *)

let MOI_FSP_BSD2 = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision t)) /\
         UNIONS (barycentric_subdivision (barycentric_subdivision t)) = UNIONS t /\
         simplicial_subcomplex (barycentric_subdivision (barycentric_subdivision l))
                               (barycentric_subdivision (barycentric_subdivision t)) /\
         UNIONS (barycentric_subdivision (barycentric_subdivision l)) = UNIONS l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
                BARYCENTRIC_SUBDIVISION_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `barycentric_subdivision (l:(real^N->bool)->bool)`]
                BARYCENTRIC_SUBDIVISION_SUBCOMPLEX) THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF; UNIONS_BARYCENTRIC_SUBDIVISION]);;

let MOI_FSP_BALL1_ARC = prove
 (`!s:real^N->bool.
     pl_ball 1 s
     ==> ?h. arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\ path_image h = s`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  EXISTS_TAC `(f:real^N->real^N) o linepath(x0,x1)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[ARC_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `segment[x0:real^N,x1]` THEN
    ASM_SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
    REWRITE_TAC[GSYM path_image; PATH_IMAGE_LINEPATH; SUBSET_REFL];
    ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE; PATH_IMAGE_LINEPATH]]);;

(* An edge of a complex at a vertex w is a segment from w to a vertex u.      *)

let MOI_FSP_EDGE_AT_VERTEX = prove
 (`!(K:(real^N->bool)->bool) w f.
     lf_simplicial_complex K /\ {w} IN K /\ f IN K /\ aff_dim f = &1 /\ w IN f
     ==> ?u. ~(u = w) /\ f = segment[w,u] /\ {u} IN K`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 simplex (f:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_SIMPLEX]; ALL_TAC] THEN
  REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(w:real^N) extreme_point_of f` MP_TAC THENL
   [REWRITE_TAC[GSYM FACE_OF_SING] THEN
    SUBGOAL_THEN `({w} INTER f) face_of (f:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_INTER]; ALL_TAC] THEN
    UNDISCH_TAC `(w:real^N) IN f` THEN
    SIMP_TAC[SET_RULE `(w:real^N) IN f ==> {w} INTER f = {w}`];
    ALL_TAC] THEN
  SUBGOAL_THEN `{p:real^N} IN K /\ {q:real^N} IN K` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `f:real^N->bool` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [EXISTS_TAC `q:real^N` THEN ASM_MESON_TAC[];
    EXISTS_TAC `p:real^N` THEN ASM_MESON_TAC[SEGMENT_SYM]]);;

(* The link of a vertex on the surface boundary of a finite combinatorial    *)
(* surface with boundary is a PL arc.                                        *)

let MOI_FSP_BDV_LINK = prove
 (`!(K:(real^N->bool)->bool) w.
     FINITE K /\ combinatorial_manifold_with_boundary 2 K /\ {w} IN K /\
     w IN surface_boundary K
     ==> pl_ball 1 (UNIONS (simplicial_link K w))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (UNIONS (simplicial_link K (w:real^N))) \/
                pl_ball 1 (UNIONS (simplicial_link K w))` MP_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold_with_boundary 2 (K:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
  UNDISCH_TAC `(w:real^N) IN surface_boundary K` THEN
  REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`; `f:real^N->bool`]
                MOI_FSP_EDGE_AT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{u:real^N} IN simplicial_link K w` ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[IN_SING] THEN
    TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`; `{u:real^N}`; `&1:int`; `&2:int`]
                MOI_FM3_LINK_CARD) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN
  SUBGOAL_THEN `convex hull (w INSERT {u:real^N}) = f` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `?e0:real^N->bool.
                  {t | t IN simplicial_link K w /\ aff_dim t = &1 /\ {u} SUBSET t} = {e0}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_FM3_CARD_EQ_1] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[MOI_FM3_LINK_FINITE];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_sphere 1 (UNIONS (simplicial_link K (w:real^N)))` THEN
  REWRITE_TAC[pl_sphere; pl_homeomorphism; ARITH_RULE `1 + 1 = 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `ff:real^N->real^N`
    (X_CHOOSE_THEN `gg:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC MOI_FRN_SA_LK_NOT1 THEN
  MAP_EVERY EXISTS_TAC [`simplicial_link K (w:real^N)`; `k:real^N->bool`;
                        `ff:real^N->real^N`; `gg:real^N->real^N`; `u:real^N`;
                        `e0:real^N->bool`] THEN
  ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
  SUBGOAL_THEN `(e0:real^N->bool) IN {t | t IN simplicial_link K w /\ aff_dim t = &1 /\
                                          {u} SUBSET t}` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM; SING_SUBSET] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^N->bool) IN {t | t IN simplicial_link K w /\ aff_dim t = &1 /\
                                         {u} SUBSET t}` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; SING_SUBSET]; ASM_REWRITE_TAC[IN_SING]]);;

(* Links of an intersection of subcomplexes.                                 *)

let MOI_FSP_LINK_INTER = prove
 (`!(K:(real^N->bool)->bool) K1 K2 w.
     lf_simplicial_complex K /\ simplicial_subcomplex K1 K /\ simplicial_subcomplex K2 K /\
     {w} IN K
     ==> UNIONS (simplicial_link K1 w) INTER UNIONS (simplicial_link K2 w) =
         UNIONS (simplicial_link (K1 INTER K2) w)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN
    REWRITE_TAC[simplicial_link; SUBSET; IN_ELIM_THM; IN_INTER] THEN MESON_TAC[]] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN X_GEN_TAC `z:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s1:real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `s2:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `lf_simplicial_complex (K1:(real^N->bool)->bool) /\
                lf_simplicial_complex (K2:(real^N->bool)->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^N} IN K1 /\ {w:real^N} IN K2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(s1:real^N->bool) IN simplicial_link K1 w`;
      UNDISCH_TAC `(s2:real^N->bool) IN simplicial_link K2 w`] THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
    MATCH_MP_TAC MOI_FSP_VERTEX_SUB THEN
    MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K1 \/ s IN K2 ==> s IN K` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex K1 (K:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `simplicial_subcomplex K2 (K:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K1:(real^N->bool)->bool`; `w:real^N`; `s1:real^N->bool`]
                MOI_FM3_LINK_JOIN) THEN
  MP_TAC(ISPECL [`K2:(real^N->bool)->bool`; `w:real^N`; `s2:real^N->bool`]
                MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s1:real^N->bool) IN K1 /\ (s2:real^N->bool) IN K2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LINK_IN]; ALL_TAC] THEN
  ABBREV_TAC `f = (s1:real^N->bool) INTER s2` THEN
  SUBGOAL_THEN `(f:real^N->bool) face_of s1 /\ f face_of s2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN MATCH_MP_TAC MOI_FM3_LF_INTER THEN
    EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->bool) IN K1 /\ f IN K2 /\ f IN K /\ ~((w:real^N) IN f) /\
                (z:real^N) IN f` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s1:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s2:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s1:real^N->bool` THEN ASM_SIMP_TAC[];
      EXPAND_TAC "f" THEN ASM SET_TAC[];
      EXPAND_TAC "f" THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->bool) IN simplicial_link K w` ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `convex hull (w INSERT (s1:real^N->bool))` THEN ASM_SIMP_TAC[] THEN
    MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `s1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FSP_LINK_FACE_JOIN THEN EXISTS_TAC `K1:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `w:real^N`; `f:real^N->bool`]
                MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `hf = convex hull (w INSERT (f:real^N->bool))` THEN
  SUBGOAL_THEN `(hf:real^N->bool) IN K1 /\ hf IN K2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_FACE THEN
      EXISTS_TAC `convex hull (w INSERT (s1:real^N->bool))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
      ASM_SIMP_TAC[] THEN EXPAND_TAC "hf" THEN MATCH_MP_TAC HULL_MONO THEN
      EXPAND_TAC "f" THEN SET_TAC[];
      MATCH_MP_TAC MOI_FM3_LF_FACE THEN
      EXISTS_TAC `convex hull (w INSERT (s2:real^N->bool))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
      ASM_SIMP_TAC[] THEN EXPAND_TAC "hf" THEN MATCH_MP_TAC HULL_MONO THEN
      EXPAND_TAC "f" THEN SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM; IN_INTER] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `hf:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  EXPAND_TAC "hf" THEN MATCH_MP_TAC MOI_FSP_LINK_FACE_JOIN THEN
  EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

(* The 2D cut: E a disk in a 2-sphere S, D a disk in E meeting the boundary  *)
(* circle of E in an arc of its own boundary; the closure of E minus D is a *)
(* disk.                                                                      *)

let MOI_FSP_DISK_CUT = prove
 (`!(S:real^3->bool) E jE D jD al.
     pl_sphere 2 S /\ pl_cell_with_boundary 2 E jE /\ E SUBSET S /\
     pl_cell_with_boundary 2 D jD /\ D SUBSET E /\ D INTER jE = al /\ al SUBSET jD /\
     pl_ball 1 al
     ==> pl_ball 2 (closure (E DIFF D))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `E:real^3->bool`; `jE:real^3->bool`] DISK_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(jE:real^3->bool) SUBSET E /\ (jD:real^3->bool) SUBSET D` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSP_CELL_BASIC]; ALL_TAC] THEN
  ABBREV_TAC `Ec = ((S:real^3->bool) DIFF E) UNION jE` THEN
  SUBGOAL_THEN `D INTER Ec = (al:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Ec" THEN ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `h:real^1->real^3` STRIP_ASSUME_TAC o MATCH_MP MOI_FSP_BALL1_ARC) THEN
  MP_TAC(ISPECL [`D:real^3->bool`; `jD:real^3->bool`; `Ec:real^3->bool`; `jE:real^3->bool`;
                 `h:real^1->real^3`] MOI_FSA_GLUE) THEN
  ASM_REWRITE_TAC[GSYM MOI_SS2_CELL_EQ_FSA] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `J' = ((jD:real^3->bool) UNION jE) DIFF
                   (al DIFF {pathstart h,pathfinish (h:real^1->real^3)})` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `D UNION Ec:real^3->bool`; `J':real^3->bool`]
                DISK_COMPLEMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "Ec" THEN
    UNDISCH_TAC `(D:real^3->bool) SUBSET E` THEN UNDISCH_TAC `(E:real^3->bool) SUBSET S` THEN
    UNDISCH_TAC `(jE:real^3->bool) SUBSET E` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `K' = ((S:real^3->bool) DIFF (D UNION Ec)) UNION J'` THEN DISCH_TAC THEN
  SUBGOAL_THEN `closure (E DIFF D) = (K':real^3->bool)` SUBST1_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[MOI_FSP_CELL_BALL]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [MAP_EVERY EXPAND_TAC ["K'"; "J'"; "Ec"] THEN ASM SET_TAC[];
      ASM_MESON_TAC[MOI_FSP_CELL_BASIC; COMPACT_IMP_CLOSED]];
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV
      [SYM(MATCH_MP MOI_FSP_CELL_CLOSURE th)]) o
      check (fun th -> can (term_match [] `pl_cell_with_boundary 2 (K':real^3->bool) J'`)
                           (concl th))) THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN MAP_EVERY EXPAND_TAC ["K'"; "J'"; "Ec"] THEN
    ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Tools for the side lemma.  The topological core (the part of             *)
(* the frontier sphere off M inside y is the interior of the two disks,     *)
(* given connected witnesses), the sphere minus two disks is connected, the *)
(* 2D two-sidedness of the core circle of the trace annulus (Jordan), the  *)
(* witnesses from the cycle of simplices around a boundary edge of the     *)
(* trace circle, and the combinatorics of the second derived (fullness,    *)
(* frontier simplices, the fan around an edge).                             *)
(* ========================================================================= *)

(* A connected set covered by three closed sets meeting pairwise outside it  *)
(* lies in one of them.                                                      *)

let MOI_FSP_CONN3 = prove
 (`!(Z:real^N->bool) A1 A2 A3.
     connected Z /\ closed A1 /\ closed A2 /\ closed A3 /\
     Z SUBSET A1 UNION A2 UNION A3 /\
     A1 INTER A2 INTER Z = {} /\ A1 INTER A3 INTER Z = {} /\ A2 INTER A3 INTER Z = {}
     ==> Z SUBSET A1 \/ Z SUBSET A2 \/ Z SUBSET A3`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED]) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(fun th -> MP_TAC(SPECL [`A1:real^N->bool`; `A2 UNION A3:real^N->bool`] th) THEN
                       MP_TAC(SPECL [`A2:real^N->bool`; `A3:real^N->bool`] th)) THEN
  ASM_SIMP_TAC[CLOSED_UNION] THEN
  MAP_EVERY UNDISCH_TAC
   [`Z SUBSET (A1:real^N->bool) UNION A2 UNION A3`;
    `A1 INTER A2 INTER Z = {}:real^N->bool`; `A1 INTER A3 INTER Z = {}:real^N->bool`;
    `A2 INTER A3 INTER Z = {}:real^N->bool`] THEN
  SET_TAC[]);;

(* The topological core of the side lemma.  FR is the frontier sphere, M the *)
(* surface, d1 and d2 the two disks of FR bounded by the ends j1 and j2;    *)
(* Z0 is a connected set off M outside Y reaching both ends, Z1 and Z2      *)
(* connected sets off M inside Y reaching m1 and m2, which lie on different *)
(* ends.  Then the part of FR off M inside Y is the interior of the disks.  *)

let MOI_FSP_SIDE_TOP = prove
 (`!(FR:real^3->bool) M Y d1 d2 j1 j2 Z0 Z1 Z2 (m1:real^3) m2.
     FR INTER M = j1 UNION j2 /\
     d1 SUBSET FR /\ d2 SUBSET FR /\ j1 SUBSET d1 /\ j2 SUBSET d2 /\
     d1 INTER d2 = {} /\ d1 INTER M = j1 /\ d2 INTER M = j2 /\
     closed d1 /\ closed d2 /\
     closed ((FR DIFF d1) UNION j1) /\ closed ((FR DIFF d2) UNION j2) /\
     connected (d1 DIFF j1) /\ connected (d2 DIFF j2) /\
     connected (FR DIFF (d1 UNION d2)) /\
     (!S. connected S /\ S SUBSET FR DIFF M ==> S SUBSET Y \/ S INTER Y = {}) /\
     connected Z0 /\ Z0 SUBSET FR DIFF M /\ Z0 INTER Y = {} /\
     m1 IN closure Z0 /\ m2 IN closure Z0 /\
     connected Z1 /\ Z1 SUBSET (FR DIFF M) INTER Y /\ m1 IN closure Z1 /\
     connected Z2 /\ Z2 SUBSET (FR DIFF M) INTER Y /\ m2 IN closure Z2 /\
     ~(m1 IN j1 /\ m2 IN j1) /\ ~(m1 IN j2 /\ m2 IN j2) /\
     m1 IN j1 UNION j2 /\ m2 IN j1 UNION j2
     ==> (FR DIFF M) INTER Y = (d1 UNION d2) DIFF (j1 UNION j2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `A3 = ((FR DIFF d1) UNION j1) INTER ((FR DIFF d2) UNION (j2:real^3->bool))` THEN
  SUBGOAL_THEN `closed (A3:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A3" THEN ASM_SIMP_TAC[CLOSED_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z:real^3->bool. connected Z /\ Z SUBSET FR DIFF M
                     ==> Z SUBSET d1 \/ Z SUBSET d2 \/ Z SUBSET A3`
  (LABEL_TAC "C3") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSP_CONN3 THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "A3" THEN
    MAP_EVERY UNDISCH_TAC
     [`(Z:real^3->bool) SUBSET FR DIFF M`; `FR INTER M = j1 UNION (j2:real^3->bool)`;
      `(d1:real^3->bool) INTER d2 = {}`; `(d1:real^3->bool) INTER M = j1`;
      `(d2:real^3->bool) INTER M = j2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d1:real^3->bool) INTER (j1 UNION j2) = j1 /\
                (d2:real^3->bool) INTER (j1 UNION j2) = j2`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(d1:real^3->bool) INTER d2 = {}`; `(j1:real^3->bool) SUBSET d1`;
      `(j2:real^3->bool) SUBSET d2`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Z0:real^3->bool = {}) /\ ~(Z1:real^3->bool = {}) /\ ~(Z2:real^3->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CLOSURE_EMPTY; NOT_IN_EMPTY]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Z0:real^3->bool) SUBSET A3` ASSUME_TAC THENL
   [USE_THEN "C3" (MP_TAC o SPEC `Z0:real^3->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p /\ ~q ==> p \/ q \/ r ==> r`) THEN CONJ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `closure Z0 SUBSET (d1:real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(m1:real^3) IN closure Z0`; `(m2:real^3) IN closure Z0`;
        `(m1:real^3) IN j1 UNION j2`; `(m2:real^3) IN j1 UNION j2`;
        `(d1:real^3->bool) INTER (j1 UNION j2) = j1`; `~((m1:real^3) IN j1 /\ m2 IN j1)`] THEN
      SET_TAC[];
      SUBGOAL_THEN `closure Z0 SUBSET (d2:real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(m1:real^3) IN closure Z0`; `(m2:real^3) IN closure Z0`;
        `(m1:real^3) IN j1 UNION j2`; `(m2:real^3) IN j1 UNION j2`;
        `(d2:real^3->bool) INTER (j1 UNION j2) = j2`; `~((m1:real^3) IN j2 /\ m2 IN j2)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(FR DIFF (d1 UNION d2)) INTER (Y:real^3->bool) = {}` ASSUME_TAC THENL
   [MP_TAC(SPEC `FR DIFF (d1 UNION d2):real^3->bool` (ASSUME
      `!S:real^3->bool. connected S /\ S SUBSET FR DIFF M ==> S SUBSET Y \/ S INTER Y = {}`)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`FR INTER M = j1 UNION (j2:real^3->bool)`; `(j1:real^3->bool) SUBSET d1`;
        `(j2:real^3->bool) SUBSET d2`] THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(Z0:real^3->bool) SUBSET A3`; `(Z0:real^3->bool) SUBSET FR DIFF M`;
      `Z0 INTER (Y:real^3->bool) = {}`; `~(Z0:real^3->bool = {})`;
      `FR DIFF (d1 UNION d2) SUBSET (Y:real^3->bool)`;
      `FR INTER M = j1 UNION (j2:real^3->bool)`] THEN
    EXPAND_TAC "A3" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!Z:real^3->bool. connected Z /\ Z SUBSET (FR DIFF M) INTER Y /\ ~(Z = {})
                                 ==> Z SUBSET d1 \/ Z SUBSET d2`
  (LABEL_TAC "C2") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "C3" (MP_TAC o SPEC `Z:real^3->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~r ==> p \/ q \/ r ==> p \/ q`) THEN DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(Z:real^3->bool) SUBSET A3`; `(Z:real^3->bool) SUBSET (FR DIFF M) INTER Y`;
      `~(Z:real^3->bool = {})`;
      `(FR DIFF (d1 UNION d2)) INTER (Y:real^3->bool) = {}`;
      `FR INTER M = j1 UNION (j2:real^3->bool)`] THEN
    EXPAND_TAC "A3" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!(Z:real^3->bool) m.
      Z SUBSET (FR DIFF M) INTER Y /\ ~(Z = {}) /\ m IN closure Z /\ m IN j1 UNION j2
      ==> (Z SUBSET d1 ==> m IN j1 /\ ~((d1 DIFF j1) INTER Y = {})) /\
          (Z SUBSET d2 ==> m IN j2 /\ ~((d2 DIFF j2) INTER Y = {}))`
  (LABEL_TAC "ZM") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `closure Z SUBSET (d1:real^3->bool)` ASSUME_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(m:real^3) IN closure Z`; `closure Z SUBSET (d1:real^3->bool)`;
          `(m:real^3) IN j1 UNION j2`; `(d1:real^3->bool) INTER (j1 UNION j2) = j1`] THEN
        SET_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`(Z:real^3->bool) SUBSET d1`; `(Z:real^3->bool) SUBSET (FR DIFF M) INTER Y`;
          `~(Z:real^3->bool = {})`; `(d1:real^3->bool) INTER M = j1`] THEN
        SET_TAC[]];
      SUBGOAL_THEN `closure Z SUBSET (d2:real^3->bool)` ASSUME_TAC THENL
       [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`(m:real^3) IN closure Z`; `closure Z SUBSET (d2:real^3->bool)`;
          `(m:real^3) IN j1 UNION j2`; `(d2:real^3->bool) INTER (j1 UNION j2) = j2`] THEN
        SET_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`(Z:real^3->bool) SUBSET d2`; `(Z:real^3->bool) SUBSET (FR DIFF M) INTER Y`;
          `~(Z:real^3->bool = {})`; `(d2:real^3->bool) INTER M = j2`] THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((d1 DIFF j1) INTER (Y:real^3->bool) = {}) /\
                ~((d2 DIFF j2) INTER (Y:real^3->bool) = {})`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `((Z1:real^3->bool) SUBSET d1 \/ Z1 SUBSET d2) /\
                  ((Z2:real^3->bool) SUBSET d1 \/ Z2 SUBSET d2)` MP_TAC THENL
     [CONJ_TAC THEN USE_THEN "C2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "ZM" (MP_TAC o SPECL [`Z1:real^3->bool`; `m1:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "ZM" (MP_TAC o SPECL [`Z2:real^3->bool`; `m2:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`~((m1:real^3) IN j1 /\ m2 IN j1)`; `~((m1:real^3) IN j2 /\ m2 IN j2)`] THEN
    CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN `d1 DIFF j1 SUBSET (Y:real^3->bool) /\ d2 DIFF j2 SUBSET (Y:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(SPEC `d1 DIFF j1:real^3->bool` (ASSUME
        `!S:real^3->bool. connected S /\ S SUBSET FR DIFF M ==> S SUBSET Y \/ S INTER Y = {}`));
      MP_TAC(SPEC `d2 DIFF j2:real^3->bool` (ASSUME
        `!S:real^3->bool. connected S /\ S SUBSET FR DIFF M ==> S SUBSET Y \/ S INTER Y = {}`))] THEN
    (ANTS_TAC THENL
      [ASM_REWRITE_TAC[] THEN MAP_EVERY UNDISCH_TAC
        [`(d1:real^3->bool) SUBSET FR`; `(d2:real^3->bool) SUBSET FR`;
         `(d1:real^3->bool) INTER M = j1`; `(d2:real^3->bool) INTER M = j2`] THEN
       SET_TAC[];
       ASM_REWRITE_TAC[]]);
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`d1 DIFF j1 SUBSET (Y:real^3->bool)`; `d2 DIFF j2 SUBSET (Y:real^3->bool)`;
    `(FR DIFF (d1 UNION d2)) INTER (Y:real^3->bool) = {}`;
    `FR INTER M = j1 UNION (j2:real^3->bool)`;
    `(d1:real^3->bool) SUBSET FR`; `(d2:real^3->bool) SUBSET FR`;
    `(d1:real^3->bool) INTER M = j1`; `(d2:real^3->bool) INTER M = j2`;
    `(d1:real^3->bool) INTER (j1 UNION j2) = j1`;
    `(d2:real^3->bool) INTER (j1 UNION j2) = j2`] THEN
  SET_TAC[]);;

(* An open PL disk minus a PL 2-ball inside it is connected (the open disk  *)
(* is homeomorphic to the plane, where the complement of a cell is          *)
(* connected).                                                               *)

let MOI_FSP_OPEN_DISK_MINUS = prove
 (`!(E:real^3->bool) J D.
     pl_cell_with_boundary 2 E J /\ pl_ball 2 D /\ D SUBSET E DIFF J
     ==> connected ((E DIFF J) DIFF D)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(E DIFF J:real^3->bool) homeomorphic (:real^2)` MP_TAC THENL
   [MATCH_MP_TAC(ISPECL [`E DIFF J:real^3->bool`; `relative_interior k:real^3->bool`;
                          `(:real^2)`] HOMEOMORPHIC_TRANS) THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`f:real^3->real^3`; `g:real^3->real^3`] THEN
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `E:real^3->bool`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[pl_homeomorphism];
        REWRITE_TAC[RELATIVE_INTERIOR_SUBSET];
        SET_TAC[];
        FIRST_ASSUM(ACCEPT_TAC o SYM o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `E DIFF J:real^3->bool`))];
      SUBGOAL_THEN `convex (k:real^3->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      MATCH_MP_TAC HOMEOMORPHIC_RELATIVELY_OPEN_CONVEX_SETS THEN
      ASM_SIMP_TAC[CONVEX_RELATIVE_INTERIOR; AFFINE_HULL_RELATIVE_INTERIOR;
                   OPEN_IN_RELATIVE_INTERIOR; CONVEX_UNIV; AFFINE_HULL_UNIV;
                   AFF_DIM_RELATIVE_INTERIOR; AFF_DIM_UNIV; DIMINDEX_2] THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_UNIV];
        ASM_MESON_TAC[AFF_DIM_SIMPLEX]]];
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^2` (X_CHOOSE_THEN `psi':real^2->real^3`
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `homeomorphism (D,IMAGE (psi:real^3->real^2) D) (psi,psi')` ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`E DIFF J:real^3->bool`; `(:real^2)`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected ((:real^2) DIFF IMAGE (psi:real^3->real^2) D)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_ball 2 (D:real^3->bool)` THEN REWRITE_TAC[pl_ball; pl_homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k2:real^3->bool` (X_CHOOSE_THEN `f2:real^3->real^3`
      (X_CHOOSE_THEN `g2:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC(ISPECL [`IMAGE (psi:real^3->real^2) D`; `k2:real^3->bool`]
      CONNECTED_COMPLEMENT_HOMEOMORPHIC_CONVEX_COMPACT) THEN
    REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ISPECL [`IMAGE (psi:real^3->real^2) D`; `D:real^3->bool`;
                            `k2:real^3->bool`] HOMEOMORPHIC_TRANS) THEN
      CONJ_TAC THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E DIFF J) DIFF D =
                IMAGE (psi':real^2->real^3) ((:real^2) DIFF IMAGE psi D)`
  SUBST1_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
      can (term_match [] `homeomorphism (E DIFF J,(:real^2)) (psi:real^3->real^2,psi')`)
          (concl th))) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_UNIV] THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `(psi:real^3->real^2) x` THEN
      MP_TAC(ASSUME `!x. x IN E DIFF J ==> (psi':real^2->real^3) ((psi:real^3->real^2) x) = x`) THEN
      MP_TAC(ASSUME `(D:real^3->bool) SUBSET E DIFF J`) THEN
      UNDISCH_TAC `(x:real^3) IN E` THEN UNDISCH_TAC `~((x:real^3) IN J)` THEN
      UNDISCH_TAC `~((x:real^3) IN D)` THEN
      REWRITE_TAC[SUBSET; IN_DIFF] THEN MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `x = (psi':real^2->real^3) y`)) THEN
      CONJ_TAC THENL
       [MP_TAC(ASSUME `IMAGE (psi':real^2->real^3) (:real^2) = E DIFF J`) THEN SET_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `~(?x. y = (psi:real^3->real^2) x /\ x IN D)` THEN
        REWRITE_TAC[] THEN EXISTS_TAC `(psi':real^2->real^3) y` THEN ASM_SIMP_TAC[IN_UNIV]]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[SUBSET_UNIV] THEN
  ASM_MESON_TAC[homeomorphism]);;

(* The sphere FR minus two disjoint disks d1, d2 in it is connected; the     *)
(* complements of the open disks are closed; the open disks are connected.  *)

let MOI_FSP_SPHERE_TWO_DISKS = prove
 (`!(FR:real^3->bool) d1 j1 d2 j2.
     pl_sphere 2 FR /\ pl_cell_with_boundary 2 d1 j1 /\ pl_cell_with_boundary 2 d2 j2 /\
     d1 SUBSET FR /\ d2 SUBSET FR /\ d1 INTER d2 = {}
     ==> connected (FR DIFF (d1 UNION d2)) /\
         closed ((FR DIFF d1) UNION j1) /\ closed ((FR DIFF d2) UNION j2) /\
         connected (d1 DIFF j1) /\ connected (d2 DIFF j2) /\ closed d1 /\ closed d2 /\
         j1 SUBSET d1 /\ j2 SUBSET d2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`FR:real^3->bool`; `d1:real^3->bool`; `j1:real^3->bool`] DISK_COMPLEMENT) THEN
  MP_TAC(ISPECL [`FR:real^3->bool`; `d2:real^3->bool`; `j2:real^3->bool`] DISK_COMPLEMENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  MAP_EVERY (fun t -> FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SS2_CELL_FACTS o
    check (fun th -> concl th = t)))
   [`pl_cell_with_boundary 2 (d1:real^3->bool) j1`;
    `pl_cell_with_boundary 2 (d2:real^3->bool) j2`;
    `pl_cell_with_boundary 2 ((FR DIFF d1) UNION j1:real^3->bool) j1`;
    `pl_cell_with_boundary 2 ((FR DIFF d2) UNION j2:real^3->bool) j2`] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  MP_TAC(ISPECL [`(FR DIFF d1) UNION j1:real^3->bool`; `j1:real^3->bool`; `d2:real^3->bool`]
    MOI_FSP_OPEN_DISK_MINUS) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC MOI_FSP_CELL_BALL THEN EXISTS_TAC `j2:real^3->bool` THEN
      FIRST_ASSUM ACCEPT_TAC;
      MAP_EVERY UNDISCH_TAC
       [`(d2:real^3->bool) SUBSET FR`; `(d1:real^3->bool) INTER d2 = {}`;
        `(j1:real^3->bool) SUBSET d1`] THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[] `s = t ==> connected s ==> connected (t:real^3->bool)`) THEN
  UNDISCH_TAC `(j1:real^3->bool) SUBSET d1` THEN SET_TAC[]);;

(* Planar side argument: an open set U around a point x0 of J0 = frontier  *)
(* of S', whose part off J0 lies in two connected sets off J0 meeting S,     *)
(* contradicts the separation of the complement of J0 into S and S'.         *)

let MOI_FSP_JORDAN_SIDE = prove
 (`!(J0:real^2->bool) S S' U V1 V2 x0.
     open S /\ open S' /\ S INTER S' = {} /\ S UNION S' = (:real^2) DIFF J0 /\
     J0 SUBSET closure S' /\
     open U /\ x0 IN U /\ x0 IN J0 /\ U DIFF J0 SUBSET V1 UNION V2 /\
     connected V1 /\ connected V2 /\ V1 INTER J0 = {} /\ V2 INTER J0 = {} /\
     ~(V1 INTER S = {}) /\ ~(V2 INTER S = {})
     ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!V:real^2->bool. connected V /\ V INTER J0 = {} /\ ~(V INTER S = {})
                                 ==> V INTER S' = {}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected] o check (fun th ->
      concl th = `connected (V:real^2->bool)`)) THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`S:real^2->bool`; `S':real^2->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(S:real^2->bool) INTER S' = {}`; `(S:real^2->bool) UNION S' = (:real^2) DIFF J0`;
      `(V:real^2->bool) INTER J0 = {}`; `~((V:real^2->bool) INTER S = {})`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((U:real^2->bool) INTER S' = {})` MP_TAC THENL
   [SUBGOAL_THEN `(x0:real^2) IN closure S'` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [open_def] o check (fun th ->
      concl th = `open (U:real^2->bool)`)) THEN
    DISCH_THEN(MP_TAC o SPEC `x0:real^2`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^2` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `V1:real^2->bool` th) THEN
                          MP_TAC(SPEC `V2:real^2->bool` th)) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`(U:real^2->bool) DIFF J0 SUBSET V1 UNION V2`;
    `(S:real^2->bool) UNION S' = (:real^2) DIFF J0`] THEN
  SET_TAC[]);;

(* The 2D two-sidedness at the core circle j of an annulus a with ends j1,  *)
(* j2: if near a point p of j the annulus minus j lies in two connected     *)
(* sets C1, C2 of a minus j containing m1, m2, then m1 and m2 do not lie on *)
(* the same end (Jordan curve theorem through the annulus chart).           *)

let MOI_FSP_TWO_ENDS = prove
 (`!(a:real^3->bool) j1 j2 j W C1 C2 (p:real^3) m1 m2.
     pl_annulus_with_ends a j1 j2 /\ pl_sphere 1 j /\ j SUBSET a DIFF (j1 UNION j2) /\
     connected j1 /\ connected j2 /\ j1 SUBSET a /\ j2 SUBSET a /\
     p IN j /\ open W /\ p IN W /\ W INTER a SUBSET a DIFF (j1 UNION j2) /\
     (W INTER a) DIFF j SUBSET C1 UNION C2 /\
     connected C1 /\ connected C2 /\ C1 SUBSET a DIFF j /\ C2 SUBSET a DIFF j /\
     m1 IN C1 /\ m2 IN C2
     ==> ~(m1 IN j1 /\ m2 IN j1) /\ ~(m1 IN j2 /\ m2 IN j2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_annulus_with_ends (a:real^3->bool) j1 j2` THEN
  REWRITE_TAC[pl_annulus_with_ends; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `g:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `A0 = interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                   interval(--vector[&1;&1]:real^2,vector[&1;&1])` THEN
  ABBREV_TAC `O0 = interval(--vector[&2;&2]:real^2,vector[&2;&2]) DIFF
                   interval[--vector[&1;&1]:real^2,vector[&1;&1]]` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `open (O0:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "O0" THEN SIMP_TAC[OPEN_DIFF; OPEN_INTERVAL; CLOSED_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN `(O0:real^2->bool) SUBSET A0` ASSUME_TAC THENL
   [EXPAND_TAC "O0" THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `A0:real^2->bool` && is_binary "DIFF" (lhs(concl th)))) THEN
    MP_TAC(ISPECL [`--vector[&2;&2]:real^2`; `vector[&2;&2]:real^2`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
    MP_TAC(ISPECL [`--vector[&1;&1]:real^2`; `vector[&1;&1]:real^2`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN a DIFF (j1 UNION j2) ==> (g:real^3->real^2) x IN O0`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_DIFF; IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^3->real^2) x IN A0` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((g:real^3->real^2) x IN
                    relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]])) /\
                  ~((g:real^3->real^2) x IN
                    relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`
    MP_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THENL
       [UNDISCH_TAC `~((x:real^3) IN j1)`; UNDISCH_TAC `~((x:real^3) IN j2)`] THEN
      ASM_REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g:real^3->real^2) x` THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[MOI_FN2_RF_SQUARE; REAL_ARITH `&0 < &1 /\ &0 < &2`] THEN
    EXPAND_TAC "O0" THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `A0:real^2->bool` && is_binary "DIFF" (lhs(concl th)))) THEN
    SUBGOAL_THEN `interval[--vector[&1;&1]:real^2,vector[&1;&1]] SUBSET
                  interval(--vector[&2;&2],vector[&2;&2])` MP_TAC THENL
     [REWRITE_TAC[SUBSET_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2; VECTOR_NEG_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c:real^1->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MOI_SLV_CIRCLE_LOOP) THEN
  ABBREV_TAC `J0 = IMAGE (g:real^3->real^2) j` THEN
  SUBGOAL_THEN `simple_path ((g:real^3->real^2) o c) /\
                pathfinish ((g:real^3->real^2) o c) = pathstart (g o c) /\
                path_image ((g:real^3->real^2) o c) = J0` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
    MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `a:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN a /\ (y:real^3) IN a` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(g:real^3->real^2) o (c:real^1->real^3)` JORDAN_INSIDE_OUTSIDE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ASSUME `path_image ((g:real^3->real^2) o (c:real^1->real^3)) = J0`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN a DIFF j ==> ~((g:real^3->real^2) x IN J0)` ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM(ASSUME `IMAGE (g:real^3->real^2) j = J0`)] THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^3) IN a` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `U = IMAGE (g:real^3->real^2) (W INTER a)` THEN
  SUBGOAL_THEN `open (U:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `O0:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `A0:real^2->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `U = {y:real^2 | y IN A0 /\ (f:real^2->real^3) y IN W}` SUBST1_TAC THENL
       [EXPAND_TAC "U" THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^2` THEN
        REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; IN_INTER] THEN EQ_TAC THENL
         [DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
          ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
          STRIP_TAC THEN EXISTS_TAC `(f:real^2->real^3) y` THEN ASM_SIMP_TAC[] THEN
          ASM SET_TAC[]];
        MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[]];
      EXPAND_TAC "U" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^2) p IN U /\ (g:real^3->real^2) p IN J0 /\
                U DIFF J0 SUBSET IMAGE (g:real^3->real^2) C1 UNION IMAGE g C2 /\
                connected (IMAGE (g:real^3->real^2) C1) /\
                connected (IMAGE (g:real^3->real^2) C2) /\
                IMAGE (g:real^3->real^2) C1 INTER J0 = {} /\
                IMAGE (g:real^3->real^2) C2 INTER J0 = {} /\
                J0 SUBSET closure (inside J0) /\ J0 SUBSET closure (outside J0)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "U" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      UNDISCH_TAC `(p:real^3) IN W` THEN UNDISCH_TAC `(p:real^3) IN j` THEN
      UNDISCH_TAC `(j:real^3->bool) SUBSET a DIFF (j1 UNION j2)` THEN SET_TAC[];
      REWRITE_TAC[GSYM(ASSUME `IMAGE (g:real^3->real^2) j = J0`)] THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "U" THEN REWRITE_TAC[SUBSET; IN_DIFF; IMP_CONJ; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:real^3` THEN REPEAT DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^3) IN (W INTER a) DIFF j` MP_TAC THENL
       [REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        UNDISCH_TAC `~((g:real^3->real^2) x IN J0)` THEN
        REWRITE_TAC[GSYM(ASSUME `IMAGE (g:real^3->real^2) j = J0`)] THEN
        MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(W INTER a) DIFF j SUBSET (C1:real^3->bool) UNION C2` THEN
      SET_TAC[];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `a:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(C1:real^3->bool) SUBSET a DIFF j` THEN SET_TAC[];
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `a:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(C2:real^3->bool) SUBSET a DIFF j` THEN SET_TAC[];
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_IMAGE] THEN
      X_GEN_TAC `y:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      SUBGOAL_THEN `~((g:real^3->real^2) x IN J0)` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `J0:real^2->bool`)) (concl th))) THEN
        UNDISCH_TAC `(C1:real^3->bool) SUBSET a DIFF j` THEN
        UNDISCH_TAC `(x:real^3) IN C1` THEN SET_TAC[];
        UNDISCH_TAC `(y:real^2) IN J0` THEN
        UNDISCH_TAC `(y:real^2) = (g:real^3->real^2) x` THEN MESON_TAC[]];
      REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_IMAGE] THEN
      X_GEN_TAC `y:real^2` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      SUBGOAL_THEN `~((g:real^3->real^2) x IN J0)` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `J0:real^2->bool`)) (concl th))) THEN
        UNDISCH_TAC `(C2:real^3->bool) SUBSET a DIFF j` THEN
        UNDISCH_TAC `(x:real^3) IN C2` THEN SET_TAC[];
        UNDISCH_TAC `(y:real^2) IN J0` THEN
        UNDISCH_TAC `(y:real^2) = (g:real^3->real^2) x` THEN MESON_TAC[]];
      UNDISCH_TAC `frontier (inside J0) = (J0:real^2->bool)` THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      UNDISCH_TAC `frontier (outside J0) = (J0:real^2->bool)` THEN
      REWRITE_TAC[frontier] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!jp:real^3->bool. connected jp /\ jp SUBSET a /\ jp INTER j = {} /\
                      m1 IN jp /\ m2 IN jp ==> F`
  (fun th -> CONJ_TAC THEN STRIP_TAC THEN MATCH_MP_TAC th THENL
    [EXISTS_TAC `j1:real^3->bool`; EXISTS_TAC `j2:real^3->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `(j:real^3->bool) SUBSET a DIFF (j1 UNION j2)` THEN SET_TAC[]) THEN
  X_GEN_TAC `jp:real^3->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected (IMAGE (g:real^3->real^2) jp)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `a:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^2) jp SUBSET (:real^2) DIFF J0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `J0:real^2->bool`)) (concl th))) THEN
    UNDISCH_TAC `(jp:real^3->bool) SUBSET a` THEN UNDISCH_TAC `(jp:real^3->bool) INTER j = {}` THEN
    UNDISCH_TAC `(x:real^3) IN jp` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^2) m1 IN IMAGE g jp /\ (g:real^3->real^2) m1 IN IMAGE g C1 /\
                (g:real^3->real^2) m2 IN IMAGE g jp /\ (g:real^3->real^2) m2 IN IMAGE g C2`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!S S':real^2->bool. open S /\ open S' /\ S INTER S' = {} /\
                        S UNION S' = (:real^2) DIFF J0 /\ J0 SUBSET closure S' /\
                        IMAGE (g:real^3->real^2) jp SUBSET S ==> F`
  MATCH_MP_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSP_JORDAN_SIDE THEN
    MAP_EVERY EXISTS_TAC
     [`J0:real^2->bool`; `S:real^2->bool`; `S':real^2->bool`;
      `U:real^2->bool`; `IMAGE (g:real^3->real^2) C1`; `IMAGE (g:real^3->real^2) C2`;
      `(g:real^3->real^2) p`] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (g:real^3->real^2) jp SUBSET S`;
      `(g:real^3->real^2) m1 IN IMAGE g jp`; `(g:real^3->real^2) m1 IN IMAGE g C1`;
      `(g:real^3->real^2) m2 IN IMAGE g jp`; `(g:real^3->real^2) m2 IN IMAGE g C2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [connected] o check (fun th ->
    concl th = `connected (IMAGE (g:real^3->real^2) jp)`)) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`inside J0:real^2->bool`; `outside J0:real^2->bool`]) THEN
  REWRITE_TAC[ASSUME `open (inside J0:real^2->bool)`; ASSUME `open (outside J0:real^2->bool)`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^2) jp SUBSET inside J0 \/
                IMAGE (g:real^3->real^2) jp SUBSET outside J0`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE (g:real^3->real^2) jp SUBSET (:real^2) DIFF J0`;
      `inside J0 INTER outside J0 = {}:real^2->bool`;
      `inside J0 UNION outside J0 = (:real^2) DIFF J0`;
      `~(IMAGE (g:real^3->real^2) jp SUBSET inside J0 UNION outside J0 /\
         inside J0 INTER outside J0 INTER IMAGE g jp = {} /\
         ~(inside J0 INTER IMAGE g jp = {}) /\ ~(outside J0 INTER IMAGE g jp = {}))`] THEN
    SET_TAC[];
    MAP_EVERY EXISTS_TAC [`inside J0:real^2->bool`; `outside J0:real^2->bool`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`outside J0:real^2->bool`; `inside J0:real^2->bool`] THEN
    ONCE_REWRITE_TAC[INTER_COMM; UNION_COMM] THEN ASM_REWRITE_TAC[]]);;

(* Paths along a sequence of points: the start point and the segments of   *)
(* the first n steps form a connected set containing both ends.             *)

let MOI_FSP_PATH_CONN = prove
 (`!(U:num->real^N) a n.
     connected ({U a} UNION UNIONS {segment[U(a + j),U(SUC(a + j))] | j | j < n}) /\
     U(a + n) IN {U a} UNION UNIONS {segment[U(a + j),U(SUC(a + j))] | j | j < n}`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT; ADD_CLAUSES] THEN
    REWRITE_TAC[SET_RULE `{(f:num->real^N->bool) j | j | F} = {}`; UNIONS_0; UNION_EMPTY;
                CONNECTED_SING; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{U a} UNION UNIONS {segment[(U:num->real^N)(a + j),U(SUC(a + j))] | j | j < SUC n} =
    ({U a} UNION UNIONS {segment[U(a + j),U(SUC(a + j))] | j | j < n}) UNION
    segment[U(a + n),U(SUC(a + n))]`
  SUBST1_TAC THENL
   [REWRITE_TAC[LT] THEN
    REWRITE_TAC[SET_RULE `{(f:num->real^N->bool) j | j | j = n \/ P j} =
                          f n INSERT {f j | j | P j}`] THEN
    REWRITE_TAC[UNIONS_INSERT] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[CONNECTED_SEGMENT] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(U:num->real^N)(a + n)` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    REWRITE_TAC[IN_UNION; ADD_CLAUSES] THEN DISJ2_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT]]);;

let MOI_FSP_PATH_MEMBER = prove
 (`!(U:num->real^N) a n x.
     x IN {U a} UNION UNIONS {segment[U(a + j),U(SUC(a + j))] | j | j < n}
     <=> x = U a \/ ?j. j < n /\ x IN segment[U(a + j),U(SUC(a + j))]`,
  REWRITE_TAC[IN_UNION; IN_SING; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FSP_SEMI_CLOSURE = prove
 (`!a b:real^N. ~(a = b)
                ==> a IN closure(segment[a,b] DELETE a) /\ b IN closure(segment[a,b] DELETE b)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `segment[a,b] SUBSET closure(segment[a,b] DELETE (a:real^N)) /\
                segment[a,b] SUBSET closure(segment[a,b] DELETE (b:real^N))`
  MP_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(segment(a:real^N,b))` THEN
    (CONJ_TAC THENL [ASM_REWRITE_TAC[CLOSURE_SEGMENT; SUBSET_REFL]; ALL_TAC]) THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN REWRITE_TAC[open_segment] THEN SET_TAC[];
    REWRITE_TAC[SUBSET] THEN MESON_TAC[ENDS_IN_SEGMENT]]);;

(* Arithmetic on the num facts among the assumptions only (ASM_ARITH_TAC  *)
(* also takes the quantified set facts, which makes it very slow).          *)

let MOI_FSP_NUM_ARITH_TAC : tactic =
  let is_numrel tm =
    let tm' = if is_neg tm then dest_neg tm else tm in
    (is_eq tm' ||
     (is_comb tm' && is_comb (rator tm') && is_const (rator(rator tm')) &&
      mem (fst(dest_const(rator(rator tm')))) ["<="; "<"; ">="; ">"])) &&
    (try type_of (lhand tm') = `:num` with Failure _ -> false) in
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_numrel o concl))) THEN ARITH_TAC;;

(* The witnesses of the side lemma from a cycle U of points around an edge  *)
(* of the trace circle: U(c0) is in d (the only one), U(c0 + r1) and        *)
(* U(c0 + r2) are the two on M, and the segments of the cycle avoid B, meet *)
(* M only at cycle points in M, and lie in the frontier FR when both ends   *)
(* are off d.                                                                *)

let MOI_FSP_WIT_PATH = prove
 (`!(FR:real^3->bool) M B Y d (U:num->real^3) dd c0 r1 r2.
     (!S. connected S /\ S INTER (M UNION B) = {} ==> S SUBSET Y \/ S INTER Y = {}) /\
     (!i. segment[U i,U(SUC i)] INTER B = {}) /\
     (!i. ~(U i IN M) /\ ~(U(SUC i) IN M) ==> segment[U i,U(SUC i)] INTER M = {}) /\
     (!i. U i IN M /\ ~(U(SUC i) IN M) ==> segment[U i,U(SUC i)] INTER M = {U i}) /\
     (!i. ~(U i IN M) /\ U(SUC i) IN M ==> segment[U i,U(SUC i)] INTER M = {U(SUC i)}) /\
     (!i. ~(U i IN d) /\ ~(U(SUC i) IN d) ==> segment[U i,U(SUC i)] SUBSET FR) /\
     (!i. ~(U i = U(SUC i))) /\
     (!r. 0 < r /\ r < dd ==> ~(U(c0 + r) IN d)) /\
     U(c0 + dd) = U c0 /\ ~(U c0 IN M) /\
     (!r. r < dd /\ ~(r = r1) /\ ~(r = r2) ==> ~(U(c0 + r) IN M)) /\
     U(c0 + r1) IN M /\ U(c0 + r2) IN M /\
     2 <= r1 /\ r1 + 2 <= r2 /\ r2 + 2 <= dd /\
     U c0 IN Y /\
     ~(U(c0 + r1 - 1) IN Y /\ U(c0 + r1 + 1) IN Y)
     ==> ?Z0 Z1 Z2. connected Z0 /\ Z0 SUBSET FR DIFF M /\ Z0 INTER Y = {} /\
                    U(c0 + r1) IN closure Z0 /\ U(c0 + r2) IN closure Z0 /\
                    connected Z1 /\ Z1 SUBSET (FR DIFF M) INTER Y /\ U(c0 + r1) IN closure Z1 /\
                    connected Z2 /\ Z2 SUBSET (FR DIFF M) INTER Y /\ U(c0 + r2) IN closure Z2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r <= dd /\ ~(r = r1) /\ ~(r = r2) ==> ~((U:num->real^3)(c0 + r) IN M)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN ASM_CASES_TAC `r:num = dd` THENL
     [ASM_REWRITE_TAC[]; FIRST_X_ASSUM MATCH_MP_TAC THEN MOI_FSP_NUM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a n. (!r. a <= r /\ r <= a + n ==> ~((U:num->real^3)(c0 + r) IN M))
          ==> ({U(c0 + a)} UNION UNIONS {segment[U((c0 + a) + j),U(SUC((c0 + a) + j))] | j | j < n})
              INTER (M UNION B) = {}`
  (LABEL_TAC "PM") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
    X_GEN_TAC `x:real^3` THEN REWRITE_TAC[MOI_FSP_PATH_MEMBER] THEN
    STRIP_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC) THEN
      UNDISCH_TAC `(U:num->real^3)(c0 + a) IN M UNION B` THEN REWRITE_TAC[IN_UNION] THEN
      STRIP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `a:num`) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC;
        FIRST_X_ASSUM(MP_TAC o SPEC `c0 + a:num` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `B:real^3->bool`)) (concl th))) THEN
        REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
        DISCH_THEN(MP_TAC o SPEC `(U:num->real^3)(c0 + a)`) THEN
        ASM_REWRITE_TAC[ENDS_IN_SEGMENT]];
      UNDISCH_TAC `(x:real^3) IN M UNION B` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
       [SUBGOAL_THEN `segment[(U:num->real^3)((c0 + a) + j),U(SUC((c0 + a) + j))] INTER M = {}`
        MP_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
            can (term_match [] `!i. ~((U:num->real^3) i IN M) /\ ~(U(SUC i) IN M) ==> P i`)
                (concl th))) THEN
          REWRITE_TAC[ADD1; GSYM ADD_ASSOC] THEN CONJ_TAC THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN MOI_FSP_NUM_ARITH_TAC;
          ASM SET_TAC[]];
        FIRST_X_ASSUM(MP_TAC o SPEC `(c0 + a) + j:num` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `B:real^3->bool`)) (concl th))) THEN
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a n. (!r. a <= r /\ r <= a + n ==> ~((U:num->real^3)(c0 + r) IN M)) /\
          ~(Y INTER ({U(c0 + a)} UNION
                     UNIONS {segment[U((c0 + a) + j),U(SUC((c0 + a) + j))] | j | j < n}) = {})
          ==> {U(c0 + a)} UNION
              UNIONS {segment[U((c0 + a) + j),U(SUC((c0 + a) + j))] | j | j < n} SUBSET Y`
  (LABEL_TAC "PY") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`U:num->real^3`; `c0 + a:num`; `n:num`] MOI_FSP_PATH_CONN) THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC
      `{(U:num->real^3)(c0 + a)} UNION
       UNIONS {segment[U((c0 + a) + j),U(SUC((c0 + a) + j))] | j | j < n}` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Y:real^3->bool`)) (concl th) &&
      can (find_term ((=) `connected:(real^3->bool)->bool`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "PM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
    UNDISCH_TAC `~(Y INTER ({(U:num->real^3)(c0 + a)} UNION
                 UNIONS {segment[U((c0 + a) + j),U(SUC((c0 + a) + j))] | j | j < n}) = {})` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^3)(c0 + r1 - 1) IN Y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:num->real^3`; `c0 + 0:num`; `r1 - 1`] MOI_FSP_PATH_CONN) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `(c0 + 0) + r1 - 1 = c0 + r1 - 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s. s SUBSET Y ==> (x:real^3) IN s ==> x IN Y`) THEN
    USE_THEN "PY" MATCH_MP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MOI_FSP_NUM_ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION; IN_SING; ADD_CLAUSES] THEN
      EXISTS_TAC `(U:num->real^3) c0` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^3)(c0 + r2 + 1) IN Y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:num->real^3`; `c0 + r2 + 1:num`; `dd - r2 - 1`] MOI_FSP_PATH_CONN) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `(c0 + r2 + 1) + dd - r2 - 1 = c0 + dd` SUBST1_TAC THENL
     [MOI_FSP_NUM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s. s SUBSET Y /\ x IN s ==> (x:real^3) IN Y`) THEN
    EXISTS_TAC `{(U:num->real^3)(c0 + r2 + 1)} UNION
       UNIONS {segment[U((c0 + r2 + 1) + j),U(SUC((c0 + r2 + 1) + j))] | j | j < dd - r2 - 1}` THEN
    REWRITE_TAC[IN_UNION; IN_SING] THEN
    SUBGOAL_THEN `c0 + r2 + 1 = c0 + (r2 + 1)` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    USE_THEN "PY" MATCH_MP_TAC THEN CONJ_TAC THENL
     [X_GEN_TAC `r:num` THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      MOI_FSP_NUM_ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(U:num->real^3) c0` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(U:num->real^3) c0 IN
        {U(c0 + r2 + 1)} UNION
        UNIONS {segment[U((c0 + r2 + 1) + j),U(SUC((c0 + r2 + 1) + j))] | j | j < dd - r2 - 1}` THEN
      REWRITE_TAC[ADD_ASSOC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((U:num->real^3)(c0 + r1 + 1) IN Y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `SUC(c0 + r1 - 1) = c0 + r1 /\ SUC(c0 + r1) = c0 + r1 + 1 /\
                SUC(c0 + r2 - 1) = c0 + r2 /\ SUC(c0 + r2) = c0 + r2 + 1`
  STRIP_ASSUME_TAC THENL [MOI_FSP_NUM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((U:num->real^3)(c0 + r1 - 1) IN M) /\ ~((U:num->real^3)(c0 + r1 + 1) IN M) /\
                ~((U:num->real^3)(c0 + r2 - 1) IN M) /\ ~((U:num->real^3)(c0 + r2 + 1) IN M)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `c0 + r1 - 1 = c0 + (r1 - 1) /\ c0 + r1 + 1 = c0 + (r1 + 1) /\
                  c0 + r2 - 1 = c0 + (r2 - 1) /\ c0 + r2 + 1 = c0 + (r2 + 1)`
    (fun th -> REWRITE_TAC[th]) THENL [MOI_FSP_NUM_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MOI_FSP_NUM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((U:num->real^3)(c0 + r1 - 1) IN d) /\ ~((U:num->real^3)(c0 + r1) IN d) /\
                ~((U:num->real^3)(c0 + r1 + 1) IN d) /\ ~((U:num->real^3)(c0 + r2 - 1) IN d) /\
                ~((U:num->real^3)(c0 + r2) IN d) /\ ~((U:num->real^3)(c0 + r2 + 1) IN d)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `c0 + r1 - 1 = c0 + (r1 - 1) /\ c0 + r1 + 1 = c0 + (r1 + 1) /\
                  c0 + r2 - 1 = c0 + (r2 - 1) /\ c0 + r2 + 1 = c0 + (r2 + 1)`
    (fun th -> REWRITE_TAC[th]) THENL [MOI_FSP_NUM_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MOI_FSP_NUM_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m1 = (U:num->real^3)(c0 + r1)` THEN
  ABBREV_TAC `m2 = (U:num->real^3)(c0 + r2)` THEN
  ABBREV_TAC `P = {(U:num->real^3)(c0 + r1 + 1)} UNION
                  UNIONS {segment[U((c0 + r1 + 1) + j),U(SUC((c0 + r1 + 1) + j))] | j |
                          j < r2 - r1 - 2}` THEN
  SUBGOAL_THEN `connected (P:real^3->bool) /\ (U:num->real^3)(c0 + r1 + 1) IN P /\
                (U:num->real^3)(c0 + r2 - 1) IN P`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`U:num->real^3`; `c0 + r1 + 1:num`; `r2 - r1 - 2`] MOI_FSP_PATH_CONN) THEN
    SUBGOAL_THEN `(c0 + r1 + 1) + r2 - r1 - 2 = c0 + r2 - 1` SUBST1_TAC THENL
     [MOI_FSP_NUM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[] THEN EXPAND_TAC "P" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(P:real^3->bool) INTER (M UNION B) = {} /\ P SUBSET FR` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "P" THEN
      SUBGOAL_THEN `c0 + r1 + 1 = c0 + (r1 + 1)` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      USE_THEN "PM" MATCH_MP_TAC THEN X_GEN_TAC `r:num` THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN MOI_FSP_NUM_ARITH_TAC;
      EXPAND_TAC "P" THEN REWRITE_TAC[SUBSET; MOI_FSP_PATH_MEMBER] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THENL
       [FIRST_X_ASSUM SUBST1_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `c0 + r1 + 1:num` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `FR:real^3->bool`)) (concl th))) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `SUC(c0 + r1 + 1) = c0 + (r1 + 2)` SUBST1_TAC THENL
           [ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM MATCH_MP_TAC THEN MOI_FSP_NUM_ARITH_TAC;
          REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT]];
        FIRST_X_ASSUM(MP_TAC o SPEC `(c0 + r1 + 1) + j:num` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `FR:real^3->bool`)) (concl th))) THEN
        ANTS_TAC THENL
         [SUBGOAL_THEN `(c0 + r1 + 1) + j = c0 + (r1 + 1 + j) /\
                        SUC((c0 + r1 + 1) + j) = c0 + (r1 + 2 + j)`
          (fun th -> REWRITE_TAC[th]) THENL [ARITH_TAC; ALL_TAC] THEN
          CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN MOI_FSP_NUM_ARITH_TAC;
          ASM SET_TAC[]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[m1,(U:num->real^3)(c0 + r1 + 1)] INTER (M UNION B) = {m1} /\
    segment[(U:num->real^3)(c0 + r2 - 1),m2] INTER (M UNION B) = {m2} /\
    segment[(U:num->real^3)(c0 + r1 - 1),m1] INTER (M UNION B) = {m1} /\
    segment[m2,(U:num->real^3)(c0 + r2 + 1)] INTER (M UNION B) = {m2} /\
    segment[m1,(U:num->real^3)(c0 + r1 + 1)] SUBSET FR /\
    segment[(U:num->real^3)(c0 + r2 - 1),m2] SUBSET FR /\
    segment[(U:num->real^3)(c0 + r1 - 1),m1] SUBSET FR /\
    segment[m2,(U:num->real^3)(c0 + r2 + 1)] SUBSET FR`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t ->
      MP_TAC(SPEC t (ASSUME `!i. ~((U:num->real^3) i IN d) /\ ~(U(SUC i) IN d)
                                 ==> segment[U i,U(SUC i)] SUBSET FR`)) THEN
      MP_TAC(SPEC t (ASSUME `!i. segment[(U:num->real^3) i,U(SUC i)] INTER B = {}`)))
     [`c0 + r1:num`; `c0 + r2 - 1`; `c0 + r1 - 1`; `c0 + r2:num`] THEN
    MAP_EVERY (fun t ->
      MP_TAC(SPEC t (ASSUME `!i. (U:num->real^3) i IN M /\ ~(U(SUC i) IN M)
                                 ==> segment[U i,U(SUC i)] INTER M = {U i}`)))
     [`c0 + r1:num`; `c0 + r2:num`] THEN
    MAP_EVERY (fun t ->
      MP_TAC(SPEC t (ASSUME `!i. ~((U:num->real^3) i IN M) /\ U(SUC i) IN M
                                 ==> segment[U i,U(SUC i)] INTER M = {U(SUC i)}`)))
     [`c0 + r1 - 1`; `c0 + r2 - 1`] THEN
    REWRITE_TAC(map ASSUME
     [`(U:num->real^3)(c0 + r1) = m1`; `(U:num->real^3)(c0 + r2) = m2`;
      `SUC(c0 + r1 - 1) = c0 + r1`; `SUC(c0 + r1) = c0 + r1 + 1`;
      `SUC(c0 + r2 - 1) = c0 + r2`; `SUC(c0 + r2) = c0 + r2 + 1`;
      `(m1:real^3) IN M`; `(m2:real^3) IN M`;
      `~((U:num->real^3)(c0 + r1 - 1) IN M)`; `~((U:num->real^3)(c0 + r1 + 1) IN M)`;
      `~((U:num->real^3)(c0 + r2 - 1) IN M)`; `~((U:num->real^3)(c0 + r2 + 1) IN M)`;
      `~((U:num->real^3)(c0 + r1 - 1) IN d)`; `~((m1:real^3) IN d)`;
      `~((U:num->real^3)(c0 + r1 + 1) IN d)`; `~((U:num->real^3)(c0 + r2 - 1) IN d)`;
      `~((m2:real^3) IN d)`; `~((U:num->real^3)(c0 + r2 + 1) IN d)`]) THEN
    SIMP_TAC[UNION_OVER_INTER; UNION_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(m1 = (U:num->real^3)(c0 + r1 + 1)) /\ ~((U:num->real^3)(c0 + r2 - 1) = m2) /\
                ~((U:num->real^3)(c0 + r1 - 1) = m1) /\ ~(m2 = (U:num->real^3)(c0 + r2 + 1))`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(SPEC t (ASSUME `!i. ~((U:num->real^3) i = U(SUC i))`)))
     [`c0 + r1:num`; `c0 + r2 - 1`; `c0 + r1 - 1`; `c0 + r2:num`] THEN
    REWRITE_TAC(map ASSUME
     [`(U:num->real^3)(c0 + r1) = m1`; `(U:num->real^3)(c0 + r2) = m2`;
      `SUC(c0 + r1 - 1) = c0 + r1`; `SUC(c0 + r1) = c0 + r1 + 1`;
      `SUC(c0 + r2 - 1) = c0 + r2`; `SUC(c0 + r2) = c0 + r2 + 1`]) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(segment[m1,(U:num->real^3)(c0 + r1 + 1)] DELETE m1) UNION P UNION
              (segment[(U:num->real^3)(c0 + r2 - 1),m2] DELETE m2)` THEN
  EXISTS_TAC `segment[(U:num->real^3)(c0 + r1 - 1),m1] DELETE m1` THEN
  EXISTS_TAC `segment[m2,(U:num->real^3)(c0 + r2 + 1)] DELETE m2` THEN
  REWRITE_TAC[CONNECTED_SEMIOPEN_SEGMENT] THEN
  SUBGOAL_THEN
   `connected ((segment[m1,(U:num->real^3)(c0 + r1 + 1)] DELETE m1) UNION P UNION
               (segment[(U:num->real^3)(c0 + r2 - 1),m2] DELETE m2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN REWRITE_TAC[CONNECTED_SEMIOPEN_SEGMENT] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[CONNECTED_SEMIOPEN_SEGMENT] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN
      EXISTS_TAC `(U:num->real^3)(c0 + r2 - 1)` THEN ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN
      EXISTS_TAC `(U:num->real^3)(c0 + r1 + 1)` THEN
      ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((segment[m1,(U:num->real^3)(c0 + r1 + 1)] DELETE m1) UNION P UNION
     (segment[(U:num->real^3)(c0 + r2 - 1),m2] DELETE m2)) INTER Y = {}`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC
     `(segment[m1,(U:num->real^3)(c0 + r1 + 1)] DELETE m1) UNION P UNION
      (segment[(U:num->real^3)(c0 + r2 - 1),m2] DELETE m2)` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `Y:real^3->bool`)) (concl th) &&
      can (find_term ((=) `connected:(real^3->bool)->bool`)) (concl th))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`segment[m1,(U:num->real^3)(c0 + r1 + 1)] INTER (M UNION B) = {m1}`;
        `segment[(U:num->real^3)(c0 + r2 - 1),m2] INTER (M UNION B) = {m2}`;
        `(P:real^3->bool) INTER (M UNION B) = {}`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~((U:num->real^3)(c0 + r1 + 1) IN Y)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `m1 IN closure (segment[m1,(U:num->real^3)(c0 + r1 + 1)] DELETE m1) /\
                m2 IN closure (segment[(U:num->real^3)(c0 + r2 - 1),m2] DELETE m2) /\
                m1 IN closure (segment[(U:num->real^3)(c0 + r1 - 1),m1] DELETE m1) /\
                m2 IN closure (segment[m2,(U:num->real^3)(c0 + r2 + 1)] DELETE m2)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FSP_SEMI_CLOSURE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`segment[m1,(U:num->real^3)(c0 + r1 + 1)] INTER (M UNION B) = {m1}`;
      `segment[(U:num->real^3)(c0 + r2 - 1),m2] INTER (M UNION B) = {m2}`;
      `(P:real^3->bool) INTER (M UNION B) = {}`; `(P:real^3->bool) SUBSET FR`;
      `segment[m1,(U:num->real^3)(c0 + r1 + 1)] SUBSET FR`;
      `segment[(U:num->real^3)(c0 + r2 - 1),m2] SUBSET FR`] THEN
    SET_TAC[];
    MATCH_MP_TAC(SET_RULE `!s t. s SUBSET t /\ x IN s ==> (x:real^3) IN t`) THEN
    EXISTS_TAC `closure (segment[m1,(U:num->real^3)(c0 + r1 + 1)] DELETE m1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[];
    MATCH_MP_TAC(SET_RULE `!s t. s SUBSET t /\ x IN s ==> (x:real^3) IN t`) THEN
    EXISTS_TAC `closure (segment[(U:num->real^3)(c0 + r2 - 1),m2] DELETE m2)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`segment[(U:num->real^3)(c0 + r1 - 1),m1] INTER (M UNION B) = {m1}`;
        `segment[(U:num->real^3)(c0 + r1 - 1),m1] SUBSET FR`] THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `segment[(U:num->real^3)(c0 + r1 - 1),m1] DELETE m1` o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `Y:real^3->bool`)) (concl th) &&
               can (find_term ((=) `connected:(real^3->bool)->bool`)) (concl th))) THEN
      REWRITE_TAC[CONNECTED_SEMIOPEN_SEGMENT] THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `segment[(U:num->real^3)(c0 + r1 - 1),m1] INTER (M UNION B) = {m1}` THEN
        SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(U:num->real^3)(c0 + r1 - 1)` THEN
      ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT]];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`segment[m2,(U:num->real^3)(c0 + r2 + 1)] INTER (M UNION B) = {m2}`;
        `segment[m2,(U:num->real^3)(c0 + r2 + 1)] SUBSET FR`] THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `segment[m2,(U:num->real^3)(c0 + r2 + 1)] DELETE m2` o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `Y:real^3->bool`)) (concl th) &&
               can (find_term ((=) `connected:(real^3->bool)->bool`)) (concl th))) THEN
      REWRITE_TAC[CONNECTED_SEMIOPEN_SEGMENT] THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `segment[m2,(U:num->real^3)(c0 + r2 + 1)] INTER (M UNION B) = {m2}` THEN
        SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(U:num->real^3)(c0 + r2 + 1)` THEN
      ASM_REWRITE_TAC[IN_DELETE; ENDS_IN_SEGMENT]]]);;

(* Fullness of subcomplexes in a barycentric subdivision, for segments and *)
(* hulls: a segment of the subdivision meets UNIONS l in the face spanned  *)
(* by its ends in UNIONS l; a simplex with all its vertices in UNIONS l is *)
(* a simplex of the subdivision of l.                                        *)

let MOI_FSP_SEG_FULL = prove
 (`!(t:(real^N->bool)->bool) l x z.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     segment[x,z] IN barycentric_subdivision t /\ ~(x = z)
     ==> (~(x IN UNIONS l) /\ ~(z IN UNIONS l) ==> segment[x,z] INTER UNIONS l = {}) /\
         (x IN UNIONS l /\ ~(z IN UNIONS l) ==> segment[x,z] INTER UNIONS l = {x}) /\
         (~(x IN UNIONS l) /\ z IN UNIONS l ==> segment[x,z] INTER UNIONS l = {z})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `segment[x:real^N,z]`]
    MOI_FRN_FULL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ABBREV_TAC `f = segment[x:real^N,z] INTER UNIONS l` THEN
  REWRITE_TAC[face_of] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p:real^N. p IN f /\ p IN segment(x,z) ==> x IN f /\ z IN f` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^N`; `z:real^N`; `p:real^N`]) THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->bool) SUBSET {x,z} \/ (x IN f /\ z IN f)` MP_TAC THENL
   [ASM_CASES_TAC `(f:real^N->bool) SUBSET {x,z}` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((f:real^N->bool) SUBSET {x,z})` THEN
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `p:real^N` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[open_segment; IN_DIFF] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:real^N. p IN f <=> p IN segment[x,z] /\ p IN UNIONS l` ASSUME_TAC THENL
   [EXPAND_TAC "f" THEN REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_SING] THEN
  MP_TAC(ISPECL [`x:real^N`; `z:real^N`] ENDS_IN_SEGMENT) THEN
  ASM SET_TAC[]);;

let MOI_FSP_HULL_FULL = prove
 (`!(t:(real^N->bool)->bool) l S.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     convex hull S IN barycentric_subdivision t /\ S SUBSET UNIONS l
     ==> convex hull S IN barycentric_subdivision l /\ convex hull S SUBSET UNIONS l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull S SUBSET UNIONS (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `convex hull S:real^N->bool`] MOI_FRN_FULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP FACE_OF_IMP_CONVEX o CONJUNCT2) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `convex hull S SUBSET convex hull S INTER UNIONS (l:(real^N->bool)->bool)`
    MP_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[SUBSET_INTER; HULL_SUBSET];
      SET_TAC[]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FRN_FULL_SUBSET THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

(* A simplex of the derived neighbourhood complex missing UNIONS l lies in  *)
(* the derived frontier.                                                     *)

let MOI_FSP_NC_FR = prove
 (`!(t:(real^N->bool)->bool) l s.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     s IN derived_nbhd_complex t l /\ s INTER UNIONS l = {}
     ==> s SUBSET derived_frontier t l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN barycentric_subdivision (barycentric_subdivision t)`
  MP_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
      MOI_FDN_DERIVED_NBHD_COMPLEX_SUBCOMPLEX) THEN
    ASM_REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `g:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; EMPTY_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (t:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `INTERS g IN (g:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `g:(real^N->bool)->bool`;
                   `barycentric_subdivision (t:(real^N->bool)->bool)`] MOI_FN2_CHAIN_MIN_IN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[simplicial_subcomplex; SUBSET_REFL] THEN
        ASM_MESON_TAC[moi_bar_complex];
        UNDISCH_TAC `moi_bar_chain (barycentric_subdivision t) (g:(real^N->bool)->bool)` THEN
        REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `s0 = INTERS (g:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(s0:real^N->bool) IN barycentric_subdivision t /\ ~(s0 = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision t) (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
    UNDISCH_TAC `(s0:real^N->bool) IN g` THEN
    UNDISCH_TAC `g SUBSET barycentric_subdivision (t:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `~({}:real^N->bool IN g)` THEN MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((s0:real^N->bool) SUBSET UNIONS l)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `simplex_barycentre (s0:real^N->bool) IN UNIONS l` MP_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `s0:real^N->bool`]
        MOI_FN2_BARY_IN_L) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `simplex_barycentre (s0:real^N->bool) IN s` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u:real^N. {u} IN barycentric_subdivision t /\ u IN s0 /\ ~(u IN UNIONS l)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(!u:real^N. {u} IN barycentric_subdivision t /\ u IN s0 ==> u IN UNIONS l)`
    MP_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `~((s0:real^N->bool) SUBSET UNIONS l)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `convex (s0:real^N->bool) /\ compact s0` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_CONVEX; MOI_FM3_LF_COMPACT; BARYCENTRIC_SUBDIVISION_LF];
      ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP KREIN_MILMAN_MINKOWSKI o CONJ
      (ASSUME `convex (s0:real^N->bool)`)) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `s0:real^N->bool`]
      MOI_FRN_FULL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP FACE_OF_IMP_CONVEX o CONJUNCT2) THEN
    DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `s0 INTER UNIONS (l:(real^N->bool)->bool)` THEN
    REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^N) IN s0` ASSUME_TAC THENL
     [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s0:real^N->bool` THEN
    ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF; FACE_OF_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t) ({u:real^N} INSERT g)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FN2_CHAIN_INSERT_MIN THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(convex hull (IMAGE simplex_barycentre ({u:real^N} INSERT g)) IN
                  derived_nbhd_complex t l)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `{u:real^N} INSERT g`] MOI_FN2_NC_CHAIN) THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INTERS_INSERT; NOT_EXISTS_THM] THEN X_GEN_TAC `r:real^N->bool` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `r = {u:real^N}` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `r SUBSET {u:real^N} INTER INTERS g` THEN
      UNDISCH_TAC `~(r:real^N->bool = {})` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~((u:real^N) IN UNIONS l)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS (barycentric_subdivision (l:(real^N->bool)->bool))`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (IMAGE simplex_barycentre ({u:real^N} INSERT g)) IN
                barycentric_subdivision (barycentric_subdivision t)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `{u:real^N} INSERT g` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOI_FN2_FRONTIER_NC] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `derived_nbhd t l = UNIONS (derived_nbhd_complex t (l:(real^N->bool)->bool))`
    SUBST1_TAC THENL
     [ASM_MESON_TAC[MOI_FDN_UNIONS_DERIVED_NBHD_COMPLEX]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre ({u:real^N} INSERT g))` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
    SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

(* No simplex of the barycentric subdivision of a subdivision has a vertex *)
(* in UNIONS P off UNIONS Q and a vertex in UNIONS Q off UNIONS P.          *)

let MOI_FSP_NO_CROSS = prove
 (`!(t:(real^N->bool)->bool) P Q x z.
     lf_simplicial_complex t /\ simplicial_subcomplex P t /\ simplicial_subcomplex Q t /\
     segment[x,z] IN barycentric_subdivision (barycentric_subdivision t) /\
     x IN UNIONS P /\ ~(x IN UNIONS Q) /\ z IN UNIONS Q /\ ~(z IN UNIONS P)
     ==> F`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `segment[x:real^N,z] IN barycentric_subdivision (barycentric_subdivision t)` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN IMAGE simplex_barycentre g /\ (z:real^N) IN IMAGE simplex_barycentre g`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `p:real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(p:real^N->bool) IN barycentric_subdivision t /\ ~(p = {}) /\
                (q:real^N->bool) IN barycentric_subdivision t /\ ~(q = {}) /\
                (p SUBSET q \/ q SUBSET p)`
  (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THENL
   [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision t) (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
    UNDISCH_TAC `(p:real^N->bool) IN g` THEN UNDISCH_TAC `(q:real^N->bool) IN g` THEN
    UNDISCH_TAC `g SUBSET barycentric_subdivision (t:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `~({}:real^N->bool IN g)` THEN
    UNDISCH_TAC `!s t:real^N->bool. s IN g /\ t IN g ==> s SUBSET t \/ t SUBSET s` THEN
    MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `P:(real^N->bool)->bool`; `p:real^N->bool`]
    MOI_FN2_BARY_IN_L) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `Q:(real^N->bool)->bool`; `p:real^N->bool`]
    MOI_FN2_BARY_IN_L) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `P:(real^N->bool)->bool`; `q:real^N->bool`]
    MOI_FN2_BARY_IN_L) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `Q:(real^N->bool)->bool`; `q:real^N->bool`]
    MOI_FN2_BARY_IN_L) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(x:real^N) = simplex_barycentre p`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `(z:real^N) = simplex_barycentre q`)) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(p:real^N->bool) SUBSET q \/ q SUBSET p` THEN SET_TAC[]);;

(* Links of interior vertices are finite combinatorial 2-manifolds (as      *)
(* MOI_FTP_LINK_CM2 of pc_moi_fnd_tubep, which this file does not load).     *)

let MOI_FSP_LINK_CM2 = prove
 (`!(c:(real^N->bool)->bool) v.
     lf_simplicial_complex c /\ {v} IN c /\
     pl_sphere 2 (UNIONS (simplicial_link c v))
     ==> FINITE (simplicial_link c v) /\ combinatorial_manifold 2 (simplicial_link c v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{s:real^N->bool | ?r. r IN c /\ v IN r /\ s face_of r}` THEN
    ASM_SIMP_TAC[MOI_FTA_CSTAR_COMPLEX] THEN
    REWRITE_TAC[SUBSET; simplicial_link; IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_SIMP_TAC[MOI_FTA_LINK_LF] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FTA_S2LINK THEN ASM_REWRITE_TAC[]]);;

(* Two simplices of an lf complex of the same dimension, the relative       *)
(* interior of one meeting the other, are equal; hence an edge (triangle)   *)
(* on the surface boundary (complex boundary) is a boundary edge (triangle). *)

let MOI_FSP_RELINT_SAME_DIM = prove
 (`!(c:(real^N->bool)->bool) s r x.
     lf_simplicial_complex c /\ s IN c /\ r IN c /\ aff_dim s = aff_dim r /\
     x IN relative_interior s /\ x IN r
     ==> s = r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET r` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) face_of r` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `r:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ASM_REWRITE_TAC[INT_LT_REFL] THEN
  ASM_MESON_TAC[MOI_FM3_LF_CONVEX]);;

let MOI_FSP_BD_TRI = prove
 (`!(c:(real^N->bool)->bool) s.
     lf_simplicial_complex c /\ s IN c /\ aff_dim s = &2 /\ s SUBSET complex_boundary c
     ==> CARD {r | r IN c /\ aff_dim r = &3 /\ s SUBSET r} = 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x:real^N. x IN relative_interior s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `convex (s:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN complex_boundary c` MP_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s:real^N->bool = r` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOI_FSP_RELINT_SAME_DIM THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN ASM_REWRITE_TAC[]);;

let MOI_FSP_BD_EDGE = prove
 (`!(c:(real^N->bool)->bool) s.
     lf_simplicial_complex c /\ s IN c /\ aff_dim s = &1 /\ s SUBSET surface_boundary c
     ==> CARD {r | r IN c /\ aff_dim r = &2 /\ s SUBSET r} = 1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x:real^N. x IN relative_interior s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `convex (s:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN surface_boundary c` MP_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s:real^N->bool = r` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOI_FSP_RELINT_SAME_DIM THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN ASM_REWRITE_TAC[]);;

(* A triangle of a combinatorial surface with boundary is not inside its    *)
(* surface boundary.                                                         *)

let MOI_FSP_TRI_NOT_IN_SB = prove
 (`!(c:(real^N->bool)->bool) s.
     lf_simplicial_complex c /\ s IN c /\ aff_dim s = &2
     ==> ~(s SUBSET surface_boundary c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x:real^N. x IN relative_interior s` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `convex (s:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN surface_boundary c` MP_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET r` MP_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC]);;

(* The fan around an edge [v0,y0] of an lf complex TT: with the cycle U of *)
(* the link of y0 in the link K of v0 (MOI_FN2_ROT), the triangles of TT    *)
(* containing the edge are the hulls of v0, y0, U i, and the tetrahedra    *)
(* v0, y0, U i, U(SUC i) are in TT.                                          *)

let MOI_FSP_FAN = prove
 (`!(TT:(real^N->bool)->bool) v0 y0 dd (U:num->real^N).
     lf_simplicial_complex TT /\ {v0} IN TT /\ segment[v0,y0] IN TT /\ ~(v0 = y0) /\
     moi_fn2_kcyc (simplicial_link (simplicial_link TT v0) y0) dd U /\
     (!i. ~(U i = y0)) /\
     (!i. ~affine_dependent {y0, U i, U(SUC i)} /\
          convex hull {y0, U i, U(SUC i)} IN simplicial_link TT v0)
     ==> (!i. convex hull {v0, y0, U i} IN TT /\ aff_dim (convex hull {v0, y0, U i}) = &2 /\
              segment[v0,y0] SUBSET convex hull {v0, y0, U i} /\
              ~(U i = v0) /\ {U i} IN TT /\ segment[U i,U(SUC i)] IN TT /\
              convex hull {v0, y0, U i, U(SUC i)} IN TT /\
              aff_dim (convex hull {v0, y0, U i, U(SUC i)}) = &3 /\
              segment[U i,U(SUC i)] SUBSET convex hull {v0, y0, U i, U(SUC i)} /\
              convex hull {v0, y0, U i} SUBSET convex hull {v0, y0, U i, U(SUC i)} /\
              convex hull {v0, y0, U(SUC i)} SUBSET convex hull {v0, y0, U i, U(SUC i)}) /\
         (!r. r IN TT /\ aff_dim r = &2 /\ segment[v0,y0] SUBSET r
              ==> ?i. i < dd /\ r = convex hull {v0, y0, U i}) /\
         (!i j. convex hull {v0, y0, U i} = convex hull {v0, y0, U j} ==> U i = U j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `K = simplicial_link (TT:(real^N->bool)->bool) v0` THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^N->bool)->bool) /\
                (!s:real^N->bool. s IN K ==> s IN TT)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FTA_LINK_LF]; REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{y0:real^N} IN TT /\ {y0:real^N} IN K` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{y0:real^N} IN TT` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `segment[v0:real^N,y0]` THEN
      ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "K" THEN REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[IN_SING] THEN EXISTS_TAC `segment[v0:real^N,y0]` THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT; FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. {(U:num->real^N) i} IN simplicial_link K y0 /\
                    segment[U i,U(SUC i)] IN simplicial_link K y0`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fn2_kcyc (simplicial_link K y0) dd (U:num->real^N)` THEN
    ASM_REWRITE_TAC[moi_fn2_kcyc] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. convex hull {y0,(U:num->real^N) i} IN K /\
                    aff_dim (convex hull {y0,(U:num->real^N) i}) = &1 /\
                    {(U:num->real^N) i} IN K /\ ~(U i = v0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `y0:real^N`; `{(U:num->real^N) i}`]
      MOI_FM3_LINK_JOIN) THEN
    ASM_REWRITE_TAC[AFF_DIM_SING] THEN CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{(U:num->real^N) i} IN K` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LINK_IN]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{(U:num->real^N) i} IN K` THEN EXPAND_TAC "K" THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM; IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. ~((U:num->real^N) i = U(SUC i))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC_ALL THEN EXISTS_TAC `dd:num` THEN
    UNDISCH_TAC `moi_fn2_kcyc (simplicial_link K y0) dd (U:num->real^N)` THEN
    REWRITE_TAC[moi_fn2_kcyc] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th))) THEN
    MP_TAC(ISPECL [`TT:(real^N->bool)->bool`; `v0:real^N`; `convex hull {y0,(U:num->real^N) i}`]
      MOI_FM3_LINK_JOIN) THEN
    MP_TAC(ISPECL [`TT:(real^N->bool)->bool`; `v0:real^N`;
                   `convex hull {y0,(U:num->real^N) i, U(SUC i)}`] MOI_FM3_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM HULL_INSERT] THEN
    SUBGOAL_THEN `aff_dim (convex hull {y0,(U:num->real^N) i,U(SUC i)}) = &2` SUBST1_TAC THENL
     [REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
      FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `affine_dependent:(real^N->bool)->bool`)) (concl th))) THEN
      DISCH_THEN(SUBST1_TAC o MATCH_MP AFF_DIM_AFFINE_INDEPENDENT) THEN
      SUBGOAL_THEN `CARD {y0:real^N,U(i:num),U(SUC i)} = 3` SUBST1_TAC THENL
       [SUBGOAL_THEN `~(y0 = (U:num->real^N) i) /\ ~(y0 = U(SUC i)) /\ ~(U i = U(SUC i))`
        STRIP_ASSUME_TAC THENL
         [MP_TAC(SPEC `i:num` (ASSUME `!i. ~((U:num->real^N) i = y0)`)) THEN
          MP_TAC(SPEC `SUC i` (ASSUME `!i. ~((U:num->real^N) i = y0)`)) THEN
          MP_TAC(SPEC `i:num` (ASSUME `!i. ~((U:num->real^N) i = U(SUC i))`)) THEN
          MESON_TAC[];
          ALL_TAC] THEN
        SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
        REWRITE_TAC[ASSUME `~(y0 = (U:num->real^N) i)`; ASSUME `~(y0 = (U:num->real^N) (SUC i))`;
                    ASSUME `~((U:num->real^N) i = U (SUC i))`] THEN
        CONV_TAC NUM_REDUCE_CONV;
        CONV_TAC INT_REDUCE_CONV];
      ALL_TAC] THEN
    CONV_TAC INT_REDUCE_CONV THEN
    DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
    REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
           MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
           MATCH_MP_TAC(ASSUME `!s:real^N->bool. s IN K ==> s IN TT`) THEN
           FIRST_ASSUM ACCEPT_TAC;
           MATCH_MP_TAC(ASSUME `!s:real^N->bool. s IN K ==> s IN TT`) THEN
           MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `y0:real^N`;
                          `segment[(U:num->real^N) i,U(SUC i)]`] MOI_FM3_LINK_IN) THEN
           ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(v0:real^N) IN r /\ (y0:real^N) IN r` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`TT:(real^N->bool)->bool`; `v0:real^N`; `r:real^N->bool`] MOI_FM3_LINK_OPP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`TT:(real^N->bool)->bool`; `v0:real^N`; `s:real^N->bool`] MOI_FM3_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `aff_dim (s:real^N->bool) = &1` ASSUME_TAC THENL
     [UNDISCH_TAC `aff_dim (r:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(y0:real^N) IN s` ASSUME_TAC THENL
     [SUBGOAL_THEN `(y0:real^N) extreme_point_of r` MP_TAC THENL
       [REWRITE_TAC[GSYM FACE_OF_SING] THEN
        SUBGOAL_THEN `{y0:real^N} INTER r = {y0}` (SUBST1_TAC o SYM) THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[MOI_FM3_LF_INTER];
        ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th = `r = convex hull ((v0:real^N) INSERT s)`)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) IN K` ASSUME_TAC THENL
     [EXPAND_TAC "K" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `y0:real^N`; `s:real^N->bool`] MOI_FSP_EDGE_AT_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `{u:real^N} IN simplicial_link K y0` ASSUME_TAC THENL
     [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[IN_SING] THEN
      TRY(CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_fn2_kcyc (simplicial_link K y0) dd (U:num->real^N)` THEN
    REWRITE_TAC[moi_fn2_kcyc] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^N` o el 4 o CONJUNCTS) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL; GSYM HULL_INSERT];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
    FIRST_ASSUM((fun th -> MP_TAC(SPEC `i:num` th) THEN MP_TAC(SPEC `j:num` th)) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th))) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `convex hull {v0,y0,(U:num->real^N) j} IN TT` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`TT:(real^N->bool)->bool`; `v0:real^N`; `convex hull {y0,(U:num->real^N) j}`]
        MOI_FM3_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM HULL_INSERT] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `((U:num->real^N) i) extreme_point_of convex hull {v0,y0,U j}` MP_TAC THENL
     [REWRITE_TAC[GSYM FACE_OF_SING] THEN
      SUBGOAL_THEN `{(U:num->real^N) i} INTER convex hull {v0,y0,U j} = {U i}`
        (SUBST1_TAC o SYM) THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
          `convex hull {v0,y0,(U:num->real^N) i} = convex hull {v0,y0,U j}`)) THEN
        MATCH_MP_TAC(SET_RULE `(x:real^N) IN s ==> {x} INTER s = {x}`) THEN
        MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`TT:(real^N->bool)->bool`; `{(U:num->real^N) i}`;
                     `convex hull {v0,y0,(U:num->real^N) j}`] MOI_FM3_LF_INTER) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(ASSUME `!s:real^N->bool. s IN K ==> s IN TT`) THEN
        ASM_REWRITE_TAC[];
        SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    MP_TAC(SPEC `i:num` (ASSUME `!i. ~((U:num->real^N) i = y0)`)) THEN
    UNDISCH_TAC `~((U:num->real^N) i = v0)` THEN MESON_TAC[]]);;

(* Injectivity of a cycle on any window of length n.                         *)

let MOI_FSP_WINDOW_INJ = prove
 (`!n (S:num->A) c r r'.
     3 <= n /\ (!i. S(i + n) = S i) /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     r < n /\ r' < n /\ S(c + r) = S(c + r')
     ==> r = r'`,
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(ARITH_RULE `r:num <= r' \/ r' <= r`) THENL
   [MP_TAC(ISPECL [`n:num`; `S:num->A`; `c + r:num`; `r' - r:num`] MOI_FN2_CYC_INJ_WINDOW) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c + r) + r' - r = c + r':num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC];
    MP_TAC(ISPECL [`n:num`; `S:num->A`; `c + r':num`; `r - r':num`] MOI_FN2_CYC_INJ_WINDOW) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(c + r') + r - r' = c + r:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

(* The cycle around a boundary edge of the trace circle J: an edge [v0,y0] *)
(* of the second derived of ld on J, the cycle U around it (the link of y0 *)
(* in the link of v0), the only point U c0 of the cycle on d = UNIONS ld,   *)
(* and the two points U(c0 + r1), U(c0 + r2) on M = UNIONS lm.               *)

let MOI_FSP_SIDE_CYCLE = prove
 (`!(t:(real^N->bool)->bool) ld lm.
     FINITE t /\ lf_simplicial_complex t /\
     simplicial_subcomplex ld t /\ simplicial_subcomplex lm t /\
     FINITE (barycentric_subdivision (barycentric_subdivision ld)) /\
     combinatorial_manifold_with_boundary 2
       (barycentric_subdivision (barycentric_subdivision ld)) /\
     surface_boundary (barycentric_subdivision (barycentric_subdivision ld)) =
     UNIONS ld INTER UNIONS lm /\
     ~(UNIONS ld INTER UNIONS lm = {}) /\
     FINITE (barycentric_subdivision (barycentric_subdivision lm)) /\
     combinatorial_manifold 2 (barycentric_subdivision (barycentric_subdivision lm)) /\
     (!w. {w} IN barycentric_subdivision (barycentric_subdivision t) /\
          w IN UNIONS ld INTER UNIONS lm
          ==> pl_sphere 2 (UNIONS (simplicial_link
                (barycentric_subdivision (barycentric_subdivision t)) w)))
     ==> ?v0 y0 dd (U:num->real^N) c0 r1 r2.
           ~(v0 = y0) /\
           segment[v0,y0] IN barycentric_subdivision (barycentric_subdivision t) /\
           segment[v0,y0] SUBSET UNIONS ld INTER UNIONS lm /\
           (!i. convex hull {v0, y0, U i} IN barycentric_subdivision (barycentric_subdivision t) /\
                aff_dim (convex hull {v0, y0, U i}) = &2 /\
                segment[v0,y0] SUBSET convex hull {v0, y0, U i} /\
                ~(U i = v0) /\ {U i} IN barycentric_subdivision (barycentric_subdivision t) /\
                segment[U i,U(SUC i)] IN barycentric_subdivision (barycentric_subdivision t) /\
                convex hull {v0, y0, U i, U(SUC i)} IN
                  barycentric_subdivision (barycentric_subdivision t) /\
                aff_dim (convex hull {v0, y0, U i, U(SUC i)}) = &3 /\
                segment[U i,U(SUC i)] SUBSET convex hull {v0, y0, U i, U(SUC i)} /\
                convex hull {v0, y0, U i} SUBSET convex hull {v0, y0, U i, U(SUC i)} /\
                convex hull {v0, y0, U(SUC i)} SUBSET convex hull {v0, y0, U i, U(SUC i)}) /\
           (!i. ~(U i = y0)) /\ (!i. ~(U i = U(SUC i))) /\
           (!i j. convex hull {v0, y0, U i} = convex hull {v0, y0, U j} ==> U i = U j) /\
           3 <= dd /\ (!i. U(i + dd) = U i) /\
           (!r r'. r < dd /\ r' < dd /\ U(c0 + r) = U(c0 + r') ==> r = r') /\
           U c0 IN UNIONS ld /\ ~(U c0 IN UNIONS lm) /\
           (!r. 0 < r /\ r < dd ==> ~(U(c0 + r) IN UNIONS ld)) /\
           U(c0 + r1) IN UNIONS lm /\ U(c0 + r2) IN UNIONS lm /\
           ~(U(c0 + r1) IN UNIONS ld) /\ ~(U(c0 + r2) IN UNIONS ld) /\
           0 < r1 /\ r1 < r2 /\ r2 < dd /\
           (!r. r < dd /\ ~(r = r1) /\ ~(r = r2) ==> ~(U(c0 + r) IN UNIONS lm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `TT = barycentric_subdivision (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
  ABBREV_TAC `ldT = barycentric_subdivision (barycentric_subdivision (ld:(real^N->bool)->bool))` THEN
  ABBREV_TAC `lmT = barycentric_subdivision (barycentric_subdivision (lm:(real^N->bool)->bool))` THEN
  ABBREV_TAC `J = UNIONS ld INTER UNIONS (lm:(real^N->bool)->bool)` THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `ld:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `lm:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `ld:(real^N->bool)->bool`] MOI_FSP_BSD2) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `lm:(real^N->bool)->bool`] MOI_FSP_BSD2) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (ldT:(real^N->bool)->bool) /\
                lf_simplicial_complex (lmT:(real^N->bool)->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary; combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. (s IN ldT ==> s IN TT) /\ (s IN lmT ==> s IN TT)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`simplicial_subcomplex (ldT:(real^N->bool)->bool) TT`;
      `simplicial_subcomplex (lmT:(real^N->bool)->bool) TT`] THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the boundary edge *)
  SUBGOAL_THEN `?e:real^N->bool. e IN ldT /\ aff_dim e = &1 /\
                  CARD {r | r IN ldT /\ aff_dim r = &2 /\ e SUBSET r} = 1 /\ e SUBSET J`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(J:real^N->bool = {})` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `surface_boundary (ldT:(real^N->bool)->bool)`)) THEN
    REWRITE_TAC[surface_boundary; GSYM MEMBER_NOT_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `e:real^N->bool` THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v0 y0:real^N. ~(v0 = y0) /\ e = segment[v0,y0]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_PL2_SIMPLEX_1] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `aff_dim (e:real^N->bool) = &1`)) THEN
    MATCH_MP_TAC MOI_FM3_LF_SIMPLEX THEN EXISTS_TAC `ldT:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `segment[v0:real^N,y0] IN TT /\ {v0:real^N} IN TT /\ {y0:real^N} IN TT /\
                (v0:real^N) IN J /\ (y0:real^N) IN J`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `segment[v0:real^N,y0] IN TT` ASSUME_TAC THENL
     [MATCH_MP_TAC(CONJUNCT1(SPEC `segment[v0:real^N,y0]` (ASSUME
        `!s:real^N->bool. (s IN ldT ==> s IN TT) /\ (s IN lmT ==> s IN TT)`))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `segment[v0:real^N,y0]` THEN
      ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `segment[v0:real^N,y0]` THEN
      ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      MP_TAC(ASSUME `segment[v0:real^N,y0] SUBSET J`) THEN MESON_TAC[ENDS_IN_SEGMENT; SUBSET];
      MP_TAC(ASSUME `segment[v0:real^N,y0] SUBSET J`) THEN MESON_TAC[ENDS_IN_SEGMENT; SUBSET]];
    ALL_TAC] THEN
  (* the link of v0 and the cycle around y0 *)
  SUBGOAL_THEN `FINITE (simplicial_link TT (v0:real^N)) /\
                combinatorial_manifold 2 (simplicial_link TT (v0:real^N))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSP_LINK_CM2 THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{y0:real^N} IN simplicial_link TT v0` ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[IN_SING] THEN
    EXISTS_TAC `segment[v0:real^N,y0]` THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT; FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`simplicial_link TT (v0:real^N)`; `y0:real^N`] MOI_FN2_ROT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:num` (X_CHOOSE_THEN `U:num->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`TT:(real^N->bool)->bool`; `v0:real^N`; `y0:real^N`; `dd:num`; `U:num->real^N`]
    MOI_FSP_FAN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "FB") (LABEL_TAC "FC"))) THEN
  SUBGOAL_THEN `3 <= dd /\ (!i. (U:num->real^N)(i + dd) = U i) /\
                (!i j. i < dd /\ j < dd /\ (U:num->real^N) i = U j ==> i = j)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fn2_kcyc (simplicial_link (simplicial_link TT v0) y0) dd (U:num->real^N)` THEN
    REWRITE_TAC[moi_fn2_kcyc] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. ~((U:num->real^N) i = U(SUC i))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC_ALL THEN EXISTS_TAC `dd:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* full subcomplexes: triangles at the edge with the third vertex in d or M *)
  SUBGOAL_THEN
   `!i. ((U:num->real^N) i IN UNIONS ld ==> convex hull {v0,y0,U i} IN ldT) /\
        ((U:num->real^N) i IN UNIONS lm ==> convex hull {v0,y0,U i} IN lmT)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN CONJ_TAC THEN DISCH_TAC THENL
     [EXPAND_TAC "ldT" THEN
      MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                     `barycentric_subdivision (ld:(real^N->bool)->bool)`;
                     `{v0:real^N,y0,U(i:num)}`] MOI_FSP_HULL_FULL);
      EXPAND_TAC "lmT" THEN
      MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                     `barycentric_subdivision (lm:(real^N->bool)->bool)`;
                     `{v0:real^N,y0,U(i:num)}`] MOI_FSP_HULL_FULL)] THEN
    ASM_REWRITE_TAC[] THEN
    (ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]]) THEN
    UNDISCH_TAC `(v0:real^N) IN J` THEN UNDISCH_TAC `(y0:real^N) IN J` THEN
    REWRITE_TAC[GSYM(ASSUME `UNIONS ld INTER UNIONS (lm:(real^N->bool)->bool) = J`)] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  (* the triangle of ldT at the edge, and the unique cycle point on d *)
  SUBGOAL_THEN `?kap:real^N->bool. {r | r IN ldT /\ aff_dim r = &2 /\ segment[v0,y0] SUBSET r} = {kap}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_FRN_SA_CARD_EQ_1] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(kap:real^N->bool) IN ldT /\ aff_dim kap = &2 /\ segment[v0,y0] SUBSET kap`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(kap:real^N->bool) IN {r | r IN ldT /\ aff_dim r = &2 /\ segment[v0,y0] SUBSET r}`
    MP_TAC THENL [ASM_REWRITE_TAC[IN_SING]; REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?ik. ik < (dd:num) /\ kap = convex hull {v0:real^N,y0,(U:num->real^N) ik}` STRIP_ASSUME_TAC THENL
   [USE_THEN "FB" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(CONJUNCT1(SPEC `kap:real^N->bool` (ASSUME
      `!s:real^N->bool. (s IN ldT ==> s IN TT) /\ (s IN lmT ==> s IN TT)`))) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^N) ik IN UNIONS ld` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS (ldT:(real^N->bool)->bool)` &&
      rhs(concl th) = `UNIONS (ld:(real^N->bool)->bool)`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `kap:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. (U:num->real^N) i IN UNIONS ld ==> U i = U ik` (LABEL_TAC "DU") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN USE_THEN "FC" MATCH_MP_TAC THEN
    SUBGOAL_THEN `convex hull {v0:real^N,y0,U(i:num)} IN
                  {r | r IN ldT /\ aff_dim r = &2 /\ segment[v0,y0] SUBSET r}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  (* the two triangles of lmT at the edge, and the two cycle points on M *)
  SUBGOAL_THEN `segment[v0:real^N,y0] IN lmT` ASSUME_TAC THENL
   [EXPAND_TAC "lmT" THEN MATCH_MP_TAC MOI_FRN_FULL_SUBSET THEN
    EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `segment[v0:real^N,y0] SUBSET J` THEN
    REWRITE_TAC[GSYM(ASSUME `UNIONS ld INTER UNIONS (lm:(real^N->bool)->bool) = J`)] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lmT:(real^N->bool)->bool`; `segment[v0:real^N,y0]`] MOI_FCL_EDGE_TRIANGLES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?i1 i2. i1 < (dd:num) /\ i2 < dd /\ s1 = convex hull {v0:real^N,y0,(U:num->real^N) i1} /\
                        s2 = convex hull {v0:real^N,y0,(U:num->real^N) i2}` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(s1:real^N->bool) IN TT /\ (s2:real^N->bool) IN TT` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      MATCH_MP_TAC(CONJUNCT2(SPEC_ALL(ASSUME
        `!s:real^N->bool. (s IN ldT ==> s IN TT) /\ (s IN lmT ==> s IN TT)`))) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "FB" (MP_TAC o SPEC `s1:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i1:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "FB" (MP_TAC o SPEC `s2:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i2:num` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`i1:num`; `i2:num`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th =
    `s2 = convex hull {v0:real^N,y0,U(i2:num)}`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th =
    `s1 = convex hull {v0:real^N,y0,U(i1:num)}`)) THEN
  SUBGOAL_THEN `(U:num->real^N) i1 IN UNIONS lm /\ (U:num->real^N) i2 IN UNIONS lm`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS (lmT:(real^N->bool)->bool)` &&
      rhs(concl th) = `UNIONS (lm:(real^N->bool)->bool)`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN CONJ_TAC THENL
     [EXISTS_TAC `convex hull {v0:real^N,y0,(U:num->real^N) i1}`;
      EXISTS_TAC `convex hull {v0:real^N,y0,(U:num->real^N) i2}`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. (U:num->real^N) i IN UNIONS lm ==> U i = U i1 \/ U i = U i2`
  (LABEL_TAC "MU") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `convex hull {v0:real^N,y0,U(i:num)} IN
                  {t | t IN lmT /\ aff_dim t = &2 /\ segment[v0,y0] SUBSET t}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    USE_THEN "FC" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN `~((U:num->real^N) i1 = U i2)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(convex hull {v0:real^N,y0,U(i1:num)} = convex hull {v0,y0,U i2})` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((U:num->real^N) ik IN UNIONS lm)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(kap:real^N->bool) IN lmT` ASSUME_TAC THENL
     [USE_THEN "MU" (MP_TAC o SPEC `ik:num`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ldT:(real^N->bool)->bool`; `kap:real^N->bool`] MOI_FSP_TRI_NOT_IN_SB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `surface_boundary (ldT:(real^N->bool)->bool) = J`] THEN
    SUBGOAL_THEN `(kap:real^N->bool) SUBSET UNIONS ld /\ kap SUBSET UNIONS lm` MP_TAC THENL
     [CONJ_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `UNIONS (ldT:(real^N->bool)->bool)` &&
          rhs(concl th) = `UNIONS (ld:(real^N->bool)->bool)`));
        FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `UNIONS (lmT:(real^N->bool)->bool)` &&
          rhs(concl th) = `UNIONS (lm:(real^N->bool)->bool)`))] THEN
      MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN c ==> s SUBSET UNIONS c`) THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM(ASSUME `UNIONS ld INTER UNIONS (lm:(real^N->bool)->bool) = J`)] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((U:num->real^N) i1 IN UNIONS ld) /\ ~((U:num->real^N) i2 IN UNIONS ld)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~((U:num->real^N) ik IN UNIONS lm)` THEN REWRITE_TAC[] THENL
     [USE_THEN "DU" (MP_TAC o SPEC `i1:num`); USE_THEN "DU" (MP_TAC o SPEC `i2:num`)] THEN
    (ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dd:num`; `U:num->real^N`; `ik:num`; `i1:num`] MOI_FN2_CYC_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q1:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`dd:num`; `U:num->real^N`; `ik:num`; `i2:num`] MOI_FN2_CYC_REP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `q2:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!r r'. r < dd /\ r' < dd /\ (U:num->real^N)(ik + r) = U(ik + r') ==> r = r'`
  (LABEL_TAC "WI") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`dd:num`; `U:num->real^N`; `ik:num`] MOI_FSP_WINDOW_INJ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^N)(ik + q1) IN UNIONS lm /\ (U:num->real^N)(ik + q2) IN UNIONS lm /\
                ~((U:num->real^N)(ik + q1) IN UNIONS ld) /\ ~((U:num->real^N)(ik + q2) IN UNIONS ld)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `(U:num->real^N) i1 = U(ik + q1)`);
                GSYM(ASSUME `(U:num->real^N) i2 = U(ik + q2)`)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q1 = 0) /\ ~(q2 = 0) /\ ~(q1 = q2)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `(U:num->real^N)(ik + q1) IN UNIONS lm` THEN
      ASM_REWRITE_TAC[ADD_CLAUSES];
      UNDISCH_TAC `(U:num->real^N)(ik + q2) IN UNIONS lm` THEN
      ASM_REWRITE_TAC[ADD_CLAUSES];
      UNDISCH_TAC `~((U:num->real^N) i1 = U i2)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. 0 < r /\ r < dd ==> ~((U:num->real^N)(ik + r) IN UNIONS ld)` ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN DISCH_TAC THEN
    USE_THEN "DU" (MP_TAC o SPEC `ik + r:num`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN DISCH_TAC THEN
    SUBGOAL_THEN `r = 0` (fun th -> UNDISCH_TAC `0 < r` THEN REWRITE_TAC[th] THEN ARITH_TAC) THEN
    USE_THEN "WI" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN MOI_FSP_NUM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r < dd /\ ~(r = q1) /\ ~(r = q2) ==> ~((U:num->real^N)(ik + r) IN UNIONS lm)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN DISCH_TAC THEN
    USE_THEN "MU" (MP_TAC o SPEC `ik + r:num`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    REWRITE_TAC[ASSUME `(U:num->real^N) i1 = U(ik + q1)`; ASSUME `(U:num->real^N) i2 = U(ik + q2)`] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `~(r:num = q1)` THEN REWRITE_TAC[] THEN USE_THEN "WI" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `~(r:num = q2)` THEN REWRITE_TAC[] THEN USE_THEN "WI" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v0:real^N`; `y0:real^N`; `dd:num`; `U:num->real^N`; `ik:num`] THEN
  DISJ_CASES_TAC(MP (ARITH_RULE `~(q1:num = q2) ==> q1 < q2 \/ q2 < q1`)
                    (ASSUME `~(q1:num = q2)`)) THENL
   [MAP_EVERY EXISTS_TAC [`q1:num`; `q2:num`]; MAP_EVERY EXISTS_TAC [`q2:num`; `q1:num`]] THEN
  REPEAT CONJ_TAC THEN
  FIRST [FIRST_ASSUM ACCEPT_TAC;
         MOI_FSP_NUM_ARITH_TAC;
         X_GEN_TAC `r:num` THEN STRIP_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* A face of a triangle missing a vertex lies in the opposite edge.          *)

let MOI_FSP_FACE_TRI_OPP = prove
 (`!(m:real^N) v0 y0 f.
     f face_of convex hull {v0, y0, m} /\ ~(m IN f) ==> f SUBSET segment[v0,y0]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(q:real^N) IN convex hull {v0,y0,m}` MP_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `{v0:real^N,y0,m} = m INSERT {v0,y0}` SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{v0:real^N,y0}`; `m:real^N`] CONVEX_HULL_INSERT) THEN
  REWRITE_TAC[NOT_INSERT_EMPTY] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_ELIM_THM; GSYM SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `w:real` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC))) THEN
  ASM_CASES_TAC `u = &0` THENL
   [UNDISCH_TAC `(q:real^N) = u % m + w % b` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `w = &1` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_LID] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `w = &0` THENL
   [UNDISCH_TAC `~((m:real^N) IN f)` THEN
    SUBGOAL_THEN `u = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(q:real^N) = u % m + w % b` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_LID; VECTOR_ADD_RID] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `b:real^N = m` THENL
   [UNDISCH_TAC `~((m:real^N) IN f)` THEN
    UNDISCH_TAC `(q:real^N) = u % m + w % b` THEN ASM_REWRITE_TAC[GSYM VECTOR_ADD_RDISTRIB] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `f face_of convex hull {v0:real^N,y0,m}` THEN REWRITE_TAC[face_of] THEN
  DISCH_THEN(MP_TAC o SPECL [`m:real^N`; `b:real^N`; `q:real^N`] o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
      MP_TAC(ISPECL [`v0:real^N`; `y0:real^N`] SEGMENT_CONVEX_HULL) THEN
      DISCH_THEN(fun th -> UNDISCH_TAC `(b:real^N) IN segment[v0,y0]` THEN REWRITE_TAC[th]) THEN
      SPEC_TAC(`b:real^N`,`b:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `w:real` THEN REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[] THEN AP_THM_TAC THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        ASM_REAL_ARITH_TAC]];
    ASM_REWRITE_TAC[]]);;

(* The half triangle at a point p of the edge [v0,y0] of a triangle of the  *)
(* second derived whose third vertex m is off d: connected, inside the       *)
(* triangle minus d, containing m.                                           *)

let MOI_FSP_HALF_TRI = prove
 (`!(t:(real^N->bool)->bool) ld v0 y0 (m:real^N) p r.
     lf_simplicial_complex t /\ simplicial_subcomplex ld t /\
     segment[v0,y0] IN barycentric_subdivision (barycentric_subdivision t) /\
     convex hull {v0,y0,m} IN barycentric_subdivision (barycentric_subdivision t) /\
     segment[v0,y0] SUBSET convex hull {v0,y0,m} /\ segment[v0,y0] SUBSET UNIONS ld /\
     ~(m IN UNIONS ld) /\ p IN segment[v0,y0] /\ &0 < r
     ==> connected ((ball(p,r) INTER (convex hull {v0,y0,m} DIFF segment[v0,y0])) UNION
                    (segment[p,m] DELETE p)) /\
         (ball(p,r) INTER (convex hull {v0,y0,m} DIFF segment[v0,y0])) UNION
         (segment[p,m] DELETE p) SUBSET convex hull {v0,y0,m} DIFF UNIONS ld /\
         m IN (ball(p,r) INTER (convex hull {v0,y0,m} DIFF segment[v0,y0])) UNION
              (segment[p,m] DELETE p) /\
         convex hull {v0,y0,m} SUBSET derived_nbhd t ld /\
         ball(p,r) INTER (convex hull {v0,y0,m} DIFF segment[v0,y0]) SUBSET
         (ball(p,r) INTER (convex hull {v0,y0,m} DIFF segment[v0,y0])) UNION
         (segment[p,m] DELETE p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `tau = convex hull {v0:real^N,y0,m}` THEN
  ABBREV_TAC `TT = barycentric_subdivision (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
  SUBGOAL_THEN `lf_simplicial_complex (TT:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "TT" THEN ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[v0:real^N,y0] face_of tau` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN EXISTS_TAC `TT:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau INTER UNIONS ld SUBSET segment[v0:real^N,y0]` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN MATCH_MP_TAC(ISPEC `m:real^N` MOI_FSP_FACE_TRI_OPP) THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                     `barycentric_subdivision (ld:(real^N->bool)->bool)`; `tau:real^N->bool`]
        MOI_FRN_FULL) THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `ld:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N) IN tau /\ (p:real^N) IN tau` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "tau" THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(p:real^N = m)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((m:real^N) IN UNIONS ld)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(p:real^N) IN segment[v0,y0]` THEN
    UNDISCH_TAC `segment[v0:real^N,y0] SUBSET UNIONS ld` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p:real^N,m] SUBSET tau` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "tau" THEN REWRITE_TAC[CONVEX_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p:real^N,m] DELETE p SUBSET tau DIFF segment[v0,y0]` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DELETE; IN_DIFF] THEN X_GEN_TAC `q:real^N` THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM SET_TAC[];
      DISCH_TAC THEN ASM_CASES_TAC `q:real^N = m` THENL
       [UNDISCH_TAC `~((m:real^N) IN UNIONS ld)` THEN REWRITE_TAC[] THEN
        UNDISCH_TAC `segment[v0:real^N,y0] SUBSET UNIONS ld` THEN ASM SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(q:real^N) IN segment(p,m)` ASSUME_TAC THENL
       [REWRITE_TAC[open_segment] THEN ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `segment[v0:real^N,y0] face_of tau` THEN REWRITE_TAC[face_of] THEN
      DISCH_THEN(MP_TAC o SPECL [`p:real^N`; `m:real^N`; `q:real^N`] o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((m:real^N) IN UNIONS ld)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `segment[v0:real^N,y0] SUBSET UNIONS ld` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `tau DIFF segment[v0:real^N,y0] SUBSET tau DIFF UNIONS ld` ASSUME_TAC THENL
   [UNDISCH_TAC `tau INTER UNIONS ld SUBSET segment[v0:real^N,y0]` THEN SET_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
      REWRITE_TAC[CONVEX_BALL] THEN
      MP_TAC(ISPECL [`tau:real^N->bool`; `segment[v0:real^N,y0]`] FACE_OF_STILLCONVEX) THEN
      EXPAND_TAC "tau" THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      REWRITE_TAC[ASSUME `convex hull {v0:real^N,y0,m} = tau`] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CONNECTED_SEMIOPEN_SEGMENT] THEN
    SUBGOAL_THEN `~(ball(p:real^N,r) INTER (segment[p,m] DELETE p) = {})` MP_TAC THENL
     [MP_TAC(ISPECL [`p:real^N`; `m:real^N`] MOI_FSP_SEMI_CLOSURE) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
      DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `z:real^N` THEN
      ASM_REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `segment[p:real^N,m] DELETE p SUBSET tau DIFF segment[v0,y0]` THEN SET_TAC[]];
    MAP_EVERY UNDISCH_TAC
     [`segment[p:real^N,m] DELETE p SUBSET tau DIFF segment[v0,y0]`;
      `tau DIFF segment[v0:real^N,y0] SUBSET tau DIFF UNIONS ld`] THEN SET_TAC[];
    REWRITE_TAC[IN_UNION; IN_DELETE; ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[];
    REWRITE_TAC[derived_nbhd] THEN MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN c ==> s SUBSET UNIONS c`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "TT" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `v0:real^N` THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET];
      ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]];
    SET_TAC[]]);;

(* The 2D fact at the boundary edge [v0,y0] of the trace circle J: the far  *)
(* vertices m1, m2 of the two triangles of M at the edge are not on the     *)
(* same end of the trace annulus.                                            *)

let MOI_FSP_SIDE_2D = prove
 (`!(t:(real^3->bool)->bool) ld lm j1 j2 v0 y0 (m1:real^3) m2.
     FINITE t /\ lf_simplicial_complex t /\
     simplicial_subcomplex ld t /\ simplicial_subcomplex lm t /\
     FINITE (barycentric_subdivision (barycentric_subdivision lm)) /\
     combinatorial_manifold 2 (barycentric_subdivision (barycentric_subdivision lm)) /\
     pl_annulus_with_ends (derived_nbhd t ld INTER UNIONS lm) j1 j2 /\
     UNIONS ld INTER UNIONS lm SUBSET (derived_nbhd t ld INTER UNIONS lm) DIFF (j1 UNION j2) /\
     pl_sphere 1 (UNIONS ld INTER UNIONS lm) /\ pl_sphere 1 j1 /\ pl_sphere 1 j2 /\
     j1 UNION j2 SUBSET derived_nbhd t ld INTER UNIONS lm /\
     ~(v0 = y0) /\
     segment[v0,y0] IN barycentric_subdivision (barycentric_subdivision t) /\
     segment[v0,y0] SUBSET UNIONS ld INTER UNIONS lm /\
     convex hull {v0,y0,m1} IN barycentric_subdivision (barycentric_subdivision t) /\
     convex hull {v0,y0,m2} IN barycentric_subdivision (barycentric_subdivision t) /\
     aff_dim (convex hull {v0,y0,m1}) = &2 /\ aff_dim (convex hull {v0,y0,m2}) = &2 /\
     segment[v0,y0] SUBSET convex hull {v0,y0,m1} /\
     segment[v0,y0] SUBSET convex hull {v0,y0,m2} /\
     m1 IN UNIONS lm /\ ~(m1 IN UNIONS ld) /\ m2 IN UNIONS lm /\ ~(m2 IN UNIONS ld) /\
     ~(convex hull {v0,y0,m1} = convex hull {v0,y0,m2})
     ==> ~(m1 IN j1 /\ m2 IN j1) /\ ~(m1 IN j2 /\ m2 IN j2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `lmT = barycentric_subdivision (barycentric_subdivision (lm:(real^3->bool)->bool))` THEN
  ABBREV_TAC `J = UNIONS ld INTER UNIONS (lm:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `lf_simplicial_complex (lmT:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v0:real^3) IN J /\ (y0:real^3) IN J` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `segment[v0:real^3,y0] SUBSET J` THEN MESON_TAC[ENDS_IN_SEGMENT; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^3->bool) SUBSET UNIONS lm /\ J SUBSET UNIONS ld` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "J" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {v0:real^3,y0,m1} IN lmT /\ convex hull {v0:real^3,y0,m2} IN lmT /\
                segment[v0:real^3,y0] IN lmT`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [EXPAND_TAC "lmT" THEN
      MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                     `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                     `{v0:real^3,y0,m1}`] MOI_FSP_HULL_FULL);
      EXPAND_TAC "lmT" THEN
      MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                     `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                     `{v0:real^3,y0,m2}`] MOI_FSP_HULL_FULL);
      EXPAND_TAC "lmT" THEN MATCH_MP_TAC MOI_FRN_FULL_SUBSET THEN
      EXISTS_TAC `barycentric_subdivision (t:(real^3->bool)->bool)` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]] THEN
    ASM_REWRITE_TAC[] THEN (ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (segment[v0:real^3,y0]) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `{r | r IN lmT /\ aff_dim r = &2 /\ segment[v0:real^3,y0] SUBSET r} =
                {convex hull {v0,y0,m1}, convex hull {v0,y0,m2}}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FN2_CARD2_EQ THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FRN_SA_CM_EDGE2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `p = midpoint(v0:real^3,y0)` THEN
  SUBGOAL_THEN `(p:real^3) IN relative_interior (segment[v0,y0]) /\ p IN segment[v0,y0] /\ p IN J`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "p" THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT; MIDPOINT_IN_SEGMENT; ASSUME `~(v0:real^3 = y0)`] THEN
    MP_TAC(ISPECL [`v0:real^3`; `y0:real^3`] (CONJUNCT1 MIDPOINT_IN_SEGMENT)) THEN
    UNDISCH_TAC `segment[v0:real^3,y0] SUBSET J` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e1. &0 < e1 /\ !x:real^3. x IN ball(p,e1) /\ x IN UNIONS lm
                     ==> x IN convex hull {v0,y0,m1} UNION convex hull {v0,y0,m2}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `closed (UNIONS {s:real^3->bool | s IN lmT /\ ~(p IN s)})` MP_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        ASM_MESON_TAC[MOI_FM3_LF_COMPACT]];
      ALL_TAC] THEN
    REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e1:real` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN UNIONS lmT` MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(p:real^3) IN s` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `ball(p:real^3,e1) SUBSET (:real^3) DIFF
                   UNIONS {s | s IN lmT /\ ~(p IN s)}` THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[v0:real^3,y0] SUBSET s` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`lmT:(real^3->bool)->bool`; `p:real^3`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (s:real^3->bool) = &1 \/ aff_dim s = &2` MP_TAC THENL
     [MP_TAC(ISPECL [`segment[v0:real^3,y0]`; `s:real^3->bool`] AFF_DIM_SUBSET) THEN
      MP_TAC(ISPECL [`lmT:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FRN_SA_CM_DIM) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `segment[v0:real^3,y0] = s` (SUBST_ALL_TAC o SYM) THENL
       [MATCH_MP_TAC MOI_FSP_RELINT_SAME_DIM THEN
        MAP_EVERY EXISTS_TAC [`lmT:(real^3->bool)->bool`; `p:real^3`] THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `segment[v0:real^3,y0] SUBSET convex hull {v0,y0,m1}` THEN ASM SET_TAC[]];
      SUBGOAL_THEN `(s:real^3->bool) IN {r | r IN lmT /\ aff_dim r = &2 /\ segment[v0:real^3,y0] SUBSET r}`
      MP_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e2. &0 < e2 /\ ball(p:real^3,e2) INTER (j1 UNION j2) = {}` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `closed (j1 UNION j2:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC CLOSED_UNION THEN ASM_MESON_TAC[MOI_SLV_CIRCLE_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      UNDISCH_TAC `J SUBSET (derived_nbhd t ld INTER UNIONS lm) DIFF (j1 UNION j2:real^3->bool)` THEN
      UNDISCH_TAC `(p:real^3) IN J` THEN SET_TAC[];
      MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `r = min e1 e2` THEN
  SUBGOAL_THEN `&0 < r /\ ball(p:real^3,r) SUBSET ball(p,e1) /\ ball(p:real^3,r) SUBSET ball(p,e2)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[BALL_MIN_INTER; INTER_SUBSET] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`; `v0:real^3`; `y0:real^3`;
                 `m1:real^3`; `p:real^3`; `r:real`] MOI_FSP_HALF_TRI) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`; `v0:real^3`; `y0:real^3`;
                 `m2:real^3`; `p:real^3`; `r:real`] MOI_FSP_HALF_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `convex hull {v0:real^3,y0,m1} SUBSET UNIONS lm /\
                convex hull {v0:real^3,y0,m2} SUBSET UNIONS lm` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS (lmT:(real^3->bool)->bool)` &&
      rhs(concl th) = `UNIONS (lm:(real^3->bool)->bool)`)) THEN
    CONJ_TAC THEN MATCH_MP_TAC(SET_RULE `(s:real^3->bool) IN c ==> s SUBSET UNIONS c`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSP_TWO_ENDS THEN
  MAP_EVERY EXISTS_TAC
   [`derived_nbhd t ld INTER UNIONS (lm:(real^3->bool)->bool)`; `J:real^3->bool`;
    `ball(p:real^3,r)`;
    `(ball(p,r) INTER (convex hull {v0,y0,m1} DIFF segment[v0,y0])) UNION
     (segment[p:real^3,m1] DELETE p)`;
    `(ball(p,r) INTER (convex hull {v0,y0,m2} DIFF segment[v0,y0])) UNION
     (segment[p:real^3,m2] DELETE p)`;
    `p:real^3`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `j1:real^3->bool` MOI_SLV_CIRCLE_CLOSED) THEN ASM_SIMP_TAC[];
    MP_TAC(ISPEC `j2:real^3->bool` MOI_SLV_CIRCLE_CLOSED) THEN ASM_SIMP_TAC[];
    UNDISCH_TAC `j1 UNION j2 SUBSET derived_nbhd t ld INTER UNIONS (lm:(real^3->bool)->bool)` THEN
    SET_TAC[];
    UNDISCH_TAC `j1 UNION j2 SUBSET derived_nbhd t ld INTER UNIONS (lm:(real^3->bool)->bool)` THEN
    SET_TAC[];
    UNDISCH_TAC `ball(p:real^3,r) SUBSET ball(p,e2)` THEN
    UNDISCH_TAC `ball(p:real^3,e2) INTER (j1 UNION j2) = {}` THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_INTER; IN_UNION] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN convex hull {v0,y0,m1} UNION convex hull {v0,y0,m2}` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `e1:real`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `ball(p:real^3,r) SUBSET ball(p,e1)` THEN
      UNDISCH_TAC `(x:real^3) IN ball(p,r)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((x:real^3) IN segment[v0,y0])` ASSUME_TAC THENL
     [UNDISCH_TAC `~((x:real^3) IN J)` THEN UNDISCH_TAC `segment[v0:real^3,y0] SUBSET J` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL [DISJ1_TAC; DISJ2_TAC] THEN DISJ1_TAC THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DIFF];
    MAP_EVERY UNDISCH_TAC
     [`(ball(p,r) INTER (convex hull {v0,y0,m1} DIFF segment[v0,y0])) UNION
       (segment[p:real^3,m1] DELETE p) SUBSET convex hull {v0,y0,m1} DIFF UNIONS ld`;
      `convex hull {v0:real^3,y0,m1} SUBSET derived_nbhd t ld`;
      `convex hull {v0:real^3,y0,m1} SUBSET UNIONS lm`; `(J:real^3->bool) SUBSET UNIONS ld`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`(ball(p,r) INTER (convex hull {v0,y0,m2} DIFF segment[v0,y0])) UNION
       (segment[p:real^3,m2] DELETE p) SUBSET convex hull {v0,y0,m2} DIFF UNIONS ld`;
      `convex hull {v0:real^3,y0,m2} SUBSET derived_nbhd t ld`;
      `convex hull {v0:real^3,y0,m2} SUBSET UNIONS lm`; `(J:real^3->bool) SUBSET UNIONS ld`] THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* The cut.  For a combinatorial 3-manifold with boundary y in t            *)
(* containing the disk d, whose boundary is M plus a closed set B away from *)
(* N, the simplices of the second derived of y inside the closure of |y|    *)
(* minus N form a combinatorial 3-manifold with boundary whose boundary is  *)
(* the boundary of y minus N plus the two disks d1, d2.                     *)
(* ========================================================================= *)

(* The frontier of the closure of Y minus N, given which parts of the frontier *)
(* F of N lie in Y.                                                           *)

let MOI_FSP_CUT_FRONTIER = prove
 (`!(Y:real^3->bool) N FR M B d1 d2 j1 j2.
     closed Y /\ closed N /\ closure (interior N) = N /\ frontier N = FR /\
     frontier Y = M UNION B /\ DISJOINT B N /\ FR INTER M = j1 UNION j2 /\
     (FR DIFF M) INTER Y = (d1 UNION d2) DIFF (j1 UNION j2) /\
     closure (d1 DIFF j1) = d1 /\ closure (d2 DIFF j2) = d2 /\
     j1 SUBSET d1 /\ j2 SUBSET d2 /\ d1 INTER j2 = {} /\ d2 INTER j1 = {} /\
     d1 SUBSET FR /\ d2 SUBSET FR
     ==> frontier (closure (Y DIFF N)) = ((M UNION B) DIFF N) UNION d1 UNION d2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `W = closure (Y DIFF N:real^3->bool)` THEN
  SUBGOAL_THEN `(W:real^3->bool) SUBSET Y /\ closed W` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[CLOSED_CLOSURE] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior N INTER (W:real^3->bool) = {}` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_INTERIOR] THEN
    MP_TAC(ISPEC `N:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FR = N DIFF interior (N:real^3->bool) /\ M UNION B = Y DIFF interior (Y:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      (rhs(concl th) = `FR:real^3->bool` || rhs(concl th) = `M UNION B:real^3->bool`)))) THEN
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (W:real^3->bool) SUBSET (M UNION B) UNION FR` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `frontier (Y DIFF N:real^3->bool)` THEN
    CONJ_TAC THENL [EXPAND_TAC "W" THEN REWRITE_TAC[FRONTIER_CLOSURE_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `Y DIFF N = Y INTER ((:real^3) DIFF N:real^3->bool)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `frontier Y UNION frontier ((:real^3) DIFF N)` THEN
    REWRITE_TAC[FRONTIER_INTER_SUBSET; FRONTIER_COMPLEMENT] THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (W:real^3->bool) SUBSET W` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `interior (W:real^3->bool) SUBSET interior Y` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(d1 UNION d2) DIFF (j1 UNION j2) SUBSET frontier (W:real^3->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(p:real^3) IN FR /\ p IN Y /\ ~(p IN M)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(FR DIFF M) INTER Y = (d1 UNION d2) DIFF (j1 UNION (j2:real^3->bool))` THEN
      UNDISCH_TAC `(p:real^3) IN (d1 UNION d2) DIFF (j1 UNION j2)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^3) IN interior Y` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      SUBGOAL_THEN `(p:real^3) IN M UNION B` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
      UNDISCH_TAC `DISJOINT B (N:real^3->bool)` THEN
      UNDISCH_TAC `FR = N DIFF interior (N:real^3->bool)` THEN
      UNDISCH_TAC `(p:real^3) IN FR` THEN UNDISCH_TAC `~((p:real^3) IN M)` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; IN_DIFF] THEN CONJ_TAC THENL
     [EXPAND_TAC "W" THEN
      SUBGOAL_THEN `(p:real^3) IN interior Y INTER closure ((:real^3) DIFF N)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; CLOSURE_COMPLEMENT; IN_DIFF; IN_UNIV] THEN
        UNDISCH_TAC `FR = N DIFF interior (N:real^3->bool)` THEN
        UNDISCH_TAC `(p:real^3) IN FR` THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `!s t. s SUBSET t ==> (x:real^3) IN s ==> x IN t`) THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure (interior Y INTER ((:real^3) DIFF N))` THEN
      SIMP_TAC[OPEN_INTER_CLOSURE_SUBSET; OPEN_INTERIOR] THEN
      MATCH_MP_TAC SUBSET_CLOSURE THEN MP_TAC(ISPEC `Y:real^3->bool` INTERIOR_SUBSET) THEN
      SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(p:real^3) IN closure (interior N)` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `FR = N DIFF interior (N:real^3->bool)` THEN
        UNDISCH_TAC `(p:real^3) IN FR` THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `interior W INTER interior (N:real^3->bool) = {}` MP_TAC THENL
       [MP_TAC(ISPEC `W:real^3->bool` INTERIOR_SUBSET) THEN
        UNDISCH_TAC `interior N INTER (W:real^3->bool) = {}` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`interior W:real^3->bool`; `interior N:real^3->bool`]
                    OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(p:real^3) IN interior W` THEN
      UNDISCH_TAC `(p:real^3) IN closure (interior N)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `d1 SUBSET frontier (W:real^3->bool) /\ d2 SUBSET frontier W`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [GEN_REWRITE_TAC LAND_CONV [GSYM(ASSUME `closure (d1 DIFF j1) = (d1:real^3->bool)`)];
      GEN_REWRITE_TAC LAND_CONV [GSYM(ASSUME `closure (d2 DIFF j2) = (d2:real^3->bool)`)]] THEN
    MATCH_MP_TAC CLOSURE_MINIMAL THEN REWRITE_TAC[FRONTIER_CLOSED] THEN
    UNDISCH_TAC `(d1 UNION d2) DIFF (j1 UNION j2) SUBSET frontier (W:real^3->bool)` THEN
    UNDISCH_TAC `(d1:real^3->bool) INTER j2 = {}` THEN
    UNDISCH_TAC `(d2:real^3->bool) INTER j1 = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`frontier (W:real^3->bool) SUBSET (M UNION B) UNION FR`;
      `frontier (W:real^3->bool) SUBSET W`; `(W:real^3->bool) SUBSET Y`;
      `interior N INTER (W:real^3->bool) = {}`; `FR = N DIFF interior (N:real^3->bool)`;
      `DISJOINT B (N:real^3->bool)`; `FR INTER M = j1 UNION (j2:real^3->bool)`;
      `(FR DIFF M) INTER Y = (d1 UNION d2) DIFF (j1 UNION (j2:real^3->bool))`;
      `(j1:real^3->bool) SUBSET d1`; `(j2:real^3->bool) SUBSET d2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[UNION_SUBSET] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^3` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; IN_DIFF] THEN CONJ_TAC THENL
   [EXPAND_TAC "W" THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    ASM_REWRITE_TAC[IN_DIFF];
    UNDISCH_TAC `interior (W:real^3->bool) SUBSET interior Y` THEN
    UNDISCH_TAC `~((p:real^3) IN interior Y)` THEN SET_TAC[]]);;

(* The context of the cut.                                                    *)

let MOI_FSP_CUT_CTX = prove
 (`!(m:(real^3->bool)->bool) d j v a b t ld lm j1 j2 d1 d2 y B.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     moi_fsp_box m d v a b t ld lm /\ moi_fsp_ends m j t ld j1 j2 d1 d2 /\
     simplicial_subcomplex y t /\ combinatorial_manifold_with_boundary 3 y /\
     ld SUBSET y /\ complex_boundary y = UNIONS m UNION B /\ closed B /\
     DISJOINT B (derived_nbhd t ld)
     ==> FINITE y /\ lf_simplicial_complex y /\ simplicial_subcomplex ld y /\
         UNIONS m SUBSET UNIONS y /\
         FINITE (barycentric_subdivision (barycentric_subdivision y)) /\
         lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision y)) /\
         UNIONS (barycentric_subdivision (barycentric_subdivision y)) = UNIONS y /\
         combinatorial_manifold_with_boundary 3
           (barycentric_subdivision (barycentric_subdivision y)) /\
         complex_boundary (barycentric_subdivision (barycentric_subdivision y)) =
         UNIONS m UNION B /\
         simplicial_subcomplex (barycentric_subdivision (barycentric_subdivision y))
                               (barycentric_subdivision (barycentric_subdivision t)) /\
         simplicial_subcomplex (derived_nbhd_complex y ld)
                               (barycentric_subdivision (barycentric_subdivision y)) /\
         FINITE (derived_nbhd_complex y ld) /\
         lf_simplicial_complex (derived_nbhd_complex y ld) /\
         combinatorial_manifold_with_boundary 3 (derived_nbhd_complex y ld) /\
         UNIONS (derived_nbhd_complex y ld) = derived_nbhd t ld INTER UNIONS y /\
         complex_boundary (derived_nbhd_complex y ld) =
         (derived_frontier t ld INTER UNIONS y) UNION (derived_nbhd t ld INTER UNIONS m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m d v a b t ld (lm:(real^3->bool)->bool)`) (concl th))) THEN
  SUBGOAL_THEN `lf_simplicial_complex (y:(real^3->bool)->bool) /\ FINITE y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `simplicial_subcomplex ld (y:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex ld (t:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `ld SUBSET (y:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `UNIONS m SUBSET UNIONS (y:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `y:(real^3->bool)->bool` MOI_FMB_CB_SUBSET) THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `y:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; BARYCENTRIC_SUBDIVISION_LF] THEN
  MP_TAC(ISPEC `y:(real^3->bool)->bool` COMBINATORIAL_WB_BARYCENTRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `barycentric_subdivision (y:(real^3->bool)->bool)`
               COMBINATORIAL_WB_BARYCENTRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                 `y:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ld INTER y = (ld:(real^3->bool)->bool)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `FINITE (ld:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `y:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`y:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`]
                DERIVED_NBHD_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t))
   [`UNIONS m SUBSET UNIONS (y:(real^3->bool)->bool)`;
    `DISJOINT B (derived_nbhd t (ld:(real^3->bool)->bool))`] THEN
  SET_TAC[]);;

(* The corners: vertices of the second derived of y on j1 UNION j2.            *)

let MOI_FSP_CUT_CORNER = prove
 (`!(m:(real^3->bool)->bool) d j v a b t ld lm j1 j2 d1 d2 y B w.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     moi_fsp_box m d v a b t ld lm /\ moi_fsp_ends m j t ld j1 j2 d1 d2 /\
     simplicial_subcomplex y t /\ combinatorial_manifold_with_boundary 3 y /\
     ld SUBSET y /\ complex_boundary y = UNIONS m UNION B /\ closed B /\
     DISJOINT B (derived_nbhd t ld) /\
     {w} IN barycentric_subdivision (barycentric_subdivision y) /\ w IN j1 UNION j2
     ==> pl_ball 2 (UNIONS (simplicial_link
           {s | s IN barycentric_subdivision (barycentric_subdivision y) /\
                s SUBSET closure (UNIONS (barycentric_subdivision (barycentric_subdivision y)) DIFF
                                  UNIONS (derived_nbhd_complex y ld))} w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                 `y:(real^3->bool)->bool`; `B:real^3->bool`] MOI_FSP_CUT_CTX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m d v a b t ld (lm:(real^3->bool)->bool)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_ends] o check (fun th ->
    can (term_match [] `moi_fsp_ends m j t ld j1 j2 d1 (d2:real^3->bool)`) (concl th))) THEN
  ABBREV_TAC `yT = barycentric_subdivision (barycentric_subdivision (y:(real^3->bool)->bool))` THEN
  ABBREV_TAC `A = derived_nbhd_complex y (ld:(real^3->bool)->bool)` THEN
  ABBREV_TAC `T2 = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  MP_TAC(ISPECL [`yT:(real^3->bool)->bool`; `A:(real^3->bool)->bool`; `w:real^3`]
                MOI_FSP_COMP_LINK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN derived_frontier t ld /\ w IN UNIONS m /\
                w IN derived_nbhd t ld /\ ~(w IN B) /\ w IN UNIONS y /\
                w IN interval(a:real^3,b)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`derived_frontier t ld INTER UNIONS m = j1 UNION (j2:real^3->bool)`;
      `derived_frontier t ld SUBSET derived_nbhd t (ld:(real^3->bool)->bool)`;
      `DISJOINT B (derived_nbhd t (ld:(real^3->bool)->bool))`;
      `UNIONS m SUBSET UNIONS (y:(real^3->bool)->bool)`;
      `derived_nbhd t ld SUBSET v INTER interval(a:real^3,b)`;
      `(w:real^3) IN j1 UNION j2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (T2:(real^3->bool)->bool) /\
                combinatorial_manifold_with_boundary 3 T2 /\
                complex_boundary T2 = interval[a,b] DIFF interval(a:real^3,b) /\
                {w:real^3} IN T2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T2" THEN ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF] THEN
    MP_TAC(ISPEC `t:(real^3->bool)->bool` COMBINATORIAL_WB_BARYCENTRIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `barycentric_subdivision (t:(real^3->bool)->bool)`
                 COMBINATORIAL_WB_BARYCENTRIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `simplicial_subcomplex yT (T2:(real^3->bool)->bool)` THEN
    EXPAND_TAC "T2" THEN REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (simplicial_link T2 (w:real^3)))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `T2:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[IN_DIFF] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^3} IN A` ASSUME_TAC THENL
   [SUBGOAL_THEN `(w:real^3) IN UNIONS A` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FSP_VERTEX_SUB THEN
    MAP_EVERY EXISTS_TAC [`yT:(real^3->bool)->bool`; `s:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_ball 2 (UNIONS (simplicial_link yT (w:real^3))) /\
                pl_ball 2 (UNIONS (simplicial_link A (w:real^3)))` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `yT:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[IN_UNION] THEN SIMP_TAC[];
      MP_TAC(ISPEC `A:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN
      ASM_REWRITE_TAC[IN_UNION; IN_INTER] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (simplicial_link yT (w:real^3)) SUBSET UNIONS (simplicial_link T2 w) /\
                UNIONS (simplicial_link A (w:real^3)) SUBSET UNIONS (simplicial_link yT w)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THENL
     [MP_TAC(ISPECL [`T2:(real^3->bool)->bool`; `yT:(real^3->bool)->bool`; `w:real^3`]
                    MOI_FSP_LINK_SUB);
      MP_TAC(ISPECL [`yT:(real^3->bool)->bool`; `A:(real^3->bool)->bool`; `w:real^3`]
                    MOI_FSP_LINK_SUB)] THEN
    ASM_REWRITE_TAC[simplicial_subcomplex] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 2 (UNIONS (simplicial_link yT (w:real^3)))
                            (UNIONS (simplicial_link (boundary_complex yT) w)) /\
    pl_cell_with_boundary 2 (UNIONS (simplicial_link A (w:real^3)))
                            (UNIONS (simplicial_link (boundary_complex A) w))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FM3_BC_LINK] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `simplicial_link yT (w:real^3)` MOI_FM3_DISK_PL);
      MP_TAC(ISPEC `simplicial_link A (w:real^3)` MOI_FM3_DISK_PL)] THEN
    ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
    REWRITE_TAC[pl_cell_with_boundary] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`yT:(real^3->bool)->bool`; `A:(real^3->bool)->bool`;
                 `boundary_complex yT:(real^3->bool)->bool`; `w:real^3`] MOI_FSP_LINK_INTER) THEN
  MP_TAC(ISPEC `yT:(real^3->bool)->bool` MOI_FM3_BC_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `Ka = A INTER boundary_complex (yT:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `simplicial_subcomplex Ka (yT:(real^3->bool)->bool) /\ FINITE Ka /\
                lf_simplicial_complex Ka /\
                UNIONS Ka = derived_nbhd t ld INTER UNIONS (m:(real^3->bool)->bool) /\
                Ka SUBSET boundary_complex A /\ {w:real^3} IN Ka`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `simplicial_subcomplex Ka (yT:(real^3->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "Ka" THEN
      UNDISCH_TAC `simplicial_subcomplex A (yT:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `simplicial_subcomplex (boundary_complex yT) (yT:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_subcomplex; IN_INTER] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `A:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Ka" THEN SET_TAC[];
      MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `yT:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      EXPAND_TAC "Ka" THEN
      MP_TAC(ISPECL [`yT:(real^3->bool)->bool`; `A:(real^3->bool)->bool`;
                     `boundary_complex yT:(real^3->bool)->bool`] MOI_FN2_UNIONS_INTER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`UNIONS m SUBSET UNIONS (y:(real^3->bool)->bool)`;
        `DISJOINT B (derived_nbhd t (ld:(real^3->bool)->bool))`] THEN
      SET_TAC[];
      EXPAND_TAC "Ka" THEN GEN_REWRITE_TAC I [SUBSET] THEN
      REWRITE_TAC[IN_INTER; boundary_complex; IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(s:real^3->bool) SUBSET UNIONS A` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET complex_boundary yT` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT B (derived_nbhd t (ld:(real^3->bool)->bool))` THEN SET_TAC[];
      EXPAND_TAC "Ka" THEN ASM_REWRITE_TAC[IN_INTER; boundary_complex; IN_ELIM_THM] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 2 (Ka:(real^3->bool)->bool) /\
                surface_boundary Ka = j1 UNION (j2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `simplicial_subcomplex (ld INTER lm) (lm:(real^3->bool)->bool) /\
                  UNIONS (ld INTER lm) = (j:real^3->bool)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `simplicial_subcomplex ld (t:(real^3->bool)->bool)` THEN
        UNDISCH_TAC `simplicial_subcomplex lm (t:(real^3->bool)->bool)` THEN
        REWRITE_TAC[simplicial_subcomplex; IN_INTER] THEN SET_TAC[];
        MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                       `lm:(real^3->bool)->bool`] MOI_FN2_UNIONS_INTER) THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `ld INTER lm:(real^3->bool)->bool`]
                  MOI_FN2_NC_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_FSP_CELL_SPHERE1]; ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (ASSUME_TAC o SYM)) THEN
    MP_TAC(ISPECL [`derived_nbhd_complex lm (ld INTER lm:(real^3->bool)->bool)`;
                   `Ka:(real^3->bool)->bool`; `\x:real^3. x`; `\x:real^3. x`]
                  MOI_FRB_SURF_INVARIANT) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MOI_SCF_LF_SC] THEN ASM_REWRITE_TAC[HOMEOMORPHISM_ID];
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_ID] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `surface_boundary (Ka:(real^3->bool)->bool)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSP_DISK_CUT THEN
  MAP_EVERY EXISTS_TAC [`UNIONS (simplicial_link T2 (w:real^3))`;
                        `UNIONS (simplicial_link (boundary_complex yT) (w:real^3))`;
                        `UNIONS (simplicial_link (boundary_complex A) (w:real^3))`;
                        `UNIONS (simplicial_link Ka (w:real^3))`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_UNIONS THEN REWRITE_TAC[simplicial_link; SUBSET; IN_ELIM_THM] THEN
    UNDISCH_TAC `Ka SUBSET boundary_complex (A:(real^3->bool)->bool)` THEN SET_TAC[];
    MATCH_MP_TAC MOI_FSP_BDV_LINK THEN ASM_REWRITE_TAC[IN_UNION]]);;

(* Through a boundary triangle tau of the second derived of y there is only *)
(* one tetrahedron of it, so the two fan neighbours w and p of the far      *)
(* vertex q of tau are not both in y.                                        *)

let MOI_FSP_FAN_NOT_BOTH = prove
 (`!(t:(real^3->bool)->bool) y (M:real^3->bool) v0 y0 p q w.
     lf_simplicial_complex t /\ simplicial_subcomplex y t /\
     lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision y)) /\
     FINITE (barycentric_subdivision (barycentric_subdivision y)) /\
     M SUBSET complex_boundary (barycentric_subdivision (barycentric_subdivision y)) /\
     convex hull {v0,y0,q} IN barycentric_subdivision (barycentric_subdivision t) /\
     aff_dim (convex hull {v0,y0,q}) = &2 /\ convex hull {v0,y0,q} SUBSET M /\
     convex hull {v0,y0,p,q} IN barycentric_subdivision (barycentric_subdivision t) /\
     aff_dim (convex hull {v0,y0,p,q}) = &3 /\
     convex hull {v0,y0,q,w} IN barycentric_subdivision (barycentric_subdivision t) /\
     aff_dim (convex hull {v0,y0,q,w}) = &3 /\
     {w} IN barycentric_subdivision (barycentric_subdivision t) /\
     v0 IN UNIONS y /\ y0 IN UNIONS y /\ p IN UNIONS y /\ q IN UNIONS y /\ w IN UNIONS y /\
     ~(w = v0) /\ ~(w = y0) /\ ~(w = p) /\ ~(w = q)
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `y:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `TT = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  ABBREV_TAC `yT = barycentric_subdivision (barycentric_subdivision (y:(real^3->bool)->bool))` THEN
  SUBGOAL_THEN `lf_simplicial_complex (TT:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "TT" THEN ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `!S. convex hull S IN TT /\ S SUBSET UNIONS (y:(real^3->bool)->bool)
                    ==> convex hull S IN yT`
  (LABEL_TAC "YF") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision (y:(real^3->bool)->bool)`;
                   `S:real^3->bool`] MOI_FSP_HULL_FULL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `tau = convex hull {v0:real^3,y0,q}` THEN
  SUBGOAL_THEN `(tau:real^3->bool) IN yT` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN USE_THEN "YF" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {r:real^3->bool | r IN yT /\ aff_dim r = &3 /\ tau SUBSET r} = 1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSP_BD_TRI THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `?aa:real^3->bool. {r | r IN yT /\ aff_dim r = &3 /\ tau SUBSET r} = {aa}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_FRN_SA_CARD_EQ_1] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {v0,y0,p,q} = convex hull {v0:real^3,y0,q,w}` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `convex hull {v0,y0,p,q} IN {r | r IN yT /\ aff_dim r = &3 /\ tau SUBSET r} /\
      convex hull {v0:real^3,y0,q,w} IN {r | r IN yT /\ aff_dim r = &3 /\ tau SUBSET r}`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THEN CONJ_TAC THENL
       [USE_THEN "YF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
        EXPAND_TAC "tau" THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
        USE_THEN "YF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
        EXPAND_TAC "tau" THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
      ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) extreme_point_of convex hull {v0,y0,p,q}` MP_TAC THENL
   [REWRITE_TAC[GSYM FACE_OF_SING] THEN
    SUBGOAL_THEN `{w:real^3} INTER convex hull {v0,y0,p,q} = {w}` (SUBST1_TAC o SYM) THENL
     [ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> {x} INTER s = {x}`) THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`TT:(real^3->bool)->bool`; `{w:real^3}`;
                   `convex hull {v0,y0,p,q}:real^3->bool`] MOI_FM3_LF_INTER) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP EXTREME_POINT_OF_CONVEX_HULL) THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]);;

(* The witnesses of the side lemma in the cut context.                        *)

let MOI_FSP_SIDE_WIT = prove
 (`!(m:(real^3->bool)->bool) d j v a b t ld lm j1 j2 d1 d2 y B.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     moi_fsp_box m d v a b t ld lm /\ moi_fsp_ends m j t ld j1 j2 d1 d2 /\
     simplicial_subcomplex y t /\ combinatorial_manifold_with_boundary 3 y /\
     ld SUBSET y /\ complex_boundary y = UNIONS m UNION B /\ closed B /\
     DISJOINT B (derived_nbhd t ld)
     ==> ?Z0 Z1 Z2 (m1:real^3) m2.
           connected Z0 /\ Z0 SUBSET derived_frontier t ld DIFF UNIONS m /\
           Z0 INTER UNIONS y = {} /\ m1 IN closure Z0 /\ m2 IN closure Z0 /\
           connected Z1 /\ Z1 SUBSET (derived_frontier t ld DIFF UNIONS m) INTER UNIONS y /\
           m1 IN closure Z1 /\
           connected Z2 /\ Z2 SUBSET (derived_frontier t ld DIFF UNIONS m) INTER UNIONS y /\
           m2 IN closure Z2 /\
           ~(m1 IN j1 /\ m2 IN j1) /\ ~(m1 IN j2 /\ m2 IN j2) /\
           m1 IN j1 UNION j2 /\ m2 IN j1 UNION j2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                 `y:(real^3->bool)->bool`; `B:real^3->bool`] MOI_FSP_CUT_CTX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m d v a b t ld (lm:(real^3->bool)->bool)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_ends] o check (fun th ->
    can (term_match [] `moi_fsp_ends m j t ld j1 j2 d1 (d2:real^3->bool)`) (concl th))) THEN
  ABBREV_TAC `TT = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  ABBREV_TAC `ldT = barycentric_subdivision (barycentric_subdivision (ld:(real^3->bool)->bool))` THEN
  ABBREV_TAC `lmT = barycentric_subdivision (barycentric_subdivision (lm:(real^3->bool)->bool))` THEN
  ABBREV_TAC `yT = barycentric_subdivision (barycentric_subdivision (y:(real^3->bool)->bool))` THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `lf_simplicial_complex (ldT:(real^3->bool)->bool) /\
                lf_simplicial_complex (lmT:(real^3->bool)->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `TT:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS ld INTER UNIONS lm = (j:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (j:real^3->bool) /\ ~(j:real^3->bool = {})` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `pl_sphere 1 (j:real^3->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FSP_CELL_SPHERE1]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSP_SPHERE1_NONEMPTY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the second derived of ld: a combinatorial disk with boundary j *)
  SUBGOAL_THEN `FINITE (ldT:(real^3->bool)->bool) /\ FINITE (lmT:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ldT"; "lmT"] THEN
    ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 2 (ldT:(real^3->bool)->bool) /\
                surface_boundary ldT = (j:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d:real^3->bool`; `j:real^3->bool`] MOI_FSP_DISK_COMPLEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `ldT:(real^3->bool)->bool`;
                   `\x:real^3. x`; `\x:real^3. x`] MOI_FRB_SURF_INVARIANT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
      SUBGOAL_THEN `UNIONS (ldT:(real^3->bool)->bool) = UNIONS c` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; REWRITE_TAC[HOMEOMORPHISM_ID]];
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_ID] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `surface_boundary (ldT:(real^3->bool)->bool)`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold 2 (lmT:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `lmT:(real^3->bool)->bool`;
                   `\x:real^3. x`; `\x:real^3. x`] MOI_FRB_SURF_INVARIANT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF; HOMEOMORPHISM_ID] THEN
      UNDISCH_TAC `combinatorial_manifold 2 (lm:(real^3->bool)->bool)` THEN
      REWRITE_TAC[combinatorial_manifold; combinatorial_manifold_with_boundary] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  (* the box second derived: interior vertices have sphere links *)
  SUBGOAL_THEN `!w. {w} IN TT /\ w IN j ==> pl_sphere 2 (UNIONS (simplicial_link TT (w:real^3)))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `t:(real^3->bool)->bool` COMBINATORIAL_WB_BARYCENTRIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `barycentric_subdivision (t:(real^3->bool)->bool)` COMBINATORIAL_WB_BARYCENTRIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `TT:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    REWRITE_TAC[IN_DIFF] THEN
    MAP_EVERY UNDISCH_TAC
     [`(w:real^3) IN j`; `d INTER UNIONS m = (j:real^3->bool)`;
      `d UNION UNIONS m SUBSET interval(a:real^3,b)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`]
    MOI_FSP_SIDE_CYCLE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^3` (X_CHOOSE_THEN `y0:real^3` (X_CHOOSE_THEN `dd:num`
    (X_CHOOSE_THEN `U:num->real^3` (X_CHOOSE_THEN `c0:num` (X_CHOOSE_THEN `r1:num`
    (X_CHOOSE_THEN `r2:num` STRIP_ASSUME_TAC))))))) THEN
  (* simplices of the fan are in the neighbourhood *)
  SUBGOAL_THEN `(v0:real^3) IN d /\ (y0:real^3) IN d /\ v0 IN UNIONS m /\ y0 IN UNIONS m`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `segment[v0:real^3,y0] SUBSET j` THEN
    UNDISCH_TAC `d INTER UNIONS m = (j:real^3->bool)` THEN
    MP_TAC(ISPECL [`v0:real^3`; `y0:real^3`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. convex hull {v0,y0,(U:num->real^3) i,U(SUC i)} SUBSET derived_nbhd t ld`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[derived_nbhd] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) IN c ==> s SUBSET UNIONS c`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `v0:real^3` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. segment[(U:num->real^3) i,U(SUC i)] IN derived_nbhd_complex t ld /\
                    {(U:num->real^3) i} IN derived_nbhd_complex t ld`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN EXISTS_TAC `convex hull {v0,y0,(U:num->real^3) i,U(SUC i)}` THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `v0:real^3` THEN
       ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
       ALL_TAC]) THEN
    MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN EXISTS_TAC `TT:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN
    TRY(MATCH_MP_TAC(SET_RULE `(x:real^3) IN s ==> {x} SUBSET s`)) THEN
    TRY(REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]) THEN
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  (* the hypotheses of MOI_FSP_WIT_PATH *)
  SUBGOAL_THEN `!S. connected S /\ S INTER (UNIONS m UNION B) = {}
                    ==> S SUBSET UNIONS (y:(real^3->bool)->bool) \/ S INTER UNIONS y = {}`
  ASSUME_TAC THENL
   [X_GEN_TAC `S:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> q) ==> p \/ q`) THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `UNIONS (y:(real^3->bool)->bool)`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `y:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
    UNDISCH_TAC `S INTER (UNIONS m UNION B) = {}:real^3->bool` THEN
    UNDISCH_TAC `~((S:real^3->bool) SUBSET UNIONS y)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. segment[(U:num->real^3) i,U(SUC i)] INTER B = {}` ASSUME_TAC THENL
   [GEN_TAC THEN
    FIRST_ASSUM((fun th -> STRIP_ASSUME_TAC(SPEC `i:num` th)) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `aff_dim:(real^3->bool)->int`)) (concl th))) THEN
    MP_TAC(SPEC `i:num` (ASSUME
      `!i. convex hull {v0,y0,(U:num->real^3) i,U(SUC i)} SUBSET derived_nbhd t ld`)) THEN
    UNDISCH_TAC `DISJOINT B (derived_nbhd t (ld:(real^3->bool)->bool))` THEN
    UNDISCH_TAC `segment[(U:num->real^3) i,U(SUC i)] SUBSET convex hull {v0, y0, U i, U(SUC i)}` THEN
    REWRITE_TAC[DISJOINT] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `y:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  DISCH_THEN(STRIP_ASSUME_TAC) THEN
  (* fullness for the segments of the cycle *)
  SUBGOAL_THEN
   `!i. (~((U:num->real^3) i IN UNIONS m) /\ ~(U(SUC i) IN UNIONS m)
         ==> segment[U i,U(SUC i)] INTER UNIONS m = {}) /\
        ((U:num->real^3) i IN UNIONS m /\ ~(U(SUC i) IN UNIONS m)
         ==> segment[U i,U(SUC i)] INTER UNIONS m = {U i}) /\
        (~((U:num->real^3) i IN UNIONS m) /\ U(SUC i) IN UNIONS m
         ==> segment[U i,U(SUC i)] INTER UNIONS m = {U(SUC i)}) /\
        (~((U:num->real^3) i IN d) /\ ~(U(SUC i) IN d)
         ==> segment[U i,U(SUC i)] INTER d = {})`
  (LABEL_TAC "SF") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                   `(U:num->real^3) i`; `(U:num->real^3) (SUC i)`] MOI_FSP_SEG_FULL) THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision (ld:(real^3->bool)->bool)`;
                   `(U:num->real^3) i`; `(U:num->real^3) (SUC i)`] MOI_FSP_SEG_FULL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!i. ~((U:num->real^3) i IN UNIONS m) /\ ~(U(SUC i) IN UNIONS m)
         ==> segment[U i,U(SUC i)] INTER UNIONS m = {}) /\
    (!i. (U:num->real^3) i IN UNIONS m /\ ~(U(SUC i) IN UNIONS m)
         ==> segment[U i,U(SUC i)] INTER UNIONS m = {U i}) /\
    (!i. ~((U:num->real^3) i IN UNIONS m) /\ U(SUC i) IN UNIONS m
         ==> segment[U i,U(SUC i)] INTER UNIONS m = {U(SUC i)}) /\
    (!i. ~((U:num->real^3) i IN d) /\ ~(U(SUC i) IN d)
         ==> segment[U i,U(SUC i)] SUBSET derived_frontier t ld)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN GEN_TAC THENL
     [USE_THEN "SF" (fun th -> REWRITE_TAC[th]);
      USE_THEN "SF" (fun th -> REWRITE_TAC[th]);
      USE_THEN "SF" (fun th -> REWRITE_TAC[th]);
      STRIP_TAC THEN MATCH_MP_TAC MOI_FSP_NC_FR THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "SF" (MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o SPEC `i:num`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  (* the non-adjacent positions of the three special points of the cycle *)
  SUBGOAL_THEN `2 <= r1 /\ r1 + 2 <= r2 /\ r2 + 2 <= dd` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(r1 = 1) /\ ~(r2 = r1 + 1) /\ ~(r2 + 1 = dd)` MP_TAC THENL
     [ALL_TAC; MOI_FSP_NUM_ARITH_TAC] THEN
    REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                     `(U:num->real^3) c0`; `(U:num->real^3) (SUC c0)`] MOI_FSP_NO_CROSS) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `SUC c0 = c0 + r1` SUBST1_TAC THENL [MOI_FSP_NUM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `convex hull {v0,y0,(U:num->real^3)(c0 + r1),U(SUC(c0 + r1))} IN lmT`
      MP_TAC THENL
       [EXPAND_TAC "lmT" THEN
        MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                       `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                       `{v0:real^3,y0,U(c0 + r1),U(SUC(c0 + r1))}`] MOI_FSP_HULL_FULL) THEN
        ASM_REWRITE_TAC[] THEN
        ANTS_TAC THENL
         [SUBGOAL_THEN `SUC(c0 + r1) = c0 + r2` SUBST1_TAC THENL
           [MOI_FSP_NUM_ARITH_TAC; ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]];
          SIMP_TAC[]];
        ALL_TAC] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`lmT:(real^3->bool)->bool`;
                     `convex hull {v0,y0,(U:num->real^3)(c0 + r1),U(SUC(c0 + r1))}`]
        MOI_FRN_SA_CM_DIM) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                     `(U:num->real^3) (c0 + r2)`; `(U:num->real^3) (SUC(c0 + r2))`]
        MOI_FSP_NO_CROSS) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `SUC(c0 + r2) = c0 + dd` SUBST1_TAC THENL [MOI_FSP_NUM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^3) c0 IN UNIONS y` ASSUME_TAC THENL
   [UNDISCH_TAC `(U:num->real^3) c0 IN d` THEN
    UNDISCH_TAC `UNIONS ld = (d:real^3->bool)` THEN
    UNDISCH_TAC `ld SUBSET (y:(real^3->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  (* the triangle of M at the edge with far vertex U(c0 + r1) *)
  SUBGOAL_THEN `convex hull {v0,y0,(U:num->real^3)(c0 + r1)} SUBSET UNIONS m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                   `{v0:real^3,y0,(U:num->real^3)(c0 + r1)}`] MOI_FSP_HULL_FULL) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]; SIMP_TAC[]];
    ALL_TAC] THEN
  (* it is a boundary triangle of yT, so its two fan neighbours are not both in y *)
  SUBGOAL_THEN `~((U:num->real^3)(c0 + r1 - 1) IN UNIONS y /\ U(c0 + r1 + 1) IN UNIONS y)`
  ASSUME_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `SUC(c0 + r1 - 1) = c0 + r1 /\ SUC(c0 + r1) = c0 + r1 + 1` STRIP_ASSUME_TAC THENL
     [MOI_FSP_NUM_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM((fun th -> MAP_EVERY (fun t -> STRIP_ASSUME_TAC(REWRITE_RULE
        [ASSUME `SUC(c0 + r1 - 1) = c0 + r1`; ASSUME `SUC(c0 + r1) = c0 + r1 + 1`] (SPEC t th)))
      [`c0 + r1 - 1`; `c0 + r1:num`; `c0 + r1 + 1`]) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `aff_dim:(real^3->bool)->int`)) (concl th))) THEN
    SUBGOAL_THEN `(v0:real^3) IN UNIONS y /\ (y0:real^3) IN UNIONS y /\
                  (U:num->real^3)(c0 + r1) IN UNIONS y` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`UNIONS m SUBSET UNIONS (y:(real^3->bool)->bool)`; `(v0:real^3) IN UNIONS m`;
        `(y0:real^3) IN UNIONS m`; `(U:num->real^3)(c0 + r1) IN UNIONS m`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((U:num->real^3)(c0 + r1 + 1) = U(c0 + r1 - 1)) /\
                  ~((U:num->real^3)(c0 + r1 + 1) = U(c0 + r1))` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [DISCH_THEN(fun th ->
          MP_TAC(SPECL [`r1 + 1`; `r1 - 1`] (ASSUME
            `!r r'. r < dd /\ r' < dd /\ (U:num->real^3)(c0 + r) = U(c0 + r') ==> r = r'`)) THEN
          REWRITE_TAC[th]) THEN
        MOI_FSP_NUM_ARITH_TAC;
        MP_TAC(SPEC `c0 + r1:num` (ASSUME `!i. ~((U:num->real^3) i = U(SUC i))`)) THEN
        REWRITE_TAC[ASSUME `SUC(c0 + r1) = c0 + r1 + 1`] THEN MESON_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `y:(real^3->bool)->bool`;
       `UNIONS m:real^3->bool`; `v0:real^3`; `y0:real^3`; `(U:num->real^3)(c0 + r1 - 1)`;
       `(U:num->real^3)(c0 + r1)`; `(U:num->real^3)(c0 + r1 + 1)`] MOI_FSP_FAN_NOT_BOTH) THEN
    ASM_REWRITE_TAC[SUBSET_UNION];
    ALL_TAC] THEN
  (* the witnesses from the cycle *)
  MP_TAC(ISPECL [`derived_frontier t (ld:(real^3->bool)->bool)`; `UNIONS (m:(real^3->bool)->bool)`;
                 `B:real^3->bool`; `UNIONS (y:(real^3->bool)->bool)`; `d:real^3->bool`;
                 `U:num->real^3`; `dd:num`; `c0:num`; `r1:num`; `r2:num`] MOI_FSP_WIT_PATH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z0:real^3->bool` (X_CHOOSE_THEN `Z1:real^3->bool`
    (X_CHOOSE_THEN `Z2:real^3->bool` STRIP_ASSUME_TAC))) THEN
  (* the two triangles at the edge with far vertices on M are different *)
  SUBGOAL_THEN `~(convex hull {v0,y0,(U:num->real^3)(c0 + r1)} = convex hull {v0,y0,U(c0 + r2)})`
  ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
      `!i j. convex hull {v0, y0, (U:num->real^3) i} = convex hull {v0, y0, U j} ==> U i = U j`)) THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPECL [`r1:num`; `r2:num`] (ASSUME
        `!r r'. r < dd /\ r' < dd /\ (U:num->real^3)(c0 + r) = U(c0 + r') ==> r = r'`)) THEN
      REWRITE_TAC[th]) THEN
    MOI_FSP_NUM_ARITH_TAC;
    ALL_TAC] THEN
  (* the ends lie in the annulus *)
  SUBGOAL_THEN `j1 UNION j2 SUBSET derived_nbhd t ld INTER UNIONS (m:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`derived_frontier t ld INTER UNIONS m = j1 UNION (j2:real^3->bool)`;
      `derived_frontier t ld SUBSET derived_nbhd t (ld:(real^3->bool)->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the 2D fact at the edge *)
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`; `v0:real^3`; `y0:real^3`;
                 `(U:num->real^3)(c0 + r1)`; `(U:num->real^3)(c0 + r2)`] MOI_FSP_SIDE_2D) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* cycle points off d are in the frontier, so the two points are on the ends *)
  SUBGOAL_THEN `!i. ~((U:num->real^3) i IN d) ==> U i IN derived_frontier t ld` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                   `{(U:num->real^3) i}`] MOI_FSP_NC_FR) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~((U:num->real^3) i IN d)` THEN SET_TAC[];
      REWRITE_TAC[SING_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^3)(c0 + r1) IN j1 UNION j2 /\ (U:num->real^3)(c0 + r2) IN j1 UNION j2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `c0 + r1:num` (ASSUME
      `!i. ~((U:num->real^3) i IN d) ==> U i IN derived_frontier t ld`)) THEN
    MP_TAC(SPEC `c0 + r2:num` (ASSUME
      `!i. ~((U:num->real^3) i IN d) ==> U i IN derived_frontier t ld`)) THEN
    MAP_EVERY UNDISCH_TAC
     [`derived_frontier t ld INTER UNIONS m = j1 UNION (j2:real^3->bool)`;
      `~((U:num->real^3)(c0 + r1) IN d)`; `~((U:num->real^3)(c0 + r2) IN d)`;
      `(U:num->real^3)(c0 + r1) IN UNIONS m`; `(U:num->real^3)(c0 + r2) IN UNIONS m`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Z0:real^3->bool`; `Z1:real^3->bool`; `Z2:real^3->bool`;
                        `(U:num->real^3)(c0 + r1)`; `(U:num->real^3)(c0 + r2)`] THEN
  ASM_REWRITE_TAC[]);;

(* The side lemma: the part of F off M inside y is the interior of the disks. *)

let MOI_FSP_CUT_SIDE = prove
 (`!(m:(real^3->bool)->bool) d j v a b t ld lm j1 j2 d1 d2 y B.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     moi_fsp_box m d v a b t ld lm /\ moi_fsp_ends m j t ld j1 j2 d1 d2 /\
     simplicial_subcomplex y t /\ combinatorial_manifold_with_boundary 3 y /\
     ld SUBSET y /\ complex_boundary y = UNIONS m UNION B /\ closed B /\
     DISJOINT B (derived_nbhd t ld)
     ==> (derived_frontier t ld DIFF UNIONS m) INTER UNIONS y =
         (d1 UNION d2) DIFF (j1 UNION j2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                 `y:(real^3->bool)->bool`; `B:real^3->bool`] MOI_FSP_SIDE_WIT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z0:real^3->bool` (X_CHOOSE_THEN `Z1:real^3->bool`
    (X_CHOOSE_THEN `Z2:real^3->bool` (X_CHOOSE_THEN `m1:real^3` (X_CHOOSE_THEN `m2:real^3`
    STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_ends] o check (fun th ->
    can (term_match [] `moi_fsp_ends m j t ld j1 j2 d1 (d2:real^3->bool)`) (concl th))) THEN
  MP_TAC(ISPECL [`derived_frontier t (ld:(real^3->bool)->bool)`; `d1:real^3->bool`;
                 `j1:real^3->bool`; `d2:real^3->bool`; `j2:real^3->bool`]
    MOI_FSP_SPHERE_TWO_DISKS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (y:(real^3->bool)->bool) /\ FINITE y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
    UNDISCH_TAC `moi_fsp_box m d v a b t ld (lm:(real^3->bool)->bool)` THEN
    REWRITE_TAC[moi_fsp_box] THEN STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (UNIONS y) = UNIONS m UNION (B:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `y:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSP_SIDE_TOP THEN
  MAP_EVERY EXISTS_TAC [`Z0:real^3->bool`; `Z1:real^3->bool`; `Z2:real^3->bool`;
                        `m1:real^3`; `m2:real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`derived_frontier t ld INTER UNIONS m = j1 UNION (j2:real^3->bool)`;
      `(d1:real^3->bool) SUBSET derived_frontier t ld`; `(d1:real^3->bool) INTER j2 = {}`;
      `(j1:real^3->bool) SUBSET d1`] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`derived_frontier t ld INTER UNIONS m = j1 UNION (j2:real^3->bool)`;
      `(d2:real^3->bool) SUBSET derived_frontier t ld`; `(d2:real^3->bool) INTER j1 = {}`;
      `(j2:real^3->bool) SUBSET d2`] THEN SET_TAC[];
    X_GEN_TAC `S:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> q) ==> p \/ q`) THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `UNIONS (y:(real^3->bool)->bool)`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(S:real^3->bool) SUBSET derived_frontier t ld DIFF UNIONS m`;
      `~((S:real^3->bool) SUBSET UNIONS y)`;
      `derived_frontier t ld SUBSET derived_nbhd t (ld:(real^3->bool)->bool)`;
      `DISJOINT B (derived_nbhd t (ld:(real^3->bool)->bool))`] THEN
    REWRITE_TAC[DISJOINT] THEN SET_TAC[]]);;

let MOI_FSP_CUT = prove
 (`!(m:(real^3->bool)->bool) d j v a b t ld lm j1 j2 d1 d2 y B.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     moi_fsp_box m d v a b t ld lm /\ moi_fsp_ends m j t ld j1 j2 d1 d2 /\
     simplicial_subcomplex y t /\ combinatorial_manifold_with_boundary 3 y /\
     ld SUBSET y /\ complex_boundary y = UNIONS m UNION B /\ closed B /\
     DISJOINT B (derived_nbhd t ld)
     ==> FINITE {s | s IN barycentric_subdivision (barycentric_subdivision y) /\
                     s SUBSET closure (UNIONS y DIFF derived_nbhd t ld)} /\
         combinatorial_manifold_with_boundary 3
           {s | s IN barycentric_subdivision (barycentric_subdivision y) /\
                s SUBSET closure (UNIONS y DIFF derived_nbhd t ld)} /\
         UNIONS {s | s IN barycentric_subdivision (barycentric_subdivision y) /\
                     s SUBSET closure (UNIONS y DIFF derived_nbhd t ld)} =
         closure (UNIONS y DIFF derived_nbhd t ld) /\
         complex_boundary
           {s | s IN barycentric_subdivision (barycentric_subdivision y) /\
                s SUBSET closure (UNIONS y DIFF derived_nbhd t ld)} =
         ((UNIONS m UNION B) DIFF derived_nbhd t ld) UNION d1 UNION d2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                 `y:(real^3->bool)->bool`; `B:real^3->bool`] MOI_FSP_CUT_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m d v a b t ld (lm:(real^3->bool)->bool)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_ends] o check (fun th ->
    can (term_match [] `moi_fsp_ends m j t ld j1 j2 d1 (d2:real^3->bool)`) (concl th))) THEN
  SUBGOAL_THEN `lf_simplicial_complex (y:(real^3->bool)->bool) /\ FINITE y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
    ASM_MESON_TAC[FINITE_SUBSET; simplicial_subcomplex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                 `y:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `ld INTER y = (ld:(real^3->bool)->bool)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `simplicial_subcomplex ld (y:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex ld (t:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `ld SUBSET (y:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`y:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`]
                DERIVED_NBHD_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `yT = barycentric_subdivision (barycentric_subdivision (y:(real^3->bool)->bool))` THEN
  ABBREV_TAC `A = derived_nbhd_complex y (ld:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `FINITE (yT:(real^3->bool)->bool) /\ lf_simplicial_complex yT /\
                UNIONS yT = UNIONS y /\ combinatorial_manifold_with_boundary 3 yT /\
                complex_boundary yT = UNIONS m UNION B`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "yT" THEN
    ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; BARYCENTRIC_SUBDIVISION_LF;
                 UNIONS_BARYCENTRIC_SUBDIVISION] THEN
    MP_TAC(ISPEC `y:(real^3->bool)->bool` COMBINATORIAL_WB_BARYCENTRIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `barycentric_subdivision (y:(real^3->bool)->bool)`
                 COMBINATORIAL_WB_BARYCENTRIC) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure (UNIONS y DIFF derived_nbhd t ld) =
                closure (UNIONS yT DIFF UNIONS (A:(real^3->bool)->bool))` SUBST1_TAC THENL
   [AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_subcomplex A (yT:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN EXPAND_TAC "yT" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `interior (derived_nbhd t ld) =
                derived_nbhd t ld DIFF derived_frontier t (ld:(real^3->bool)->bool) /\
                closure (interior (derived_nbhd t ld)) = derived_nbhd t (ld:(real^3->bool)->bool) /\
                frontier (derived_nbhd t ld) = derived_frontier t (ld:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `derived_nbhd_complex t (ld:(real^3->bool)->bool)` MOI_FSP_REG_CLOSED) THEN
    MP_TAC(ISPEC `derived_nbhd_complex t (ld:(real^3->bool)->bool)`
                 COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `derived_nbhd t (ld:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `C = {s | s IN yT /\ s SUBSET
                        closure (UNIONS yT DIFF UNIONS (A:(real^3->bool)->bool))}` THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3 (C:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC MOI_FSP_COMP_CMWB THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN j1 UNION j2` ASSUME_TAC THENL
     [SUBGOAL_THEN `~((w:real^3) IN interior (derived_nbhd t ld))` ASSUME_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `interior (derived_nbhd t ld) INTER
                      closure (UNIONS y DIFF derived_nbhd t ld INTER UNIONS y) =
                      {}:real^3->bool` MP_TAC THENL
         [SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_INTERIOR] THEN
          MP_TAC(ISPEC `derived_nbhd t (ld:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN
          SET_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(w:real^3) IN interior (derived_nbhd t ld)` THEN
        UNDISCH_TAC `(w:real^3) IN closure (UNIONS y DIFF derived_nbhd t ld INTER UNIONS y)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`derived_frontier t ld INTER UNIONS m = j1 UNION (j2:real^3->bool)`;
        `derived_frontier t ld SUBSET derived_nbhd t (ld:(real^3->bool)->bool)`;
        `interior (derived_nbhd t ld) =
         derived_nbhd t ld DIFF derived_frontier t (ld:(real^3->bool)->bool)`;
        `DISJOINT B (derived_nbhd t (ld:(real^3->bool)->bool))`;
        `(w:real^3) IN UNIONS m UNION B`] THEN
      UNDISCH_TAC `(w:real^3) IN derived_frontier t ld INTER UNIONS y UNION
                   (derived_nbhd t ld INTER UNIONS y) INTER (UNIONS m UNION B)` THEN
      UNDISCH_TAC `~((w:real^3) IN interior (derived_nbhd t ld))` THEN SET_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "C" THEN EXPAND_TAC "yT" THEN EXPAND_TAC "A" THEN
    MATCH_MP_TAC MOI_FSP_CUT_CORNER THEN
    MAP_EVERY EXISTS_TAC [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
      `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
      `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
      `d1:real^3->bool`; `d2:real^3->bool`; `B:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (C:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS C = closure (UNIONS yT DIFF UNIONS (A:(real^3->bool)->bool))`
  ASSUME_TAC THENL [EXPAND_TAC "C" THEN ASM_SIMP_TAC[MOI_FSP_COMP_UNIONS2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `C:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `UNIONS y DIFF derived_nbhd t ld INTER UNIONS y =
                UNIONS y DIFF derived_nbhd t (ld:(real^3->bool)->bool)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSP_CUT_FRONTIER THEN
  MAP_EVERY EXISTS_TAC [`derived_frontier t (ld:(real^3->bool)->bool)`;
                        `j1:real^3->bool`; `j2:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `y:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`2`; `d1:real^3->bool`; `j1:real^3->bool`] MOI_FSP_CELL_BASIC) THEN
  MP_TAC(ISPECL [`2`; `d2:real^3->bool`; `j2:real^3->bool`] MOI_FSP_CELL_BASIC) THEN
  ASM_SIMP_TAC[MOI_FSP_CELL_CLOSURE; COMPACT_IMP_CLOSED] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[MOI_FM3_LF_COMPACT]);;

(* ========================================================================= *)
(* The x-clause.  Case d SUBSET X: x' is the cut of X.  Case d              *)
(* meets X only in j: Y is the closed complement of X in the box, Y' its    *)
(* cut, and x' the closed complement of Y' in the box, which is X UNION N.   *)
(* ========================================================================= *)

let MOI_FSP_RESTRICT_SUBCX = prove
 (`!(K:(real^N->bool)->bool) S.
     lf_simplicial_complex K ==> simplicial_subcomplex {s | s IN K /\ s SUBSET S} K`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_subcomplex; IN_ELIM_THM] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_FACE];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]);;

(* Facts shared by both cases.                                               *)

let MOI_FSP_X_CONTEXT = prove
 (`!(m:(real^3->bool)->bool) d j v a b t ld lm x.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     moi_fsp_box m d v a b t ld lm /\
     FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
     frontier (UNIONS x) = UNIONS m
     ==> UNIONS x SUBSET interval(a,b) /\ compact (UNIONS x) /\
         closure (interior (UNIONS x)) = UNIONS x /\
         simplicial_subcomplex {s | s IN t /\ s SUBSET UNIONS x} t /\
         UNIONS {s | s IN t /\ s SUBSET UNIONS x} = UNIONS x /\
         FINITE {s | s IN t /\ s SUBSET UNIONS x} /\
         combinatorial_manifold_with_boundary 3 {s | s IN t /\ s SUBSET UNIONS x} /\
         complex_boundary {s | s IN t /\ s SUBSET UNIONS x} = UNIONS m /\
         closure (interior (derived_nbhd t ld)) = derived_nbhd t ld /\
         interior (derived_nbhd t ld) = derived_nbhd t ld DIFF derived_frontier t ld /\
         d SUBSET interior (derived_nbhd t ld) /\
         (d SUBSET UNIONS x \/ d INTER UNIONS x = j) /\
         ~(d SUBSET UNIONS x /\ d INTER UNIONS x = j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_fsp_box m d v a b t ld (lm:(real^3->bool)->bool)` THEN
  REWRITE_TAC[moi_fsp_box] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (x:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS x:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[MOI_FM3_LF_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS x SUBSET interval(a:real^3,b)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSP_X_IN_BOX THEN EXISTS_TAC `UNIONS m:real^3->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `x:(real^3->bool)->bool`] MOI_FSP_XCX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`a:real^3`; `b:real^3`]
      INTERVAL_OPEN_SUBSET_CLOSED) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` MOI_FSP_REG_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `derived_nbhd_complex t (ld:(real^3->bool)->bool)` MOI_FSP_REG_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `interior (derived_nbhd t ld) =
                derived_nbhd t ld DIFF derived_frontier t (ld:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `derived_nbhd_complex t (ld:(real^3->bool)->bool)`
                 COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MP_TAC(ISPEC `derived_nbhd t (ld:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FSP_X_CASES THEN EXISTS_TAC `UNIONS m:real^3->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
  ASM SET_TAC[]);;

(* Case d SUBSET X.                                                          *)

let MOI_FSP_XCASE_B = prove
 (`!(m:(real^3->bool)->bool) d j v a b t ld lm j1 j2 d1 d2 x.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     moi_fsp_box m d v a b t ld lm /\ moi_fsp_ends m j t ld j1 j2 d1 d2 /\
     FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
     frontier (UNIONS x) = UNIONS m /\ d SUBSET UNIONS x
     ==> ?x':(real^3->bool)->bool.
           FINITE x' /\ combinatorial_manifold_with_boundary 3 x' /\
           frontier (UNIONS x') =
           (UNIONS m DIFF (derived_nbhd t ld INTER UNIONS m)) UNION d1 UNION d2 /\
           (UNIONS x DIFF UNIONS x') UNION (UNIONS x' DIFF UNIONS x) SUBSET v /\
           UNIONS x' SUBSET UNIONS x /\ DISJOINT d (UNIONS x')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `x:(real^3->bool)->bool`] MOI_FSP_X_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `xt = {s | s IN t /\ s SUBSET UNIONS (x:(real^3->bool)->bool)}` THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                 `xt:(real^3->bool)->bool`; `{}:real^3->bool`] MOI_FSP_CUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[UNION_EMPTY; CLOSED_EMPTY; DISJOINT_EMPTY] THEN
    UNDISCH_TAC `moi_fsp_box m d v a b t ld (lm:(real^3->bool)->bool)` THEN
    REWRITE_TAC[moi_fsp_box] THEN STRIP_TAC THEN
    EXPAND_TAC "xt" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
      UNDISCH_TAC `d SUBSET UNIONS (x:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `UNIONS ld = (d:real^3->bool)` THEN
      UNDISCH_TAC `(s:real^3->bool) IN ld` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[UNION_EMPTY] THEN
  ABBREV_TAC `cx = {s | s IN barycentric_subdivision (barycentric_subdivision xt) /\
                        s SUBSET closure (UNIONS x DIFF derived_nbhd t (ld:(real^3->bool)->bool))}` THEN
  STRIP_TAC THEN EXISTS_TAC `cx:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `cx:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closure (UNIONS x DIFF derived_nbhd t ld) SUBSET
                UNIONS (x:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure (UNIONS x DIFF derived_nbhd t ld) SUBSET
                (:real^3) DIFF interior (derived_nbhd t (ld:(real^3->bool)->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN
    SIMP_TAC[GSYM OPEN_CLOSED; OPEN_INTERIOR] THEN
    MP_TAC(ISPEC `derived_nbhd t (ld:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    MP_TAC(ISPEC `UNIONS x DIFF derived_nbhd t (ld:(real^3->bool)->bool)` CLOSURE_SUBSET) THEN
    UNDISCH_TAC `derived_nbhd t ld SUBSET v INTER interval(a:real^3,b)` THEN
    UNDISCH_TAC `closure (UNIONS x DIFF derived_nbhd t ld) SUBSET
                 UNIONS (x:(real^3->bool)->bool)` THEN
    SET_TAC[];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `d SUBSET interior (derived_nbhd t (ld:(real^3->bool)->bool))` THEN
    UNDISCH_TAC `closure (UNIONS x DIFF derived_nbhd t ld) SUBSET
                 (:real^3) DIFF interior (derived_nbhd t (ld:(real^3->bool)->bool))` THEN
    SET_TAC[]]);;

let MOI_FSP_SUBCX_TRANS = prove
 (`!(a:(real^N->bool)->bool) b c.
     simplicial_subcomplex a b /\ simplicial_subcomplex b c ==> simplicial_subcomplex a c`,
  REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[]);;

(* Case d INTER X = j.                                                       *)

let MOI_FSP_XCASE_A = prove
 (`!(m:(real^3->bool)->bool) d j v a b t ld lm j1 j2 d1 d2 x.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     moi_fsp_box m d v a b t ld lm /\ moi_fsp_ends m j t ld j1 j2 d1 d2 /\
     FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
     frontier (UNIONS x) = UNIONS m /\ d INTER UNIONS x = j
     ==> ?x':(real^3->bool)->bool.
           FINITE x' /\ combinatorial_manifold_with_boundary 3 x' /\
           frontier (UNIONS x') =
           (UNIONS m DIFF (derived_nbhd t ld INTER UNIONS m)) UNION d1 UNION d2 /\
           (UNIONS x DIFF UNIONS x') UNION (UNIONS x' DIFF UNIONS x) SUBSET v /\
           UNIONS x SUBSET UNIONS x' /\ d SUBSET interior (UNIONS x')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `x:(real^3->bool)->bool`] MOI_FSP_X_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m d v a b t ld (lm:(real^3->bool)->bool)`) (concl th))) THEN
  ABBREV_TAC `X = UNIONS (x:(real^3->bool)->bool)` THEN
  ABBREV_TAC `N = derived_nbhd t (ld:(real^3->bool)->bool)` THEN
  ABBREV_TAC `xt = {s | s IN t /\ s SUBSET (X:real^3->bool)}` THEN
  ABBREV_TAC `yA = {s | s IN t /\ s SUBSET closure (UNIONS t DIFF UNIONS (xt:(real^3->bool)->bool))}` THEN
  SUBGOAL_THEN `interior (interval[a:real^3,b]) = interval(a,b)` ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL]; ALL_TAC] THEN
  (* the closed complement Y of X in the box *)
  SUBGOAL_THEN
   `simplicial_subcomplex yA (t:(real^3->bool)->bool) /\
    UNIONS yA = closure (interval[a,b] DIFF X) /\ FINITE yA /\
    combinatorial_manifold_with_boundary 3 yA /\
    complex_boundary yA = UNIONS m UNION (interval[a,b] DIFF interval(a:real^3,b)) /\
    closure (interval[a,b] DIFF X) = interval[a,b] DIFF interior X`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `simplicial_subcomplex yA (t:(real^3->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "yA" THEN MATCH_MP_TAC MOI_FSP_COMP_SUBCX THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `UNIONS yA = closure (interval[a,b] DIFF (X:real^3->bool))` ASSUME_TAC THENL
     [EXPAND_TAC "yA" THEN ASM_SIMP_TAC[MOI_FSP_COMP_UNIONS2]; ALL_TAC] THEN
    SUBGOAL_THEN `FINITE (yA:(real^3->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; simplicial_subcomplex]; ALL_TAC] THEN
    MP_TAC(ISPECL [`X:real^3->bool`; `interval[a:real^3,b]`] MOI_FSP_FRONTIER_COMPL_BOX) THEN
    ASM_SIMP_TAC[CLOSED_INTERVAL; COMPACT_IMP_CLOSED] THEN
    DISCH_THEN(fun th -> let th1 = CONJUNCT1 th and th2 = CONJUNCT2 th in
      ASSUME_TAC th1 THEN ASSUME_TAC (REWRITE_RULE[th1] th2)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `combinatorial_manifold_with_boundary 3 (yA:(real^3->bool)->bool)`
    ASSUME_TAC THENL
     [EXPAND_TAC "yA" THEN MATCH_MP_TAC MOI_FSP_COMP_CMWB THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `(w:real^3) IN UNIONS m` THEN
      UNDISCH_TAC `(w:real^3) IN interval[a,b] DIFF interval(a,b)` THEN
      UNDISCH_TAC `d UNION UNIONS m SUBSET interval(a:real^3,b)` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `yA:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  (* ld lies in Y *)
  SUBGOAL_THEN `ld SUBSET (yA:(real^3->bool)->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `d SUBSET closure (interval[a,b] DIFF (X:real^3->bool))` ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP MOI_FSP_CELL_CLOSURE) THEN
      MATCH_MP_TAC SUBSET_CLOSURE THEN
      MP_TAC(ISPECL [`a:real^3`; `b:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
      UNDISCH_TAC `d UNION UNIONS m SUBSET interval(a:real^3,b)` THEN
      UNDISCH_TAC `d INTER X = (j:real^3->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "yA" THEN GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `simplicial_subcomplex ld (t:(real^3->bool)->bool)`) THEN
      REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `closure (UNIONS t DIFF UNIONS xt) =
                    closure (interval[a,b] DIFF (X:real^3->bool))` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `d:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `UNIONS ld = (d:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(s:real^3->bool) IN ld` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the cut of Y and its closed complement *)
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                 `yA:(real^3->bool)->bool`; `interval[a,b] DIFF interval(a:real^3,b)`]
                MOI_FSP_CUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_INTERVAL; OPEN_INTERVAL];
      UNDISCH_TAC `N SUBSET v INTER interval(a:real^3,b)` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Z = closure ((interval[a,b] DIFF interior X) DIFF (N:real^3->bool))` THEN
  ABBREV_TAC `cy = {s | s IN barycentric_subdivision (barycentric_subdivision yA) /\
                        s SUBSET (Z:real^3->bool)}` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `yA:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `T2 = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  SUBGOAL_THEN `FINITE (T2:(real^3->bool)->bool) /\ combinatorial_manifold_with_boundary 3 T2 /\
                complex_boundary T2 = interval[a,b] DIFF interval(a:real^3,b)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "T2" THEN ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE] THEN
    MP_TAC(ISPEC `t:(real^3->bool)->bool` COMBINATORIAL_WB_BARYCENTRIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `barycentric_subdivision (t:(real^3->bool)->bool)`
                 COMBINATORIAL_WB_BARYCENTRIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_subcomplex cy (T2:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSP_SUBCX_TRANS THEN
    EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (yA:(real^3->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "cy" THEN MATCH_MP_TAC MOI_FSP_RESTRICT_SUBCX THEN
    MP_TAC(ISPECL [`yA:(real^3->bool)->bool`; `yA:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
      REWRITE_TAC[simplicial_subcomplex; SUBSET_REFL] THEN
      ASM_MESON_TAC[combinatorial_manifold_with_boundary; MOI_FM3_LF_FACE];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (Z:real^3->bool) /\ closure (interior Z) = Z` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `closure ((interval[a,b] DIFF interior X) DIFF N) =
                               (Z:real^3->bool)`); CLOSED_CLOSURE];
      MP_TAC(ISPEC `cy:(real^3->bool)->bool` MOI_FSP_REG_CLOSED) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[a,b] DIFF interval(a,b) SUBSET (Z:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `closure ((interval[a,b] DIFF interior X) DIFF N) =
                               (Z:real^3->bool)`)] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(interval[a,b] DIFF interior X) DIFF (N:real^3->bool)` THEN
    REWRITE_TAC[CLOSURE_SUBSET] THEN
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `X SUBSET interval(a:real^3,b)` THEN
    UNDISCH_TAC `N SUBSET v INTER interval(a:real^3,b)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure (interval[a,b] DIFF Z) = X UNION (N:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN
      ASM_SIMP_TAC[CLOSED_UNION; COMPACT_IMP_CLOSED] THEN
      REWRITE_TAC[GSYM(ASSUME `closure ((interval[a,b] DIFF interior X) DIFF N) =
                               (Z:real^3->bool)`)] THEN
      MP_TAC(ISPEC `(interval[a,b] DIFF interior X) DIFF (N:real^3->bool)` CLOSURE_SUBSET) THEN
      MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Z:real^3->bool) SUBSET (:real^3) DIFF interior X /\
                  Z SUBSET (:real^3) DIFF interior N` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `closure ((interval[a,b] DIFF interior X) DIFF N) =
                               (Z:real^3->bool)`)] THEN
      CONJ_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
      SIMP_TAC[GSYM OPEN_CLOSED; OPEN_INTERIOR] THEN
      MP_TAC(ISPEC `N:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure (interior X:real^3->bool)` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_CLOSURE THEN
      MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
      MP_TAC(ISPECL [`a:real^3`; `b:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
      UNDISCH_TAC `X SUBSET interval(a:real^3,b)` THEN
      UNDISCH_TAC `(Z:real^3->bool) SUBSET (:real^3) DIFF interior X` THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure (interior N:real^3->bool)` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_CLOSURE THEN
      MP_TAC(ISPEC `N:real^3->bool` INTERIOR_SUBSET) THEN
      MP_TAC(ISPECL [`a:real^3`; `b:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
      UNDISCH_TAC `N SUBSET v INTER interval(a:real^3,b)` THEN
      UNDISCH_TAC `(Z:real^3->bool) SUBSET (:real^3) DIFF interior N` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS T2 = interval[a:real^3,b] /\ lf_simplicial_complex (T2:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `barycentric_subdivision (barycentric_subdivision t) =
                             (T2:(real^3->bool)->bool)`)] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `xx = {s | s IN T2 /\ s SUBSET closure (UNIONS T2 DIFF UNIONS (cy:(real^3->bool)->bool))}` THEN
  SUBGOAL_THEN `UNIONS xx = X UNION (N:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "xx" THEN ASM_SIMP_TAC[MOI_FSP_COMP_UNIONS2]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (xx:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "xx" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3 (xx:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "xx" THEN MATCH_MP_TAC MOI_FSP_COMP_CMWB THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
    UNDISCH_TAC `(w:real^3) IN interval[a,b] DIFF interval(a,b)` THEN
    UNDISCH_TAC `(w:real^3) IN X UNION N` THEN
    UNDISCH_TAC `X SUBSET interval(a:real^3,b)` THEN
    UNDISCH_TAC `N SUBSET v INTER interval(a:real^3,b)` THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `xx:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `frontier (X UNION N) = frontier Z INTER interval(a:real^3,b)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `closure (interval[a,b] DIFF Z) = X UNION (N:real^3->bool)`);
                GSYM(ASSUME `interior (interval[a:real^3,b]) = interval(a,b)`)] THEN
    MATCH_MP_TAC MOI_FSP_FRONTIER_COMP THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `X SUBSET interval(a:real^3,b)` THEN
    UNDISCH_TAC `N SUBSET v INTER interval(a:real^3,b)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `cy:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_fsp_ends m j t ld j1 j2 d1 (d2:real^3->bool)` THEN
  REWRITE_TAC[moi_fsp_ends] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`(d1:real^3->bool) SUBSET derived_frontier t ld`;
      `(d2:real^3->bool) SUBSET derived_frontier t ld`;
      `derived_frontier t ld SUBSET (N:real^3->bool)`;
      `N SUBSET v INTER interval(a:real^3,b)`;
      `d UNION UNIONS m SUBSET interval(a:real^3,b)`] THEN
    SET_TAC[];
    UNDISCH_TAC `N SUBSET v INTER interval(a:real^3,b)` THEN SET_TAC[];
    SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior N:real^3->bool` THEN
    REWRITE_TAC[ASSUME `d SUBSET interior (N:real^3->bool)`] THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]]);;

(* The x-clause.                                                              *)

let MOI_FSP_XCLAUSE = prove
 (`!(m:(real^3->bool)->bool) d j v a b t ld lm j1 j2 d1 d2.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_cell_with_boundary 2 d j /\ d INTER UNIONS m = j /\
     moi_fsp_box m d v a b t ld lm /\ moi_fsp_ends m j t ld j1 j2 d1 d2
     ==> !x:(real^3->bool)->bool.
           FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
           frontier (UNIONS x) = UNIONS m
           ==> ?x':(real^3->bool)->bool.
                 FINITE x' /\ combinatorial_manifold_with_boundary 3 x' /\
                 frontier (UNIONS x') =
                 (UNIONS m DIFF (derived_nbhd t ld INTER UNIONS m)) UNION d1 UNION d2 /\
                 (UNIONS x DIFF UNIONS x') UNION (UNIONS x' DIFF UNIONS x) SUBSET v /\
                 (d SUBSET UNIONS x
                  ==> UNIONS x' SUBSET UNIONS x /\ DISJOINT d (UNIONS x')) /\
                 (d INTER UNIONS x = j
                  ==> UNIONS x SUBSET UNIONS x' /\ d SUBSET interior (UNIONS x'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:(real^3->bool)->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                 `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `x:(real^3->bool)->bool`] MOI_FSP_X_CONTEXT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let ths = CONJUNCTS th in
    ASSUME_TAC (el 11 ths) THEN ASSUME_TAC (el 12 ths)) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                   `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                   `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                   `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                   `x:(real^3->bool)->bool`] MOI_FSP_XCASE_B) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                   `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                   `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                   `j1:real^3->bool`; `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                   `x:(real^3->bool)->bool`] MOI_FSP_XCASE_A) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* The split at a disk, with the three explicit inputs.                       *)

let MOI_FSP_SPLIT_DISK_COND = prove
 (mk_imp(list_mk_conj[inst [`:3`,`:N`] MOI_FND_DERIVED_NBHD_POLYGON_2;
                      MOI_FND_SPLIT_TRACE_ANNULUS;
                      inst [`:3`,`:N`] MOI_S26_SURF_GLUE_BODY],
         MOI_FND_SPLIT_DISK_R3),
  DISCH_THEN(fun th -> ASSUME_TAC th THEN LABEL_TAC "IN3" th) THEN
  MAP_EVERY X_GEN_TAC [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                       `v:real^3->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                 `v:real^3->bool`] MOI_FSP_SETUP_BOX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3`
    (X_CHOOSE_THEN `t:(real^3->bool)->bool` (X_CHOOSE_THEN `ld:(real^3->bool)->bool`
      (X_CHOOSE_THEN `lm:(real^3->bool)->bool` ASSUME_TAC))))) THEN
  USE_THEN "IN3" (fun th ->
    MP_TAC(SPECL [`m:(real^3->bool)->bool`; `d:real^3->bool`; `j:real^3->bool`;
                  `v:real^3->bool`; `a:real^3`; `b:real^3`; `t:(real^3->bool)->bool`;
                  `ld:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`]
                 (MP MOI_FSP_PART_B th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j1:real^3->bool` (X_CHOOSE_THEN `j2:real^3->bool`
    (X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
      (X_CHOOSE_THEN `mm:(real^3->bool)->bool` STRIP_ASSUME_TAC))))) THEN
  MAP_EVERY EXISTS_TAC
   [`derived_nbhd t ld INTER UNIONS (m:(real^3->bool)->bool)`; `j1:real^3->bool`;
    `j2:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`; `mm:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FSP_XCLAUSE THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`; `lm:(real^3->bool)->bool`;
                        `j1:real^3->bool`; `j2:real^3->bool`] THEN
  ASM_REWRITE_TAC[]);;

(* The main theorem, with POLYGON_2 (pc_moi_fnd_nb2f) and SURF_GLUE          *)
(* (pc_moi_s26_surf) at real^3 as explicit hypotheses.                       *)

let SPLIT_SURFACE_DISK_3_COND = prove
 (mk_imp(mk_conj(inst [`:3`,`:N`] MOI_FND_DERIVED_NBHD_POLYGON_2,
                 inst [`:3`,`:N`] MOI_S26_SURF_GLUE),
         mk_imp(list_mk_conj [MOI_FND_DERIVED_NBHD_BALL_2; MOI_FND_SPLIT_TRACE_ANNULUS],
                MOI_FND_SPLIT_DISK_R3)),
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GL")) THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  MATCH_MP_TAC MOI_FSP_SPLIT_DISK_COND THEN ASM_REWRITE_TAC[] THEN
  USE_THEN "GL" MATCH_MP_TAC THEN
  ACCEPT_TAC(INST_TYPE [`:3`,`:N`] MOI_FRB_SURF_INVARIANT));;

(* The main theorem, unconditional: the polygon lemma at real^3 from         *)
(* pc_moi_fnd_nb2f and the gluing lemma at real^3 from pc_moi_s26_surf.      *)

let SPLIT_SURFACE_DISK_3 = prove
 (mk_imp(list_mk_conj [MOI_FND_DERIVED_NBHD_BALL_2; MOI_FND_SPLIT_TRACE_ANNULUS],
         MOI_FND_SPLIT_DISK_R3),
  ACCEPT_TAC(MP SPLIT_SURFACE_DISK_3_COND
    (CONJ (INST_TYPE [`:3`,`:N`] DERIVED_NBHD_POLYGON_2)
          (INST_TYPE [`:3`,`:N`] SURF_GLUE))));;

