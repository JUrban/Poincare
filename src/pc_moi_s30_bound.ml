(* ========================================================================= *)
(* pc_moi_s30_bound: Moise GTM 47, Secs 22.5 and 26.6 as used in Sec 30      *)
(* (pp.194, 216).  Main theorems (statements of pc_moi_s3032_stmt.ml):       *)
(*   EULER_NAT |- MOI_S30_EULER_NAT  (chi of a closed connected surface is  *)
(*     2 - n: an integer at most 2 by SURFACE_SPHERE);                     *)
(*   BOUNDS    |- MOI_S30_BOUNDS     (a closed connected surface in real^3  *)
(*     bounds the compact combinatorial 3-manifold |m| UNION inside |m|:   *)
(*     26.6, a compact combinatorial neighbourhood, the cut along the       *)
(*     refined surface (combinatorial by SURF_INVARIANT), boundary =        *)
(*     frontier (COMPLEX_BOUNDARY_FRONTIER_3), PL invariance of chi).       *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_s28_trib.ml";;
needs "src/pc_moi_fnd_m3a.ml";;

prioritize_real();;
type_invention_error := true;;


(* ------------------------------------------------------------------------- *)
(* EULER_NAT.  complex_euler is a signed sum of cardinalities,               *)
(* hence an integer; SURFACE_SPHERE bounds it by 2.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3BD_EULER_INTEGER = prove
 (`!c:(real^N->bool)->bool. integer(complex_euler c)`,
  GEN_TAC THEN REWRITE_TAC[complex_euler] THEN MATCH_MP_TAC INTEGER_SUM THEN
  X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SIMP_TAC[INTEGER_CLOSED]);;

let EULER_NAT = prove
 (MOI_S30_EULER_NAT,
  DISCH_TAC THEN X_GEN_TAC `c:(real^3->bool)->bool` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(real^3->bool)->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPEC `&2 - complex_euler (c:(real^3->bool)->bool)` INTEGER_POS) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SIMP_TAC[INTEGER_CLOSED; MOI_S3BD_EULER_INTEGER] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN EXISTS_TAC `n:num` THEN ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* The inside of a surface after 26.6, the compact set                      *)
(* |m| UNION inside |m|, the identity PL homeomorphism of a polyhedron, and *)
(* the triangulated surface invariance in the form used here.               *)
(* ------------------------------------------------------------------------- *)

let MOI_S3BD_INSIDE_COMPONENT = prove
 (`!(s:real^3->bool) b.
     components ((:real^3) DIFF s) = {b, outside s} /\ ~(b = outside s)
     ==> inside s = b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(:real^3) DIFF s = b UNION outside s` ASSUME_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [UNIONS_COMPONENTS] THEN ASM_REWRITE_TAC[UNIONS_2];
    ALL_TAC] THEN
  SUBGOAL_THEN `b INTER outside (s:real^3->bool) = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(:real^3) DIFF s`; `b:real^3->bool`; `outside(s:real^3->bool)`]
      COMPONENTS_NONOVERLAP) THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^3->bool` INSIDE_UNION_OUTSIDE) THEN
  MP_TAC(ISPEC `s:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
  ASM SET_TAC[]);;

let MOI_S3BD_K_COMPACT = prove
 (`!s:real^3->bool. compact s ==> compact (s UNION inside s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
   [REWRITE_TAC[BOUNDED_UNION] THEN
    ASM_SIMP_TAC[BOUNDED_INSIDE; COMPACT_IMP_BOUNDED];
    SUBGOAL_THEN `s UNION inside s = (:real^3) DIFF outside s` SUBST1_TAC THENL
     [MP_TAC(ISPEC `s:real^3->bool` INSIDE_UNION_OUTSIDE) THEN
      MP_TAC(ISPEC `s:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
      MP_TAC(ISPEC `s:real^3->bool` OUTSIDE_NO_OVERLAP) THEN SET_TAC[];
      REWRITE_TAC[GSYM OPEN_CLOSED] THEN MATCH_MP_TAC OPEN_OUTSIDE THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]]);;

let MOI_S3BD_PLH_ID = prove
 (`!s:real^N->bool. pl_polyhedron s ==> pl_homeomorphism (s,s) ((\x. x),(\x. x))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]);;

let MOI_S3BD_SURF_INV = MP SURF_INVARIANT
  (CONJ (INST_TYPE [`:M`,`:N`] SURF_CHARTS) SURF_LOCAL);;


(* ------------------------------------------------------------------------- *)
(* BOUNDS.  26.6 gives the bounded complementary component b =              *)
(* inside |m|; K = |m| UNION inside |m| is compact; a compact combinatorial *)
(* 3-manifold neighbourhood w of K contains a refinement s of m, which is   *)
(* a combinatorial surface (SURF_INVARIANT) away from complex_boundary w =  *)
(* |w| DIFF interior |w|; the cut along s gives w1 with |w1| = K, boundary  *)
(* |m| = frontier |w1|; chi by PL invariance through the identity.          *)
(* ------------------------------------------------------------------------- *)

let BOUNDS = prove
 (MOI_S30_BOUNDS,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "266") (CONJUNCTS_THEN2 (LABEL_TAC "nbhd")
    (CONJUNCTS_THEN2 (LABEL_TAC "cut") (LABEL_TAC "eul")))) THEN
  X_GEN_TAC `m:(real^3->bool)->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^3->bool)->bool) /\ simplicial_complex m`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `lf_simplicial_complex (m:(real^3->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
    ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS m:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_FM3_LF_COMPACT];
    ALL_TAC] THEN
  (* 26.6: the inside is the bounded component *)
  USE_THEN "266" (MP_TAC o SPEC `m:(real^3->bool)->bool` o
    REWRITE_RULE[MOISE_266_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `inside (UNIONS m:real^3->bool) = b` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3BD_INSIDE_COMPONENT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THEN
  SUBGOAL_THEN `compact (UNIONS m UNION inside (UNIONS m:real^3->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3BD_K_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(UNIONS m UNION inside (UNIONS m)) UNION outside (UNIONS m) = (:real^3) /\
    (UNIONS m UNION inside (UNIONS m)) INTER outside (UNIONS m:real^3->bool) = {}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `UNIONS m:real^3->bool` INSIDE_UNION_OUTSIDE) THEN
    MP_TAC(ISPEC `UNIONS m:real^3->bool` INSIDE_INTER_OUTSIDE) THEN
    MP_TAC(ISPEC `UNIONS m:real^3->bool` OUTSIDE_NO_OVERLAP) THEN SET_TAC[];
    ALL_TAC] THEN
  (* a compact combinatorial neighbourhood *)
  USE_THEN "nbhd" (MP_TAC o SPECL [`(:real^3)`;
    `UNIONS m UNION inside (UNIONS m:real^3->bool)`; `m:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[OPEN_UNIV; SUBSET_UNIV; SUBSET_UNION]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:(real^3->bool)->bool` (X_CHOOSE_THEN `s:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `lf_simplicial_complex (w:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (s:(real^3->bool)->bool) /\ simplicial_complex s` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE (s:(real^3->bool)->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
      ASM_MESON_TAC[simplicial_subcomplex];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `w:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the refinement s is a combinatorial surface *)
  SUBGOAL_THEN `combinatorial_manifold 2 (s:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `s:(real^3->bool)->bool`;
                   `\x:real^3. x`; `\x:real^3. x`] MOI_S3BD_SURF_INV) THEN
    ASM_REWRITE_TAC[HOMEOMORPHISM_ID] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `combinatorial_manifold 2 (m:(real^3->bool)->bool)` THEN
      REWRITE_TAC[combinatorial_manifold; combinatorial_manifold_with_boundary] THEN
      MESON_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  (* the boundary of w misses K *)
  SUBGOAL_THEN `complex_boundary (w:(real^3->bool)->bool) SUBSET outside (UNIONS m)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `w:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `UNIONS m UNION inside (UNIONS m) SUBSET interior (UNIONS w:real^3->bool)` THEN
    UNDISCH_TAC `(UNIONS m UNION inside (UNIONS m)) UNION outside (UNIONS m) = (:real^3)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the cut along s *)
  USE_THEN "cut" (MP_TAC o SPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `complex_boundary (w:(real^3->bool)->bool) SUBSET outside (UNIONS m)` THEN
    UNDISCH_TAC `(UNIONS m UNION inside (UNIONS m)) INTER outside (UNIONS m:real^3->bool) = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:(real^3->bool)->bool` (X_CHOOSE_THEN `w2:(real^3->bool)->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `w1:(real^3->bool)->bool` THEN
  SUBGOAL_THEN `FINITE (w1:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS w1 = UNIONS m UNION inside (UNIONS m:real^3->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS (w1:(real^3->bool)->bool)`)) THEN
    UNDISCH_TAC `UNIONS m UNION inside (UNIONS m) SUBSET interior (UNIONS w:real^3->bool)` THEN
    MP_TAC(ISPEC `UNIONS w:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(UNIONS m UNION inside (UNIONS m)) UNION outside (UNIONS m) = (:real^3)` THEN
    UNDISCH_TAC `(UNIONS m UNION inside (UNIONS m)) INTER outside (UNIONS m:real^3->bool) = {}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `UNIONS (w1:(real^3->bool)->bool)` &&
    not (rhs(concl th) = `UNIONS m UNION inside (UNIONS m:real^3->bool)`))) THEN
  SUBGOAL_THEN `complex_boundary (w1:(real^3->bool)->bool) = UNIONS m` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `complex_boundary (w1:(real^3->bool)->bool)`)) THEN
    UNDISCH_TAC `complex_boundary (w:(real^3->bool)->bool) SUBSET outside (UNIONS m)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `complex_boundary (w1:(real^3->bool)->bool)` &&
    not (rhs(concl th) = `UNIONS m:real^3->bool`))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* frontier |w1| = |m| *)
    MP_TAC(ISPEC `w1:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o SYM o CONJUNCT2);
    (* chi *)
    MP_TAC(ISPEC `w1:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `FINITE (boundary_complex (w1:(real^3->bool)->bool))` ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `w1:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[boundary_complex] THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "eul" MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`\x:real^3. x`; `\x:real^3. x`] THEN
    ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[combinatorial_manifold];
      X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FSA_CM_DIM THEN
      EXISTS_TAC `boundary_complex (w1:(real^3->bool)->bool)` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FSA_CM_DIM THEN
      EXISTS_TAC `m:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3BD_PLH_ID THEN MATCH_MP_TAC MOI_S4L_PL_POLYHEDRON_UNIONS THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN
      ASM_MESON_TAC[MOI_FM3_LF_POLYTOPE]]]);;

