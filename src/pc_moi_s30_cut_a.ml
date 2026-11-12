(* ========================================================================= *)
(* pc_moi_s30_cut_a: the annulus and the disk chart of Moise 30.3 (GTM 47,  *)
(* p.215).  Main theorems:                                                  *)
(*   ANNULUS_2D   |- MOI_S30_ANNULUS_2D                                     *)
(*   DISK_CHART_2 |- MOI_S30_DISK_CHART_2                                   *)
(* ANNULUS_2D: a PL disk inside the interior of a PL disk in real^3 leaves a *)
(* PL annulus (the planar annulus theorem MOI_S5C_ANN2 of pc_moi_s35_minc,   *)
(* transported along a PL parametrisation of the outer disk).               *)
(* DISK_CHART_2: a PL embedding of the model cube near the inner disk       *)
(* meeting the outer one in the middle square.  The cube goes onto the      *)
(* second-derived neighbourhood N of the inner disk in a triangulation of a *)
(* 3-simplex around the outer disk (a 3-cell by the antecedent BALL_2); its *)
(* trace on the outer disk (MOI_FN2_DERIVED_TRACE of pc_moi_fnd_nb2) is the *)
(* 2D derived neighbourhood, a PL disk by MOI_S3CA_STEP4_THM (frontier a    *)
(* union of PL circles from the degree-2 frontier complex; connected by a   *)
(* retraction onto the complementary full subcomplex and planar             *)
(* unicoherence; then Jordan and PL Schoenflies in the plane), and the      *)
(* chart comes from PL Schoenflies 3 (antecedent) on the two halves.        *)
(* ========================================================================= *)

needs "src/pc_moi_s3032_stmt2.ml";;
needs "src/pc_moi_s28_plane.ml";;
needs "src/pc_moi_s35_minc.ml";;
needs "src/pc_moi_s35_finb1.ml";;
needs "src/pc_moi_fnd_nb2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Planar PL 2-cells.  A 2-simplex of the plane is a compact convex body;    *)
(* a PL 2-cell A of the plane with boundary J has J as its frontier, J is a  *)
(* PL 1-sphere and A = J UNION inside J (the interior of A is a connected   *)
(* component of the plane minus J, and bounded; MOI_S8PL_JORDAN).           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_SIMPLEX2_PLANE = prove
 (`!k:real^2->bool.
     &2 simplex k
     ==> compact k /\ convex k /\ ~(interior k = {}) /\
         relative_frontier k = frontier k /\ interior k = k DIFF frontier k /\
         frontier k SUBSET k`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `compact (k:real^2->bool) /\ convex k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `~(interior(k:real^2->bool) = {})` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM AFF_DIM_NONEMPTY_INTERIOR_EQ; DIMINDEX_2] THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; FRONTIER_SUBSET_CLOSED;
               COMPACT_IMP_CLOSED] THEN
  SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED; ASSUME `compact(k:real^2->bool)`] THEN
  MP_TAC(ISPEC `k:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[]);;

let MOI_S3CA_PLANE_CELL_FILLED = prove
 (`!(A:real^2->bool) J.
     pl_cell_with_boundary 2 A J
     ==> pl_sphere 1 J /\ frontier A = J /\ A = J UNION inside J /\ compact A`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^2`
    (X_CHOOSE_THEN `g:real^2->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(MATCH_MP MOI_S3CA_SIMPLEX2_PLANE (ASSUME `&2 simplex (k:real^2->bool)`)) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `compact (A:real^2->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (f:real^2->real^2) k = A`)) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier A = (J:real^2->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `relative_frontier k = frontier(k:real^2->bool)` THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_FPS_HOMEOMORPHISM_FRONTIER THEN
    EXISTS_TAC `g:real^2->real^2` THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (J:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
    MAP_EVERY EXISTS_TAC [`relative_frontier k:real^2->bool`; `f:real^2->real^2`;
                          `g:real^2->real^2`] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN ASM_REWRITE_TAC[ARITH_RULE `1 + 1 = 2`];
      SUBST1_TAC(ASSUME `J = IMAGE (f:real^2->real^2) (relative_frontier k)`) THEN
      MATCH_MP_TAC MOI_S27_PLH_SIMPLEX_RF THEN
      EXISTS_TAC `A:real^2->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MP_TAC(MATCH_MP MOI_S8PL_JORDAN (ASSUME `pl_sphere 1 (J:real^2->bool)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `interior A = A DIFF (J:real^2->bool) /\ frontier A SUBSET A` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `frontier A = (J:real^2->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED; ASSUME `compact(A:real^2->bool)`] THEN
    MP_TAC(ISPEC `A:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior A = IMAGE (f:real^2->real^2) (interior k)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `relative_frontier k = frontier(k:real^2->bool)` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `!x. x IN k ==> (g:real^2->real^2) (f x) = x` THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^2) k = A` THEN
    UNDISCH_TAC `J = IMAGE (f:real^2->real^2) (relative_frontier k)` THEN
    UNDISCH_TAC `relative_frontier k SUBSET (k:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior(A:real^2->bool) IN components ((:real^2) DIFF J)` MP_TAC THENL
   [MATCH_MP_TAC CLOPEN_IN_COMPONENTS THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `A:real^2->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
      MATCH_MP_TAC OPEN_SUBSET THEN REWRITE_TAC[OPEN_INTERIOR] THEN ASM SET_TAC[];
      SUBST1_TAC(ASSUME `interior A = IMAGE (f:real^2->real^2) (interior k)`) THEN
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTERIOR_SUBSET];
        ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_INTERIOR]];
      SUBST1_TAC(ASSUME `interior A = IMAGE (f:real^2->real^2) (interior k)`) THEN
      REWRITE_TAC[IMAGE_EQ_EMPTY] THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `components ((:real^2) DIFF J) = {inside J, outside(J:real^2->bool)}`;
              IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
   [UNDISCH_TAC `interior A = A DIFF (J:real^2->bool)` THEN
    UNDISCH_TAC `frontier A = (J:real^2->bool)` THEN
    UNDISCH_TAC `frontier A SUBSET (A:real^2->bool)` THEN
    UNDISCH_TAC `interior A = inside(J:real^2->bool)` THEN SET_TAC[];
    UNDISCH_TAC `~bounded(outside(J:real^2->bool))` THEN
    UNDISCH_TAC `interior A = outside(J:real^2->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `A:real^2->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; INTERIOR_SUBSET]]);;
(* ------------------------------------------------------------------------- *)
(* Transport of cells and annuli along a PL homeomorphism E of a planar set  *)
(* X onto a set d of real^N: a PL 2-cell in d pulls back to one in X; a PL   *)
(* annulus in X pushes forward with its ends.                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_CELL_PULL = prove
 (`!(X:real^2->bool) (d:real^N->bool) E E' a ja.
     pl_homeomorphism (X,d) (E,E') /\ pl_cell_with_boundary 2 a ja /\ a SUBSET d
     ==> pl_cell_with_boundary 2 (IMAGE E' a) (IMAGE E' ja) /\
         IMAGE E' a SUBSET X /\ IMAGE E (IMAGE E' a) = a /\ IMAGE E (IMAGE E' ja) = ja`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary] o check (fun th ->
    concl th = `pl_cell_with_boundary 2 (a:real^N->bool) ja`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `F1:real^N->real^N`
    (X_CHOOSE_THEN `G1:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(ja:real^N->bool) SUBSET a` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> concl th =
      `ja = IMAGE (F1:real^N->real^N) (relative_frontier k)`)) THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      concl th = `pl_homeomorphism (k:real^N->bool,a:real^N->bool) (F1:real^N->real^N,G1)`)) THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E':real^N->real^2) a SUBSET X /\ IMAGE E (IMAGE E' a) = a /\
                IMAGE (E:real^2->real^N) (IMAGE E' ja) = ja`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_S27_SIMPLEX_FROM_PLANE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` (X_CHOOSE_THEN `h:real^2->real^N`
    (X_CHOOSE_THEN `h':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_homeomorphism (a,IMAGE (E':real^N->real^2) a) (E',(E:real^2->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`d:real^N->bool`; `X:real^2->bool`] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    SUBGOAL_THEN `a = IMAGE (F1:real^N->real^N) k` SUBST1_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN EXISTS_TAC `k0:real^2->bool` THEN
  EXISTS_TAC `(E':real^N->real^2) o (F1:real^N->real^N) o (h:real^2->real^N)` THEN
  EXISTS_TAC `((h':real^N->real^2) o (G1:real^N->real^N)) o (E:real^2->real^N)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `a:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_o]]);;

let MOI_S3CA_ANNULUS_PUSH = prove
 (`!(X:real^2->bool) (d:real^N->bool) E E' Y j0 j1.
     pl_homeomorphism (X,d) (E,E') /\ pl_annulus_with_ends Y j0 j1 /\ Y SUBSET X
     ==> pl_annulus_with_ends (IMAGE E Y) (IMAGE E j0) (IMAGE E j1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
      STRIP_ASSUME_TAC)) ASSUME_TAC)) THEN
  SUBGOAL_THEN `pl_homeomorphism (Y,IMAGE (E:real^2->real^N) Y) (E,E')` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`X:real^2->bool`; `d:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    SUBGOAL_THEN `Y = IMAGE (f:real^2->real^2) moi_fps_ann` SUBST1_TAC THENL
     [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    REWRITE_TAC[MOI_FPS_ANN_PL_POLYHEDRON] THEN ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(E:real^2->real^N) o (f:real^2->real^2)`;
                        `(g:real^2->real^2) o (E':real^N->real^2)`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `Y:real^2->bool` THEN ASM_REWRITE_TAC[]);;
(* ------------------------------------------------------------------------- *)
(* ANNULUS_2D.  d = E(k0) for a 2-simplex k0 of the plane; a pulls back to a *)
(* planar PL 2-cell A = JA UNION inside JA inside the interior of k0; the    *)
(* planar annulus theorem MOI_S5C_ANN2 (pc_moi_s35_minc) makes k0 minus      *)
(* inside JA an annulus with ends JA and the boundary of k0, and it pushes   *)
(* forward along E.  The ambient Schoenflies antecedent is not needed.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_ANNULUS = prove
 (moi_std_csq MOI_S30_ANNULUS_2D,
  MAP_EVERY X_GEN_TAC [`d:real^3->bool`; `jd:real^3->bool`; `a:real^3->bool`;
                       `ja:real^3->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary] o check (fun th ->
    concl th = `pl_cell_with_boundary 2 (d:real^3->bool) jd`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `F1:real^3->real^3`
    (X_CHOOSE_THEN `G1:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^3->bool` MOI_S27_SIMPLEX_FROM_PLANE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` (X_CHOOSE_THEN `h:real^2->real^3`
    (X_CHOOSE_THEN `h':real^3->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_homeomorphism (k0,d) ((F1:real^3->real^3) o (h:real^2->real^3),
                                         (h':real^3->real^2) o (G1:real^3->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE ((F1:real^3->real^3) o (h:real^2->real^3)) (relative_frontier k0) = jd`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[IMAGE_o]; ALL_TAC] THEN
  ABBREV_TAC `E = (F1:real^3->real^3) o (h:real^2->real^3)` THEN
  ABBREV_TAC `E' = (h':real^3->real^2) o (G1:real^3->real^3)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      concl th = `pl_homeomorphism (k0,d) (E:real^2->real^3,E')`)) THEN
  MP_TAC(ISPECL [`k0:real^2->bool`; `d:real^3->bool`; `E:real^2->real^3`;
                 `E':real^3->real^2`; `a:real^3->bool`; `ja:real^3->bool`]
    MOI_S3CA_CELL_PULL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `A = IMAGE (E':real^3->real^2) a` THEN
  ABBREV_TAC `JA = IMAGE (E':real^3->real^2) ja` THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3CA_PLANE_CELL_FILLED
    (ASSUME `pl_cell_with_boundary 2 (A:real^2->bool) JA`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3CA_SIMPLEX2_PLANE (ASSUME `&2 simplex (k0:real^2->bool)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `inside(relative_frontier k0) = interior(k0:real^2->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INSIDE_FRONTIER_EQ_INTERIOR; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  (* JA lies in the interior of k0 *)
  SUBGOAL_THEN `(JA:real^2->bool) SUBSET inside(relative_frontier k0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(JA:real^2->bool) SUBSET k0 /\ JA INTER frontier k0 = {}` MP_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(A:real^2->bool) SUBSET k0` THEN
        UNDISCH_TAC `IMAGE (E':real^3->real^2) a = A` THEN
        UNDISCH_TAC `A = JA UNION inside(JA:real^2->bool)` THEN SET_TAC[];
        UNDISCH_TAC `relative_frontier k0 = frontier(k0:real^2->bool)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `IMAGE (E:real^2->real^3) (relative_frontier k0) = jd` THEN
        UNDISCH_TAC `IMAGE (E:real^2->real^3) JA = ja` THEN
        UNDISCH_TAC `IMAGE (E':real^3->real^2) ja = JA` THEN
        UNDISCH_TAC `DISJOINT (a:real^3->bool) jd` THEN
        UNDISCH_TAC `IMAGE (E:real^2->real^3) A = a` THEN
        UNDISCH_TAC `IMAGE (E':real^3->real^2) a = A` THEN
        UNDISCH_TAC `A = JA UNION inside(JA:real^2->bool)` THEN
        SET_TAC[]];
      UNDISCH_TAC `interior k0 = k0 DIFF frontier(k0:real^2->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (relative_frontier (k0:real^2->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 + 1 = 2`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`JA:real^2->bool`; `relative_frontier k0:real^2->bool`] MOI_S5C_ANN2) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k0 UNION inside(relative_frontier k0) = (k0:real^2->bool)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `interior k0 = k0 DIFF frontier(k0:real^2->bool)` THEN
    UNDISCH_TAC `frontier k0 SUBSET (k0:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`k0:real^2->bool`; `d:real^3->bool`; `E:real^2->real^3`;
                 `E':real^3->real^2`; `k0 DIFF inside(JA:real^2->bool)`; `JA:real^2->bool`;
                 `relative_frontier k0:real^2->bool`] MOI_S3CA_ANNULUS_PUSH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^2->real^3) (k0 DIFF inside JA) = (d DIFF a) UNION ja`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `inside(JA:real^2->bool) INTER JA = {}` ASSUME_TAC THENL
     [REWRITE_TAC[INSIDE_NO_OVERLAP]; ALL_TAC] THEN
    UNDISCH_TAC `(A:real^2->bool) SUBSET k0` THEN
    UNDISCH_TAC `IMAGE (E:real^2->real^3) A = a` THEN
    UNDISCH_TAC `IMAGE (E:real^2->real^3) JA = ja` THEN
    UNDISCH_TAC `A = JA UNION inside(JA:real^2->bool)` THEN
    UNDISCH_TAC `inside(JA:real^2->bool) INTER JA = {}` THEN
    UNDISCH_TAC `IMAGE (E:real^2->real^3) k0 = d` THEN
    UNDISCH_TAC `!x. x IN k0 ==> (E':real^3->real^2) (E x) = x` THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (E:real^2->real^3) (relative_frontier k0) = jd` THEN
  UNDISCH_TAC `IMAGE (E:real^2->real^3) JA = ja` THEN
  UNDISCH_TAC `IMAGE (E:real^2->real^3) (k0 DIFF inside JA) = (d DIFF a) UNION ja` THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  SUBST1_TAC(SYM(ASSUME `jd = IMAGE (F1:real^3->real^3) (relative_frontier k)`)) THEN
  SIMP_TAC[]);;

let ANNULUS_2D = prove
 (MOI_S30_ANNULUS_2D,
  DISCH_THEN(K ALL_TAC) THEN ACCEPT_TAC MOI_S3CA_ANNULUS);;

(* ------------------------------------------------------------------------- *)
(* The model squares.  moi_s30_inner is the square [-1/2,1/2]^2 x {0}, a PL *)
(* 2-cell inside the middle square moi_s35_mid and missing its boundary.     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_INNER_BOX = prove
 (`moi_s30_inner = interval[vector[-- &1 / &2;-- &1 / &2;&0]:real^3,
                            vector[&1 / &2;&1 / &2;&0]]`,
  REWRITE_TAC[moi_s30_inner; MOI_S5H_BOXES; EXTENSION; IN_ELIM_THM; IN_INTERVAL;
              DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_S3CA_MODEL_SQUARES = prove
 (`pl_cell_with_boundary 2 moi_s35_mid (relative_frontier moi_s35_mid) /\
   pl_cell_with_boundary 2 moi_s30_inner (relative_frontier moi_s30_inner) /\
   moi_s30_inner SUBSET moi_s35_mid /\
   DISJOINT moi_s30_inner (relative_frontier moi_s35_mid)`,
  STRIP_ASSUME_TAC MOI_S5H_MODEL THEN
  SUBGOAL_THEN `polytope moi_s30_inner /\ aff_dim moi_s30_inner = &2` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3CA_INNER_BOX; POLYTOPE_INTERVAL; AFF_DIM_INTERVAL] THEN
    SUBGOAL_THEN `~(interval[vector[-- &1 / &2;-- &1 / &2;&0]:real^3,
                             vector[&1 / &2;&1 / &2;&0]] = {})`
      (fun th -> REWRITE_TAC[th]) THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `vec 0:real^3` THEN
      REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[DIMINDEX_3] THEN
    SUBGOAL_THEN
     `{i | 1 <= i /\ i <= 3 /\
           (vector[-- &1 / &2;-- &1 / &2;&0]:real^3)$i <
           (vector[&1 / &2;&1 / &2;&0]:real^3)$i} = {1,2}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `i:num` THEN
      ASM_CASES_TAC `i = 1` THEN ASM_REWRITE_TAC[VECTOR_3] THEN
      TRY(CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC) THEN
      ASM_CASES_TAC `i = 2` THEN ASM_REWRITE_TAC[VECTOR_3] THEN
      TRY(CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC) THEN
      ASM_CASES_TAC `i = 3` THEN ASM_REWRITE_TAC[VECTOR_3] THEN
      TRY(CONV_TAC REAL_RAT_REDUCE_CONV THEN ARITH_TAC) THEN ASM_ARITH_TAC;
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY;
               ARITH_EQ] THEN
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S4A_POLY_CELL_2] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_s30_inner] THEN SET_TAC[];
    REWRITE_TAC[MOI_S5V_RF_MID; moi_s30_inner; DISJOINT; EXTENSION; IN_INTER;
                IN_ELIM_THM; NOT_IN_EMPTY; moi_s35_n] THEN
    GEN_TAC THEN REAL_ARITH_TAC]);;
(* ------------------------------------------------------------------------- *)
(* The middle map.  For a PL disk a inside a PL disk D missing its rim J:    *)
(* a PL homeomorphism of the middle square onto D carrying the inner square  *)
(* onto a and the rim onto J.  The two annuli (ANNULUS_2D for the model and  *)
(* for (D,a)) give alpha between them; its restriction to the inner rim      *)
(* extends over the inner square (MOI_CEL_CELL_EXTENSION); glue.            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_MIDDLE_MAP = prove
 (`!(D:real^3->bool) J a ja.
     pl_cell_with_boundary 2 D J /\ pl_cell_with_boundary 2 a ja /\
     a SUBSET D /\ DISJOINT a J
     ==> ?s s'. pl_homeomorphism (moi_s35_mid,D) (s,s') /\
                IMAGE s moi_s30_inner = a /\
                IMAGE s (relative_frontier moi_s35_mid) = J`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC MOI_S3CA_MODEL_SQUARES THEN
  MP_TAC(ISPECL [`moi_s35_mid`; `relative_frontier moi_s35_mid`; `moi_s30_inner`;
                 `relative_frontier moi_s30_inner`] MOI_S3CA_ANNULUS) THEN
  MP_TAC(ISPECL [`D:real^3->bool`; `J:real^3->bool`; `a:real^3->bool`;
                 `ja:real^3->bool`] MOI_S3CA_ANNULUS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `A1 = (moi_s35_mid DIFF moi_s30_inner) UNION relative_frontier moi_s30_inner` THEN
  ABBREV_TAC `A2 = ((D:real^3->bool) DIFF a) UNION ja` THEN
  REWRITE_TAC[pl_annulus_with_ends; GSYM moi_fps_ann] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^3` (X_CHOOSE_THEN `g2:real^3->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN (ASSUME_TAC o SYM))))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^3` (X_CHOOSE_THEN `g1:real^3->real^2`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN (ASSUME_TAC o SYM))))) THEN
  (* cells: compactness and boundaries inside *)
  MP_TAC(ISPECL [`2`; `D:real^3->bool`; `J:real^3->bool`] MOI_CEL_CELL_COMPACT) THEN
  MP_TAC(ISPECL [`2`; `a:real^3->bool`; `ja:real^3->bool`] MOI_CEL_CELL_COMPACT) THEN
  MP_TAC(ISPECL [`2`; `moi_s35_mid`; `relative_frontier moi_s35_mid`] MOI_CEL_CELL_COMPACT) THEN
  MP_TAC(ISPECL [`2`; `moi_s30_inner`; `relative_frontier moi_s30_inner`]
    MOI_CEL_CELL_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  (* alpha = f2 o g1 : A1 -> A2 *)
  SUBGOAL_THEN `pl_homeomorphism (A1,A2) ((f2:real^2->real^3) o (g1:real^3->real^2),
                                          (f1:real^2->real^3) o (g2:real^3->real^2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `moi_fps_ann` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `al = (f2:real^2->real^3) o (g1:real^3->real^2)` THEN
  ABBREV_TAC `al' = (f1:real^2->real^3) o (g2:real^3->real^2)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      concl th = `pl_homeomorphism (A1:real^3->bool,A2) (al:real^3->real^3,al')`)) THEN
  SUBGOAL_THEN
   `IMAGE (al:real^3->real^3) (relative_frontier moi_s30_inner) = ja /\
    IMAGE (al:real^3->real^3) (relative_frontier moi_s35_mid) = J`
  STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `(f2:real^2->real^3) o (g1:real^3->real^2) = al`)) THEN REWRITE_TAC[IMAGE_o] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
      GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
        concl th = `pl_homeomorphism (moi_fps_ann,A1:real^3->bool)
                                     (f1:real^2->real^3,g1)`)) THEN
    SUBGOAL_THEN
     `IMAGE (g1:real^3->real^2) (relative_frontier moi_s30_inner) =
      relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) /\
      IMAGE (g1:real^3->real^2) (relative_frontier moi_s35_mid) =
      relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]])`
    (fun th -> REWRITE_TAC[th]) THENL
     [MP_TAC(MATCH_MP MOI_S8PL_RF_FACTS (REAL_ARITH `&0 < &1`)) THEN
      MP_TAC(MATCH_MP MOI_S8PL_RF_FACTS (REAL_ARITH `&0 < &2`)) THEN
      SUBGOAL_THEN
       `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]]) SUBSET
        moi_fps_ann /\
        relative_frontier(interval[--vector[&2;&2]:real^2,vector[&2;&2]]) SUBSET
        moi_fps_ann` MP_TAC THENL
       [REWRITE_TAC[MOI_S8PL_RF12; SUBSET; IN_ELIM_THM; MOI_FPS_ANN] THEN
        CONJ_TAC THEN GEN_TAC THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (f1:real^2->real^3)
                         (relative_frontier(interval[--vector[&1;&1],vector[&1;&1]])) =
                   relative_frontier moi_s30_inner` THEN
      UNDISCH_TAC `IMAGE (f1:real^2->real^3)
                         (relative_frontier(interval[--vector[&2;&2],vector[&2;&2]])) =
                   relative_frontier moi_s35_mid` THEN
      UNDISCH_TAC `!x. x IN moi_fps_ann ==> (g1:real^3->real^2) (f1 x) = x` THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the inner rim map extends over the inner square *)
  SUBGOAL_THEN `relative_frontier moi_s30_inner SUBSET (A1:real^3->bool)` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `(moi_s35_mid DIFF moi_s30_inner) UNION relative_frontier moi_s30_inner = A1`)) THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier moi_s30_inner,ja) (al:real^3->real^3,al')`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (al:real^3->real^3) (relative_frontier moi_s30_inner) = ja` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOI_S27_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`A1:real^3->bool`; `A2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    ASM_MESON_TAC[MOI_S5H_CELL_POLY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`2`; `moi_s30_inner`; `relative_frontier moi_s30_inner`;
                 `a:real^3->bool`; `ja:real^3->bool`; `al:real^3->real^3`;
                 `al':real^3->real^3`] MOI_CEL_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `th:real^3->real^3` (X_CHOOSE_THEN `th':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  (* glue *)
  MP_TAC(ISPECL [`moi_s30_inner`; `A1:real^3->bool`; `a:real^3->bool`; `A2:real^3->bool`;
                 `th:real^3->real^3`; `th':real^3->real^3`; `al:real^3->real^3`;
                 `al':real^3->real^3`] MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  SUBGOAL_THEN `moi_s30_inner INTER A1 = relative_frontier moi_s30_inner /\
                (a:real^3->bool) INTER A2 = ja /\
                moi_s30_inner UNION A1 = moi_s35_mid /\ a UNION A2 = D`
  STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `(moi_s35_mid DIFF moi_s30_inner) UNION relative_frontier moi_s30_inner = A1`)) THEN SUBST1_TAC(SYM(ASSUME `((D:real^3->bool) DIFF a) UNION ja = A2`)) THEN
    UNDISCH_TAC `relative_frontier moi_s30_inner SUBSET moi_s30_inner` THEN
    UNDISCH_TAC `moi_s30_inner SUBSET moi_s35_mid` THEN
    UNDISCH_TAC `(ja:real^3->bool) SUBSET a` THEN
    UNDISCH_TAC `(a:real^3->bool) SUBSET D` THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      SUBGOAL_THEN `compact (A1:real^3->bool)` (fun th -> SIMP_TAC[th; COMPACT_IMP_CLOSED]) THEN
      ASM_MESON_TAC[COMPACT_CONTINUOUS_IMAGE; MOI_S8PL_ANN_CLOSED; pl_homeomorphism;
                    homeomorphism];
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      SUBGOAL_THEN `compact (A2:real^3->bool)` (fun th -> SIMP_TAC[th; COMPACT_IMP_CLOSED]) THEN
      ASM_MESON_TAC[COMPACT_CONTINUOUS_IMAGE; MOI_S8PL_ANN_CLOSED; pl_homeomorphism;
                    homeomorphism];
      FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
        GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
          concl th = `pl_homeomorphism (moi_s30_inner,a:real^3->bool)
                                       (th:real^3->real^3,th')`)) THEN
      UNDISCH_TAC `IMAGE (al:real^3->real^3) (relative_frontier moi_s30_inner) = ja` THEN
      UNDISCH_TAC `!x. x IN relative_frontier moi_s30_inner
                       ==> (th:real^3->real^3) x = al x` THEN
      REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^3. if x IN moi_s30_inner then (th:real^3->real^3) x else al x`;
    `\y:real^3. if y IN a then (th':real^3->real^3) y else al' y`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
      GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
        concl th = `pl_homeomorphism (moi_s30_inner,a:real^3->bool)
                                     (th:real^3->real^3,th')`)) THEN
    UNDISCH_TAC `IMAGE (th:real^3->real^3) moi_s30_inner = a` THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    UNDISCH_TAC `IMAGE (al:real^3->real^3) (relative_frontier moi_s35_mid) = J` THEN
    UNDISCH_TAC `DISJOINT moi_s30_inner (relative_frontier moi_s35_mid)` THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The chart from a splitting disk.  MOI_S3CA_BASE_MAP is MOI_S5H_BASE of    *)
(* pc_moi_s35_charts with the middle map th given (there: a map sending the  *)
(* centre to a point; same proof): the extensions over the two halves        *)
(* (MOI_S5H_EXTN) glued along the middle square.                             *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_BASE_MAP = prove
 (`!(du:real^N->bool) bdu dv bdv jp (th:real^3->real^N) th'.
     pl_cell_with_boundary 3 du bdu /\ pl_cell_with_boundary 3 dv bdv /\
     pl_cell_with_boundary 2 (du INTER dv) jp /\
     du INTER dv SUBSET bdu /\ du INTER dv SUBSET bdv /\
     pl_homeomorphism (moi_s35_mid,du INTER dv) (th,th') /\
     IMAGE th (relative_frontier moi_s35_mid) = jp
     ==> ?psi q. pl_homeomorphism (moi_s35_cube,du UNION dv) (psi,q) /\
                 IMAGE psi moi_s35_lower = du /\ IMAGE psi moi_s35_upper = dv /\
                 IMAGE psi moi_s35_mid = du INTER dv /\
                 IMAGE psi (relative_frontier moi_s35_lower) = bdu /\
                 IMAGE psi (relative_frontier moi_s35_upper) = bdv /\
                 IMAGE psi (relative_frontier moi_s35_mid) = jp /\
                 (!x. x IN moi_s35_mid ==> psi x = th x)`,
  REPEAT STRIP_TAC THEN STRIP_ASSUME_TAC MOI_S5H_MODEL THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary 3 moi_s35_lower (relative_frontier moi_s35_lower) /\
    pl_cell_with_boundary 3 moi_s35_upper (relative_frontier moi_s35_upper) /\
    pl_cell_with_boundary 2 moi_s35_mid (relative_frontier moi_s35_mid)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_S4A_POLY_CELL_3; MOI_S4A_POLY_CELL_2]; ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier moi_s35_lower SUBSET moi_s35_lower /\
    relative_frontier moi_s35_upper SUBSET moi_s35_upper /\
    relative_frontier moi_s35_mid SUBSET moi_s35_mid /\
    moi_s35_mid SUBSET moi_s35_lower /\ moi_s35_mid SUBSET moi_s35_upper /\
    (vec 0:real^3) IN moi_s35_mid`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_FRONTIER_SUBSET; POLYTOPE_IMP_CLOSED] THEN
    MP_TAC MOI_S5H_MID_RELINT THEN
    MP_TAC(ISPEC `moi_s35_mid` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `moi_s35_lower INTER moi_s35_upper = moi_s35_mid` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s35_lower`; `relative_frontier moi_s35_lower`; `moi_s35_mid`;
                 `relative_frontier moi_s35_mid`; `du:real^N->bool`; `bdu:real^N->bool`;
                 `du INTER dv:real^N->bool`; `jp:real^N->bool`; `th:real^3->real^N`;
                 `th':real^N->real^3`] MOI_S5H_EXTN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fu:real^3->real^N` (X_CHOOSE_THEN `gu:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`moi_s35_upper`; `relative_frontier moi_s35_upper`; `moi_s35_mid`;
                 `relative_frontier moi_s35_mid`; `dv:real^N->bool`; `bdv:real^N->bool`;
                 `du INTER dv:real^N->bool`; `jp:real^N->bool`; `th:real^3->real^N`;
                 `th':real^N->real^3`] MOI_S5H_EXTN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fv:real^3->real^N` (X_CHOOSE_THEN `gv:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (fu:real^3->real^N) moi_s35_lower = du /\
                IMAGE (fv:real^3->real^N) moi_s35_upper = dv /\
                IMAGE (th:real^3->real^N) moi_s35_mid = du INTER dv`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`pl_homeomorphism (moi_s35_lower,du:real^N->bool)
         ((fu:real^3->real^N),(gu:real^N->real^3))`;
      `pl_homeomorphism (moi_s35_upper,dv:real^N->bool)
         ((fv:real^3->real^N),(gv:real^N->real^3))`;
      `pl_homeomorphism (moi_s35_mid,du INTER dv:real^N->bool)
         ((th:real^3->real^N),(th':real^N->real^3))`] THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s35_lower`; `moi_s35_upper`; `du:real^N->bool`; `dv:real^N->bool`;
                 `fu:real^3->real^N`; `gu:real^N->real^3`; `fv:real^3->real^N`;
                 `gv:real^N->real^3`] MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `compact(du:real^N->bool) /\ compact(dv:real^N->bool)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[MOI_CEL_CELL_COMPACT]; ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    SUBGOAL_THEN `IMAGE (fu:real^3->real^N) moi_s35_mid = IMAGE th moi_s35_mid`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!z:real^3. z IN s ==> (f:real^3->real^N) z = g z) ==> IMAGE f s = IMAGE g s`) THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `psi = \x:real^3. if x IN moi_s35_lower then (fu:real^3->real^N) x
                               else fv x` THEN
  ABBREV_TAC `q = \y:real^N. if y IN du then (gu:real^N->real^3) y else gv y` THEN
  DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`psi:real^3->real^N`; `q:real^N->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(!x. x IN moi_s35_lower ==> (psi:real^3->real^N) x = fu x) /\
    (!x. x IN moi_s35_upper ==> (psi:real^3->real^N) x = fv x) /\
    (!x. x IN moi_s35_mid ==> (psi:real^3->real^N) x = th x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THENL
     [ASM_REWRITE_TAC[];
      COND_CASES_TAC THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^3) IN moi_s35_mid` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[]];
      SUBGOAL_THEN `(x:real^3) IN moi_s35_lower` ASSUME_TAC THENL
       [ASM SET_TAC[]; ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s f. s SUBSET moi_s35_cube /\ (!x. x IN s ==> (psi:real^3->real^N) x = f x)
          ==> IMAGE psi s = IMAGE f s`
  ASSUME_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s35_lower SUBSET moi_s35_cube /\ moi_s35_upper SUBSET moi_s35_cube`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s35_lower UNION moi_s35_upper = moi_s35_cube` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `IMAGE (psi:real^3->real^N) moi_s35_lower = IMAGE fu moi_s35_lower`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                        ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `IMAGE (psi:real^3->real^N) moi_s35_upper = IMAGE fv moi_s35_upper`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                        ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `IMAGE (psi:real^3->real^N) moi_s35_mid = IMAGE th moi_s35_mid`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
                        ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `IMAGE (psi:real^3->real^N) (relative_frontier moi_s35_lower) =
                  IMAGE fu (relative_frontier moi_s35_lower)`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
                        ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `IMAGE (psi:real^3->real^N) (relative_frontier moi_s35_upper) =
                  IMAGE fv (relative_frontier moi_s35_upper)`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
                        ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `IMAGE (psi:real^3->real^N) (relative_frontier moi_s35_mid) =
                  IMAGE th (relative_frontier moi_s35_mid)`
      SUBST1_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
                        ASM_REWRITE_TAC[]];
    ASM_SIMP_TAC[]]);;
(* A PL 3-cell N with boundary F is a PL 3-ball with frontier F.            *)

let MOI_S3CA_CELL3_BALL = prove
 (`!(N:real^3->bool) bN.
     pl_cell_with_boundary 3 N bN ==> pl_ball 3 N /\ frontier N = bN`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN
    EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[]]);;

let MOI_S3CA_BALL_CELL3 = prove
 (`!N:real^3->bool. pl_ball 3 N ==> pl_cell_with_boundary 3 N (frontier N)`,
  GEN_TAC THEN REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN
  EXISTS_TAC `g:real^3->real^3` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The chart core: a PL 3-cell N split by a proper PL 2-cell D (D INTER F =  *)
(* its rim J), and a PL 2-cell a inside D missing J: a PL homeomorphism of   *)
(* the model cube onto N, the middle square onto D, the inner square onto a  *)
(* (MOI_S5N_SPLIT_BALL, MOI_S3CA_MIDDLE_MAP, MOI_S3CA_BASE_MAP).            *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_CHART_CORE = prove
 (`PL_SCHOENFLIES_3_STATEMENT
   ==> !(N:real^3->bool) bN D J a ja.
         pl_cell_with_boundary 3 N bN /\ pl_cell_with_boundary 2 D J /\
         D SUBSET N /\ D INTER bN = J /\
         pl_cell_with_boundary 2 a ja /\ a SUBSET D /\ DISJOINT a J
         ==> ?psi phi. pl_homeomorphism (moi_s35_cube,N) (psi,phi) /\
                       IMAGE psi moi_s35_mid = D /\ IMAGE psi moi_s30_inner = a`,
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3CA_CELL3_BALL
    (ASSUME `pl_cell_with_boundary 3 (N:real^3->bool) bN`)) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`N:real^3->bool`; `D:real^3->bool`; `J:real^3->bool`]
    MOI_S5N_SPLIT_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^3->bool` (X_CHOOSE_THEN `x2:real^3->bool`
    (X_CHOOSE_THEN `s1:real^3->bool` (X_CHOOSE_THEN `s2:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`D:real^3->bool`; `J:real^3->bool`; `a:real^3->bool`; `ja:real^3->bool`]
    MOI_S3CA_MIDDLE_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `th:real^3->real^3` (X_CHOOSE_THEN `th':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`x1:real^3->bool`; `frontier x1:real^3->bool`; `x2:real^3->bool`;
                 `frontier x2:real^3->bool`; `J:real^3->bool`; `th:real^3->real^3`;
                 `th':real^3->real^3`] MOI_S3CA_BASE_MAP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_S3CA_BALL_CELL3] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^3` (X_CHOOSE_THEN `phi:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`psi:real^3->real^3`; `phi:real^3->real^3`] THEN
  UNDISCH_TAC `x1 UNION x2 = (N:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->real^3) moi_s30_inner = IMAGE th moi_s30_inner`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x:real^3. x IN s ==> (f:real^3->real^3) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
    STRIP_ASSUME_TAC MOI_S3CA_MODEL_SQUARES THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Setup: a triangulation of a box around d with d and a as subcomplexes,    *)
(* subdivided until the derived neighbourhood of a lies in v.  The lemmas    *)
(* MOI_S3CA_SP_... are copies of MOI_FSP_SUBPOLY, _TRIANGULATE3,             *)
(* _CELL_POLYHEDRON, _BOX, _BOX_FACTS, _ITER_FINITE of pc_moi_fnd_split      *)
(* (which is not loaded here); the setup follows its MOI_FSP_SETUP with the  *)
(* disk a in place of the surface.                                           *)
(* ------------------------------------------------------------------------- *)

(* Duplicate of MOI_FSP_SUBPOLY (pc_moi_fnd_split). *)
let MOI_S3CA_SP_SUBPOLY = prove
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

(* Duplicate of MOI_FSP_TRIANGULATE3 (pc_moi_fnd_split). *)
let MOI_S3CA_SP_TRIANGULATE3 = prove
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
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3CA_SP_SUBPOLY THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN USE_THEN "ref" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[IN_UNION] THEN REWRITE_TAC[UNIONS_UNION] THEN ASM SET_TAC[]);;

(* PL cells are compact polyhedra.                                           *)

(* Duplicate of MOI_FSP_CELL_POLYHEDRON (pc_moi_fnd_split).              *)
let MOI_S3CA_SP_CELL_POLYHEDRON = prove
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

(* Duplicate of MOI_FSP_BOX (pc_moi_fnd_split). *)
let MOI_S3CA_SP_BOX = prove
 (`!X:real^3->bool.
     bounded X /\ ~(X = {})
     ==> ?a b. (!i. 1 <= i /\ i <= 3 ==> a$i < b$i) /\ X SUBSET interval(a,b)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_TAC `b:real^3`) o
    MATCH_MP BOUNDED_SUBSET_OPEN_INTERVAL) THEN
  MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM DIMINDEX_3; GSYM(CONJUNCT2 INTERVAL_NE_EMPTY)] THEN ASM SET_TAC[]);;

(* Duplicate of MOI_FSP_BOX_FACTS (pc_moi_fnd_split). *)
let MOI_S3CA_SP_BOX_FACTS = prove
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

(* Duplicate of MOI_FSP_ITER_FINITE (pc_moi_fnd_split). *)
let MOI_S3CA_SP_ITER_FINITE = prove
 (`!(t:(real^N->bool)->bool) n.
     FINITE t ==> FINITE (ITER n barycentric_subdivision t)`,
  GEN_TAC THEN INDUCT_TAC THEN ASM_SIMP_TAC[ITER; MOI_BAR_SUBDIVISION_FINITE]);;

(* S1: a triangulated box t with d and M as subcomplexes, the vertices of d *)
(* interior, the surface subcomplex combinatorial, N(d) inside v and the box. *)


let MOI_S3CA_ITER_MONO = prove
 (`!(k:(real^N->bool)->bool) c n.
     k SUBSET c ==> ITER n barycentric_subdivision k SUBSET ITER n barycentric_subdivision c`,
  GEN_TAC THEN GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  ASM_MESON_TAC[MOI_FDN_BAR_SUBDIVISION_MONO]);;

let MOI_S3CA_FULL_SUBCOMPLEX = prove
 (`!(t:(real^N->bool)->bool) l.
     simplicial_complex t /\ simplicial_subcomplex l t
     ==> simplicial_subcomplex {s | s IN t /\ s SUBSET UNIONS l} t /\
         UNIONS {s | s IN t /\ s SUBSET UNIONS l} = UNIONS l /\
         l SUBSET {s | s IN t /\ s SUBSET UNIONS l}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_S3CA_SETUP = prove
 (`!(d:real^3->bool) jd a ja v.
     pl_cell_with_boundary 2 d jd /\ pl_cell_with_boundary 2 a ja /\ a SUBSET d /\
     open v /\ a SUBSET v
     ==> ?t ld la.
           FINITE t /\ simplicial_complex t /\ lf_simplicial_complex t /\
           simplicial_subcomplex ld t /\ UNIONS ld = d /\
           simplicial_subcomplex la t /\ UNIONS la = a /\ la SUBSET ld /\
           (!w. {w} IN la ==> pl_sphere 2 (UNIONS (simplicial_link t w))) /\
           derived_nbhd t la SUBSET v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (d:real^3->bool) /\ compact d /\
                pl_polyhedron (a:real^3->bool) /\ compact a`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3CA_SP_CELL_POLYHEDRON]; ALL_TAC] THEN
  SUBGOAL_THEN `~(d:real^3->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^3->bool) jd` THEN
    REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `IMAGE (f:real^3->real^3) k = d` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM_MESON_TAC[SIMPLEX_EMPTY; INT_ARITH `~(&2:int = -- &1)`];
    ALL_TAC] THEN
  MP_TAC(ISPEC `d:real^3->bool` MOI_S3CA_SP_BOX) THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^3` (X_CHOOSE_THEN `q0:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`p0:real^3`; `q0:real^3`] MOI_S3CA_SP_BOX_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`interval[p0:real^3,q0]`; `d:real^3->bool`; `a:real^3->bool`]
                MOI_S3CA_SP_TRIANGULATE3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:(real^3->bool)->bool` (X_CHOOSE_THEN `ld1:(real^3->bool)->bool`
    (X_CHOOSE_THEN `la1:(real^3->bool)->bool` STRIP_ASSUME_TAC))) THEN
  (* full subcomplexes, so that la0 SUBSET ld0 *)
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `ld1:(real^3->bool)->bool`]
    MOI_S3CA_FULL_SUBCOMPLEX) THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `la1:(real^3->bool)->bool`]
    MOI_S3CA_FULL_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `ld0 = {s | s IN t0 /\ s SUBSET (d:real^3->bool)}` THEN
  ABBREV_TAC `la0 = {s | s IN t0 /\ s SUBSET (a:real^3->bool)}` THEN
  SUBGOAL_THEN `(la0:(real^3->bool)->bool) SUBSET ld0` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["la0"; "ld0"] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (t0:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FMB_SC_LF THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `la0:(real^3->bool)->bool`;
                 `interval[p0:real^3,q0] INTER (v INTER interval(p0,q0))`]
                DERIVED_NBHD_SMALL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERVAL];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MAP_EVERY EXISTS_TAC
   [`ITER n barycentric_subdivision (t0:(real^3->bool)->bool)`;
    `ITER n barycentric_subdivision (ld0:(real^3->bool)->bool)`;
    `ITER n barycentric_subdivision (la0:(real^3->bool)->bool)`] THEN
  SUBGOAL_THEN `ITER n barycentric_subdivision (la0:(real^3->bool)->bool) SUBSET
                ITER n barycentric_subdivision ld0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3CA_ITER_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `t = ITER n barycentric_subdivision (t0:(real^3->bool)->bool)` THEN
  ABBREV_TAC `ld = ITER n barycentric_subdivision (ld0:(real^3->bool)->bool)` THEN
  ABBREV_TAC `la = ITER n barycentric_subdivision (la0:(real^3->bool)->bool)` THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `ld0:(real^3->bool)->bool`; `n:num`]
                MOI_FDN_ITER_SUBCOMPLEX) THEN
  MP_TAC(ISPECL [`t0:(real^3->bool)->bool`; `la0:(real^3->bool)->bool`; `n:num`]
                MOI_FDN_ITER_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC MOI_S3CA_SP_ITER_FINITE THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `interval[p0:real^3,q0] DIFF interval(p0,q0)`]
                PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `t:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN
    SUBGOAL_THEN `{w:real^3} IN t /\ (w:real^3) IN a` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
        UNDISCH_TAC `UNIONS la = (a:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^3}` THEN ASM_REWRITE_TAC[IN_SING]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    MATCH_MP_TAC(TAUT `p ==> (p <=> q) ==> q`) THEN
    REWRITE_TAC[IN_DIFF] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* DISK_CHART_2 from the setup, BALL_2 (antecedent), the trace identity of   *)
(* derived neighbourhoods (MOI_S3CA_TRACE: the statement of                  *)
(* MOI_FN2_DERIVED_TRACE in pc_moi_fnd_nb2, discharged at the end of the     *)
(* file) and MOI_S3CA_STEP4 (the 2D derived neighbourhood of a disk is a     *)
(* disk).                                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_TRACE =
 `!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (m:(real^N->bool)->bool).
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ simplicial_subcomplex m t
     ==> UNIONS (l INTER m) = UNIONS l INTER UNIONS m /\
         derived_nbhd t l INTER UNIONS m = derived_nbhd m (l INTER m) /\
         derived_frontier t l INTER UNIONS m = derived_frontier m (l INTER m)`;;

let MOI_S3CA_STEP4 =
 `!(m:(real^N->bool)->bool) l d jd.
     FINITE m /\ simplicial_complex m /\ UNIONS m = d /\ pl_cell_with_boundary 2 d jd /\
     simplicial_subcomplex l m /\ pl_ball 2 (UNIONS l) /\ DISJOINT (UNIONS l) jd
     ==> pl_cell_with_boundary 2 (derived_nbhd m l) (derived_frontier m l) /\
         UNIONS l SUBSET derived_nbhd m l DIFF derived_frontier m l`;;

let MOI_S3CA_CELL_BALL = prove
 (`!n (s:real^N->bool) b. pl_cell_with_boundary n s b ==> pl_ball n s`,
  REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[]);;

let MOI_S3CA_DISK_CHART_COND = prove
 (mk_imp(list_mk_conj [moi_n3 MOI_S3CA_TRACE; moi_n3 MOI_S3CA_STEP4],
         MOI_S30_DISK_CHART_2),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "trace") (LABEL_TAC "step4")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ball2") (K ALL_TAC))) THEN
  MAP_EVERY X_GEN_TAC [`d:real^3->bool`; `jd:real^3->bool`; `a:real^3->bool`;
                       `ja:real^3->bool`; `v:real^3->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`d:real^3->bool`; `jd:real^3->bool`; `a:real^3->bool`; `ja:real^3->bool`;
                 `v:real^3->bool`] MOI_S3CA_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` (X_CHOOSE_THEN `ld:(real^3->bool)->bool`
    (X_CHOOSE_THEN `la:(real^3->bool)->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `pl_ball 2 (a:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3CA_CELL_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (la:(real^3->bool)->bool) /\ FINITE (ld:(real^3->bool)->bool) /\
                simplicial_complex ld /\ simplicial_subcomplex la ld`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; simplicial_subcomplex];
      ASM_MESON_TAC[FINITE_SUBSET; simplicial_subcomplex];
      MATCH_MP_TAC MOI_SCF_LF_SC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[FINITE_SUBSET; simplicial_subcomplex];
        MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
        ASM_REWRITE_TAC[]];
      UNDISCH_TAC `simplicial_subcomplex (la:(real^3->bool)->bool) t` THEN
      UNDISCH_TAC `(la:(real^3->bool)->bool) SUBSET ld` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[]];
    ALL_TAC] THEN
  (* N = the derived neighbourhood of a: a PL 3-cell *)
  USE_THEN "ball2" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[LE_REFL];
    DISCH_TAC] THEN
  (* its trace on d *)
  USE_THEN "trace" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                                    `ld:(real^3->bool)->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(la:(real^3->bool)->bool) INTER ld = la` SUBST1_TAC THENL
   [UNDISCH_TAC `(la:(real^3->bool)->bool) SUBSET ld` THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the trace is a disk *)
  USE_THEN "step4" (MP_TAC o SPECL [`ld:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                                    `d:real^3->bool`; `jd:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* the chart *)
  MP_TAC(MATCH_MP MOI_S3CA_CHART_CORE (ASSUME `PL_SCHOENFLIES_3_STATEMENT`)) THEN
  DISCH_THEN(MP_TAC o SPECL
    [`derived_nbhd t (la:(real^3->bool)->bool)`; `derived_frontier t (la:(real^3->bool)->bool)`;
     `derived_nbhd ld (la:(real^3->bool)->bool)`; `derived_frontier ld (la:(real^3->bool)->bool)`;
     `a:real^3->bool`; `ja:real^3->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`3`; `derived_nbhd t (la:(real^3->bool)->bool)`;
                   `derived_frontier t (la:(real^3->bool)->bool)`] MOI_CEL_CELL_COMPACT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `derived_nbhd t la INTER d = derived_nbhd ld (la:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `derived_frontier t la INTER d = derived_frontier ld (la:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `UNIONS la SUBSET derived_nbhd ld la DIFF derived_frontier ld (la:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `UNIONS la = (a:real^3->bool)` THEN
    UNDISCH_TAC `derived_frontier t la SUBSET derived_nbhd t (la:(real^3->bool)->bool)` THEN
    REPEAT(POP_ASSUM(K ALL_TAC)) THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^3->real^3` (X_CHOOSE_THEN `phi:real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`psi:real^3->real^3`; `phi:real^3->real^3`] THEN
  SUBGOAL_THEN `IMAGE (psi:real^3->real^3) moi_s35_cube = derived_nbhd t la`
  SUBST1_TAC THENL [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* STEP4, part 1: triangulations of a PL 2-cell.  By 2D invariance           *)
(* (SURF_INVARIANT of pc_moi_s28_trib with SURF_CHARTS and SURF_LOCAL) every *)
(* finite triangulation of a PL 2-cell d is a combinatorial surface with     *)
(* boundary the rim jd; it has plane or half-plane charts, dimension at most *)
(* 2, its edges off the rim lie in exactly two triangles, and the rim is a   *)
(* union of its edges.                                                       *)
(* ------------------------------------------------------------------------- *)

(* Duplicate of MOI_FRB_FACE_COMPLEX_CMWB2 (pc_moi_fnd_rnb2; not loaded      *)
(* because it adds 1.5 MB to the load closure).                              *)

let MOI_S3CA_FACE_CMWB2 = prove
 (`!k:real^N->bool.
        &2 simplex k ==> combinatorial_manifold_with_boundary 2 {f | f face_of k}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_FMB_FACE_COMPLEX]; ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_ELIM_THM; FACE_OF_SING] THEN
  UNDISCH_TAC `&2 simplex (k:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_TAC THEN ASM_SIMP_TAC[MOI_FMB_FACE_COMPLEX_LINK] THEN DISJ2_TAC THEN
  MATCH_MP_TAC PL_BALL_SIMPLEX THEN REWRITE_TAC[simplex] THEN
  EXISTS_TAC `V DELETE (v:real^N)` THEN REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_DELETE] THEN
  UNDISCH_TAC `&(CARD(V:real^N->bool)):int = &2 + &1` THEN
  SUBGOAL_THEN `1 <= CARD(V:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SIMP_TAC[GSYM INT_OF_NUM_SUB] THEN INT_ARITH_TAC);;

(* Duplicate of MOI_FSP_FACE_SB (pc_moi_fnd_split).                          *)

let MOI_S3CA_FACE_SB = prove
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

(* 2D invariance at M = N (as MOI_FRB_SURF_INVARIANT of pc_moi_fnd_rnb2).     *)

let MOI_S3CA_SURF_INV = prove
 (inst [`:N`,`:M`] MOI_S28_SURF_INVARIANT_BODY,
  ACCEPT_TAC(INST_TYPE [`:N`,`:M`]
    (MP SURF_INVARIANT (CONJ (INST_TYPE [`:M`,`:N`] SURF_CHARTS) SURF_LOCAL))));;

let MOI_S3CA_DISK_TRI = prove
 (`!(L:(real^N->bool)->bool) d jd.
     FINITE L /\ simplicial_complex L /\ UNIONS L = d /\ pl_cell_with_boundary 2 d jd
     ==> combinatorial_manifold_with_boundary 2 L /\ surface_boundary L = jd /\
         (!y. y IN d ==> moi_s28_locally_r2 d y \/ moi_s28_locally_half d y) /\
         (!y. y IN d DIFF jd ==> moi_s28_locally_r2 d y) /\
         (!s. s IN L ==> aff_dim s <= &2) /\
         (!e. e IN L /\ aff_dim e = &1 /\ ~(e SUBSET jd)
              ==> CARD {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = 2) /\
         (!y. y IN jd ==> ?e. e IN L /\ e SUBSET jd /\ y IN e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary]) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))))) THEN
  MP_TAC(ISPECL [`&2:int`; `k:real^N->bool`] MOI_FMB_FACE_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {e:real^N->bool | e face_of k} /\
                combinatorial_manifold_with_boundary 2 {e:real^N->bool | e face_of k} /\
                homeomorphism (k,d) (f:real^N->real^N,g)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      MATCH_MP_TAC MOI_S3CA_FACE_CMWB2 THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[pl_homeomorphism]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{e:real^N->bool | e face_of k}`; `L:(real^N->bool)->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_S3CA_SURF_INV) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP MOI_S3CA_FACE_SB (ASSUME `&2 simplex (k:real^N->bool)`)] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (K ALL_TAC))) THEN
  MP_TAC(ISPEC `L:(real^N->bool)->bool` SURF_CHARTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "int") (CONJUNCTS_THEN2 (LABEL_TAC "bd") (K ALL_TAC))) THEN
  SUBGOAL_THEN `!y:real^N. y IN d ==> moi_s28_locally_r2 d y \/ moi_s28_locally_half d y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN jd` THENL
     [DISJ2_TAC THEN USE_THEN "bd" (MP_TAC o SPEC `y:real^N`) THEN ASM_SIMP_TAC[];
      DISJ1_TAC THEN USE_THEN "int" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN L ==> aff_dim s <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TB_DIM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!e:real^N->bool. e IN L /\ aff_dim e = &1 /\
                     CARD {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = 1
                     ==> e SUBSET jd`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `surface_boundary (L:(real^N->bool)->bool) = jd`)) THEN
    REWRITE_TAC[surface_boundary] THEN MATCH_MP_TAC(SET_RULE
     `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`] MOI_S8TB_EDGE_CARD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~((e:real^N->bool) SUBSET jd)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN surface_boundary L` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* STEP4, part 2: the context (first and second derived of m, fullness of    *)
(* barycentric_subdivision l) and the rim: a simplex of the first derived    *)
(* meeting UNIONS l misses jd, so the derived neighbourhood misses jd.       *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_S4_CONTEXT = prove
 (`!(m:(real^N->bool)->bool) l d jd.
     FINITE m /\ simplicial_complex m /\ UNIONS m = d /\ pl_cell_with_boundary 2 d jd /\
     simplicial_subcomplex l m
     ==> lf_simplicial_complex m /\ moi_bar_complex m /\
         FINITE (barycentric_subdivision m) /\
         simplicial_complex (barycentric_subdivision m) /\
         lf_simplicial_complex (barycentric_subdivision m) /\
         moi_bar_complex (barycentric_subdivision m) /\
         UNIONS (barycentric_subdivision m) = d /\
         FINITE (barycentric_subdivision (barycentric_subdivision m)) /\
         simplicial_complex (barycentric_subdivision (barycentric_subdivision m)) /\
         lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision m)) /\
         moi_bar_complex (barycentric_subdivision (barycentric_subdivision m)) /\
         UNIONS (barycentric_subdivision (barycentric_subdivision m)) = d /\
         simplicial_subcomplex (barycentric_subdivision l) (barycentric_subdivision m) /\
         UNIONS (barycentric_subdivision l) = UNIONS l /\
         (!r. r IN barycentric_subdivision m /\ r SUBSET UNIONS l
              ==> r IN barycentric_subdivision l) /\
         surface_boundary m = jd /\
         (!s. s IN barycentric_subdivision m ==> aff_dim s <= &2) /\
         (!e. e IN barycentric_subdivision m /\ aff_dim e = &1 /\ ~(e SUBSET jd)
              ==> CARD {t | t IN barycentric_subdivision m /\ aff_dim t = &2 /\
                            e SUBSET t} = 2) /\
         (!y. y IN jd ==> ?e. e IN m /\ e SUBSET jd /\ y IN e) /\
         (!y. y IN d ==> moi_s28_locally_r2 d y \/ moi_s28_locally_half d y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (barycentric_subdivision (m:(real^N->bool)->bool)) /\
                simplicial_complex (barycentric_subdivision m)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE (barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))) /\
    simplicial_complex (barycentric_subdivision (barycentric_subdivision m)) /\
    lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision m)) /\
    moi_bar_complex (barycentric_subdivision (barycentric_subdivision m)) /\
    UNIONS (barycentric_subdivision (barycentric_subdivision m)) = d`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX;
                 BARYCENTRIC_SUBDIVISION_LF; UNIONS_BARYCENTRIC_SUBDIVISION] THEN
    MATCH_MP_TAC MOI_FRN_LF_BAR_COMPLEX THEN ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `d:real^N->bool`; `jd:real^N->bool`]
    MOI_S3CA_DISK_TRI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `d:real^N->bool`;
                 `jd:real^N->bool`] MOI_S3CA_DISK_TRI) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FRN_LF_BAR_COMPLEX] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_FULL_SUBSET THEN
  EXISTS_TAC `m:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

(* The faces of a simplex of a complex form a subcomplex.                    *)

let MOI_S3CA_FACES_SUBCOMPLEX = prove
 (`!(m:(real^N->bool)->bool) e.
     moi_bar_complex m /\ e IN m
     ==> simplicial_subcomplex {f | f face_of e} m /\ UNIONS {f | f face_of e} = e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex (e:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; MESON_TAC[FACE_OF_TRANS]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN MESON_TAC[FACE_OF_IMP_SUBSET];
      MATCH_MP_TAC(SET_RULE `(e:real^N->bool) IN s ==> e SUBSET UNIONS s`) THEN
      ASM_SIMP_TAC[IN_ELIM_THM; FACE_OF_REFL]]]);;

(* A simplex of the first derived meeting UNIONS l misses the rim, when the *)
(* rim is a union of simplices of m missing UNIONS l.                        *)

let MOI_S3CA_FIRST_RIM = prove
 (`!(m:(real^N->bool)->bool) l jd g.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     DISJOINT (UNIONS l) jd /\
     (!y. y IN jd ==> ?e. e IN m /\ e SUBSET jd /\ y IN e) /\
     g IN barycentric_subdivision m /\ ~(g INTER UNIONS l = {})
     ==> g INTER jd = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_BAR_IN_SUBDIVISION]) THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:(real^N->bool)->bool`] MOI_FRN_CHAIN_HULL_MEETS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `y:real^N` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `h:(real^N->bool)->bool`; `y:real^N`]
    MOI_BAR_CHAIN_HULL_RI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain (m:(real^N->bool)->bool) g` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain (m:(real^N->bool)->bool) h` THEN
    UNDISCH_TAC `(g:(real^N->bool)->bool) SUBSET h` THEN
    REWRITE_TAC[moi_bar_chain] THEN MESON_TAC[SUBSET; FINITE_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(y:real^N) IN relative_interior
                   (convex hull (IMAGE simplex_barycentre ({}:(real^N->bool)->bool)))` THEN
    REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `g:(real^N->bool)->bool`; `y:real^N`]
    MOI_BAR_CHAIN_RI_MAX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `tt = UNIONS (g:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(tt:real^N->bool) IN h /\ tt IN m` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain (m:(real^N->bool)->bool) h` THEN
    REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
    can (term_match [] `!y:real^N. y IN jd ==> ?e. e IN m /\ e SUBSET jd /\ y IN e`)
        (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `e:real^N->bool`] MOI_S3CA_FACES_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `{f:real^N->bool | f face_of e}`;
                 `tt:real^N->bool`; `y:real^N`] MOI_FRN_RELINT_MEETS_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(tt:real^N->bool) SUBSET jd` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET tt \/ tt SUBSET s` MP_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {}) /\ s SUBSET UNIONS l` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain];
      MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN l ==> s SUBSET UNIONS l`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN tt` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (UNIONS l) (jd:real^N->bool)` THEN
  UNDISCH_TAC `(tt:real^N->bool) SUBSET jd` THEN
  UNDISCH_TAC `(y:real^N) IN tt` THEN UNDISCH_TAC `(s:real^N->bool) SUBSET UNIONS l` THEN
  UNDISCH_TAC `~(s:real^N->bool = {})` THEN SET_TAC[]);;

(* Hence the derived neighbourhood misses the rim.                           *)

let MOI_S3CA_NBHD_RIM = prove
 (`!(m:(real^N->bool)->bool) l jd.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     DISJOINT (UNIONS l) jd /\
     (!y. y IN jd ==> ?e. e IN m /\ e SUBSET jd /\ y IN e)
     ==> derived_nbhd m l INTER jd = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^N` THEN
  ASM_SIMP_TAC[MOI_FRN_IN_NBHD] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(f:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                 `f:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                 `f:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `jd:real^N->bool`;
                 `UNIONS f:real^N->bool`] MOI_S3CA_FIRST_RIM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision (m:(real^N->bool)->bool)) f` THEN
      REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[];
      SUBGOAL_THEN `~(s:real^N->bool = {}) /\ s SUBSET UNIONS l` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [ASM_MESON_TAC[moi_bar_chain];
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
            concl th = `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)`)) THEN
          MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN l ==> s SUBSET UNIONS l`) THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS f` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(s:real^N->bool) SUBSET UNIONS l` THEN
      UNDISCH_TAC `~(s:real^N->bool = {})` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* STEP4, part 3: vertices of first-derived simplices and the frontier of N *)
(* as the union of the segments from b f to b tri, f a first-derived simplex *)
(* meeting UNIONS l without lying in it (moi_frn_vp) and tri a larger one.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_CHAIN_EXTREME = prove
 (`!(m:(real^N->bool)->bool) h.
     moi_bar_complex m /\ moi_bar_chain m h
     ==> {v | v extreme_point_of convex hull (IMAGE simplex_barycentre h)} =
         IMAGE simplex_barycentre h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `h:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  SIMP_TAC[EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT]);;

let MOI_S3CA_MEETS_VERTEX = prove
 (`!(m:(real^N->bool)->bool) l r.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     r IN barycentric_subdivision m /\ ~(r INTER UNIONS l = {})
     ==> ?v. v extreme_point_of r /\ v IN UNIONS l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  UNDISCH_TAC `(r:real^N->bool) IN barycentric_subdivision m` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:(real^N->bool)->bool`] MOI_FRN_CHAIN_HULL_MEETS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `simplex_barycentre (s:real^N->bool)` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `h:(real^N->bool)->bool`]
      MOI_S3CA_CHAIN_EXTREME) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(s:real^N->bool) IN m /\ ~(s = {})` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
    ASM_MESON_TAC[]]);;

let MOI_S3CA_VERTICES_IN = prove
 (`!(m:(real^N->bool)->bool) l r.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     r IN barycentric_subdivision m /\
     (!v. v extreme_point_of r ==> v IN UNIONS l)
     ==> r SUBSET UNIONS l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  UNDISCH_TAC `(r:real^N->bool) IN barycentric_subdivision m` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_CASES_TAC `h:(real^N->bool)->bool = {}` THENL
   [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; EMPTY_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `h:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `h:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `tt = UNIONS (h:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(tt:real^N->bool) IN m /\ ~(tt = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex (tt:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (tt:real^N->bool) IN UNIONS l` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> can (term_match []
      `!v:real^N. v extreme_point_of s ==> v IN UNIONS l`) (concl th))) THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `h:(real^N->bool)->bool`]
      MOI_S3CA_CHAIN_EXTREME) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(tt:real^N->bool) IN l` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
    MAP_EVERY EXISTS_TAC [`m:(real^N->bool)->bool`;
                          `simplex_barycentre (tt:real^N->bool)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `tt:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN l ==> s SUBSET UNIONS l`) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3CA_VP_VERTICES = prove
 (`!(m:(real^N->bool)->bool) l r.
     lf_simplicial_complex m /\ simplicial_subcomplex l m
     ==> (moi_frn_vp m l r <=>
          r IN barycentric_subdivision m /\
          (?v. v extreme_point_of r /\ v IN UNIONS l) /\
          (?w. w extreme_point_of r /\ ~(w IN UNIONS l)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_frn_vp] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3CA_MEETS_VERTEX THEN EXISTS_TAC `m:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[TAUT `p /\ ~q <=> ~(p ==> q)`; GSYM NOT_FORALL_THM] THEN
      DISCH_TAC THEN UNDISCH_TAC `~((r:real^N->bool) SUBSET UNIONS l)` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3CA_VERTICES_IN THEN
      EXISTS_TAC `m:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `(v:real^N) IN r /\ (w:real^N) IN r` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
    ASM SET_TAC[]]);;

(* A mixed simplex has a mixed edge: the segment from a vertex in UNIONS l  *)
(* to a vertex outside it.                                                   *)

let MOI_S3CA_VP_EDGE = prove
 (`!(m:(real^N->bool)->bool) l r.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\ moi_frn_vp m l r
     ==> ?e. moi_frn_vp m l e /\ aff_dim e = &1 /\ e SUBSET r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
    MOI_S3CA_VP_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(v:real^N = w)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (m:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,w] face_of r` ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (fun th -> ONCE_REWRITE_TAC[th])) THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{v:real^N,w}` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `segment[v:real^N,w]` THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `segment[v:real^N,w]`] MOI_S3CA_VP_VERTICES) THEN
    ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN DISCH_THEN SUBST1_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex];
      EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]);;

(* A frontier point lies on a segment [b f,b tri], f mixed, tri larger: the *)
(* frontier point x lies in a simplex of the neighbourhood complex and in    *)
(* one outside it; the least member phi of the common subchain is mixed, and *)
(* (dimension at most 2) the subchain has at most the two members phi, top.  *)

let MOI_S3CA_FR_IN_SEG = prove
 (`!(m:(real^N->bool)->bool) l x.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     (!s. s IN barycentric_subdivision m ==> aff_dim s <= &2) /\
     (!e. moi_frn_vp m l e /\ aff_dim e = &1
          ==> ?tri. tri IN barycentric_subdivision m /\ e SUBSET tri /\ ~(e = tri)) /\
     x IN derived_frontier m l
     ==> ?f tri. moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\
                 f SUBSET tri /\ ~(f = tri) /\
                 x IN segment[simplex_barycentre f,simplex_barycentre tri]`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)))) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN barycentric_subdivision m /\ r SUBSET UNIONS l
                                 ==> r IN barycentric_subdivision l`
  (LABEL_TAC "full") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_FULL_SUBSET THEN
    EXISTS_TAC `m:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FN2_FRONTIER_NC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
    ASM_SIMP_TAC[MOI_FRN_IN_NBHD] THEN
    DISCH_THEN(X_CHOOSE_THEN `f0:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_BAR_IN_SUBDIVISION] o check (fun th ->
      concl th = `(s:real^N->bool) IN barycentric_subdivision (barycentric_subdivision m)`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(x:real^N) IN convex hull
                     (IMAGE simplex_barycentre ({}:(real^N->bool)->bool))` THEN
      REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:(real^N->bool)->bool`] MOI_FN2_NC_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                   `f0:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre
                     ((f0:(real^N->bool)->bool) INTER g))` ASSUME_TAC THENL
     [UNDISCH_TAC `convex hull (IMAGE simplex_barycentre (f0:(real^N->bool)->bool)) INTER
                   convex hull (IMAGE simplex_barycentre g) =
                   convex hull (IMAGE simplex_barycentre (f0 INTER g))` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision (m:(real^N->bool)->bool))
                    (f0 INTER g)` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision (m:(real^N->bool)->bool)) f0` THEN
      REWRITE_TAC[moi_bar_chain] THEN MESON_TAC[IN_INTER; SUBSET; FINITE_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((f0:(real^N->bool)->bool) INTER g = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre
                     ((f0:(real^N->bool)->bool) INTER g))` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `INTERS ((f0:(real^N->bool)->bool) INTER g) IN f0 INTER g /\
                  UNIONS ((f0:(real^N->bool)->bool) INTER g) IN f0 INTER g /\
                  INTERS (g:(real^N->bool)->bool) IN g`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC INTERS_IN_CHAIN; MATCH_MP_TAC UNIONS_IN_CHAIN;
        MATCH_MP_TAC INTERS_IN_CHAIN] THEN
      ASM_MESON_TAC[moi_bar_chain];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!psi:real^N->bool. psi IN f0 INTER g
          ==> INTERS (f0 INTER g) SUBSET psi /\ psi SUBSET UNIONS (f0 INTER g) /\
              psi IN barycentric_subdivision m /\ ~(psi = {})`
    ASSUME_TAC THENL
     [X_GEN_TAC `psi:real^N->bool` THEN DISCH_TAC THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[]; ASM SET_TAC[];
        ASM_MESON_TAC[moi_bar_chain; SUBSET];
        ASM_MESON_TAC[moi_bar_chain]];
      ALL_TAC] THEN
    SUBGOAL_THEN `INTERS (g:(real^N->bool)->bool) IN barycentric_subdivision m /\
                  ~(INTERS g = {})` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `INTERS (g:(real^N->bool)->bool) SUBSET INTERS (f0 INTER g)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> INTERS s SUBSET x`) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `phi = INTERS ((f0:(real^N->bool)->bool) INTER g)` THEN
    ABBREV_TAC `top = UNIONS ((f0:(real^N->bool)->bool) INTER g)` THEN
    SUBGOAL_THEN `(phi:real^N->bool) IN barycentric_subdivision m /\ ~(phi = {}) /\
                  (top:real^N->bool) IN barycentric_subdivision m /\ phi SUBSET top /\
                  phi IN f0`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
    (* the least member phi is mixed *)
    SUBGOAL_THEN `~((phi:real^N->bool) SUBSET UNIONS l)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_neg(concl th) && is_exists(rand(concl th)))) THEN
      REWRITE_TAC[] THEN EXISTS_TAC `INTERS (g:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN USE_THEN "full" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((phi:real^N->bool) INTER UNIONS l = {})` ASSUME_TAC THENL
     [SUBGOAL_THEN `(s0:real^N->bool) SUBSET phi \/ phi SUBSET s0` MP_TAC THENL
       [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
      SUBGOAL_THEN `~(s0:real^N->bool = {}) /\ s0 SUBSET UNIONS l` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [ASM_MESON_TAC[moi_bar_chain];
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
            concl th = `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)`)) THEN
          MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN l ==> s SUBSET UNIONS l`) THEN
          ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `~((phi:real^N->bool) SUBSET UNIONS l)` THEN
      UNDISCH_TAC `(s0:real^N->bool) SUBSET UNIONS l` THEN
      UNDISCH_TAC `~(s0:real^N->bool = {})` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_frn_vp m l (phi:real^N->bool)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[moi_frn_vp]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (phi:real^N->bool) = &1 \/ aff_dim phi = &2` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `phi:real^N->bool`] MOI_FN2_VP_NOT_VERTEX) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `aff_dim (phi:real^N->bool) <= &2 /\ ~(aff_dim phi = -- &1)` MP_TAC THENL
       [ASM_SIMP_TAC[AFF_DIM_EQ_MINUS1]; ALL_TAC] THEN
      MP_TAC(ISPEC `phi:real^N->bool` AFF_DIM_GE) THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    (* at most two members *)
    SUBGOAL_THEN `(f0:(real^N->bool)->bool) INTER g SUBSET {phi,top}` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN X_GEN_TAC `psi:real^N->bool` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `(phi:real^N->bool) SUBSET psi /\ psi SUBSET top /\
                    psi IN barycentric_subdivision m` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
      SUBGOAL_THEN `!r:real^N->bool. r IN barycentric_subdivision m ==> convex r`
      ASSUME_TAC THENL
       [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      SUBGOAL_THEN `(phi:real^N->bool) face_of psi /\ psi face_of (top:real^N->bool)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC MOI_FN2_NESTED_FACE THEN
        EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `aff_dim (phi:real^N->bool) < aff_dim (psi:real^N->bool) /\
                    aff_dim psi < aff_dim (top:real^N->bool)` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_SIMP_TAC[] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `aff_dim (top:real^N->bool) <= &2` MP_TAC THENL
       [ASM_SIMP_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `aff_dim (phi:real^N->bool) = &1 \/ aff_dim phi = &2` THEN
      INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN segment[simplex_barycentre phi,simplex_barycentre top]`
    ASSUME_TAC THENL
     [REWRITE_TAC[GSYM MOI_FN2_HULL2] THEN
      UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f0 INTER g))` THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^N) IN s ==> x IN t`) THEN
      MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `phi:real^N->bool = top` THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `phi:real^N->bool = top`)) THEN
      UNDISCH_TAC `(x:real^N) IN segment[simplex_barycentre top,simplex_barycentre top]` THEN
      REWRITE_TAC[SEGMENT_REFL; IN_SING] THEN DISCH_THEN SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
        can (find_term ((=) `aff_dim (top:real^N->bool)`)) (concl th))) THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `top:real^N->bool` o check (fun th ->
          can (term_match [] `!e:real^N->bool. moi_frn_vp m l e /\ aff_dim e = &1
              ==> ?tri. tri IN barycentric_subdivision m /\ e SUBSET tri /\ ~(e = tri)`)
              (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `tri:real^N->bool` STRIP_ASSUME_TAC) THEN
        MAP_EVERY EXISTS_TAC [`top:real^N->bool`; `tri:real^N->bool`] THEN
        ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
        MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `top:real^N->bool`] MOI_S3CA_VP_EDGE) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
        MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `top:real^N->bool`] THEN
        ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
          can (find_term ((=) `aff_dim (top:real^N->bool)`)) (concl th)))) THEN
        INT_ARITH_TAC];
      MAP_EVERY EXISTS_TAC [`phi:real^N->bool`; `top:real^N->bool`] THEN
      ASM_REWRITE_TAC[]]);;

(* Conversely the points of such segments are frontier points.             *)

let MOI_S3CA_FR_SEG_IN = prove
 (`!(m:(real^N->bool)->bool) l f tri x.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\ f SUBSET tri /\
     x IN segment[simplex_barycentre f,simplex_barycentre tri]
     ==> x IN derived_frontier m l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN barycentric_subdivision m /\ r SUBSET UNIONS l
                                 ==> r IN barycentric_subdivision l`
  (LABEL_TAC "full") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_FULL_SUBSET THEN
    EXISTS_TAC `m:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FN2_FRONTIER_NC] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
      MOI_S3CA_VP_VERTICES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `{v:real^N} IN barycentric_subdivision m /\
                  {w:real^N} IN barycentric_subdivision m /\
                  (v:real^N) IN f /\ (w:real^N) IN f` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex; FACE_OF_SING; extreme_point_of]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!y:real^N. y IN f /\ {y} IN barycentric_subdivision m
          ==> moi_bar_chain (barycentric_subdivision m) {{y},f,tri} /\
              x IN convex hull (IMAGE simplex_barycentre {{y},f,tri})`
    (LABEL_TAC "ch") THENL
     [REPEAT STRIP_TAC THENL
       [MATCH_MP_TAC MOI_FN2_CHAIN3 THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(x:real^N) IN segment[simplex_barycentre f,simplex_barycentre tri]` THEN
        REWRITE_TAC[SEGMENT_CONVEX_HULL; IMAGE_CLAUSES] THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^N) IN s ==> x IN t`) THEN
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[MOI_FRN_IN_NBHD] THEN EXISTS_TAC `{{v:real^N},f,tri}` THEN
      USE_THEN "ch" (MP_TAC o SPEC `v:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `{v:real^N}` THEN
      REWRITE_TAC[IN_INSERT] THEN USE_THEN "full" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[SING_SUBSET];
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre {{w:real^N},f,tri})` THEN
      USE_THEN "ch" (MP_TAC o SPEC `w:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `{{w:real^N},f,tri}` THEN
        ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `{{w:real^N},f,tri}`] MOI_FN2_NC_CHAIN) THEN
        ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN DISCH_THEN SUBST1_TAC THEN
        SUBGOAL_THEN `INTERS {{w:real^N},f,tri} = {w}` SUBST1_TAC THENL
         [REWRITE_TAC[INTERS_INSERT; INTERS_0; INTER_UNIV] THEN ASM SET_TAC[]; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `r = {w:real^N}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `~((w:real^N) IN UNIONS l)` THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
          concl th = `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)`)) THEN
        REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING]]]);;

(* The frontier of the second-derived neighbourhood when the first derived  *)
(* has dimension at most 2 and every mixed edge lies in a larger simplex.   *)

let MOI_S3CA_FRONTIER_SEGS = prove
 (`!(m:(real^N->bool)->bool) l.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     (!s. s IN barycentric_subdivision m ==> aff_dim s <= &2) /\
     (!e. moi_frn_vp m l e /\ aff_dim e = &1
          ==> ?tri. tri IN barycentric_subdivision m /\ e SUBSET tri /\ ~(e = tri))
     ==> derived_frontier m l =
         UNIONS {segment[simplex_barycentre f,simplex_barycentre tri] | f tri |
                 moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\
                 f SUBSET tri /\ ~(f = tri)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
      MOI_S3CA_FR_IN_SEG) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (X_CHOOSE_THEN `tri:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `segment[simplex_barycentre f,simplex_barycentre (tri:real^N->bool)]` THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->bool`; `tri:real^N->bool`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (X_CHOOSE_THEN `tri:real^N->bool`
      (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC))) THEN
    MATCH_MP_TAC MOI_S3CA_FR_SEG_IN THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->bool`; `tri:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* STEP4, part 4: the segments [b f,b tri] with their ends form a 1-complex  *)
(* in the second derived in which every vertex lies in exactly two edges   *)
(* (a mixed edge in two triangles; a mixed triangle has two mixed edges),  *)
(* so the components of the frontier are PL circles (MOI_S4L_CM1_CIRCLES).  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_SUBSET_SC = prove
 (`!(c:(real^N->bool)->bool) k.
     simplicial_complex c /\ k SUBSET c /\ (!s f. s IN k /\ f face_of s ==> f IN k)
     ==> simplicial_complex k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_BAR_SIMPLICIAL_COMPLEX; moi_bar_complex] THEN
  STRIP_TAC THEN ASM_MESON_TAC[FINITE_SUBSET; SUBSET]);;

let MOI_S3CA_FACES_SEG = prove
 (`(!(a:real^N) t. t face_of {a} <=> t = {} \/ t = {a}) /\
   (!(p:real^N) q t. t face_of segment[p,q] <=>
                     t = {} \/ t = {p} \/ t = {q} \/ t = segment[p,q])`,
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [GSYM CONVEX_HULL_SING] THEN
    SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_1] THEN
    REWRITE_TAC[SET_RULE `(c:real^N->bool) SUBSET {a} <=> c = {} \/ c = {a}`] THEN
    MESON_TAC[CONVEX_HULL_EMPTY; CONVEX_HULL_SING];
    REPEAT GEN_TAC THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_2] THEN
    REWRITE_TAC[SET_RULE `(c:real^N->bool) SUBSET {a,b} <=>
                          c = {} \/ c = {a} \/ c = {b} \/ c = {a,b}`] THEN
    MESON_TAC[CONVEX_HULL_EMPTY; CONVEX_HULL_SING]]);;

(* The barycentre of a simplex r of a complex lies on [b f,b tri] only when *)
(* r is f or tri.                                                            *)

let MOI_S3CA_SEG_BARY = prove
 (`!(c:(real^N->bool)->bool) r f tri.
     simplicial_complex c /\ r IN c /\ f IN c /\ tri IN c /\ ~(r = {}) /\ ~(f = {}) /\
     f SUBSET tri
     ==> (simplex_barycentre r IN segment[simplex_barycentre f,simplex_barycentre tri] <=>
          r = f \/ r = tri)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
    SUBGOAL_THEN `simplex_barycentre r IN relative_interior (r:real^N->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
      ASM_MESON_TAC[moi_bar_complex];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^N->bool`; `tri:real^N->bool`;
                   `simplex_barycentre (r:real^N->bool)`] MOI_FN2_SEG_RELINT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [DISJ1_TAC; DISJ2_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `!x:real^N s t. x IN s /\ x IN t /\ s INTER t = {} ==> F`) THEN
    EXISTS_TAC `simplex_barycentre (r:real^N->bool)` THENL
     [EXISTS_TAC `relative_interior (r:real^N->bool)` THEN
      EXISTS_TAC `relative_interior (f:real^N->bool)`;
      EXISTS_TAC `relative_interior (r:real^N->bool)` THEN
      EXISTS_TAC `relative_interior (tri:real^N->bool)`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SIMPLICIAL_COMPLEX_DISJOINT_RELATIVE_INTERIORS THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT]]);;

(* Proper subsets in a complex have smaller dimension; mixed first-derived   *)
(* simplices have dimension 1 or 2 when the first derived has dimension at  *)
(* most 2.                                                                   *)

let MOI_S3CA_PROPER_DIM = prove
 (`!(c:(real^N->bool)->bool) f r.
     moi_bar_complex c /\ f IN c /\ r IN c /\ f SUBSET r /\ ~(f = r)
     ==> aff_dim f < aff_dim r`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX];
    MATCH_MP_TAC MOI_FN2_NESTED_FACE THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S3CA_VP_DIM = prove
 (`!(m:(real^N->bool)->bool) l f.
     (!s. s IN barycentric_subdivision m ==> aff_dim s <= &2) /\ moi_frn_vp m l f
     ==> aff_dim f = &1 \/ aff_dim f = &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
    MOI_FN2_VP_NOT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:real^N->bool) IN barycentric_subdivision m /\ ~(f = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_frn_vp m l (f:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (f:real^N->bool) <= &2 /\ ~(aff_dim f = -- &1)` MP_TAC THENL
   [ASM_SIMP_TAC[AFF_DIM_EQ_MINUS1]; ALL_TAC] THEN
  MP_TAC(ISPEC `f:real^N->bool` AFF_DIM_GE) THEN INT_ARITH_TAC);;

(* Two halves of the count of mixed faces of a mixed triangle.             *)

let MOI_S3CA_MIXED_SUB1 = prove
 (`!(m:(real^N->bool)->bool) l r V f.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     moi_bar_complex (barycentric_subdivision m) /\
     r IN barycentric_subdivision m /\ ~affine_dependent V /\ convex hull V = r /\
     FINITE V /\ CARD V = 3 /\
     moi_frn_vp m l f /\ f SUBSET r /\ ~(f = r)
     ==> ?x y. x IN V /\ x IN UNIONS l /\ y IN V /\ ~(y IN UNIONS l) /\
               f = segment[x,y]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(f:real^N->bool) IN barycentric_subdivision m` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_frn_vp m l (f:real^N->bool)` THEN SIMP_TAC[moi_frn_vp]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->bool) face_of convex hull V` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FN2_NESTED_FACE THEN
    EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~affine_dependent (C:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^N. z extreme_point_of f <=> z IN C` ASSUME_TAC THENL
   [GEN_TAC THEN
    MP_TAC(ISPEC `C:real^N->bool` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
    MOI_S3CA_VP_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(x:real^N = y)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN
  SUBGOAL_THEN `C = {x:real^N,y}` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `?z:real^N. z IN C /\ ~(z = x) /\ ~(z = y)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(C = {x:real^N,y})` THEN UNDISCH_TAC `(x:real^N) IN C` THEN
      UNDISCH_TAC `(y:real^N) IN C` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `{x:real^N,y,z} = V` ASSUME_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `(C:real^N->bool) SUBSET V` THEN UNDISCH_TAC `(x:real^N) IN C` THEN
        UNDISCH_TAC `(y:real^N) IN C` THEN UNDISCH_TAC `(z:real^N) IN C` THEN SET_TAC[];
        SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
        ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV];
      ALL_TAC] THEN
    UNDISCH_TAC `~(f:real^N->bool = r)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `f = convex hull (C:real^N->bool)` THEN DISCH_THEN SUBST1_TAC THEN
    SUBST1_TAC(SYM(ASSUME `convex hull V = (r:real^N->bool)`)) THEN
    AP_TERM_TAC THEN
    UNDISCH_TAC `(C:real^N->bool) SUBSET V` THEN UNDISCH_TAC `{x:real^N,y,z} = V` THEN
    UNDISCH_TAC `(x:real^N) IN C` THEN UNDISCH_TAC `(y:real^N) IN C` THEN
    UNDISCH_TAC `(z:real^N) IN C` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  UNDISCH_TAC `{x:real^N,y} SUBSET V` THEN SET_TAC[]);;

let MOI_S3CA_MIXED_SUB2 = prove
 (`!(m:(real^N->bool)->bool) l r V x y.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     moi_bar_complex (barycentric_subdivision m) /\
     r IN barycentric_subdivision m /\ ~affine_dependent V /\ convex hull V = r /\
     aff_dim r = &2 /\
     x IN V /\ x IN UNIONS l /\ y IN V /\ ~(y IN UNIONS l)
     ==> moi_frn_vp m l (segment[x,y]) /\ segment[x,y] SUBSET r /\ ~(segment[x,y] = r)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x:real^N = y)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^N,y] face_of r` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `convex hull V = (r:real^N->bool)`)) THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{x:real^N,y}` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[x:real^N,y] IN barycentric_subdivision m` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_complex (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
    REWRITE_TAC[moi_bar_complex] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `segment[x:real^N,y]`] MOI_S3CA_VP_VERTICES) THEN
    ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN DISCH_THEN SUBST1_TAC THEN
    CONJ_TAC THENL
     [EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
    DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN INT_ARITH_TAC]);;

(* A mixed triangle has exactly two mixed proper faces, the segments from   *)
(* its vertices in UNIONS l to those outside (CARD A * CARD B = 2).          *)

let MOI_S3CA_MIXED_TRI = prove
 (`!(m:(real^N->bool)->bool) l r.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     moi_frn_vp m l r /\ aff_dim r = &2
     ==> CARD {f | moi_frn_vp m l f /\ f SUBSET r /\ ~(f = r)} = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (m:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision m` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_frn_vp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
    MOI_S3CA_VP_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `v0:real^N` STRIP_ASSUME_TAC) (X_CHOOSE_THEN `w0:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  SUBGOAL_THEN `(v0:real^N) IN {v | v extreme_point_of r} /\
                (w0:real^N) IN {v | v extreme_point_of r}` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC `V = {v:real^N | v extreme_point_of r}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool) /\ CARD V = 3` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
    MP_TAC(ISPEC `V:real^N->bool` AFF_DIM_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `aff_dim (V:real^N->bool) = &2` SUBST1_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_CONVEX_HULL]; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `&2:int = x - &1 <=> x = &3`; INT_OF_NUM_EQ];
    ALL_TAC] THEN
  ABBREV_TAC `A = {v:real^N | v IN V /\ v IN UNIONS l}` THEN
  ABBREV_TAC `B = {v:real^N | v IN V /\ ~(v IN UNIONS l)}` THEN
  SUBGOAL_THEN `FINITE (A:real^N->bool) /\ FINITE (B:real^N->bool) /\
                CARD A + CARD B = 3 /\ ~(CARD A = 0) /\ ~(CARD B = 0)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `FINITE (A:real^N->bool) /\ FINITE (B:real^N->bool)` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `CARD (A UNION B:real^N->bool) = CARD A + CARD B` (SUBST1_TAC o SYM) THENL
       [MATCH_MP_TAC CARD_UNION THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY EXPAND_TAC ["A"; "B"] THEN SET_TAC[];
        SUBGOAL_THEN `A UNION B:real^N->bool = V` SUBST1_TAC THENL
         [MAP_EVERY EXPAND_TAC ["A"; "B"] THEN SET_TAC[]; ASM_REWRITE_TAC[]]];
      EXPAND_TAC "A" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `v0:real^N` THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "B" THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `w0:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{f | moi_frn_vp m l f /\ f SUBSET r /\ ~(f = r)} =
    IMAGE (\p:real^N#real^N. segment[FST p,SND p]) {(x,y) | x IN A /\ y IN B}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:real^N->bool` THEN
    REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; IN_ELIM_PAIR_THM; FST; SND] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`;
                     `V:real^N->bool`; `f:real^N->bool`] MOI_S3CA_MIXED_SUB1) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N`
        (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC))) THEN
      MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_S3CA_MIXED_SUB2 THEN EXISTS_TAC `V:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_PRODUCT] THEN
    REWRITE_TAC[FORALL_PAIR_THM; IN_ELIM_PAIR_THM; FST; SND; PAIR_EQ; SEGMENT_EQ] THEN
    MAP_EVERY X_GEN_TAC [`x1:real^N`; `y1:real^N`; `x2:real^N`; `y2:real^N`] THEN
    MAP_EVERY EXPAND_TAC ["A"; "B"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[CARD_PRODUCT] THEN
  SUBGOAL_THEN `CARD(A:real^N->bool) = 1 /\ CARD(B:real^N->bool) = 2 \/
                CARD A = 2 /\ CARD B = 1` STRIP_ASSUME_TAC THENL
   [ASM_ARITH_TAC; ASM_REWRITE_TAC[] THEN ARITH_TAC; ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

(* The segments through the barycentre of a mixed simplex r: two, from the  *)
(* two triangles on r (r an edge) or to the two mixed edges of r (r a       *)
(* triangle).                                                                *)

let MOI_S3CA_FR_DEGREE = prove
 (`!(m:(real^N->bool)->bool) l r.
     FINITE m /\ simplicial_complex m /\ simplicial_subcomplex l m /\
     (!s. s IN barycentric_subdivision m ==> aff_dim s <= &2) /\
     (!e. moi_frn_vp m l e /\ aff_dim e = &1
          ==> CARD {t | t IN barycentric_subdivision m /\ aff_dim t = &2 /\ e SUBSET t} = 2) /\
     moi_frn_vp m l r
     ==> CARD {e | e IN {segment[simplex_barycentre f,simplex_barycentre tri] | f tri |
                         moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\
                         f SUBSET tri /\ ~(f = tri)} /\
                   simplex_barycentre r IN e} = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (barycentric_subdivision (m:(real^N->bool)->bool)) /\
                simplicial_complex (barycentric_subdivision m) /\
                moi_bar_complex (barycentric_subdivision m)` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX] THEN
    ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision m /\ ~(r = {})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_frn_vp m l (r:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t:real^N->bool. s IN barycentric_subdivision m /\ t IN barycentric_subdivision m /\
                       ~(s = {}) /\ ~(t = {}) /\ simplex_barycentre s = simplex_barycentre t
                       ==> s = t`
  (LABEL_TAC "binj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_BARYCENTRE_INJ THEN
    EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `E1 = {tri:real^N->bool | tri IN barycentric_subdivision m /\ r SUBSET tri /\
                                       ~(r = tri)}` THEN
  ABBREV_TAC `E2 = {f:real^N->bool | moi_frn_vp m l f /\ f SUBSET r /\ ~(f = r)}` THEN
  SUBGOAL_THEN
   `{e | e IN {segment[simplex_barycentre f,simplex_barycentre tri] | f tri |
               moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\
               f SUBSET tri /\ ~(f = tri)} /\
         simplex_barycentre r IN e} =
    IMAGE (\tri. segment[simplex_barycentre r,simplex_barycentre (tri:real^N->bool)]) E1 UNION
    IMAGE (\f. segment[simplex_barycentre f,simplex_barycentre (r:real^N->bool)]) E2`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION; IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (X_CHOOSE_THEN `tri:real^N->bool`
        (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC))) THEN
      SUBGOAL_THEN `(f:real^N->bool) IN barycentric_subdivision m /\ ~(f = {})`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `moi_frn_vp m l (f:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN
        SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `r:real^N->bool`;
                     `f:real^N->bool`; `tri:real^N->bool`] MOI_S3CA_SEG_BARY) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THENL
       [DISJ1_TAC THEN EXISTS_TAC `tri:real^N->bool` THEN REWRITE_TAC[] THEN
        EXPAND_TAC "E1" THEN ASM_REWRITE_TAC[IN_ELIM_THM];
        DISJ2_TAC THEN EXISTS_TAC `f:real^N->bool` THEN REWRITE_TAC[] THEN
        EXPAND_TAC "E2" THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
      DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `x:real^N->bool`
        (CONJUNCTS_THEN2 SUBST1_TAC MP_TAC))) THENL
       [EXPAND_TAC "E1" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        REWRITE_TAC[ENDS_IN_SEGMENT] THEN
        MAP_EVERY EXISTS_TAC [`r:real^N->bool`; `x:real^N->bool`] THEN ASM_REWRITE_TAC[];
        EXPAND_TAC "E2" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        REWRITE_TAC[ENDS_IN_SEGMENT] THEN
        MAP_EVERY EXISTS_TAC [`x:real^N->bool`; `r:real^N->bool`] THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (E1:(real^N->bool)->bool) /\ FINITE (E2:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN MAP_EVERY EXPAND_TAC ["E1"; "E2"] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[moi_frn_vp];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
    MOI_S3CA_VP_DIM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [(* r an edge: no mixed proper faces, two triangles *)
    SUBGOAL_THEN `E2:(real^N->bool)->bool = {}` SUBST1_TAC THENL
     [EXPAND_TAC "E2" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
        MOI_S3CA_VP_DIM) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `f:real^N->bool`;
                     `r:real^N->bool`] MOI_S3CA_PROPER_DIM) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[moi_frn_vp]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES; UNION_EMPTY] THEN
    SUBGOAL_THEN `E1 = {t:real^N->bool | t IN barycentric_subdivision m /\ aff_dim t = &2 /\
                                         r SUBSET t}` SUBST1_TAC THENL
     [EXPAND_TAC "E1" THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `t:real^N->bool` THEN
      ASM_CASES_TAC `(t:real^N->bool) IN barycentric_subdivision m` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(r:real^N->bool) SUBSET t` THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
       [DISCH_TAC THEN
        MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `r:real^N->bool`;
                       `t:real^N->bool`] MOI_S3CA_PROPER_DIM) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `aff_dim (t:real^N->bool) <= &2` MP_TAC THENL
         [ASM_SIMP_TAC[]; INT_ARITH_TAC];
        DISCH_TAC THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        UNDISCH_TAC `aff_dim (r:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
      ALL_TAC] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o lhand o snd) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM; SEGMENT_EQ] THEN
        MAP_EVERY X_GEN_TAC [`t1:real^N->bool`; `t2:real^N->bool`] THEN STRIP_TAC THEN
        SUBGOAL_THEN `~(t1:real^N->bool = {}) /\ ~(t2:real^N->bool = {}) /\
                      ~(r:real^N->bool = t1) /\ ~(r = t2)` STRIP_ASSUME_TAC THENL
         [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
          REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
            can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th) &&
            not (is_forall (concl th))))) THEN
          REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
          ALL_TAC] THEN
        SUBGOAL_THEN `~(simplex_barycentre (t1:real^N->bool) = simplex_barycentre r) /\
                      ~(simplex_barycentre (t2:real^N->bool) = simplex_barycentre r)`
        STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN DISCH_TAC THENL
           [UNDISCH_TAC `~(r:real^N->bool = t1)`; UNDISCH_TAC `~(r:real^N->bool = t2)`] THEN
          REWRITE_TAC[] THEN USE_THEN "binj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        USE_THEN "binj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `{simplex_barycentre r,simplex_barycentre (t1:real^N->bool)} =
                     {simplex_barycentre r,simplex_barycentre t2}` THEN
        REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]];
      DISCH_THEN SUBST1_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* r a triangle: no larger simplices, two mixed edges *)
    SUBGOAL_THEN `E1:(real^N->bool)->bool = {}` SUBST1_TAC THENL
     [EXPAND_TAC "E1" THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `r:real^N->bool`;
                     `t:real^N->bool`] MOI_S3CA_PROPER_DIM) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `aff_dim (t:real^N->bool) <= &2` MP_TAC THENL
       [ASM_SIMP_TAC[]; INT_ARITH_TAC];
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_CLAUSES; UNION_EMPTY] THEN
    W(MP_TAC o PART_MATCH (lhs o rand) CARD_IMAGE_INJ o lhand o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SEGMENT_EQ] THEN
      MAP_EVERY X_GEN_TAC [`f1:real^N->bool`; `f2:real^N->bool`] THEN
      EXPAND_TAC "E2" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(f1:real^N->bool) IN barycentric_subdivision m /\ ~(f1 = {}) /\
                    (f2:real^N->bool) IN barycentric_subdivision m /\ ~(f2 = {})`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `moi_frn_vp m l (f1:real^N->bool)` THEN
        UNDISCH_TAC `moi_frn_vp m l (f2:real^N->bool)` THEN
        REWRITE_TAC[moi_frn_vp] THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(simplex_barycentre (f1:real^N->bool) = simplex_barycentre r) /\
                    ~(simplex_barycentre (f2:real^N->bool) = simplex_barycentre r)`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN DISCH_TAC THEN
        UNDISCH_TAC `~(f1:real^N->bool = r)` THEN UNDISCH_TAC `~(f2:real^N->bool = r)` THEN
        REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "binj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `{simplex_barycentre f1,simplex_barycentre (r:real^N->bool)} =
                   {simplex_barycentre f2,simplex_barycentre r}` THEN
      REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "E2" THEN
      MATCH_MP_TAC MOI_S3CA_MIXED_TRI THEN ASM_REWRITE_TAC[]]]);;

(* The frontier complex: the empty set, the barycentres of mixed simplices  *)
(* and the segments; its components are PL circles.                          *)

let MOI_S3CA_FR_CIRCLES = prove
 (`!(m:(real^N->bool)->bool) l.
     2 <= dimindex(:N) /\ FINITE m /\ simplicial_complex m /\ simplicial_subcomplex l m /\
     (!s. s IN barycentric_subdivision m ==> aff_dim s <= &2) /\
     (!e. moi_frn_vp m l e /\ aff_dim e = &1
          ==> CARD {t | t IN barycentric_subdivision m /\ aff_dim t = &2 /\ e SUBSET t} = 2)
     ==> FINITE (components (derived_frontier m l)) /\
         (!j. j IN components (derived_frontier m l) ==> pl_sphere 1 j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (barycentric_subdivision (m:(real^N->bool)->bool)) /\
                simplicial_complex (barycentric_subdivision m) /\
                moi_bar_complex (barycentric_subdivision m) /\
                simplicial_complex (barycentric_subdivision (barycentric_subdivision m))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX] THEN
    ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s t:real^N->bool. s IN barycentric_subdivision m /\ t IN barycentric_subdivision m /\
                       ~(s = {}) /\ ~(t = {}) /\ simplex_barycentre s = simplex_barycentre t
                       ==> s = t`
  (LABEL_TAC "binj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_BARYCENTRE_INJ THEN
    EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^N->bool. moi_frn_vp m l e /\ aff_dim e = &1
                  ==> ?tri. tri IN barycentric_subdivision m /\ e SUBSET tri /\ ~(e = tri)`
  (LABEL_TAC "up") THENL
   [X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `CARD {t:real^N->bool | t IN barycentric_subdivision m /\ aff_dim t = &2 /\
                                          e SUBSET t} = 2` ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `CARD:((real^N->bool)->bool)->num`)) (concl th))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~({t:real^N->bool | t IN barycentric_subdivision m /\ aff_dim t = &2 /\
                                       e SUBSET t} = {})` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `CARD {t:real^N->bool | t IN barycentric_subdivision m /\
                                       aff_dim t = &2 /\ e SUBSET t} = 2` THEN
      ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `tri:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `tri:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim (tri:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_S3CA_FRONTIER_SEGS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `SEGS = {segment[simplex_barycentre f,simplex_barycentre tri] | f tri |
                      moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\
                      f SUBSET tri /\ ~(f = (tri:real^N->bool))}` THEN
  ABBREV_TAC `KF = ({}:real^N->bool) INSERT
                   ({{simplex_barycentre r} | r | moi_frn_vp m l (r:real^N->bool)} UNION SEGS)` THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN KF <=>
       s = {} \/ (?r. moi_frn_vp m l r /\ s = {simplex_barycentre r}) \/
       (?f tri. moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\ f SUBSET tri /\
                ~(f = tri) /\ s = segment[simplex_barycentre f,simplex_barycentre tri])`
  (LABEL_TAC "KF") THENL
   [GEN_TAC THEN MAP_EVERY EXPAND_TAC ["KF"; "SEGS"] THEN
    REWRITE_TAC[IN_INSERT; IN_UNION; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f tri. moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\ f SUBSET tri /\
            ~(f = tri) ==> ~(simplex_barycentre f = simplex_barycentre (tri:real^N->bool))`
  (LABEL_TAC "fne") THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `~(f:real^N->bool = tri)` THEN REWRITE_TAC[] THEN
    USE_THEN "binj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_frn_vp m l (f:real^N->bool)` THEN UNDISCH_TAC `(f:real^N->bool) SUBSET tri` THEN
    REWRITE_TAC[moi_frn_vp] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the vertices lie on segments *)
  SUBGOAL_THEN `UNIONS SEGS = UNIONS (KF:(real^N->bool)->bool)` SUBST1_TAC THENL
   [EXPAND_TAC "KF" THEN REWRITE_TAC[UNIONS_INSERT; UNIONS_UNION; UNION_EMPTY] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> t = s UNION t`) THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; SING_SUBSET] THEN
    X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    EXPAND_TAC "SEGS" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision m` ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_frn_vp]; ALL_TAC] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
      MOI_S3CA_VP_DIM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [USE_THEN "up" (MP_TAC o SPEC `r:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `tri:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `segment[simplex_barycentre r,simplex_barycentre (tri:real^N->bool)]` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      MAP_EVERY EXISTS_TAC [`r:real^N->bool`; `tri:real^N->bool`] THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
        MOI_S3CA_VP_EDGE) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `segment[simplex_barycentre e,simplex_barycentre (r:real^N->bool)]` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `r:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `aff_dim (r:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4L_CM1_CIRCLES THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* a subcomplex of the second derived *)
    MATCH_MP_TAC MOI_S3CA_SUBSET_SC THEN
    EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "KF" (fun kf -> MP_TAC(EQ_MP (SPEC `s:real^N->bool` kf)
        (ASSUME `(s:real^N->bool) IN KF`))) THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [MOI_BAR_IN_SUBDIVISION] THENL
       [EXISTS_TAC `{}:(real^N->bool)->bool` THEN
        REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; moi_bar_chain; EMPTY_SUBSET;
                    FINITE_EMPTY; NOT_IN_EMPTY];
        EXISTS_TAC `{r:real^N->bool}` THEN
        REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING] THEN
        REWRITE_TAC[moi_bar_chain; SING_SUBSET; FINITE_SING; IN_SING] THEN
        UNDISCH_TAC `moi_frn_vp m l (r:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN
        SIMP_TAC[SUBSET_REFL] THEN SET_TAC[];
        EXISTS_TAC `{f:real^N->bool,tri}` THEN REWRITE_TAC[MOI_FN2_HULL2] THEN
        MATCH_MP_TAC MOI_FN2_CHAIN2 THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `moi_frn_vp m l (f:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN
        SIMP_TAC[] THEN SET_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN
      USE_THEN "KF" (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN(CONJUNCTS_THEN2 (REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[MOI_S3CA_FACES_SEG; FACE_OF_EMPTY] THEN
      ASM_MESON_TAC[MOI_FN2_VP_SUPER]];
    (* dimension at most 1 *)
    X_GEN_TAC `s:real^N->bool` THEN USE_THEN "KF" (fun th -> REWRITE_TAC[th]) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_SING; AFF_DIM_SEGMENT] THEN
    TRY COND_CASES_TAC THEN INT_ARITH_TAC;
    (* every vertex in exactly two edges *)
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "KF" (fun kf -> MP_TAC(EQ_MP (SPEC `{v:real^N}` kf)
      (ASSUME `{v:real^N} IN KF`))) THEN
    STRIP_TAC THENL
     [ASM_MESON_TAC[NOT_INSERT_EMPTY];
      SUBGOAL_THEN `v = simplex_barycentre (r:real^N->bool)` SUBST_ALL_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `{e | e IN KF /\ aff_dim e = &1 /\ simplex_barycentre (r:real^N->bool) IN e} =
        {e | e IN SEGS /\ simplex_barycentre r IN e}` SUBST1_TAC THENL
       [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
         [EXPAND_TAC "KF" THEN REWRITE_TAC[IN_INSERT; IN_UNION; IN_ELIM_THM] THEN
          STRIP_TAC THENL
           [UNDISCH_TAC `aff_dim (e:real^N->bool) = &1` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN
            MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN INT_ARITH_TAC;
            UNDISCH_TAC `aff_dim (e:real^N->bool) = &1` THEN ASM_REWRITE_TAC[AFF_DIM_SING] THEN
            MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN INT_ARITH_TAC;
            ASM_REWRITE_TAC[]];
          STRIP_TAC THEN REPEAT CONJ_TAC THENL
           [EXPAND_TAC "KF" THEN REWRITE_TAC[IN_INSERT; IN_UNION] THEN ASM_REWRITE_TAC[];
            UNDISCH_TAC `(e:real^N->bool) IN SEGS` THEN EXPAND_TAC "SEGS" THEN
            REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
            COND_CASES_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
            ASM_REWRITE_TAC[]]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
        MOI_S3CA_FR_DEGREE) THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `simplex_barycentre (f:real^N->bool) = simplex_barycentre (tri:real^N->bool)`
      MP_TAC THENL
       [MP_TAC(ISPECL [`simplex_barycentre (f:real^N->bool)`;
                       `simplex_barycentre (tri:real^N->bool)`] ENDS_IN_SEGMENT) THEN
        FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
          is_setenum(lhs(concl th)))) THEN
        REWRITE_TAC[IN_SING] THEN MESON_TAC[];
        MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN USE_THEN "fne" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* STEP4, part 5 (general): the complement of the second-derived            *)
(* neighbourhood retracts onto the complementary full subcomplex of the     *)
(* first derived c (simplices of c missing UNIONS l), along segments that  *)
(* stay outside UNIONS l and outside N.  In the barycentric coordinates mu  *)
(* of a simplex tau of c the map is x |-> (sum of the coordinates outside  *)
(* UNIONS l)^-1 times their part of x, from two simplexwise affine maps.   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_SIMPLEX_REP = prove
 (`!(c:(real^N->bool)->bool) tau.
     moi_bar_complex c /\ tau IN c
     ==> FINITE {v | v extreme_point_of tau} /\
         ~affine_dependent {v | v extreme_point_of tau} /\
         convex hull {v | v extreme_point_of tau} = tau /\
         (!v. v extreme_point_of tau ==> {v} IN c) /\
         !x. x IN tau <=>
             ?mu. (!v. v extreme_point_of tau ==> &0 <= mu v) /\
                  sum {v | v extreme_point_of tau} mu = &1 /\
                  vsum {v | v extreme_point_of tau} (\v. mu v % v) = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (tau:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
  SUBGOAL_THEN `FINITE {v:real^N | v extreme_point_of tau}` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex; FACE_OF_SING]; ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [SYM th]) o check
    (fun th -> is_eq(concl th) && rhs(concl th) = `tau:real^N->bool`)) THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM]);;

(* A simplexwise affine map evaluates convex combinations of the vertices.  *)

let MOI_S3CA_SW_EVAL = prove
 (`!(c:(real^N->bool)->bool) (h:real^N->real^M) phi tau mu.
     moi_bar_complex c /\
     (!s. s IN c ==> ?L y. linear L /\ !x. x IN s ==> h x = L x + y) /\
     (!v. {v} IN c ==> h v = phi v) /\
     tau IN c /\ (!v. v extreme_point_of tau ==> &0 <= mu v) /\
     sum {v | v extreme_point_of tau} mu = &1
     ==> h (vsum {v | v extreme_point_of tau} (\v. mu v % v)) =
         vsum {v | v extreme_point_of tau} (\v. mu v % phi v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tau:real^N->bool`] MOI_S3CA_SIMPLEX_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
    (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rep"))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tau:real^N->bool` o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `linear:(real^N->real^M)->bool`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^M` (X_CHOOSE_THEN `y:real^M` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `vsum {v | v extreme_point_of tau} (\v. mu v % v) IN (tau:real^N->bool)`
  ASSUME_TAC THENL
   [USE_THEN "rep" (fun th -> REWRITE_TAC[th]) THEN EXISTS_TAC `mu:real^N->real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MATCH_MP (ASSUME
    `!x:real^N. x IN tau ==> (h:real^N->real^M) x = L x + y`) (ASSUME
    `vsum {v | v extreme_point_of tau} (\v. mu v % v) IN (tau:real^N->bool)`)] THEN
  MP_TAC(ISPECL [`L:real^N->real^M`; `y:real^M`; `{v:real^N | v extreme_point_of tau}`;
                 `mu:real^N->real`; `\v:real^N. v`] MOI_FRN_AFFINE_VSUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN
  DISCH_TAC THEN AP_TERM_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN tau` ASSUME_TAC THENL
   [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* The two simplexwise affine coordinate maps: h1 = the sum of the          *)
(* coordinates at vertices in UNIONS l, h2 = the part of the point at the   *)
(* other vertices.                                                           *)

let MOI_S3CA_CR_MAPS = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> ?(h1:real^N->real^1) (h2:real^N->real^N).
           h1 continuous_on UNIONS t /\ h2 continuous_on UNIONS t /\
           (!tau mu. tau IN barycentric_subdivision t /\
                     (!v. v extreme_point_of tau ==> &0 <= mu v) /\
                     sum {v | v extreme_point_of tau} mu = &1
                     ==> drop (h1 (vsum {v | v extreme_point_of tau} (\v. mu v % v))) =
                         sum {v | v extreme_point_of tau}
                             (\v. if v IN UNIONS l then mu v else &0) /\
                         h2 (vsum {v | v extreme_point_of tau} (\v. mu v % v)) =
                         vsum {v | v extreme_point_of tau}
                              (\v. (if v IN UNIONS l then &0 else mu v) % v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision (t:(real^N->bool)->bool)) /\
                moi_bar_complex (barycentric_subdivision t) /\
                UNIONS (barycentric_subdivision t) = UNIONS t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF; UNIONS_BARYCENTRIC_SUBDIVISION] THEN
    ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `\v:real^N. lift(if v IN UNIONS l then &1 else &0)`]
    MOI_FRN_SIMPLEXWISE_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^N->real^1` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `\v:real^N. if v IN UNIONS l then vec 0 else v`]
    MOI_FRN_SIMPLEXWISE_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`h1:real^N->real^1`; `h2:real^N->real^N`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `h1:real^N->real^1`]
      MOI_FRN_SIMPLEXWISE_PL) THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `h2:real^N->real^N`]
      MOI_FRN_SIMPLEXWISE_PL) THEN
    ASM_SIMP_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `tau:real^N->bool`]
      MOI_S3CA_SIMPLEX_REP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `h1:real^N->real^1`;
                     `\v:real^N. lift(if v IN UNIONS l then &1 else &0)`;
                     `tau:real^N->bool`; `mu:real^N->real`] MOI_S3CA_SW_EVAL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      ASM_SIMP_TAC[DROP_VSUM; o_DEF; DROP_CMUL; LIFT_DROP] THEN
      MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
      MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `h2:real^N->real^N`;
                     `\v:real^N. if v IN UNIONS l then vec 0 else v`;
                     `tau:real^N->bool`; `mu:real^N->real`] MOI_S3CA_SW_EVAL) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[] THEN COND_CASES_TAC THEN VECTOR_ARITH_TAC]]);;
(* The hull of a set of vertices of a simplex of a complex is a simplex of  *)
(* the complex with exactly those vertices.                                  *)

let MOI_S3CA_SUBFACE = prove
 (`!(c:(real^N->bool)->bool) tau C.
     moi_bar_complex c /\ tau IN c /\ C SUBSET {v | v extreme_point_of tau}
     ==> convex hull C IN c /\ convex hull C SUBSET tau /\ FINITE C /\
         {v | v extreme_point_of convex hull C} = C`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tau:real^N->bool`] MOI_S3CA_SIMPLEX_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  SUBGOAL_THEN `~affine_dependent (C:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (C:real^N->bool) face_of tau` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `convex hull {v | v extreme_point_of tau} = (tau:real^N->bool)`)) THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `C:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
    ASM_MESON_TAC[FINITE_SUBSET];
    ASM_SIMP_TAC[EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT]]);;

(* Pointwise facts in barycentric coordinates mu of a point x of a simplex  *)
(* tau of the first derived, x not in UNIONS l: the weight lam of the       *)
(* vertices outside UNIONS l is positive, equals 1 - h1 x, and the map is   *)
(* the normalised outside part.                                              *)

let MOI_S3CA_CR_POINT_A = prove
 (`!(t:(real^N->bool)->bool) l (h1:real^N->real^1) (h2:real^N->real^N) tau mu.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!tau mu. tau IN barycentric_subdivision t /\
               (!v. v extreme_point_of tau ==> &0 <= mu v) /\
               sum {v | v extreme_point_of tau} mu = &1
               ==> drop (h1 (vsum {v | v extreme_point_of tau} (\v. mu v % v))) =
                   sum {v | v extreme_point_of tau}
                       (\v. if v IN UNIONS l then mu v else &0) /\
                   h2 (vsum {v | v extreme_point_of tau} (\v. mu v % v)) =
                   vsum {v | v extreme_point_of tau}
                        (\v. (if v IN UNIONS l then &0 else mu v) % v)) /\
     tau IN barycentric_subdivision t /\
     (!v. v extreme_point_of tau ==> &0 <= mu v) /\
     sum {v | v extreme_point_of tau} mu = &1 /\
     ~(vsum {v | v extreme_point_of tau} (\v. mu v % v) IN UNIONS l)
     ==> &0 < sum {v | v extreme_point_of tau} (\v. if v IN UNIONS l then &0 else mu v) /\
         &1 - drop (h1 (vsum {v | v extreme_point_of tau} (\v. mu v % v))) =
         sum {v | v extreme_point_of tau} (\v. if v IN UNIONS l then &0 else mu v) /\
         inv(&1 - drop (h1 (vsum {v | v extreme_point_of tau} (\v. mu v % v)))) %
           h2 (vsum {v | v extreme_point_of tau} (\v. mu v % v)) =
         vsum {v | v extreme_point_of tau}
              (\v. ((if v IN UNIONS l then &0 else mu v) /
                    sum {v | v extreme_point_of tau}
                        (\v. if v IN UNIONS l then &0 else mu v)) % v)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (MP_TAC o SPECL [`tau:real^N->bool`; `mu:real^N->real`])
      STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (t:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `tau:real^N->bool`]
    MOI_S3CA_SIMPLEX_REP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `V = {v:real^N | v extreme_point_of tau}` THEN
  ABBREV_TAC `lam = sum V (\v:real^N. if v IN UNIONS l then &0 else mu v)` THEN
  SUBGOAL_THEN `sum V (\v:real^N. if v IN UNIONS l then mu v else &0) + lam = &1`
  ASSUME_TAC THENL
   [EXPAND_TAC "lam" THEN ASM_SIMP_TAC[GSYM SUM_ADD] THEN
    GEN_REWRITE_TAC RAND_CONV [SYM(ASSUME `sum V (mu:real^N->real) = &1`)] THEN
    MATCH_MP_TAC SUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < lam` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE] THEN CONJ_TAC THENL
     [EXPAND_TAC "lam" THEN MATCH_MP_TAC SUM_POS_LE THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL];
      DISCH_THEN(ASSUME_TAC o SYM) THEN
      UNDISCH_TAC `~(vsum V (\v. mu v % v) IN UNIONS (l:(real^N->bool)->bool))` THEN
      REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\v:real^N. if v IN UNIONS l then &0 else mu v`; `V:real^N->bool`]
        SUM_POS_EQ_0) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL];
        DISCH_TAC] THEN
      ABBREV_TAC `C = {v:real^N | v IN V /\ v IN UNIONS l}` THEN
      MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `tau:real^N->bool`;
                     `C:real^N->bool`] MOI_S3CA_SUBFACE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN SET_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `convex hull C SUBSET UNIONS (l:(real^N->bool)->bool)` MP_TAC THENL
       [MATCH_MP_TAC MOI_S3CA_VERTICES_IN THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(w:real^N) IN C` MP_TAC THENL
         [UNDISCH_TAC `{v:real^N | v extreme_point_of convex hull C} = C` THEN
          REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
          SUBST1_TAC(SYM(ASSUME `{v:real^N | v IN V /\ v IN UNIONS l} = C`)) THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `(x:real^N) IN s ==> s SUBSET t ==> x IN t`) THEN
      ASM_SIMP_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
      EXISTS_TAC `mu:real^N->real` THEN REPEAT CONJ_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `{v:real^N | v IN V /\ v IN UNIONS l} = C`)) THEN REWRITE_TAC[IN_ELIM_THM] THEN
        UNDISCH_TAC `!v:real^N. v extreme_point_of tau ==> &0 <= mu v` THEN
        EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
        SUBGOAL_THEN `sum C (mu:real^N->real) = sum V (\v. if v IN UNIONS l then mu v else &0)`
        SUBST1_TAC THENL
         [SUBST1_TAC(SYM(ASSUME `{v:real^N | v IN V /\ v IN UNIONS l} = C`)) THEN REWRITE_TAC[SUM_RESTRICT_SET]; ALL_TAC] THEN
        ASM_REAL_ARITH_TAC;
        CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN CONJ_TAC THENL
         [SUBST1_TAC(SYM(ASSUME `{v:real^N | v IN V /\ v IN UNIONS l} = C`)) THEN SET_TAC[]; ALL_TAC] THEN
        X_GEN_TAC `w:real^N` THEN
        SUBST1_TAC(SYM(ASSUME `{v:real^N | v IN V /\ v IN UNIONS l} = C`)) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        SUBGOAL_THEN `~((w:real^N) IN UNIONS l)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(mu:real^N->real) w = &0` (fun th -> REWRITE_TAC[th; VECTOR_MUL_LZERO]) THEN
        UNDISCH_TAC `!x:real^N. x IN V ==> (if x IN UNIONS l then &0 else mu x) = &0` THEN
        DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - sum V (\v:real^N. if v IN UNIONS l then mu v else &0) = lam`
  SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[GSYM VSUM_LMUL; VECTOR_MUL_ASSOC] THEN
  MATCH_MP_TAC VSUM_EQ THEN GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[real_div] THEN REAL_ARITH_TAC);;

(* h1 is 1 on UNIONS l; on the complementary full subcomplex (simplices of *)
(* the first derived missing UNIONS l) the map is the identity and N is     *)
(* avoided.                                                                  *)

let MOI_S3CA_CR_ONE_ON_L = prove
 (`!(t:(real^N->bool)->bool) l (h1:real^N->real^1) (h2:real^N->real^N) y.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!tau mu. tau IN barycentric_subdivision t /\
               (!v. v extreme_point_of tau ==> &0 <= mu v) /\
               sum {v | v extreme_point_of tau} mu = &1
               ==> drop (h1 (vsum {v | v extreme_point_of tau} (\v. mu v % v))) =
                   sum {v | v extreme_point_of tau}
                       (\v. if v IN UNIONS l then mu v else &0) /\
                   h2 (vsum {v | v extreme_point_of tau} (\v. mu v % v)) =
                   vsum {v | v extreme_point_of tau}
                        (\v. (if v IN UNIONS l then &0 else mu v) % v)) /\
     y IN UNIONS l
     ==> drop(h1 y) = &1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H") ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?sg:real^N->bool. sg IN barycentric_subdivision l /\ y IN sg`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^N) IN UNIONS l` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sg:real^N->bool) IN barycentric_subdivision t /\ sg SUBSET UNIONS l`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)`)) THEN
      MATCH_MP_TAC(SET_RULE `(s:real^N->bool) IN l ==> s SUBSET UNIONS l`) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `sg:real^N->bool`]
    MOI_S3CA_SIMPLEX_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real^N->real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `y:real^N`)) THEN
  USE_THEN "H" (MP_TAC o SPECL [`sg:real^N->bool`; `mu:real^N->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(SUBST1_TAC o CONJUNCT1)] THEN
  GEN_REWRITE_TAC RAND_CONV [SYM(ASSUME `sum {v | v extreme_point_of sg} (mu:real^N->real) = &1`)] THEN
  MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `v:real^N` THEN
  DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS l` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[extreme_point_of; SUBSET]);;

let MOI_S3CA_CR_CB = prove
 (`!(t:(real^N->bool)->bool) l (h1:real^N->real^1) (h2:real^N->real^N) sg x.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!tau mu. tau IN barycentric_subdivision t /\
               (!v. v extreme_point_of tau ==> &0 <= mu v) /\
               sum {v | v extreme_point_of tau} mu = &1
               ==> drop (h1 (vsum {v | v extreme_point_of tau} (\v. mu v % v))) =
                   sum {v | v extreme_point_of tau}
                       (\v. if v IN UNIONS l then mu v else &0) /\
                   h2 (vsum {v | v extreme_point_of tau} (\v. mu v % v)) =
                   vsum {v | v extreme_point_of tau}
                        (\v. (if v IN UNIONS l then &0 else mu v) % v)) /\
     sg IN barycentric_subdivision t /\ sg INTER UNIONS l = {} /\ x IN sg
     ==> ~(x IN derived_nbhd t l) /\ inv(&1 - drop(h1 x)) % h2 x = x`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (t:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `sg:real^N->bool`]
    MOI_S3CA_SIMPLEX_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real^N->real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `x:real^N`)) THEN
  SUBGOAL_THEN `!v:real^N. v extreme_point_of sg ==> ~(v IN UNIONS l)` ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^N) IN sg` MP_TAC THENL
     [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
    UNDISCH_TAC `sg INTER UNIONS (l:(real^N->bool)->bool) = {}` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `sg:real^N->bool`;
                   `mu:real^N->real`] MOI_FRN_NBHD_IMP_MAX) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    USE_THEN "H" (MP_TAC o SPECL [`sg:real^N->bool`; `mu:real^N->real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC) THEN
    SUBGOAL_THEN `sum {v | v extreme_point_of sg}
                      (\v:real^N. if v IN UNIONS l then mu v else &0) = &0`
    SUBST1_TAC THENL
     [MATCH_MP_TAC SUM_EQ_0 THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_RZERO; REAL_INV_1; VECTOR_MUL_LID] THEN
    MATCH_MP_TAC VSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]]);;

(* The image point lies in the complementary full subcomplex, and the       *)
(* segment to it stays outside UNIONS l (h1 decreases along it).            *)

let MOI_S3CA_CR_POINT_B = prove
 (`!(t:(real^N->bool)->bool) l (h1:real^N->real^1) (h2:real^N->real^N) tau mu.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!tau mu. tau IN barycentric_subdivision t /\
               (!v. v extreme_point_of tau ==> &0 <= mu v) /\
               sum {v | v extreme_point_of tau} mu = &1
               ==> drop (h1 (vsum {v | v extreme_point_of tau} (\v. mu v % v))) =
                   sum {v | v extreme_point_of tau}
                       (\v. if v IN UNIONS l then mu v else &0) /\
                   h2 (vsum {v | v extreme_point_of tau} (\v. mu v % v)) =
                   vsum {v | v extreme_point_of tau}
                        (\v. (if v IN UNIONS l then &0 else mu v) % v)) /\
     tau IN barycentric_subdivision t /\
     (!v. v extreme_point_of tau ==> &0 <= mu v) /\
     sum {v | v extreme_point_of tau} mu = &1 /\
     ~(vsum {v | v extreme_point_of tau} (\v. mu v % v) IN UNIONS l)
     ==> inv(&1 - drop (h1 (vsum {v | v extreme_point_of tau} (\v. mu v % v)))) %
           h2 (vsum {v | v extreme_point_of tau} (\v. mu v % v))
           IN UNIONS {r | r IN barycentric_subdivision t /\ r INTER UNIONS l = {}} /\
         segment[vsum {v | v extreme_point_of tau} (\v. mu v % v),
                 inv(&1 - drop (h1 (vsum {v | v extreme_point_of tau} (\v. mu v % v)))) %
                 h2 (vsum {v | v extreme_point_of tau} (\v. mu v % v))]
           SUBSET UNIONS t DIFF UNIONS l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> MP_TAC th THEN
    MP_TAC(MATCH_MP MOI_S3CA_CR_POINT_A th)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (t:(real^N->bool)->bool)) /\
                UNIONS (barycentric_subdivision t) = UNIONS t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION] THEN
    ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `tau:real^N->bool`]
    MOI_S3CA_SIMPLEX_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rep"))))) THEN
  USE_THEN "H" (MP_TAC o SPECL [`tau:real^N->bool`; `mu:real^N->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  ABBREV_TAC `V = {v:real^N | v extreme_point_of tau}` THEN
  ABBREV_TAC `lam = sum V (\v:real^N. if v IN UNIONS l then &0 else mu v)` THEN
  ABBREV_TAC `x = vsum V (\v:real^N. mu v % v)` THEN
  UNDISCH_TAC `inv(&1 - drop((h1:real^N->real^1) x)) % (h2:real^N->real^N) x =
               vsum V (\v:real^N. ((if v IN UNIONS l then &0 else mu v) / lam) % v)` THEN
  DISCH_THEN SUBST1_TAC THEN
  ABBREV_TAC `zx = vsum V (\v:real^N. ((if v IN UNIONS l then &0 else mu v) / lam) % v)` THEN
  ABBREV_TAC `C = {v:real^N | v IN V /\ ~(v IN UNIONS l)}` THEN
  SUBGOAL_THEN `!v:real^N. v IN V ==> &0 <= mu v` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  (* the weights of zx *)
  SUBGOAL_THEN `sum V (\v:real^N. (if v IN UNIONS l then &0 else mu v) / lam) = &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_div; SUM_RMUL] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. v IN V ==> &0 <= (if v IN UNIONS l then &0 else mu v) / lam`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
     [COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* the face spanned by the vertices outside UNIONS l *)
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `tau:real^N->bool`;
                 `C:real^N->bool`] MOI_S3CA_SUBFACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXPAND_TAC "C" THEN SET_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `!w:real^N. w IN C <=> w IN V /\ ~(w IN UNIONS l)` (LABEL_TAC "Cdef") THENL
   [GEN_TAC THEN
    SUBST1_TAC(SYM(ASSUME `{v:real^N | v IN V /\ ~(v IN UNIONS l)} = C`)) THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull C INTER UNIONS (l:(real^N->bool)->bool) = {}` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `convex hull C:real^N->bool`] MOI_S3CA_MEETS_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(w:real^N) IN C` MP_TAC THENL
     [UNDISCH_TAC `{v:real^N | v extreme_point_of convex hull C} = C` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      USE_THEN "Cdef" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(zx:real^N) IN convex hull C` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
    EXISTS_TAC `\v:real^N. (if v IN UNIONS l then &0 else mu v) / lam` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "Cdef" (fun th -> REWRITE_TAC[th]) THEN ASM_SIMP_TAC[];
      GEN_REWRITE_TAC RAND_CONV [SYM(ASSUME
        `sum V (\v:real^N. (if v IN UNIONS l then &0 else mu v) / lam) = &1`)] THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN
      USE_THEN "Cdef" (fun th -> REWRITE_TAC[SUBSET; th]) THEN
      CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(w:real^N) IN UNIONS l` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[]; REWRITE_TAC[real_div; REAL_MUL_LZERO]];
      EXPAND_TAC "zx" THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
      USE_THEN "Cdef" (fun th -> REWRITE_TAC[SUBSET; th]) THEN
      CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(w:real^N) IN UNIONS l` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[]; REWRITE_TAC[real_div; REAL_MUL_LZERO; VECTOR_MUL_LZERO]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!x:real^N s f. s IN f /\ x IN s ==> x IN UNIONS f`) THEN
    EXISTS_TAC `convex hull C:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_SEGMENT; IN_DIFF] THEN X_GEN_TAC `p:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  ABBREV_TAC `nu = \v:real^N. (&1 - s) * mu v + s * ((if v IN UNIONS l then &0 else mu v) / lam)` THEN
  SUBGOAL_THEN `!v:real^N. v IN V ==> &0 <= nu v` ASSUME_TAC THENL
   [EXPAND_TAC "nu" THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum V (nu:real^N->real) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "nu" THEN ASM_SIMP_TAC[SUM_ADD; SUM_LMUL] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `vsum V (\v:real^N. nu v % v) = p` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `(&1 - s) % x + s % zx = (p:real^N)`)) THEN
    SUBST1_TAC(SYM(ASSUME `vsum V (\v:real^N. mu v % v) = x`)) THEN
    EXPAND_TAC "zx" THEN EXPAND_TAC "nu" THEN
    ASM_SIMP_TAC[VECTOR_ADD_RDISTRIB; GSYM VECTOR_MUL_ASSOC; VSUM_ADD; VSUM_LMUL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N) IN tau` ASSUME_TAC THENL
   [USE_THEN "rep" (fun th -> REWRITE_TAC[th]) THEN EXISTS_TAC `nu:real^N->real` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!v:real^N. v IN V ==> &0 <= nu v` THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(p:real^N) IN tau` THEN
    UNDISCH_TAC `tau IN barycentric_subdivision (t:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision t) = UNIONS (t:(real^N->bool)->bool)` THEN
    SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h1:real^N->real^1`;
                 `h2:real^N->real^N`; `p:real^N`] MOI_S3CA_CR_ONE_ON_L) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "H" (MP_TAC o SPECL [`tau:real^N->bool`; `nu:real^N->real`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!v:real^N. v IN V ==> &0 <= nu v` THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `sum V (\v:real^N. if v IN UNIONS l then nu v else &0) =
                (&1 - s) * sum V (\v. if v IN UNIONS l then mu v else &0)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL] THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real^N` THEN
    DISCH_TAC THEN EXPAND_TAC "nu" THEN REWRITE_TAC[] THEN COND_CASES_TAC THEN
    REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum V (\v:real^N. if v IN UNIONS l then mu v else &0) = &1 - lam /\
                &0 <= sum V (\v:real^N. if v IN UNIONS l then mu v else &0)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUM_POS_LE THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= s * (&1 - lam)` MP_TAC THENL
   [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

(* Outside N the segment to the image point stays outside N: along it the  *)
(* coordinates at vertices in UNIONS l shrink and the largest coordinate,  *)
(* which is at a vertex outside UNIONS l, does not decrease.               *)

let MOI_S3CA_CR_POINT_C = prove
 (`!(t:(real^N->bool)->bool) l (h1:real^N->real^1) (h2:real^N->real^N) tau mu.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!tau mu. tau IN barycentric_subdivision t /\
               (!v. v extreme_point_of tau ==> &0 <= mu v) /\
               sum {v | v extreme_point_of tau} mu = &1
               ==> drop (h1 (vsum {v | v extreme_point_of tau} (\v. mu v % v))) =
                   sum {v | v extreme_point_of tau}
                       (\v. if v IN UNIONS l then mu v else &0) /\
                   h2 (vsum {v | v extreme_point_of tau} (\v. mu v % v)) =
                   vsum {v | v extreme_point_of tau}
                        (\v. (if v IN UNIONS l then &0 else mu v) % v)) /\
     tau IN barycentric_subdivision t /\
     (!v. v extreme_point_of tau ==> &0 <= mu v) /\
     sum {v | v extreme_point_of tau} mu = &1 /\
     ~(vsum {v | v extreme_point_of tau} (\v. mu v % v) IN derived_nbhd t l)
     ==> segment[vsum {v | v extreme_point_of tau} (\v. mu v % v),
                 inv(&1 - drop (h1 (vsum {v | v extreme_point_of tau} (\v. mu v % v)))) %
                 h2 (vsum {v | v extreme_point_of tau} (\v. mu v % v))]
           SUBSET UNIONS t DIFF derived_nbhd t l`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "H") STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(vsum {v | v extreme_point_of tau} (\v. mu v % v) IN
                  UNIONS (l:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
      MOI_FTA_GRAPH_IN_NBHD) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h1:real^N->real^1`;
                 `h2:real^N->real^N`; `tau:real^N->bool`; `mu:real^N->real`]
    MOI_S3CA_CR_POINT_A) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h1:real^N->real^1`;
                 `h2:real^N->real^N`; `tau:real^N->bool`; `mu:real^N->real`]
    MOI_S3CA_CR_POINT_B) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT2)] THEN
  USE_THEN "H" (MP_TAC o SPECL [`tau:real^N->bool`; `mu:real^N->real`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (t:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `tau:real^N->bool`]
    MOI_S3CA_SIMPLEX_REP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rep"))))) THEN
  ABBREV_TAC `V = {v:real^N | v extreme_point_of tau}` THEN
  ABBREV_TAC `lam = sum V (\v:real^N. if v IN UNIONS l then &0 else mu v)` THEN
  ABBREV_TAC `x = vsum V (\v:real^N. mu v % v)` THEN
  UNDISCH_TAC `inv(&1 - drop((h1:real^N->real^1) x)) % (h2:real^N->real^N) x =
               vsum V (\v:real^N. ((if v IN UNIONS l then &0 else mu v) / lam) % v)` THEN
  DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]) THEN REWRITE_TAC[th]) THEN
  ABBREV_TAC `zx = vsum V (\v:real^N. ((if v IN UNIONS l then &0 else mu v) / lam) % v)` THEN
  SUBGOAL_THEN `!v:real^N. v IN V ==> &0 <= mu v` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `sum V (\v:real^N. (if v IN UNIONS l then &0 else mu v) / lam) = &1`
  ASSUME_TAC THENL
   [REWRITE_TAC[real_div; SUM_RMUL] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_MUL_RINV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lam <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= sum V (\v:real^N. if v IN UNIONS l then mu v else &0)` MP_TAC THENL
     [MATCH_MP_TAC SUM_POS_LE THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_SIMP_TAC[REAL_LE_REFL];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* a vertex where mu is largest; it is outside UNIONS l *)
  SUBGOAL_THEN `?w:real^N. w IN V /\ !v. v IN V ==> mu v <= mu w` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (mu:real^N->real) V` SUP_FINITE) THEN
    ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `sum V (mu:real^N->real) = &1` THEN
      ASM_REWRITE_TAC[SUM_CLAUSES] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC `w:real^N` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!b:real^N. b IN V /\ b IN UNIONS l ==> mu b < mu w` ASSUME_TAC THENL
   [X_GEN_TAC `b:real^N` THEN STRIP_TAC THEN REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((x:real^N) IN derived_nbhd t l)` THEN REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `vsum V (\v:real^N. mu v % v) = x`)) THEN
    EXPAND_TAC "V" THEN MATCH_MP_TAC MOI_FRN_MAX_IMP_NBHD THEN EXISTS_TAC `b:real^N` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(b:real^N) IN V` THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `(mu:real^N->real) w` THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXPAND_TAC "V" THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((w:real^N) IN UNIONS l)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `(<):real->real->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_SEGMENT; IN_DIFF] THEN X_GEN_TAC `p:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  SUBGOAL_THEN `(p:real^N) IN UNIONS t` ASSUME_TAC THENL
   [UNDISCH_TAC `segment[x:real^N,zx] SUBSET UNIONS t DIFF UNIONS l` THEN
    REWRITE_TAC[SUBSET; IN_SEGMENT; IN_DIFF] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^N`) THEN ANTS_TAC THENL
     [EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `nu = \v:real^N. (&1 - s) * mu v + s * ((if v IN UNIONS l then &0 else mu v) / lam)` THEN
  SUBGOAL_THEN `!v:real^N. v IN V ==> &0 <= nu v` ASSUME_TAC THENL
   [EXPAND_TAC "nu" THEN REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[] THEN TRY(MATCH_MP_TAC REAL_LE_DIV) THEN
    TRY(COND_CASES_TAC) THEN ASM_SIMP_TAC[REAL_LE_REFL] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum V (nu:real^N->real) = &1` ASSUME_TAC THENL
   [EXPAND_TAC "nu" THEN ASM_SIMP_TAC[SUM_ADD; SUM_LMUL] THEN ASM_REWRITE_TAC[] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `vsum V (\v:real^N. nu v % v) = p` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `(&1 - s) % x + s % zx = (p:real^N)`)) THEN
    SUBST1_TAC(SYM(ASSUME `vsum V (\v:real^N. mu v % v) = x`)) THEN
    EXPAND_TAC "zx" THEN EXPAND_TAC "nu" THEN
    ASM_SIMP_TAC[VECTOR_ADD_RDISTRIB; GSYM VECTOR_MUL_ASSOC; VSUM_ADD; VSUM_LMUL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `tau:real^N->bool`;
                 `nu:real^N->real`] MOI_FRN_NBHD_IMP_MAX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!v:real^N. v IN V ==> &0 <= nu v` THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(a:real^N) IN V /\ (w:real^N) extreme_point_of tau` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^N) IN V` THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(nu:real^N->real) w <= nu a` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "nu" THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[real_div; REAL_MUL_LZERO; REAL_MUL_RZERO; REAL_ADD_RID] THEN
  SUBGOAL_THEN `(mu:real^N->real) a < mu w /\ &0 <= mu a /\ &0 <= mu w` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(mu:real^N->real) w <= mu w * inv lam` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM real_div] THEN ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s * (mu:real^N->real) w <= s * (mu w * inv lam) /\ &0 <= s * mu a`
  MP_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC REAL_LE_LMUL; MATCH_MP_TAC REAL_LE_MUL] THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

(* The retraction (general form): for a locally finite complex t and a      *)
(* subcomplex l there is a continuous z on UNIONS t DIFF UNIONS l into the *)
(* complementary full subcomplex of the first derived (its union is outside *)
(* N), the identity there, with segments [x,z x] outside UNIONS l, and      *)
(* outside N when x is.                                                      *)

let MOI_S3CA_COMPLEMENT_RETRACT = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> ?z:real^N->real^N.
           z continuous_on (UNIONS t DIFF UNIONS l) /\
           (!x. x IN UNIONS t DIFF UNIONS l
                ==> z x IN UNIONS {r | r IN barycentric_subdivision t /\
                                       r INTER UNIONS l = {}} /\
                    segment[x,z x] SUBSET UNIONS t DIFF UNIONS l) /\
           (!x. x IN UNIONS {r | r IN barycentric_subdivision t /\ r INTER UNIONS l = {}}
                ==> z x = x) /\
           UNIONS {r | r IN barycentric_subdivision t /\ r INTER UNIONS l = {}} SUBSET
             UNIONS t DIFF derived_nbhd t l /\
           (!x. x IN UNIONS t DIFF derived_nbhd t l
                ==> segment[x,z x] SUBSET UNIONS t DIFF derived_nbhd t l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_S3CA_CR_MAPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h1:real^N->real^1` (X_CHOOSE_THEN `h2:real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H"))))) THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (t:(real^N->bool)->bool)) /\
                UNIONS (barycentric_subdivision t) = UNIONS t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[UNIONS_BARYCENTRIC_SUBDIVISION] THEN
    ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN UNIONS t
       ==> ?tau mu. tau IN barycentric_subdivision t /\
                    (!v. v extreme_point_of tau ==> &0 <= mu v) /\
                    sum {v | v extreme_point_of tau} mu = &1 /\
                    vsum {v | v extreme_point_of tau} (\v. mu v % v) = x`
  (LABEL_TAC "coords") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?tau:real^N->bool. tau IN barycentric_subdivision t /\ x IN tau`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN UNIONS t` THEN
      SUBST1_TAC(SYM(ASSUME
        `UNIONS (barycentric_subdivision t) = UNIONS (t:(real^N->bool)->bool)`)) THEN
      REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `tau:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `tau:real^N->bool`]
      MOI_S3CA_SIMPLEX_REP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN UNIONS t DIFF UNIONS l ==> &0 < &1 - drop(h1 x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    USE_THEN "coords" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `tau:real^N->bool` (X_CHOOSE_THEN `mu:real^N->real`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `x:real^N`)) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h1:real^N->real^1`;
                   `h2:real^N->real^N`; `tau:real^N->bool`; `mu:real^N->real`]
      MOI_S3CA_CR_POINT_A) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\x:real^N. inv(&1 - drop((h1:real^N->real^1) x)) % (h2:real^N->real^N) x` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* continuity *)
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN CONJ_TAC THENL
     [SUBGOAL_THEN `lift o (\x:real^N. inv(&1 - drop((h1:real^N->real^1) x))) =
                    lift o inv o (\x. &1 - drop(h1 x))` SUBST1_TAC THENL
       [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
      MATCH_MP_TAC CONTINUOUS_ON_INV THEN CONJ_TAC THENL
       [REWRITE_TAC[o_DEF; LIFT_SUB; LIFT_DROP; LIFT_NUM] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUB THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `UNIONS t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `(<):real->real->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS t:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    (* into the complementary subcomplex, segment outside UNIONS l *)
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "coords" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `tau:real^N->bool` (X_CHOOSE_THEN `mu:real^N->real`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `x:real^N`)) THEN
    MATCH_MP_TAC MOI_S3CA_CR_POINT_B THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    (* the identity on the complementary subcomplex *)
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h1:real^N->real^1`;
                   `h2:real^N->real^N`; `sg:real^N->bool`; `x:real^N`] MOI_S3CA_CR_CB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    (* the complementary subcomplex misses N *)
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME
        `UNIONS (barycentric_subdivision t) = UNIONS (t:(real^N->bool)->bool)`)) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `sg:real^N->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `h1:real^N->real^1`;
                     `h2:real^N->real^N`; `sg:real^N->bool`; `x:real^N`] MOI_S3CA_CR_CB) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    (* segments outside N *)
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "coords" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `tau:real^N->bool` (X_CHOOSE_THEN `mu:real^N->real`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `x:real^N`)) THEN
    MATCH_MP_TAC MOI_S3CA_CR_POINT_C THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* Hence the complement of N is connected when that of UNIONS l is.          *)

let MOI_S3CA_COMPLEMENT_CONNECTED = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     connected (UNIONS t DIFF UNIONS l)
     ==> connected (UNIONS t DIFF derived_nbhd t l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_S3CA_COMPLEMENT_RETRACT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_GRAPH_IN_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `Z = IMAGE (z:real^N->real^N) (UNIONS t DIFF UNIONS l)` THEN
  SUBGOAL_THEN `connected (Z:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Z:real^N->bool) SUBSET UNIONS t DIFF derived_nbhd t l` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      is_binary "SUBSET" (concl th) &&
      rand(concl th) = `UNIONS t DIFF derived_nbhd t (l:(real^N->bool)->bool)`)) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `UNIONS t DIFF derived_nbhd t (l:(real^N->bool)->bool) = {}` THEN
  ASM_REWRITE_TAC[CONNECTED_EMPTY] THEN
  SUBGOAL_THEN
   `UNIONS t DIFF derived_nbhd t (l:(real^N->bool)->bool) =
    UNIONS {Z UNION segment[x,(z:real^N->real^N) x] | x | x IN UNIONS t DIFF derived_nbhd t l}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_TAC THEN EXISTS_TAC `Z UNION segment[x:real^N,z x]` THEN
      CONJ_TAC THENL [EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; UNION_SUBSET] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC CONNECTED_UNION THEN
    ASM_REWRITE_TAC[CONNECTED_SEGMENT] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(z:real^N->real^N) x` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    EXPAND_TAC "Z" THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
    SUBGOAL_THEN `~(Z:real^N->bool = {})` MP_TAC THENL
     [EXPAND_TAC "Z" THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN EXISTS_TAC `y:real^N` THEN
    REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM; IN_UNION] THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* STEP4, part 6: planar facts.  The square annulus minus its inner end is   *)
(* connected (four convex strips), hence so is a PL annulus minus its first  *)
(* end, and a PL 2-cell minus a PL 2-cell in its interior (MOI_S5C_ANN2).    *)
(* A compact planar set whose frontier is a PL circle and whose interior is  *)
(* nonempty is the circle with its inside.                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_ANN_MINUS_INNER = prove
 (`connected ((interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
               interval(--vector[&1;&1]:real^2,vector[&1;&1])) DIFF
              relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`,
  SIMP_TAC[MOI_FN2_RF_SQUARE; REAL_LT_01] THEN
  ABBREV_TAC `B = interval[--vector[&2;&2]:real^2,vector[&2;&2]]` THEN
  SUBGOAL_THEN
   `(B DIFF interval(--vector[&1;&1]:real^2,vector[&1;&1])) DIFF
    (interval[--vector[&1;&1]:real^2,vector[&1;&1]] DIFF
     interval(--vector[&1;&1]:real^2,vector[&1;&1])) =
    (({x:real^2 | x IN B /\ &1 < x$1} UNION {x | x IN B /\ &1 < x$2}) UNION
     {x | x IN B /\ x$1 < -- &1}) UNION {x | x IN B /\ x$2 < -- &1}`
  SUBST1_TAC THENL
   [EXPAND_TAC "B" THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^2` THEN
    REWRITE_TAC[IN_DIFF; IN_UNION; IN_ELIM_THM; IN_INTERVAL; DIMINDEX_2; FORALL_2;
                VECTOR_NEG_COMPONENT; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!P. convex {x:real^2 | x IN B /\ P x} <=> convex (B INTER {x | P x})`
  (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[INTER; IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `!c d. (c:real^2) IN B /\ d IN B ==> c IN B` (K ALL_TAC) THENL
   [MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `vector[&2;&2]:real^2 IN B /\ vector[-- &2;&2]:real^2 IN B /\
    vector[&2;-- &2]:real^2 IN B`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_NEG_COMPONENT; VECTOR_2] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (B:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN REWRITE_TAC[CONVEX_INTERVAL]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. (convex {x:real^2 | P x}) ==> connected {x:real^2 | x IN B /\ P x}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
    SUBGOAL_THEN `{x:real^2 | x IN B /\ P x} = B INTER {x | P x}` SUBST1_TAC THENL
     [SET_TAC[]; MATCH_MP_TAC CONVEX_INTER THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex {x:real^2 | &1 < x$1} /\ convex {x:real^2 | &1 < x$2} /\
    convex {x:real^2 | x$1 < -- &1} /\ convex {x:real^2 | x$2 < -- &1}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_ARITH `&1 < x <=> x > &1`; CONVEX_HALFSPACE_COMPONENT_GT;
                CONVEX_HALFSPACE_COMPONENT_LT];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC CONNECTED_UNION THEN CONJ_TAC) THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION; IN_ELIM_THM] THENL
   [EXISTS_TAC `vector[&2;&2]:real^2`;
    EXISTS_TAC `vector[-- &2;&2]:real^2`;
    EXISTS_TAC `vector[&2;-- &2]:real^2`] THEN
  ASM_REWRITE_TAC[VECTOR_2] THEN REAL_ARITH_TAC);;

let MOI_S3CA_ANNULUS_MINUS_END = prove
 (`!(Y:real^N->bool) j0 j1. pl_annulus_with_ends Y j0 j1 ==> connected (Y DIFF j0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ABBREV_TAC `ann = interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                    interval(--vector[&1;&1]:real^2,vector[&1;&1])` THEN
  ABBREV_TAC `rf1 = relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]])` THEN
  SUBGOAL_THEN `(rf1:real^2->bool) SUBSET ann` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["rf1"; "ann"] THEN
    SIMP_TAC[MOI_FN2_RF_SQUARE; REAL_LT_01] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2;
                VECTOR_NEG_COMPONENT; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `Y DIFF j0 = IMAGE (f:real^2->real^N) (ann DIFF rf1)` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^2->real^N) ann = Y`)) THEN
    SUBST1_TAC(ASSUME `j0 = IMAGE (f:real^2->real^N) rf1`) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ_ALT THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `ann:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MAP_EVERY EXPAND_TAC ["ann"; "rf1"] THEN REWRITE_TAC[MOI_S3CA_ANN_MINUS_INNER]]);;

(* A PL parametrisation of a PL 2-cell of real^N by a 2-simplex of the plane. *)

let MOI_S3CA_PLANE_PARAM = prove
 (`!(d:real^N->bool) jd.
     pl_cell_with_boundary 2 d jd
     ==> ?k0:real^2->bool E E'.
           &2 simplex k0 /\ pl_homeomorphism (k0,d) (E,E') /\
           IMAGE E (relative_frontier k0) = jd`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `F1:real^N->real^N`
    (X_CHOOSE_THEN `G1:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_S27_SIMPLEX_FROM_PLANE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` (X_CHOOSE_THEN `h:real^2->real^N`
    (X_CHOOSE_THEN `h':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k0:real^2->bool`; `(F1:real^N->real^N) o (h:real^2->real^N)`;
                        `(h':real^N->real^2) o (G1:real^N->real^N)`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

(* A PL 2-cell of real^N minus a PL 2-ball inside it missing the rim is     *)
(* connected (the planar annulus MOI_S5C_ANN2 minus its inner end).          *)

let MOI_S3CA_DISK_HOLE_CONNECTED = prove
 (`!(d:real^N->bool) jd a.
     pl_cell_with_boundary 2 d jd /\ pl_ball 2 a /\ a SUBSET d /\ DISJOINT a jd
     ==> connected (d DIFF a)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:real^N->bool`; `jd:real^N->bool`] MOI_S3CA_PLANE_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` (X_CHOOSE_THEN `E:real^2->real^N`
    (X_CHOOSE_THEN `E':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?ja:real^N->bool. pl_cell_with_boundary 2 a ja` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_ball 2 (a:real^N->bool)` THEN
    REWRITE_TAC[pl_ball; pl_cell_with_boundary] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism] o CONJUNCT1 o
    GEN_REWRITE_RULE I [pl_homeomorphism] o check (fun th ->
      concl th = `pl_homeomorphism (k0,d) (E:real^2->real^N,E')`)) THEN
  MP_TAC(ISPECL [`k0:real^2->bool`; `d:real^N->bool`; `E:real^2->real^N`;
                 `E':real^N->real^2`; `a:real^N->bool`; `ja:real^N->bool`]
    MOI_S3CA_CELL_PULL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `A = IMAGE (E':real^N->real^2) a` THEN
  ABBREV_TAC `JA = IMAGE (E':real^N->real^2) ja` THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3CA_PLANE_CELL_FILLED
    (ASSUME `pl_cell_with_boundary 2 (A:real^2->bool) JA`)) THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3CA_SIMPLEX2_PLANE (ASSUME `&2 simplex (k0:real^2->bool)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `inside(relative_frontier k0) = interior(k0:real^2->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[INSIDE_FRONTIER_EQ_INTERIOR; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^2->bool) SUBSET interior k0` ASSUME_TAC THENL
   [SUBGOAL_THEN `(A:real^2->bool) INTER relative_frontier k0 = {}` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (E:real^2->real^N) (relative_frontier k0) = jd` THEN
      UNDISCH_TAC `IMAGE (E:real^2->real^N) A = a` THEN
      UNDISCH_TAC `DISJOINT (a:real^N->bool) jd` THEN
      UNDISCH_TAC `(A:real^2->bool) SUBSET k0` THEN
      UNDISCH_TAC `frontier k0 SUBSET (k0:real^2->bool)` THEN
      UNDISCH_TAC `relative_frontier k0 = frontier(k0:real^2->bool)` THEN
      UNDISCH_TAC `!x. x IN k0 ==> (E':real^N->real^2) (E x) = x` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(A:real^2->bool) SUBSET k0` THEN
    UNDISCH_TAC `interior k0 = k0 DIFF frontier(k0:real^2->bool)` THEN
    UNDISCH_TAC `relative_frontier k0 = frontier(k0:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (relative_frontier (k0:real^2->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
    ASM_REWRITE_TAC[ARITH_RULE `1 + 1 = 2`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`JA:real^2->bool`; `relative_frontier k0:real^2->bool`] MOI_S5C_ANN2) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    SUBST1_TAC(ASSUME `inside(relative_frontier k0) = interior(k0:real^2->bool)`) THEN
    UNDISCH_TAC `(A:real^2->bool) SUBSET interior k0` THEN
    UNDISCH_TAC `A = JA UNION inside(JA:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k0 UNION inside(relative_frontier k0) = (k0:real^2->bool)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `interior k0 = k0 DIFF frontier(k0:real^2->bool)` THEN
    UNDISCH_TAC `frontier k0 SUBSET (k0:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S3CA_ANNULUS_MINUS_END) THEN
  SUBGOAL_THEN `(k0 DIFF inside JA) DIFF JA = k0 DIFF (A:real^2->bool)` SUBST1_TAC THENL
   [UNDISCH_TAC `A = JA UNION inside(JA:real^2->bool)` THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `d DIFF a = IMAGE (E:real^2->real^N) (k0 DIFF A)` SUBST1_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (E:real^2->real^N) A = a`)) THEN
    SUBST1_TAC(SYM(ASSUME `IMAGE (E:real^2->real^N) k0 = d`)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ_ALT THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k0:real^2->bool` THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* A compact planar set with a PL circle as frontier and nonempty interior  *)
(* is the circle with its inside.                                            *)

let MOI_S3CA_PLANE_FILL = prove
 (`!X:real^2->bool.
     compact X /\ pl_sphere 1 (frontier X) /\ ~(interior X = {})
     ==> X = frontier X UNION inside(frontier X)`,
  GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `J = frontier(X:real^2->bool)` THEN
  MP_TAC(MATCH_MP MOI_S8PL_JORDAN (ASSUME `pl_sphere 1 (J:real^2->bool)`)) THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `interior X = X DIFF (J:real^2->bool) /\ J SUBSET X` STRIP_ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `frontier(X:real^2->bool) = J`)) THEN
    SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED; ASSUME `compact(X:real^2->bool)`] THEN
    MP_TAC(ISPEC `X:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (X:real^2->bool) /\ bounded X` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!c:real^2->bool. connected c /\ c INTER J = {}
                     ==> c SUBSET interior X \/ c INTER interior X = {}`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[connected; NOT_EXISTS_THM] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`interior X:real^2->bool`; `(:real^2) DIFF X`]) THEN
    REWRITE_TAC[OPEN_INTERIOR; GSYM closed] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `X:real^2->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected(outside(J:real^2->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_OUTSIDE THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; DIMINDEX_2; LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `outside(J:real^2->bool) INTER interior X = {}` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `outside(J:real^2->bool)` o check (fun th ->
      is_forall(concl th))) THEN
    ASM_REWRITE_TAC[OUTSIDE_NO_OVERLAP] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~bounded(outside(J:real^2->bool))` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `X:real^2->bool` THEN
    ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior X SUBSET inside(J:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `J:real^2->bool` INSIDE_UNION_OUTSIDE) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside(J:real^2->bool) SUBSET interior X` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `inside(J:real^2->bool)` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `connected:(real^2->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[INSIDE_NO_OVERLAP] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* STEP4, part 7: the derived neighbourhood of a connected UNIONS l is       *)
(* connected and compact, UNIONS l misses its frontier, frontiers pass to    *)
(* the plane, and the assembly MOI_S3CA_STEP4_THM.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_NBHD_CONNECTED = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     connected (UNIONS l) /\ ~(UNIONS l = {})
     ==> connected (derived_nbhd t l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_GRAPH_IN_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (barycentric_subdivision
                  (t:(real^N->bool)->bool)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `derived_nbhd t (l:(real^N->bool)->bool) =
    UNIONS {s UNION UNIONS l | s | s IN barycentric_subdivision (barycentric_subdivision t) /\
                                   ~(s INTER UNIONS l = {})}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[derived_nbhd] THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s UNION UNIONS (l:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[IN_UNION] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC I [UNIONS_SUBSET] THEN REWRITE_TAC[FORALL_IN_GSPEC; UNION_SUBSET] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
      REWRITE_TAC[derived_nbhd; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN MATCH_MP_TAC CONNECTED_UNION THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `convex (s:real^N->bool)` (fun th -> SIMP_TAC[th; CONVEX_CONNECTED]) THEN
    ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX];
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o check (fun th ->
      concl th = `~(UNIONS l:real^N->bool = {})`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
    REWRITE_TAC[INTERS_GSPEC; IN_ELIM_THM; IN_UNION] THEN ASM_REWRITE_TAC[]]);;

let MOI_S3CA_NBHD_COMPACT = prove
 (`!(t:(real^N->bool)->bool) l.
     FINITE t /\ simplicial_complex t /\ simplicial_subcomplex l t
     ==> compact (derived_nbhd t l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_SC_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (barycentric_subdivision (barycentric_subdivision
                  (t:(real^N->bool)->bool))) /\
                moi_bar_complex (barycentric_subdivision (barycentric_subdivision t))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE] THEN
    ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  REWRITE_TAC[derived_nbhd] THEN MATCH_MP_TAC COMPACT_UNIONS THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
  ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_COMPACT]);;

(* UNIONS l misses the frontier of its derived neighbourhood.                *)

let MOI_S3CA_L_INTERIOR = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> UNIONS l SUBSET derived_nbhd t l DIFF derived_frontier t l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FTA_GRAPH_IN_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (barycentric_subdivision
                  (t:(real^N->bool)->bool)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FN2_FRONTIER_NC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  UNDISCH_TAC `~((s:real^N->bool) IN derived_nbhd_complex t l)` THEN
  REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM SET_TAC[];
    MATCH_MP_TAC FACE_OF_REFL THEN ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]]);;

(* Frontiers pass from a cell to its planar parameter domain when the set   *)
(* misses the rim.                                                            *)

let MOI_S3CA_FRONTIER_PLANE = prove
 (`!(k0:real^2->bool) (d:real^N->bool) E E' Nb.
     &2 simplex k0 /\ homeomorphism (k0,d) (E,E') /\ Nb SUBSET d /\ compact Nb /\
     Nb INTER IMAGE E (relative_frontier k0) = {}
     ==> IMAGE E' Nb SUBSET interior k0 /\ compact (IMAGE E' Nb) /\
         frontier (IMAGE E' Nb) = IMAGE E' ((subtopology euclidean d) frontier_of Nb)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(MATCH_MP MOI_S3CA_SIMPLEX2_PLANE (ASSUME `&2 simplex (k0:real^2->bool)`)) THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `IMAGE (E':real^N->real^2) Nb SUBSET interior k0` ASSUME_TAC THENL
   [UNDISCH_TAC `interior k0 = k0 DIFF frontier(k0:real^2->bool)` THEN
    DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `relative_frontier k0 = frontier(k0:real^2->bool)` THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    UNDISCH_TAC `Nb INTER IMAGE (E:real^2->real^N) (relative_frontier k0) = {}` THEN
    UNDISCH_TAC `(Nb:real^N->bool) SUBSET d` THEN
    UNDISCH_TAC `IMAGE (E':real^N->real^2) d = k0` THEN
    UNDISCH_TAC `!y. y IN d ==> (E:real^2->real^N) (E' y) = y` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (E':real^N->real^2) Nb)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`E':real^N->real^2`; `E:real^2->real^N`; `d:real^N->bool`;
                 `k0:real^2->bool`; `Nb:real^N->bool`] HOMEOMORPHISM_FRONTIER_OF) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[HOMEOMORPHISM_SYM]; DISCH_THEN SUBST1_TAC] THEN
  ABBREV_TAC `X = IMAGE (E':real^N->real^2) Nb` THEN
  SUBGOAL_THEN `frontier (X:real^2->bool) SUBSET interior k0` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `X:real^2->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(subtopology euclidean (interior k0)) frontier_of (X:real^2->bool)` THEN
    CONJ_TAC THENL
     [SIMP_TAC[FRONTIER_OF_SUBTOPOLOGY_OPEN; OPEN_IN_EUCLIDEAN; OPEN_INTERIOR] THEN
      REWRITE_TAC[EUCLIDEAN_FRONTIER_OF] THEN ASM SET_TAC[];
      MATCH_MP_TAC FRONTIER_OF_SUBTOPOLOGY_MONO THEN ASM_REWRITE_TAC[INTERIOR_SUBSET]];
    MP_TAC(ISPECL [`euclidean:(real^2)topology`; `X:real^2->bool`; `k0:real^2->bool`]
      FRONTIER_OF_SUBTOPOLOGY_SUBSET) THEN
    REWRITE_TAC[EUCLIDEAN_FRONTIER_OF] THEN
    MP_TAC(ISPECL [`euclidean:(real^2)topology`; `k0:real^2->bool`; `X:real^2->bool`]
      FRONTIER_OF_SUBSET_SUBTOPOLOGY) THEN
    SET_TAC[]]);;

(* STEP4: the derived neighbourhood of a PL 2-ball subcomplex l, missing the *)
(* rim, of a finite triangulation m of a PL 2-cell is a PL 2-cell bounded by *)
(* its frontier, which UNIONS l misses.  The frontier is a disjoint union of *)
(* PL circles (MOI_S3CA_FR_CIRCLES); in the plane (a parametrisation of the  *)
(* cell) the image of N is compact and connected with connected complement  *)
(* (MOI_S3CA_COMPLEMENT_CONNECTED), so its frontier is connected            *)
(* (CONNECTED_FRONTIER_SIMPLE): one PL circle; then Jordan and PL           *)
(* Schoenflies, and the push forward.                                        *)

let MOI_S3CA_STEP4_THM = prove
 (MOI_S3CA_STEP4,
  MAP_EVERY X_GEN_TAC [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `d:real^N->bool`; `jd:real^N->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `d:real^N->bool`;
                 `jd:real^N->bool`] MOI_S3CA_S4_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_S3CA_L_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_cell_with_boundary 2 (d:real^N->bool) jd` THEN
    REWRITE_TAC[pl_cell_with_boundary] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_LE_UNIV) THEN
    SUBGOAL_THEN `aff_dim (k:real^N->bool) = &2` SUBST1_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; REWRITE_TAC[INT_OF_NUM_LE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS l SUBSET (d:real^N->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `UNIONS m = (d:real^N->bool)`)) THEN
    MATCH_MP_TAC SUBSET_UNIONS THEN ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `jd:real^N->bool`]
    MOI_S3CA_NBHD_RIM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_S3CA_FR_CIRCLES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `CARD:((real^N->bool)->bool)->num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_frn_vp m l (e:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN
    UNDISCH_TAC `DISJOINT (UNIONS l) (jd:real^N->bool)` THEN SET_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `connected (UNIONS l:real^N->bool) /\ ~(UNIONS l = {})` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_ball 2 (UNIONS l:real^N->bool)` THEN
    REWRITE_TAC[pl_ball; pl_homeomorphism; homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `UNIONS l:real^N->bool`)) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
      ASM_MESON_TAC[SIMPLEX_EMPTY; INT_ARITH `~(&2:int = -- &1)`]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_S3CA_NBHD_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_S3CA_NBHD_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `connected (d DIFF derived_nbhd m (l:(real^N->bool)->bool))` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `UNIONS m = (d:real^N->bool)`)) THEN
    MATCH_MP_TAC MOI_S3CA_COMPLEMENT_CONNECTED THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S3CA_DISK_HOLE_CONNECTED THEN EXISTS_TAC `jd:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `derived_nbhd m (l:(real^N->bool)->bool) SUBSET d` ASSUME_TAC THENL
   [REWRITE_TAC[derived_nbhd; UNIONS_SUBSET; IN_ELIM_THM] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `UNIONS (barycentric_subdivision (barycentric_subdivision m)) = (d:real^N->bool)`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(subtopology euclidean d) frontier_of derived_nbhd m (l:(real^N->bool)->bool) =
                derived_frontier m l`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[derived_frontier]; ALL_TAC] THEN
  (* the planar parameter domain *)
  MP_TAC(ISPECL [`d:real^N->bool`; `jd:real^N->bool`] MOI_S3CA_PLANE_PARAM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k0:real^2->bool` (X_CHOOSE_THEN `E:real^2->real^N`
    (X_CHOOSE_THEN `E':real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `homeomorphism (k0,d) (E:real^2->real^N,E')` ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o check (fun th ->
    concl th = `homeomorphism (k0,d) (E:real^2->real^N,E')`)) THEN
  MP_TAC(MATCH_MP MOI_S3CA_SIMPLEX2_PLANE (ASSUME `&2 simplex (k0:real^2->bool)`)) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`k0:real^2->bool`; `d:real^N->bool`; `E:real^2->real^N`;
                 `E':real^N->real^2`; `derived_nbhd m (l:(real^N->bool)->bool)`]
    MOI_S3CA_FRONTIER_PLANE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBST1_TAC(ASSUME `(subtopology euclidean d) frontier_of
                     derived_nbhd m (l:(real^N->bool)->bool) = derived_frontier m l`) THEN
  STRIP_TAC THEN
  ABBREV_TAC `X = IMAGE (E':real^N->real^2) (derived_nbhd m l)` THEN
  ABBREV_TAC `Fr = derived_frontier m (l:(real^N->bool)->bool)` THEN
  ABBREV_TAC `Nb = derived_nbhd m (l:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(Fr:real^N->bool) SUBSET Nb` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `(subtopology euclidean d) frontier_of (Nb:real^N->bool) = Fr`)) THEN
    MATCH_MP_TAC FRONTIER_OF_SUBSET_CLOSED_IN THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  (* the planar image: connected, with connected complement *)
  SUBGOAL_THEN `connected (X:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `k0 DIFF (X:real^2->bool) = IMAGE (E':real^N->real^2) (d DIFF Nb)`
  ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    SUBST1_TAC(SYM(ASSUME `IMAGE (E':real^N->real^2) d = k0`)) THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DIFF_INJ_ALT THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected ((:real^2) DIFF X)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(:real^2) DIFF X = ((:real^2) DIFF interior k0) UNION (k0 DIFF X)`
    SUBST1_TAC THENL
     [MP_TAC(ISPEC `k0:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(X:real^2->bool) SUBSET interior k0` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPLEMENT_BOUNDED_CONVEX THEN
      ASM_SIMP_TAC[DIMINDEX_2; LE_REFL; CONVEX_INTERIOR; BOUNDED_INTERIOR;
                   COMPACT_IMP_BOUNDED];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `d:real^N->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `~(frontier(k0:real^2->bool) = {})` MP_TAC THENL
       [REWRITE_TAC[FRONTIER_EQ_EMPTY; DE_MORGAN_THM] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[INTERIOR_EMPTY];
          ASM_MESON_TAC[NOT_BOUNDED_UNIV; COMPACT_IMP_BOUNDED]];
        ALL_TAC] THEN
      MP_TAC(ISPEC `k0:real^2->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(X:real^2->bool) SUBSET interior k0` THEN
      UNDISCH_TAC `interior k0 = k0 DIFF frontier(k0:real^2->bool)` THEN
      UNDISCH_TAC `frontier k0 SUBSET (k0:real^2->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `X:real^2->bool` CONNECTED_FRONTIER_SIMPLE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* the frontier of N is one PL circle *)
  SUBGOAL_THEN `IMAGE (E:real^2->real^N) (frontier X) = Fr` ASSUME_TAC THENL
   [SUBST1_TAC(ASSUME `frontier X = IMAGE (E':real^N->real^2) Fr`) THEN
    SUBGOAL_THEN `(Fr:real^N->bool) SUBSET d` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `Nb:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `!y. y IN d ==> (E:real^2->real^N) (E' y) = y` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier X SUBSET (k0:real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `X:real^2->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (Fr:real^N->bool)` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (E:real^2->real^N) (frontier X) = Fr`)) THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k0:real^2->bool` THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      SUBST1_TAC(ASSUME `frontier X = IMAGE (E':real^N->real^2) Fr`) THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(X:real^2->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    UNDISCH_TAC `UNIONS l SUBSET (Nb:real^N->bool) DIFF Fr` THEN
    UNDISCH_TAC `~(UNIONS l:real^N->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Fr:real^N->bool = {})` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (E:real^2->real^N) (frontier X) = Fr`)) THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY; FRONTIER_EQ_EMPTY; DE_MORGAN_THM] THEN
    CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_TAC THEN MP_TAC(INST_TYPE [`:2`,`:N`] NOT_BOUNDED_UNIV) THEN REWRITE_TAC[] THEN
    SUBST1_TAC(SYM(ASSUME `X = (:real^2)`)) THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (Fr:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ASSUME `!j:real^N->bool. j IN components Fr ==> pl_sphere 1 j`) THEN
    SUBGOAL_THEN `components (Fr:real^N->bool) = {Fr}` SUBST1_TAC THENL
     [REWRITE_TAC[COMPONENTS_EQ_SING] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fr:real^N->bool) SUBSET d` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `Nb:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k0:real^2->bool`; `d:real^N->bool`; `Fr:real^N->bool`;
                 `E:real^2->real^N`; `E':real^N->real^2`] MOI_S8PL_SPHERE_PULL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))] THEN
  SUBGOAL_THEN `pl_sphere 1 (frontier(X:real^2->bool))` ASSUME_TAC THENL
   [SUBST1_TAC(ASSUME `frontier X = IMAGE (E':real^N->real^2) Fr`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(interior (X:real^2->bool) = {})` ASSUME_TAC THENL
   [SUBGOAL_THEN `interior X = X DIFF frontier(X:real^2->bool)` SUBST1_TAC THENL
     [SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED;
               ASSUME `compact (X:real^2->bool)`] THEN
      MP_TAC(ISPEC `X:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBST1_TAC(ASSUME `frontier X = IMAGE (E':real^N->real^2) Fr`) THEN
    SUBGOAL_THEN `IMAGE (E':real^N->real^2) (UNIONS l) SUBSET X DIFF IMAGE E' Fr /\
                  ~(IMAGE (E':real^N->real^2) (UNIONS l) = {})` MP_TAC THENL
     [REWRITE_TAC[IMAGE_EQ_EMPTY] THEN CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      SUBST1_TAC(SYM(ASSUME `IMAGE (E':real^N->real^2) Nb = X`)) THEN
      UNDISCH_TAC `UNIONS l SUBSET (Nb:real^N->bool) DIFF Fr` THEN
      UNDISCH_TAC `(Fr:real^N->bool) SUBSET Nb` THEN
      UNDISCH_TAC `(Nb:real^N->bool) SUBSET d` THEN
      UNDISCH_TAC `!y. y IN d ==> (E:real^2->real^N) (E' y) = y` THEN SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `X:real^2->bool` MOI_S3CA_PLANE_FILL) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(ASSUME_TAC o SYM)] THEN
  SUBGOAL_THEN `pl_ball 2 (X:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(REWRITE_RULE[PL_SCHOENFLIES_2_STATEMENT] PL_SCHOENFLIES_2) THEN
    DISCH_THEN(MP_TAC o SPEC `frontier(X:real^2->bool)`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    SUBST1_TAC(ASSUME `frontier X UNION inside(frontier X) = (X:real^2->bool)`) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k0:real^2->bool`; `d:real^N->bool`; `Fr:real^N->bool`;
                 `E:real^2->real^N`; `E':real^N->real^2`; `X:real^2->bool`]
    MOI_S8PL_CELL_PUSH) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    ASM_MESON_TAC[INTERIOR_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (E:real^2->real^N) X = Nb` (fun th -> SIMP_TAC[th]) THEN
  SUBST1_TAC(SYM(ASSUME `IMAGE (E':real^N->real^2) Nb = X`)) THEN
  UNDISCH_TAC `(Nb:real^N->bool) SUBSET d` THEN
  UNDISCH_TAC `!y. y IN d ==> (E:real^2->real^N) (E' y) = y` THEN SET_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* The main theorem DISK_CHART_2: the trace identity (MOI_FN2_DERIVED_TRACE  *)
(* of pc_moi_fnd_nb2) and STEP4 discharge MOI_S3CA_DISK_CHART_COND.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S3CA_TRACE_THM = prove
 (moi_n3 MOI_S3CA_TRACE,
  ACCEPT_TAC(INST_TYPE [`:3`,`:N`] MOI_FN2_DERIVED_TRACE));;

let MOI_S3CA_STEP4_3 = prove
 (moi_n3 MOI_S3CA_STEP4,
  ACCEPT_TAC(INST_TYPE [`:3`,`:N`] MOI_S3CA_STEP4_THM));;

let DISK_CHART_2 = prove
 (MOI_S30_DISK_CHART_2,
  MATCH_MP_TAC MOI_S3CA_DISK_CHART_COND THEN
  CONJ_TAC THENL [ACCEPT_TAC MOI_S3CA_TRACE_THM; ACCEPT_TAC MOI_S3CA_STEP4_3]);;

