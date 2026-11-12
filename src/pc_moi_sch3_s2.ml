needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_sch3_amb2.ml";;
needs "src/pc_moi_fnd_surfa.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_sch3_s2: Moise GTM 47, Sec 17 (pp.121, 123): the 2-dimensional    *)
(* facts on PL 2-spheres in real^3 used throughout Sec 17.                  *)
(*   SPHERE_SPLIT     a PL circle in a PL 2-sphere splits it into two PL    *)
(*                    2-cells with boundary the circle;                     *)
(*   DISK_COMPLEMENT  the closed complement of a PL 2-cell in a PL 2-sphere *)
(*                    is a PL 2-cell with the same boundary;               *)
(*   DISK_UNION       two PL 2-cells meeting exactly in their common        *)
(*                    boundary form a PL 2-sphere;                          *)
(*   PLANE_CELL_HULL  a plane PL 2-cell lies in the convex hull of its     *)
(*                    boundary.                                             *)
(* Route.  A PL 2-sphere is PL homeomorphic to the boundary of a           *)
(* 3-simplex.  A point of a facet off the circle is moved to the vertex    *)
(* vec 0 of the standard simplex by two cone maps; the complement of a     *)
(* small corner at vec 0 is a PL disk (glued from the far facet and three  *)
(* trapezoids, with the disk gluing lemmas of pc_moi_fnd_surfa), so the    *)
(* planar PL Schoenflies theorem of pc_moi_pl2 and the Jordan curve        *)
(* theorem apply there.  Doing this at a point on each side of the circle  *)
(* gives both disks.  The gluing of two disks along their boundary is      *)
(* MOI_FSA_TWO_DISKS of pc_moi_fnd_surfa; the plane-cell hull fact comes   *)
(* from invariance of domain.                                              *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 0. Transfer of PL triangles, PL disks and PL circles between spaces.     *)
(* ------------------------------------------------------------------------- *)

let MOI_SS2_STD_NONCOLLINEAR = prove
 (`2 <= dimindex(:N) ==> ~collinear{vec 0:real^N,basis 1,basis 2}`,
  DISCH_TAC THEN REWRITE_TAC[COLLINEAR_LEMMA] THEN
  SUBGOAL_THEN `~(basis 1:real^N = vec 0) /\ ~(basis 2:real^N = vec 0)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC BASIS_NONZERO THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (MP_TAC o AP_TERM `\x:real^N. x$2`)) THEN
  BETA_TAC THEN REWRITE_TAC[VECTOR_MUL_COMPONENT] THEN
  ASM_SIMP_TAC[BASIS_COMPONENT; ARITH] THEN REAL_ARITH_TAC);;

let MOI_SS2_STD_TRIANGLE = prove
 (`2 <= dimindex(:N)
   ==> &2 simplex (convex hull {vec 0:real^N,basis 1,basis 2})`,
  DISCH_TAC THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
  ASM_MESON_TAC[MOI_SS2_STD_NONCOLLINEAR]);;

let MOI_SS2_TRI_TRANSFER = prove
 (`!(k:real^N->bool) (e0:real^M) e1 e2.
     &2 simplex k /\ ~collinear{e0,e1,e2}
     ==> ?f g. pl_homeomorphism (convex hull {e0,e1,e2},k) (f,g) /\
               IMAGE f (relative_frontier(convex hull {e0,e1,e2})) =
               relative_frontier k`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_2]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(a:real^N = b)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PL2_NONCOLLINEAR_DISTINCT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `e0:real^M`; `e1:real^M`;
                 `e2:real^M`; `linepath(a:real^N,b)`]
    MOI_PL2_TRIANGLE_BOUNDARY_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[ARC_LINEPATH; MOI_PL2_PL_LINEPATH;
                 MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
    ASM_SIMP_TAC[PATH_IMAGE_LINEPATH; RELATIVE_FRONTIER_OF_TRIANGLE] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f0:real^M->real^N` (X_CHOOSE_THEN
    `g0:real^N->real^M` (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MP_TAC(ISPECL [`convex hull {e0:real^M,e1,e2}`;
                 `k:real^N->bool`; `2`; `f0:real^M->real^N`;
                 `g0:real^N->real^M`] PL_HOMEOMORPHISM_CONE_EXTENSION) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^M->real^N` (X_CHOOSE_THEN
    `g:real^N->real^M` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  TRANS_TAC EQ_TRANS
   `IMAGE (f0:real^M->real^N)
      (relative_frontier(convex hull {e0:real^M,e1,e2}))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x:real^M. x IN s ==> (f:real^M->real^N) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC
     `pl_homeomorphism
        (relative_frontier (convex hull {e0:real^M, e1, e2}),
         relative_frontier k) (f0:real^M->real^N,g0)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism]]);;

(* PL 2-cells and PL disks with planar models (moi_fsa_disk) agree.         *)

let MOI_SS2_FSA_OF_CELL = prove
 (`!(d:real^N->bool) j. pl_cell_with_boundary 2 d j ==> moi_fsa_disk d j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; moi_fsa_disk] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `vec 0:real^2`; `basis 1:real^2`;
                 `basis 2:real^2`] MOI_SS2_TRI_TRANSFER) THEN
  ASM_REWRITE_TAC[MOI_PL2_STD_TRIANGLES] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^2->real^N` (X_CHOOSE_THEN
    `v:real^N->real^2` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull {vec 0:real^2,basis 1,basis 2}`;
    `(f:real^N->real^N) o (u:real^2->real^N)`;
    `(v:real^N->real^2) o (g:real^N->real^N)`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN MESON_TAC[MOI_PL2_STD_TRIANGLES];
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_o]]);;

let MOI_SS2_CELL_OF_FSA = prove
 (`!(d:real^N->bool) j.
     2 <= dimindex(:N) /\ moi_fsa_disk d j ==> pl_cell_with_boundary 2 d j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; moi_fsa_disk] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^N`
    (X_CHOOSE_THEN `g:real^N->real^2` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `vec 0:real^N`; `basis 1:real^N`;
                 `basis 2:real^N`] MOI_SS2_TRI_TRANSFER) THEN
  ASM_SIMP_TAC[MOI_SS2_STD_NONCOLLINEAR] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real^2` (X_CHOOSE_THEN
    `v:real^2->real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull {vec 0:real^N,basis 1,basis 2}`;
    `(f:real^2->real^N) o (u:real^N->real^2)`;
    `(v:real^2->real^N) o (g:real^N->real^2)`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[MOI_SS2_STD_TRIANGLE];
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `k:real^2->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_o]]);;

let MOI_SS2_CELL_EQ_FSA = prove
 (`!(d:real^3->bool) j. pl_cell_with_boundary 2 d j <=> moi_fsa_disk d j`,
  REPEAT GEN_TAC THEN EQ_TAC THEN REWRITE_TAC[MOI_SS2_FSA_OF_CELL] THEN
  DISCH_TAC THEN MATCH_MP_TAC MOI_SS2_CELL_OF_FSA THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC);;

let MOI_SS2_CELL_EQ_FSA_2 = prove
 (`!(d:real^2->bool) j. pl_cell_with_boundary 2 d j <=> moi_fsa_disk d j`,
  REWRITE_TAC[pl_cell_with_boundary; moi_fsa_disk] THEN MESON_TAC[]);;

(* Polyhedra, PL disks and PL circles under PL homeomorphisms.              *)

let MOI_SS2_FSA_POLYHEDRON = prove
 (`!(d:real^N->bool) j. moi_fsa_disk d j ==> pl_polyhedron d /\ pl_polyhedron j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_disk] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^N`
    (X_CHOOSE_THEN `g:real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `polytope (k:real^2->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) k = d` (SUBST1_TAC o SYM) THENL
   [ASM_MESON_TAC[MOI_PL2_PL_HOMEO_IMAGE]; ALL_TAC] THEN
  EXPAND_TAC "j" THEN CONJ_TAC THEN
  MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON; MOI_SA2_POLYTOPE_RF_POLYHEDRON] THEN
  FIRST_X_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o
    GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  DISCH_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `k:real^2->bool` THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON;
               MOI_SA2_POLYTOPE_RF_POLYHEDRON] THEN
  ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; POLYTOPE_IMP_CLOSED]);;

let MOI_SS2_FSA_IMAGE = prove
 (`!(d:real^M->bool) j s (t:real^N->bool) f g.
     moi_fsa_disk d j /\ pl_homeomorphism (s,t) (f,g) /\ d SUBSET s
     ==> moi_fsa_disk (IMAGE f d) (IMAGE f j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_SS2_FSA_POLYHEDRON) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `t:real^N->bool`; `f:real^M->real^N`;
                 `g:real^N->real^M`; `d:real^M->bool`]
    MOI_FSA_PL_HOMEO_RESTRICT) THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_fsa_disk (d:real^M->bool) j` THEN
  REWRITE_TAC[moi_fsa_disk] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `h:real^2->real^M`
    (X_CHOOSE_THEN `h':real^M->real^2` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^2->bool`; `(f:real^M->real^N) o (h:real^2->real^M)`;
                        `(h':real^M->real^2) o (g:real^N->real^M)`] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `d:real^M->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_SS2_SPHERE1_IMAGE = prove
 (`!(j:real^M->bool) s (t:real^N->bool) f g.
     2 <= dimindex(:N) /\
     pl_sphere 1 j /\ pl_homeomorphism (s,t) (f,g) /\ j SUBSET s
     ==> pl_sphere 1 (IMAGE f j)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_SCD_PL_SPHERE_POLYHEDRON) THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `t:real^N->bool`; `f:real^M->real^N`;
                 `g:real^N->real^M`; `j:real^M->bool`]
    MOI_FSA_PL_HOMEO_RESTRICT) THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN DISCH_TAC THEN
  UNDISCH_TAC `pl_sphere 1 (j:real^M->bool)` THEN
  REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `h:real^M->real^M`
    (X_CHOOSE_THEN `h':real^M->real^M` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k:real^M->bool`; `vec 0:real^N`; `basis 1:real^N`;
                 `basis 2:real^N`] MOI_SS2_TRI_TRANSFER) THEN
  ASM_SIMP_TAC[MOI_SS2_STD_NONCOLLINEAR] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real^M` (X_CHOOSE_THEN
    `v:real^M->real^N` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `e = convex hull {vec 0:real^N,basis 1,basis 2}` THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier e,relative_frontier k)
                  ((u:real^N->real^M),(v:real^M->real^N))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (u:real^N->real^M) (relative_frontier e) =
                  relative_frontier k` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_FSA_PL_HOMEO_RESTRICT THEN
    EXISTS_TAC `e:real^N->bool` THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `polytope (e:real^N->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "e" THEN MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
      REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      ALL_TAC] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON;
                 MOI_SA2_POLYTOPE_RF_POLYHEDRON] THEN
    ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; POLYTOPE_IMP_CLOSED];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`e:real^N->bool`;
    `(f:real^M->real^N) o ((h:real^M->real^M) o (u:real^N->real^M))`;
    `((v:real^M->real^N) o (h':real^M->real^M)) o (g:real^N->real^M)`] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "e" THEN ASM_SIMP_TAC[MOI_SS2_STD_TRIANGLE]; ALL_TAC] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `j:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_frontier k:real^M->bool` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 1. Planar facts.  For a compact set s inside the interior of a compact   *)
(* convex body k (dimension at least 2) the part of the outside of s in k  *)
(* is connected and contains the frontier of k: every component of it     *)
(* meets the frontier, since otherwise it would be open and closed in the  *)
(* connected unbounded outside of s.                                        *)
(* ------------------------------------------------------------------------- *)

let MOI_SS2_OUTSIDE_INTER_CONNECTED = prove
 (`!(s:real^N->bool) k.
     2 <= dimindex(:N) /\ compact s /\ ~(s = {}) /\
     convex k /\ compact k /\ s SUBSET interior k
     ==> frontier k SUBSET k INTER outside s /\
         connected (k INTER outside s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `inside s SUBSET interior (k:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_SUBSET_INTERIOR_CONVEX THEN
    ASM_MESON_TAC[SUBSET_TRANS; INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier k = (k:real^N->bool) DIFF interior k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier k SUBSET (k:real^N->bool) INTER outside s`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` INSIDE_UNION_OUTSIDE) THEN
    ASM SET_TAC[];
    ASM_REWRITE_TAC[]] THEN
  SUBGOAL_THEN `connected(frontier k:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(interior k:real^N->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o
      MATCH_MP RELATIVE_FRONTIER_NONEMPTY_INTERIOR) THEN
    MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; AFF_DIM_NONEMPTY_INTERIOR] THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN k INTER outside s
               ==> ?z. z IN frontier k /\
                       z IN connected_component (k INTER outside s) x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `~(s INTER t = {}) ==> ?z:real^N. z IN s /\ z IN t`) THEN
    DISCH_TAC THEN
    ABBREV_TAC `c = connected_component (k INTER outside s) (x:real^N)` THEN
    SUBGOAL_THEN `(x:real^N) IN c /\ connected c` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT] THEN
      REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:real^N->bool) SUBSET k INTER outside s` ASSUME_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[CONNECTED_COMPONENT_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:real^N->bool) SUBSET interior k INTER outside s`
    ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `open (c:real^N->bool)` ASSUME_TAC THENL
     [SUBGOAL_THEN
       `c = connected_component (interior k INTER outside s) (x:real^N)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
          EXPAND_TAC "c" THEN MATCH_MP_TAC CONNECTED_COMPONENT_MONO THEN
          MP_TAC(ISPEC `k:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[]];
        MATCH_MP_TAC OPEN_CONNECTED_COMPONENT THEN
        ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR; OPEN_OUTSIDE;
                     COMPACT_IMP_CLOSED]];
      ALL_TAC] THEN
    SUBGOAL_THEN `closed_in (subtopology euclidean (outside s))
                            (c:real^N->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSED_IN_TRANS THEN
      EXISTS_TAC `k INTER outside s:real^N->bool` THEN CONJ_TAC THENL
       [EXPAND_TAC "c" THEN REWRITE_TAC[CLOSED_IN_CONNECTED_COMPONENT];
        ONCE_REWRITE_TAC[INTER_COMM] THEN
        MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(c:real^N->bool) SUBSET outside s /\ c SUBSET k`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `s:real^N->bool` CONNECTED_OUTSIDE) THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; CONNECTED_CLOPEN] THEN
    DISCH_THEN(MP_TAC o SPEC `c:real^N->bool`) THEN
    ASM_SIMP_TAC[OPEN_SUBSET] THEN
    STRIP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `s:real^N->bool` UNBOUNDED_OUTSIDE) THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_IFF_CONNECTED_COMPONENT] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `x:real^N` th) THEN
                          MP_TAC(SPEC `y:real^N` th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `zy:real^N` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `zx:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `frontier k SUBSET connected_component (k INTER outside s) (zx:real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_TRANS; CONNECTED_COMPONENT_SYM;
                SUBSET; IN]);;

(* The planar package for a PL circle J inside a triangle k of real^2:     *)
(* J UNION inside J is a PL disk bounded by J (PL Schoenflies), the inside *)
(* is a connected open set in the interior of k, and the rest of k off J  *)
(* is connected and contains the boundary of k.                            *)

let MOI_SS2_PLANAR = prove
 (`!(k:real^2->bool) J.
     &2 simplex k /\ pl_sphere 1 J /\ J SUBSET interior k
     ==> moi_fsa_disk (J UNION inside J) J /\
         compact (J UNION inside J) /\
         inside J SUBSET interior k /\
         open (inside J) /\ connected (inside J) /\ ~(inside J = {}) /\
         connected (k INTER outside J) /\
         relative_frontier k SUBSET k INTER outside J /\
         inside J INTER outside J = {} /\
         inside J UNION outside J = (:real^2) DIFF J`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP PL_SPHERE_1_POLYGON) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^2)list` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `polygonal_path (p:(real^2)list)` JORDAN_INSIDE_OUTSIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (J:real^2->bool) /\ ~(J = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON; PL_POLYHEDRON_IMP_COMPACT;
                  MOI_SCD_PL_SPHERE_NONEMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (k:real^2->bool) /\ compact k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYTOPE;
                  POLYTOPE_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k = frontier (k:real^2->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_NONEMPTY_INTERIOR THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`J:real^2->bool`; `k:real^2->bool`]
    MOI_SS2_OUTSIDE_INTER_CONNECTED) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_ball 2 (J UNION inside J:real^2->bool)` MP_TAC THENL
   [MP_TAC PL_SCHOENFLIES_2 THEN REWRITE_TAC[PL_SCHOENFLIES_2_STATEMENT] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^2->bool` (X_CHOOSE_THEN
    `f:real^2->real^2` (X_CHOOSE_THEN `g:real^2->real^2`
    STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_fsa_disk] THEN
    MAP_EVERY EXISTS_TAC
     [`k1:real^2->bool`; `f:real^2->real^2`; `g:real^2->real^2`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`k1:real^2->bool`; `J UNION inside J:real^2->bool`;
                   `f:real^2->real^2`; `g:real^2->real^2`]
      MOI_PL2_FRONTIER_PL_BALL_2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPEC `polygonal_path (p:(real^2)list)`
      MOI_PL2_FRONTIER_JORDAN_REGION) THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[MOI_PL2_PL_HOMEO_COMPACT; SIMPLEX_IMP_POLYTOPE;
                  POLYTOPE_IMP_COMPACT];
    MATCH_MP_TAC INSIDE_SUBSET_INTERIOR_CONVEX THEN
    ASM_MESON_TAC[SUBSET_TRANS; INTERIOR_SUBSET]]);;

(* ------------------------------------------------------------------------- *)
(* 2. Trapezoids in cone coordinates.  For independent x, y and 0 < e < 1   *)
(* the trapezoid with corners x, y, e y, e x is the set of a x + b y with   *)
(* a, b >= 0 and e <= a + b <= 1; it is the union of the triangles          *)
(* x, e y, y and x, e y, e x meeting along their common edge, hence a PL    *)
(* disk bounded by its four edges.                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_SS2_LINCOMB_EQ = prove
 (`!(x:real^N) y a b c d. a = c /\ b = d ==> a % x + b % y = c % x + d % y`,
  SIMP_TAC[]);;

let MOI_SS2_INDEP2 = prove
 (`!(x:real^N) y a b c d.
     ~collinear{vec 0,x,y} /\ a % x + b % y = c % x + d % y
     ==> a = c /\ b = d`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `b:real = d` ASSUME_TAC THENL
   [ASM_CASES_TAC `b:real = d` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(c - a) / (b - d):real`) THEN
    REWRITE_TAC[] THEN
    MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN
    EXISTS_TAC `b - d:real` THEN
    ASM_REWRITE_TAC[REAL_SUB_0; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_SUB_0] THEN
    UNDISCH_TAC `a % (x:real^N) + b % y = c % x + d % y` THEN
    VECTOR_ARITH_TAC;
    ASM_REWRITE_TAC[]] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(a - c) % (x:real^N) = vec 0` MP_TAC THENL
   [UNDISCH_TAC `a % (x:real^N) + d % y = c % x + d % y` THEN
    VECTOR_ARITH_TAC;
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_SUB_0]]);;

let MOI_SS2_INDEP2_ZERO = prove
 (`!(x:real^N) y a b.
     ~collinear{vec 0,x,y} /\ a % x + b % y = vec 0 ==> a = &0 /\ b = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `a:real`; `b:real`; `&0`; `&0`]
    MOI_SS2_INDEP2) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_LID] THEN SIMP_TAC[]);;

let MOI_SS2_SEG_XY = prove
 (`!(x:real^N) y.
     segment[x,y] = {a % x + b % y | &0 <= a /\ &0 <= b /\ a + b = &1}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_SEGMENT; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`&1 - u`; `u:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `b:real` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `a = &1 - b` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; REFL_TAC]]);;

let MOI_SS2_SEG_YEY = prove
 (`!(x:real^N) y e.
     &0 < e /\ e < &1
     ==> segment[y,e % y] = {a % x + b % y | a = &0 /\ e <= b /\ b <= &1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_SEGMENT; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`&0`; `&1 - u * (&1 - e)`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= u * (&1 - e) /\ &0 <= (&1 - u) * (&1 - e)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    EXISTS_TAC `(&1 - b) / (&1 - e)` THEN
    ABBREV_TAC `u = (&1 - b) / (&1 - e)` THEN
    SUBGOAL_THEN `u * (&1 - e) = &1 - b` ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= u /\ u <= &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC EQ_TRANS `&0 % x + (&1 - u + u * e) % (y:real^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SS2_LINCOMB_EQ THEN ASM_REAL_ARITH_TAC;
      VECTOR_ARITH_TAC]]);;

let MOI_SS2_SEG_EYEX = prove
 (`!(x:real^N) y e.
     &0 < e
     ==> segment[e % y,e % x] =
         {a % x + b % y | &0 <= a /\ &0 <= b /\ a + b = e}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_SEGMENT; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`u * e`; `(&1 - u) * e`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      VECTOR_ARITH_TAC];
    EXISTS_TAC `a / e` THEN
    ABBREV_TAC `u = a / e` THEN
    SUBGOAL_THEN `u * e = a` ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= u /\ u <= &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC EQ_TRANS `(u * e) % x + (e - u * e) % (y:real^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SS2_LINCOMB_EQ THEN ASM_REAL_ARITH_TAC;
      VECTOR_ARITH_TAC]]);;

let MOI_SS2_SEG_EXX = prove
 (`!(x:real^N) y e.
     &0 < e /\ e < &1
     ==> segment[e % x,x] = {a % x + b % y | b = &0 /\ e <= a /\ a <= &1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_SEGMENT; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`(&1 - u) * e + u`; `&0`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `&0 <= u * (&1 - e) /\ &0 <= (&1 - u) * (&1 - e)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    EXISTS_TAC `(a - e) / (&1 - e)` THEN
    ABBREV_TAC `u = (a - e) / (&1 - e)` THEN
    SUBGOAL_THEN `u * (&1 - e) = a - e` ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN MATCH_MP_TAC REAL_DIV_RMUL THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= u /\ u <= &1` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "u" THEN CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC EQ_TRANS `((&1 - u) * e + u) % x + &0 % (y:real^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SS2_LINCOMB_EQ THEN ASM_REAL_ARITH_TAC;
      VECTOR_ARITH_TAC]]);;

let MOI_SS2_TRAP_NONCOLLINEAR = prove
 (`!(x:real^N) y e.
     ~collinear{vec 0,x,y} /\ &0 < e /\ e < &1
     ==> ~collinear{x,e % y,y} /\ ~collinear{x,e % y,e % x}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[COLLINEAR_3] THEN
  REWRITE_TAC[COLLINEAR_LEMMA; DE_MORGAN_THM; NOT_EXISTS_THM] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `&1`; `--e:real`]
      MOI_SS2_INDEP2_ZERO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[VECTOR_ARITH
     `x - e % y = vec 0 ==> &1 % x + --e % y = vec 0:real^N`];
     REAL_ARITH_TAC];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `&0`; `&1 - e`]
      MOI_SS2_INDEP2_ZERO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[VECTOR_ARITH
     `y - e % y = vec 0 ==> &0 % x + (&1 - e) % y = vec 0:real^N`];
     ASM_REAL_ARITH_TAC];
    X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `--c:real`; `&1 - e + c * e`]
      MOI_SS2_INDEP2_ZERO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[VECTOR_ARITH
     `y - e % y = c % (x - e % y)
      ==> --c % x + (&1 - e + c * e) % y = vec 0:real^N`];
     ALL_TAC] THEN
    REWRITE_TAC[REAL_NEG_EQ_0] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
    ASM_REWRITE_TAC[REAL_MUL_LZERO] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `&1`; `--e:real`]
      MOI_SS2_INDEP2_ZERO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[VECTOR_ARITH
     `x - e % y = vec 0 ==> &1 % x + --e % y = vec 0:real^N`];
     REAL_ARITH_TAC];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `e:real`; `--e:real`]
      MOI_SS2_INDEP2_ZERO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[VECTOR_ARITH
     `e % x - e % y = vec 0 ==> e % x + --e % y = vec 0:real^N`];
     ASM_REAL_ARITH_TAC];
    X_GEN_TAC `c:real` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `e - c:real`; `c * e - e:real`]
      MOI_SS2_INDEP2_ZERO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[VECTOR_ARITH
     `e % x - e % y = c % (x - e % y)
      ==> (e - c) % x + (c * e - e) % y = vec 0:real^N`];
     ALL_TAC] THEN
    REWRITE_TAC[REAL_SUB_0] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ARITH `e * e = e <=> e * (e - &1) = &0`] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN ASM_REAL_ARITH_TAC]);;

(* The two triangles of the trapezoid meet in their common edge.            *)

let MOI_SS2_TRAP_INTER = prove
 (`!(x:real^N) y e.
     ~collinear{vec 0,x,y} /\ &0 < e /\ e < &1
     ==> convex hull {x,e % y,y} INTER convex hull {x,e % y,e % x} =
         segment[x,e % y]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&1 - e = &0) /\ ~(e = &0)` STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CONVEX_HULL_3; EXTENSION; IN_INTER; IN_ELIM_THM; IN_SEGMENT] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `w:real`
         STRIP_ASSUME_TAC)))
      (X_CHOOSE_THEN `u':real` (X_CHOOSE_THEN `v':real`
         (X_CHOOSE_THEN `w':real` STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `u % (x:real^N) + (v * e + w) % y =
                  (u' + w' * e) % x + (v' * e) % y` ASSUME_TAC THENL
     [UNDISCH_TAC `z = u % (x:real^N) + v % e % y + w % y` THEN
      UNDISCH_TAC `z = u' % (x:real^N) + v' % e % y + w' % e % x` THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `u:real`; `v * e + w:real`;
                   `u' + w' * e:real`; `v' * e:real`] MOI_SS2_INDEP2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w + w' * e) * (&1 - e) = &0` MP_TAC THENL
     [UNDISCH_TAC `u + v + w = &1` THEN UNDISCH_TAC `u' + v' + w' = &1` THEN
      UNDISCH_TAC `u = u' + w' * e` THEN UNDISCH_TAC `v * e + w = v' * e` THEN
      CONV_TAC REAL_RING;
      REWRITE_TAC[REAL_ENTIRE; ASSUME `~(&1 - e = &0)`]] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= w' * e` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `w = &0` SUBST_ALL_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXISTS_TAC `v:real` THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `u = &1 - v` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    STRIP_TAC THEN CONJ_TAC THEN
    MAP_EVERY EXISTS_TAC [`&1 - u`; `u:real`; `&0`] THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC])]);;

(* The two triangles of the trapezoid cover it.                            *)

let MOI_SS2_TRAP_UNION = prove
 (`!(x:real^N) y e.
     &0 < e /\ e < &1
     ==> convex hull {x,e % y,y} UNION convex hull {x,e % y,e % x} =
         {a % x + b % y | &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(&1 - e = &0) /\ ~(e = &0) /\ &0 < &1 - e`
  STRIP_ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!p. &0 <= p ==> e * p <= p /\ p * e <= p /\ &0 <= p * e`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 <= p * (&1 - e) /\ &0 <= p * e` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[CONVEX_HULL_3; EXTENSION; IN_UNION; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN EQ_TAC THENL
   [STRIP_TAC THENL
     [SUBGOAL_THEN `e * u <= u /\ &0 <= v * e /\ v * e <= v /\ e * w <= w`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `e * (u + v + w) = e` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`u:real`; `v * e + w:real`] THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN VECTOR_ARITH_TAC;
      SUBGOAL_THEN `e * u <= u /\ &0 <= w * e /\ w * e <= w /\
                    &0 <= v * e /\ v * e <= v`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `e * (u + v + w) = e` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_MUL_RID]; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`u + w * e:real`; `v * e:real`] THEN
      ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN VECTOR_ARITH_TAC];
    STRIP_TAC THEN ASM_CASES_TAC `e <= e * a + b` THENL
     [DISJ1_TAC THEN
      MAP_EVERY EXISTS_TAC [`a:real`; `(&1 - a - b) / (&1 - e)`;
                            `(b - e + e * a) / (&1 - e)`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        UNDISCH_TAC `~(&1 - e = &0)` THEN CONV_TAC REAL_FIELD;
        TRANS_TAC EQ_TRANS
         `a % x + (((&1 - a - b) / (&1 - e)) * e +
                   (b - e + e * a) / (&1 - e)) % (y:real^N)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MOI_SS2_LINCOMB_EQ THEN REWRITE_TAC[] THEN
          UNDISCH_TAC `~(&1 - e = &0)` THEN CONV_TAC REAL_FIELD;
          VECTOR_ARITH_TAC]];
      DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`(a + b - e) / (&1 - e)`; `b / e`;
                            `(e - e * a - b) / (e * (&1 - e))`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LE_DIV THEN CONJ_TAC THENL
         [ASM_REAL_ARITH_TAC;
          MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC];
        UNDISCH_TAC `~(&1 - e = &0)` THEN UNDISCH_TAC `~(e = &0)` THEN
        CONV_TAC REAL_FIELD;
        TRANS_TAC EQ_TRANS
         `((a + b - e) / (&1 - e) + ((e - e * a - b) / (e * (&1 - e))) * e) %
          x + ((b / e) * e) % (y:real^N)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MOI_SS2_LINCOMB_EQ THEN
          UNDISCH_TAC `~(&1 - e = &0)` THEN UNDISCH_TAC `~(e = &0)` THEN
          CONV_TAC REAL_FIELD;
          VECTOR_ARITH_TAC]]]]);;

(* The trapezoid is a PL disk bounded by its four edges.                   *)

let MOI_SS2_TRAP = prove
 (`!(x:real^N) y e.
     ~collinear{vec 0,x,y} /\ &0 < e /\ e < &1
     ==> moi_fsa_disk
           {a % x + b % y | &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1}
           (segment[x,y] UNION segment[y,e % y] UNION
            segment[e % y,e % x] UNION segment[e % x,x])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `e:real`]
    MOI_SS2_TRAP_NONCOLLINEAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `e:real`] MOI_SS2_TRAP_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`x:real^N`; `y:real^N`; `e:real`] MOI_SS2_TRAP_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`convex hull {x:real^N,e % y,y}`;
                 `relative_frontier(convex hull {x:real^N,e % y,y})`;
                 `x:real^N`; `e % y:real^N`; `e % x:real^N`]
    MOI_FSA_ATTACH1) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSA_DISK_TRI THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
      ASM_MESON_TAC[];
      ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(s:real^N->bool) = t ==> moi_fsa_disk (d:real^N->bool) s
                              ==> moi_fsa_disk d t`) THEN
  REWRITE_TAC[SET_RULE
   `((a:real^N->bool) UNION b) DIFF c = (a DIFF c) UNION (b DIFF c)`] THEN
  ASM_SIMP_TAC[MOI_FSA_TRI_RF_DIFF] THEN
  REWRITE_TAC[SEGMENT_SYM] THEN SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 3. The standard 3-simplex conv {0, e1, e2, e3} of real^3 in coordinates. *)
(* ------------------------------------------------------------------------- *)

let MOI_SS2_COORDS2 = prove
 (`!(P:real->real->bool) z:real^3.
     ((?a b. P a b /\ z = a % basis 1 + b % basis 2) <=>
      z$3 = &0 /\ P (z$1) (z$2)) /\
     ((?a b. P a b /\ z = a % basis 2 + b % basis 3) <=>
      z$1 = &0 /\ P (z$2) (z$3)) /\
     ((?a b. P a b /\ z = a % basis 3 + b % basis 1) <=>
      z$2 = &0 /\ P (z$3) (z$1))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; REAL_ADD_LID] THEN
  MESON_TAC[]);;

let MOI_SS2_COORDS3 = prove
 (`!(P:real->real->real->bool) z:real^3.
     (?u v w. P u v w /\ z = u % basis 1 + v % basis 2 + w % basis 3) <=>
     P (z$1) (z$2) (z$3)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID; REAL_ADD_RID; REAL_ADD_LID] THEN
  MESON_TAC[]);;

let MOI_SS2_STD_POINTS = prove
 (`!(z:real^3) e.
     (z = basis 1 <=> z$1 = &1 /\ z$2 = &0 /\ z$3 = &0) /\
     (z = basis 2 <=> z$1 = &0 /\ z$2 = &1 /\ z$3 = &0) /\
     (z = basis 3 <=> z$1 = &0 /\ z$2 = &0 /\ z$3 = &1) /\
     (z = e % basis 1 <=> z$1 = e /\ z$2 = &0 /\ z$3 = &0) /\
     (z = e % basis 2 <=> z$1 = &0 /\ z$2 = e /\ z$3 = &0) /\
     (z = e % basis 3 <=> z$1 = &0 /\ z$2 = &0 /\ z$3 = e) /\
     (z = vec 0 <=> z$1 = &0 /\ z$2 = &0 /\ z$3 = &0)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_MUL_COMPONENT;
              VEC_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[REAL_MUL_RZERO; REAL_MUL_RID]);;

let MOI_SS2_STD_NONCOL3 = prove
 (`~collinear{vec 0:real^3,basis 1,basis 2} /\
   ~collinear{vec 0:real^3,basis 2,basis 3} /\
   ~collinear{vec 0:real^3,basis 3,basis 1} /\
   ~collinear{basis 1:real^3,basis 2,basis 3}`,
  REWRITE_TAC[COLLINEAR_LEMMA] THEN ONCE_REWRITE_TAC[COLLINEAR_3] THEN
  REWRITE_TAC[COLLINEAR_LEMMA] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_MUL_COMPONENT;
              VECTOR_SUB_COMPONENT; VEC_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
  REWRITE_TAC[NOT_EXISTS_THM; DE_MORGAN_THM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC);;

let MOI_SS2_STD_SB = prove
 (`{basis i | 1 <= i /\ i <= dimindex(:3)} = {basis 1:real^3,basis 2,basis 3}`,
  REWRITE_TAC[DIMINDEX_3; EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `i = 1 \/ i = 2 \/ i = 3` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THENL
     [EXISTS_TAC `1`; EXISTS_TAC `2`; EXISTS_TAC `3`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let MOI_SS2_STD_F0 = prove
 (`convex hull {basis 1:real^3,basis 2,basis 3} =
   {z:real^3 | &0 <= z$1 /\ &0 <= z$2 /\ &0 <= z$3 /\ z$1 + z$2 + z$3 = &1}`,
  REWRITE_TAC[CONVEX_HULL_3; EXTENSION; IN_ELIM_THM; MOI_SS2_COORDS3]);;

let MOI_SS2_STD_S0 = prove
 (`relative_frontier(convex hull {vec 0:real^3,basis 1,basis 2,basis 3}) =
   {z:real^3 | &0 <= z$1 /\ &0 <= z$2 /\ &0 <= z$3 /\
               z$1 + z$2 + z$3 <= &1 /\
               (z$1 = &0 \/ z$2 = &0 \/ z$3 = &0 \/ z$1 + z$2 + z$3 = &1)}`,
  SUBGOAL_THEN `{vec 0:real^3,basis 1,basis 2,basis 3} =
                vec 0 INSERT {basis i | 1 <= i /\ i <= dimindex(:3)}`
  SUBST1_TAC THENL [REWRITE_TAC[MOI_SS2_STD_SB]; ALL_TAC] THEN
  ABBREV_TAC
   `s = convex hull (vec 0 INSERT {basis i:real^3 | 1 <= i /\ i <= dimindex(:3)})` THEN
  SUBGOAL_THEN `~(interior s:real^3->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN
    REWRITE_TAC[INTERIOR_STD_SIMPLEX; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `vector[&1 / &4; &1 / &4; &1 / &4]:real^3` THEN
    REWRITE_TAC[IN_ELIM_THM; DIMINDEX_3; FORALL_3; SUM_3; VECTOR_3] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP RELATIVE_FRONTIER_NONEMPTY_INTERIOR) THEN
  SUBGOAL_THEN `closed (s:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s" THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
    REWRITE_TAC[MOI_SS2_STD_SB; FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN
  EXPAND_TAC "s" THEN REWRITE_TAC[STD_SIMPLEX; INTERIOR_STD_SIMPLEX] THEN
  REWRITE_TAC[DIMINDEX_3; FORALL_3; SUM_3; EXTENSION; IN_DIFF; IN_ELIM_THM] THEN
  GEN_TAC THEN REAL_ARITH_TAC);;

let MOI_SS2_STD_TRAPS = prove
 (`!e. {a % basis 1 + b % basis 2:real^3 |
        &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1} =
       {z:real^3 | z$3 = &0 /\ &0 <= z$1 /\ &0 <= z$2 /\
                   e <= z$1 + z$2 /\ z$1 + z$2 <= &1} /\
       {a % basis 2 + b % basis 3:real^3 |
        &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1} =
       {z:real^3 | z$1 = &0 /\ &0 <= z$2 /\ &0 <= z$3 /\
                   e <= z$2 + z$3 /\ z$2 + z$3 <= &1} /\
       {a % basis 3 + b % basis 1:real^3 |
        &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1} =
       {z:real^3 | z$2 = &0 /\ &0 <= z$3 /\ &0 <= z$1 /\
                   e <= z$3 + z$1 /\ z$3 + z$1 <= &1}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; MOI_SS2_COORDS2]);;

let MOI_SS2_STD_SEGS = prove
 (`!e. &0 < e /\ e < &1
   ==> segment[basis 1:real^3,basis 2] =
       {z:real^3 | z$3 = &0 /\ &0 <= z$1 /\ &0 <= z$2 /\ z$1 + z$2 = &1} /\
       segment[basis 2:real^3,e % basis 2] =
       {z:real^3 | z$3 = &0 /\ z$1 = &0 /\ e <= z$2 /\ z$2 <= &1} /\
       segment[e % basis 2:real^3,e % basis 1] =
       {z:real^3 | z$3 = &0 /\ &0 <= z$1 /\ &0 <= z$2 /\ z$1 + z$2 = e} /\
       segment[e % basis 1:real^3,basis 1] =
       {z:real^3 | z$3 = &0 /\ z$2 = &0 /\ e <= z$1 /\ z$1 <= &1} /\
       segment[basis 2:real^3,basis 3] =
       {z:real^3 | z$1 = &0 /\ &0 <= z$2 /\ &0 <= z$3 /\ z$2 + z$3 = &1} /\
       segment[basis 3:real^3,e % basis 3] =
       {z:real^3 | z$1 = &0 /\ z$2 = &0 /\ e <= z$3 /\ z$3 <= &1} /\
       segment[e % basis 3:real^3,e % basis 2] =
       {z:real^3 | z$1 = &0 /\ &0 <= z$2 /\ &0 <= z$3 /\ z$2 + z$3 = e} /\
       segment[e % basis 2:real^3,basis 2] =
       {z:real^3 | z$1 = &0 /\ z$3 = &0 /\ e <= z$2 /\ z$2 <= &1} /\
       segment[basis 3:real^3,basis 1] =
       {z:real^3 | z$2 = &0 /\ &0 <= z$3 /\ &0 <= z$1 /\ z$3 + z$1 = &1} /\
       segment[basis 1:real^3,e % basis 1] =
       {z:real^3 | z$2 = &0 /\ z$3 = &0 /\ e <= z$1 /\ z$1 <= &1} /\
       segment[e % basis 1:real^3,e % basis 3] =
       {z:real^3 | z$2 = &0 /\ &0 <= z$3 /\ &0 <= z$1 /\ z$3 + z$1 = e} /\
       segment[e % basis 3:real^3,basis 3] =
       {z:real^3 | z$2 = &0 /\ z$1 = &0 /\ e <= z$3 /\ z$3 <= &1}`,
  GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun (x,y) ->
     MP_TAC(ISPECL [x; y] MOI_SS2_SEG_XY) THEN
     MP_TAC(ISPECL [x; y; `e:real`] MOI_SS2_SEG_YEY) THEN
     MP_TAC(ISPECL [x; y; `e:real`] MOI_SS2_SEG_EYEX) THEN
     MP_TAC(ISPECL [x; y; `e:real`] MOI_SS2_SEG_EXX))
   [`basis 1:real^3`,`basis 2:real^3`; `basis 2:real^3`,`basis 3:real^3`;
    `basis 3:real^3`,`basis 1:real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN SUBST1_TAC) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; MOI_SS2_COORDS2]);;

(* ------------------------------------------------------------------------- *)
(* 4. The flattening: the boundary of the standard 3-simplex minus a small  *)
(* corner at vec 0 is a PL disk bounded by the corner's rim.  It is glued   *)
(* from the far facet and the three trapezoids in the coordinate planes.    *)
(* All set identities are decided in coordinates.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_SS2_COORD_TAC =
  REWRITE_TAC[EXTENSION; SUBSET; IN_ELIM_THM; IN_UNION; IN_INTER; IN_DIFF;
              IN_INSERT; NOT_IN_EMPTY; MOI_SS2_STD_POINTS] THEN
  X_GEN_TAC `z:real^3` THEN
  UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `e < &1` THEN REAL_ARITH_TAC;;

let MOI_SS2_FLAT_COORD_TAC =
  MP_TAC(SPEC `e:real` MOI_SS2_STD_SEGS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[th; MOI_SS2_STD_F0; MOI_SS2_STD_TRAPS;
                                    MOI_SS2_STD_S0]) THEN
  MOI_SS2_COORD_TAC;;

let MOI_SS2_STD_DISTINCT = prove
 (`!e. &0 < e /\ e < &1
       ==> ~(basis 1:real^3 = basis 2) /\ ~(basis 2:real^3 = basis 3) /\
           ~(basis 3:real^3 = basis 1) /\ ~(e % basis 1:real^3 = basis 1) /\
           ~(e % basis 2:real^3 = basis 2) /\ ~(e % basis 3:real^3 = basis 3)`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_SS2_STD_POINTS; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC);;

let MOI_SS2_STD_DISKS = prove
 (`!e. &0 < e /\ e < &1
       ==> moi_fsa_disk (convex hull {basis 1:real^3,basis 2,basis 3})
             (segment[basis 1,basis 2] UNION segment[basis 2,basis 3] UNION
              segment[basis 3,basis 1]) /\
           moi_fsa_disk
             {a % basis 1 + b % basis 2:real^3 |
              &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1}
             (segment[basis 1,basis 2] UNION segment[basis 2,e % basis 2] UNION
              segment[e % basis 2,e % basis 1] UNION
              segment[e % basis 1,basis 1]) /\
           moi_fsa_disk
             {a % basis 2 + b % basis 3:real^3 |
              &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1}
             (segment[basis 2,basis 3] UNION segment[basis 3,e % basis 3] UNION
              segment[e % basis 3,e % basis 2] UNION
              segment[e % basis 2,basis 2]) /\
           moi_fsa_disk
             {a % basis 3 + b % basis 1:real^3 |
              &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1}
             (segment[basis 3,basis 1] UNION segment[basis 1,e % basis 1] UNION
              segment[e % basis 1,e % basis 3] UNION
              segment[e % basis 3,basis 3])`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `convex hull {basis 1:real^3,basis 2,basis 3}`
      MOI_FSA_DISK_TRI) THEN
    SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; MOI_SS2_STD_NONCOL3] THEN
    DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN MESON_TAC[MOI_SS2_STD_NONCOL3];
    MATCH_MP_TAC MOI_SS2_TRAP THEN ASM_REWRITE_TAC[MOI_SS2_STD_NONCOL3];
    MATCH_MP_TAC MOI_SS2_TRAP THEN ASM_REWRITE_TAC[MOI_SS2_STD_NONCOL3];
    MATCH_MP_TAC MOI_SS2_TRAP THEN ASM_REWRITE_TAC[MOI_SS2_STD_NONCOL3]]);;

(* Step 1: the facet and the trapezoid in the plane x3 = 0.               *)

let MOI_SS2_FLAT_STEP1 = prove
 (`!e. &0 < e /\ e < &1
       ==> moi_fsa_disk
            (convex hull {basis 1:real^3,basis 2,basis 3} UNION
             {a % basis 1 + b % basis 2:real^3 |
              &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1})
            (segment[basis 2:real^3,basis 3] UNION segment[basis 3,basis 1] UNION
             segment[basis 2,e % basis 2] UNION
             segment[e % basis 2,e % basis 1] UNION
             segment[e % basis 1,basis 1])`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `e:real` MOI_SS2_STD_DISTINCT) THEN
  MP_TAC(SPEC `e:real` MOI_SS2_STD_DISKS) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`convex hull {basis 1:real^3,basis 2,basis 3}`;
    `segment[basis 1:real^3,basis 2] UNION segment[basis 2,basis 3] UNION
     segment[basis 3,basis 1]`;
    `{a % basis 1 + b % basis 2:real^3 |
      &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1}`;
    `segment[basis 1:real^3,basis 2] UNION segment[basis 2,e % basis 2] UNION
     segment[e % basis 2,e % basis 1] UNION segment[e % basis 1,basis 1]`;
    `linepath(basis 1:real^3,basis 2)`] MOI_FSA_GLUE) THEN
  ASM_SIMP_TAC[ARC_LINEPATH; MOI_PL2_PL_LINEPATH;
               MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL; PATH_IMAGE_LINEPATH;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN MOI_SS2_FLAT_COORD_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(j:real^3->bool) = j' ==> moi_fsa_disk (d:real^3->bool) j
                              ==> moi_fsa_disk d j'`) THEN
  SUBGOAL_THEN
   `(segment[basis 1,basis 2] DIFF {basis 1:real^3,basis 2}) INTER
    (segment[basis 2:real^3,basis 3] UNION segment[basis 3,basis 1] UNION
     segment[basis 2,e % basis 2] UNION
     segment[e % basis 2,e % basis 1] UNION
     segment[e % basis 1,basis 1]) = {}` MP_TAC THENL
   [MOI_SS2_FLAT_COORD_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`basis 3:real^3`; `basis 1:real^3`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`basis 2:real^3`; `basis 3:real^3`] ENDS_IN_SEGMENT) THEN
  SET_TAC[]);;

(* Step 2: the trapezoid in the plane x1 = 0.                             *)

let MOI_SS2_FLAT_STEP2 = prove
 (`!e. &0 < e /\ e < &1
       ==> moi_fsa_disk
            ((convex hull {basis 1:real^3,basis 2,basis 3} UNION
              {a % basis 1 + b % basis 2:real^3 |
               &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1}) UNION
             {a % basis 2 + b % basis 3:real^3 |
              &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1})
            (segment[basis 3:real^3,basis 1] UNION
             segment[e % basis 2,e % basis 1] UNION
             segment[e % basis 1,basis 1] UNION
             segment[basis 3,e % basis 3] UNION
             segment[e % basis 3,e % basis 2])`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `e:real` MOI_SS2_STD_DISTINCT) THEN
  MP_TAC(SPEC `e:real` MOI_SS2_STD_DISKS) THEN
  MP_TAC(SPEC `e:real` MOI_SS2_FLAT_STEP1) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`convex hull {basis 1:real^3,basis 2,basis 3} UNION
     {a % basis 1 + b % basis 2:real^3 |
      &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1}`;
    `segment[basis 2:real^3,basis 3] UNION segment[basis 3,basis 1] UNION
     segment[basis 2,e % basis 2] UNION
     segment[e % basis 2,e % basis 1] UNION
     segment[e % basis 1,basis 1]`;
    `{a % basis 2 + b % basis 3:real^3 |
      &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1}`;
    `segment[basis 2:real^3,basis 3] UNION segment[basis 3,e % basis 3] UNION
     segment[e % basis 3,e % basis 2] UNION segment[e % basis 2,basis 2]`;
    `linepath(e % basis 2:real^3,basis 2) ++ linepath(basis 2,basis 3)`]
   MOI_FSA_GLUE) THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
               PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH;
               PATHFINISH_LINEPATH] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_JOIN THEN
      ASM_SIMP_TAC[ARC_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                   PATH_IMAGE_LINEPATH] THEN
      MOI_SS2_FLAT_COORD_TAC;
      MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
      SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
      MOI_SS2_FLAT_COORD_TAC;
      MOI_SS2_FLAT_COORD_TAC;
      MOI_SS2_FLAT_COORD_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `(j:real^3->bool) = j' ==> moi_fsa_disk (d:real^3->bool) j
                              ==> moi_fsa_disk d j'`) THEN
  SUBGOAL_THEN
   `((segment[e % basis 2,basis 2] UNION segment[basis 2,basis 3]) DIFF
     {e % basis 2:real^3,basis 3}) INTER
    (segment[basis 3:real^3,basis 1] UNION
     segment[e % basis 2,e % basis 1] UNION
     segment[e % basis 1,basis 1] UNION
     segment[basis 3,e % basis 3] UNION
     segment[e % basis 3,e % basis 2]) = {}` MP_TAC THENL
   [MOI_SS2_FLAT_COORD_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`e % basis 2:real^3`; `e % basis 1:real^3`]
    ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`basis 3:real^3`; `basis 1:real^3`] ENDS_IN_SEGMENT) THEN
  MP_TAC(ISPECL [`basis 2:real^3`; `e % basis 2:real^3`] (CONJUNCT1 SEGMENT_SYM)) THEN
  SET_TAC[]);;

(* Step 3: the trapezoid in the plane x2 = 0 closes the annulus.          *)

let MOI_SS2_FLAT_STD = prove
 (`!e. &0 < e /\ e < &1
       ==> moi_fsa_disk
             {z:real^3 | z IN relative_frontier
                                (convex hull {vec 0,basis 1,basis 2,basis 3}) /\
                         e <= z$1 + z$2 + z$3}
             {z:real^3 | z IN relative_frontier
                                (convex hull {vec 0,basis 1,basis 2,basis 3}) /\
                         z$1 + z$2 + z$3 = e}`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC `e:real` MOI_SS2_STD_DISTINCT) THEN
  MP_TAC(SPEC `e:real` MOI_SS2_STD_DISKS) THEN
  MP_TAC(SPEC `e:real` MOI_SS2_FLAT_STEP2) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`(convex hull {basis 1:real^3,basis 2,basis 3} UNION
      {a % basis 1 + b % basis 2:real^3 |
       &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1}) UNION
     {a % basis 2 + b % basis 3:real^3 |
      &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1}`;
    `segment[basis 3:real^3,basis 1] UNION
     segment[e % basis 2,e % basis 1] UNION
     segment[e % basis 1,basis 1] UNION
     segment[basis 3,e % basis 3] UNION
     segment[e % basis 3,e % basis 2]`;
    `{a % basis 3 + b % basis 1:real^3 |
      &0 <= a /\ &0 <= b /\ e <= a + b /\ a + b <= &1}`;
    `segment[basis 3:real^3,basis 1] UNION segment[basis 1,e % basis 1] UNION
     segment[e % basis 1,e % basis 3] UNION segment[e % basis 3,basis 3]`;
    `(linepath(e % basis 3:real^3,basis 3) ++ linepath(basis 3,basis 1)) ++
     linepath(basis 1,e % basis 1)`]
   MOI_FSA_GLUE) THEN
  ASM_SIMP_TAC[PATH_IMAGE_JOIN; PATHSTART_JOIN; PATHFINISH_JOIN;
               PATH_IMAGE_LINEPATH; PATHSTART_LINEPATH;
               PATHFINISH_LINEPATH] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC ARC_JOIN THEN
      ASM_SIMP_TAC[ARC_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                   PATH_IMAGE_LINEPATH; PATH_IMAGE_JOIN; PATHSTART_JOIN;
                   PATHFINISH_JOIN] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC ARC_JOIN THEN
        ASM_SIMP_TAC[ARC_LINEPATH; PATHSTART_LINEPATH; PATHFINISH_LINEPATH;
                     PATH_IMAGE_LINEPATH] THEN
        MOI_SS2_FLAT_COORD_TAC;
        MOI_SS2_FLAT_COORD_TAC];
      MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_JOIN; PATHFINISH_LINEPATH] THEN
      SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
      MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
      SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL;
               PATHSTART_LINEPATH; PATHFINISH_LINEPATH];
      MOI_SS2_FLAT_COORD_TAC;
      MOI_SS2_FLAT_COORD_TAC;
      MOI_SS2_FLAT_COORD_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC(MESON[]
   `!j'':real^3->bool.
      (d:real^3->bool) = d' /\ (j:real^3->bool) = j'' /\ j'' = j'
      ==> moi_fsa_disk d j ==> moi_fsa_disk d' j'`) THEN
  EXISTS_TAC
   `segment[e % basis 2:real^3,e % basis 1] UNION
    segment[e % basis 3,e % basis 2] UNION segment[e % basis 1,e % basis 3]` THEN
  REPEAT CONJ_TAC THENL
   [MOI_SS2_FLAT_COORD_TAC;
    SUBGOAL_THEN
     `(((segment[e % basis 3,basis 3] UNION segment[basis 3,basis 1]) UNION
        segment[basis 1,e % basis 1]) DIFF
       {e % basis 3:real^3,e % basis 1}) INTER
      (segment[e % basis 2:real^3,e % basis 1] UNION
       segment[e % basis 3,e % basis 2] UNION
       segment[e % basis 1,e % basis 3]) = {}` MP_TAC THENL
     [MOI_SS2_FLAT_COORD_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`e % basis 2:real^3`; `e % basis 1:real^3`]
      ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`e % basis 3:real^3`; `e % basis 2:real^3`]
      ENDS_IN_SEGMENT) THEN
    MP_TAC(ISPECL [`e % basis 1:real^3`; `basis 1:real^3`] (CONJUNCT1 SEGMENT_SYM)) THEN
    MP_TAC(ISPECL [`basis 3:real^3`; `e % basis 3:real^3`] (CONJUNCT1 SEGMENT_SYM)) THEN
    SET_TAC[];
    MOI_SS2_FLAT_COORD_TAC]);;

(* ------------------------------------------------------------------------- *)
(* 5. The two sides of a PL circle on the boundary of the standard simplex *)
(* that misses the vertex vec 0.  The corner {sum <= e} misses the circle  *)
(* for small e; the rest is flattened onto a triangle of real^2, where the *)
(* planar Schoenflies theorem and the Jordan curve theorem give the side   *)
(* not containing vec 0 as an open PL disk and the other side as a         *)
(* connected open set containing the corner.                               *)
(* ------------------------------------------------------------------------- *)

let MOI_SS2_STD_CORNER = prove
 (`!e. &0 < e /\ e < &1
       ==> vec 0 IN {z:real^3 | z IN relative_frontier
                                  (convex hull {vec 0,basis 1,basis 2,basis 3}) /\
                                z$1 + z$2 + z$3 <= e} /\
           connected {z:real^3 | z IN relative_frontier
                                  (convex hull {vec 0,basis 1,basis 2,basis 3}) /\
                                z$1 + z$2 + z$3 <= e} /\
           (!z:real^3. z IN relative_frontier
                              (convex hull {vec 0,basis 1,basis 2,basis 3}) /\
                       z$1 + z$2 + z$3 <= e
                       ==> norm z <= e)`,
  GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MOI_SS2_STD_S0; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VEC_COMPONENT] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC STARLIKE_IMP_CONNECTED THEN REWRITE_TAC[starlike] THEN
    EXISTS_TAC `vec 0:real^3` THEN
    REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT; SUBSET; IN_SEGMENT] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID;
                    VECTOR_MUL_COMPONENT] THEN
    SUBGOAL_THEN `!p. &0 <= p ==> &0 <= u * p /\ u * p <= p` ASSUME_TAC THENL
     [X_GEN_TAC `p:real` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 <= u * p /\ &0 <= (&1 - u) * p` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
        REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= u * (x:real^3)$1 /\ u * x$1 <= x$1 /\
                  &0 <= u * x$2 /\ u * x$2 <= x$2 /\
                  &0 <= u * x$3 /\ u * x$3 <= x$3` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3)$1 = &0 \/ x$2 = &0 \/ x$3 = &0` MP_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPEC `z:real^3` NORM_LE_L1) THEN
    REWRITE_TAC[DIMINDEX_3; SUM_3] THEN ASM_REAL_ARITH_TAC]);;

let MOI_SS2_STD_OPEN_LEVEL = prove
 (`!e. open {z:real^3 | e < z$1 + z$2 + z$3}`,
  GEN_TAC THEN
  SUBGOAL_THEN `{z:real^3 | e < z$1 + z$2 + z$3} =
                {z | (vector[&1; &1; &1]:real^3) dot z > e}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; DOT_3; VECTOR_3; real_gt] THEN
    REAL_ARITH_TAC;
    REWRITE_TAC[OPEN_HALFSPACE_GT]]);;

let MOI_SS2_LEVEL_SETS = prove
 (`!(s0:real^3->bool) e.
     s0 = {z | z IN s0 /\ e <= z$1 + z$2 + z$3} UNION
          {z | z IN s0 /\ z$1 + z$2 + z$3 <= e} /\
     {z | z IN s0 /\ e <= z$1 + z$2 + z$3} INTER
     {z | z IN s0 /\ z$1 + z$2 + z$3 <= e} =
     {z | z IN s0 /\ z$1 + z$2 + z$3 = e} /\
     {z | z IN s0 /\ z$1 + z$2 + z$3 = e} SUBSET
     {z | z IN s0 /\ z$1 + z$2 + z$3 <= e} /\
     {z | z IN s0 /\ e <= z$1 + z$2 + z$3} SUBSET s0 /\
     {z | z IN s0 /\ z$1 + z$2 + z$3 <= e} SUBSET s0 /\
     {z | z IN s0 /\ e <= z$1 + z$2 + z$3} DIFF
     {z | z IN s0 /\ z$1 + z$2 + z$3 = e} =
     s0 INTER {z | e < z$1 + z$2 + z$3}`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER; IN_DIFF; SUBSET; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THEN X_GEN_TAC `x:real^3` THEN
  ASM_CASES_TAC `(x:real^3) IN s0` THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_SS2_INJ_IMAGE = prove
 (`!(f:real^M->real^N) g k s t.
     (!x. x IN k ==> g (f x) = x) /\ s SUBSET k /\ t SUBSET k
     ==> IMAGE f s INTER IMAGE f t = IMAGE f (s INTER t) /\
         IMAGE f s DIFF IMAGE f t = IMAGE f (s DIFF t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_IMAGE] THEN ASM SET_TAC[]);;

let MOI_SS2_SIDES_STD = prove
 (`!j:real^3->bool.
     pl_sphere 1 j /\
     j SUBSET relative_frontier(convex hull {vec 0,basis 1,basis 2,basis 3}) /\
     ~(vec 0 IN j)
     ==> ?si so.
           si UNION so =
           relative_frontier(convex hull {vec 0,basis 1,basis 2,basis 3}) DIFF j /\
           si INTER so = {} /\
           open_in (subtopology euclidean
             (relative_frontier(convex hull {vec 0,basis 1,basis 2,basis 3}))) si /\
           open_in (subtopology euclidean
             (relative_frontier(convex hull {vec 0,basis 1,basis 2,basis 3}))) so /\
           connected si /\ connected so /\ vec 0 IN so /\
           moi_fsa_disk (si UNION j) j`,
  GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (j:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCD_PL_SPHERE_POLYHEDRON; PL_POLYHEDRON_IMP_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j:real^3->bool`; `vec 0:real^3`] SEPARATE_POINT_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; DIST_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `e = min (&1 / &2) (r / &2)` THEN
  SUBGOAL_THEN `&0 < e /\ e < &1 /\ e < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "e" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPEC `e:real` MOI_SS2_STD_CORNER) THEN
  MP_TAC(SPEC `e:real` MOI_SS2_FLAT_STD) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC
   `s0 = relative_frontier(convex hull {vec 0:real^3,basis 1,basis 2,basis 3})` THEN
  ABBREV_TAC `d = {z:real^3 | z IN s0 /\ e <= z$1 + z$2 + z$3}` THEN
  ABBREV_TAC `b = {z:real^3 | z IN s0 /\ z$1 + z$2 + z$3 = e}` THEN
  ABBREV_TAC `h = {z:real^3 | z IN s0 /\ z$1 + z$2 + z$3 <= e}` THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN
    `f:real^2->real^3` (X_CHOOSE_THEN `g:real^3->real^2`
    STRIP_ASSUME_TAC)) o REWRITE_RULE[moi_fsa_disk]) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s0:real^3->bool`; `e:real`] MOI_SS2_LEVEL_SETS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(j:real^3->bool) INTER h = {}` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN s0 /\ z$1 + z$2 + z$3 <= e` STRIP_ASSUME_TAC
    THENL
     [UNDISCH_TAC `(z:real^3) IN h` THEN EXPAND_TAC "h" THEN
      REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    MP_TAC(MATCH_MP (ASSUME `!x:real^3. x IN j ==> r <= norm x`)
                    (ASSUME `(z:real^3) IN j`)) THEN
    MP_TAC(MATCH_MP (ASSUME
     `!z:real^3. z IN s0 /\ z$1 + z$2 + z$3 <= e ==> norm z <= e`)
     (CONJ (ASSUME `(z:real^3) IN s0`)
           (ASSUME `(z:real^3)$1 + z$2 + z$3 <= e`))) THEN
    UNDISCH_TAC `e < r` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET d /\ j INTER b = {}` STRIP_ASSUME_TAC
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior k = interior (k:real^2->bool) /\
                k DIFF relative_frontier k = interior k /\
                closed k /\ convex k /\ compact k`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `compact (k:real^2->bool) /\ convex k` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT;
                    SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    SUBGOAL_THEN `relative_interior k = interior (k:real^2->bool)` ASSUME_TAC
    THENL
     [MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
      REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_2] THEN
      ASM_MESON_TAC[AFF_DIM_SIMPLEX];
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; relative_frontier; CLOSURE_CLOSED] THEN
    MP_TAC(ISPEC `k:real^2->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `jj = IMAGE (g:real^3->real^2) j` THEN
  SUBGOAL_THEN `jj SUBSET interior (k:real^2->bool) /\
                IMAGE (f:real^2->real^3) jj = j`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "jj" THEN CONJ_TAC THENL
     [UNDISCH_TAC `k DIFF relative_frontier k = interior (k:real^2->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_DIFF] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN d` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
      SUBGOAL_THEN `(f:real^2->real^3) ((g:real^3->real^2) y) IN b`
      MP_TAC THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]] THEN ASM SET_TAC[];
      REWRITE_TAC[GSYM IMAGE_o] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x:real^3. x IN j ==> (f:real^3->real^3) x = x) ==> IMAGE f j = j`) THEN
      REWRITE_TAC[o_THM] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (jj:real^2->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "jj" THEN MATCH_MP_TAC MOI_SS2_SPHERE1_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`d:real^3->bool`; `k:real^2->bool`;
                          `f:real^2->real^3`] THEN
    ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^2->bool`; `jj:real^2->bool`] MOI_SS2_PLANAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(jj:real^2->bool) SUBSET k /\ inside jj SUBSET k /\
    inside jj INTER jj = {} /\ outside jj INTER jj = {} /\
    relative_frontier k SUBSET (k:real^2->bool) /\
    relative_frontier k INTER inside jj = {} /\
    ~(relative_frontier k:real^2->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INSIDE_NO_OVERLAP; OUTSIDE_NO_OVERLAP] THEN
    MP_TAC(ISPECL [`k:real^2->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `k:real^2->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `k:real^2->bool` RELATIVE_FRONTIER_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `k DIFF relative_frontier k = interior (k:real^2->bool)` THEN
    UNDISCH_TAC `inside jj SUBSET interior (k:real^2->bool)` THEN
    UNDISCH_TAC `jj SUBSET interior (k:real^2->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (f:real^2->real^3) (inside jj)` THEN
  EXISTS_TAC `IMAGE (f:real^2->real^3) (k INTER outside jj) UNION h` THEN
  MP_TAC(ISPECL [`f:real^2->real^3`; `g:real^3->real^2`; `k:real^2->bool`]
    MOI_SS2_INJ_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MAP_EVERY (fun (s,t) ->
    MP_TAC(MATCH_MP (ASSUME `!s t. s SUBSET k /\ t SUBSET k
                   ==> IMAGE (f:real^2->real^3) s INTER IMAGE f t =
                       IMAGE f (s INTER t) /\
                       IMAGE f s DIFF IMAGE f t = IMAGE f (s DIFF t)`)
              (CONJ (ASSUME s) (ASSUME t))))
   [`inside jj SUBSET (k:real^2->bool)`,`(jj:real^2->bool) SUBSET k`;
    `inside jj SUBSET (k:real^2->bool)`,`relative_frontier k SUBSET (k:real^2->bool)`] THEN
  MP_TAC(MATCH_MP (ASSUME `!s t. s SUBSET k /\ t SUBSET k
                   ==> IMAGE (f:real^2->real^3) s INTER IMAGE f t =
                       IMAGE f (s INTER t) /\
                       IMAGE f s DIFF IMAGE f t = IMAGE f (s DIFF t)`)
         (CONJ (ASSUME `inside jj SUBSET (k:real^2->bool)`)
               (SET_RULE `(k:real^2->bool) INTER outside jj SUBSET k`))) THEN
  MP_TAC(MATCH_MP (ASSUME `!s t. s SUBSET k /\ t SUBSET k
                   ==> IMAGE (f:real^2->real^3) s INTER IMAGE f t =
                       IMAGE f (s INTER t) /\
                       IMAGE f s DIFF IMAGE f t = IMAGE f (s DIFF t)`)
         (CONJ (SET_RULE `(k:real^2->bool) SUBSET k`)
               (ASSUME `(jj:real^2->bool) SUBSET k`))) THEN
  REPEAT(DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^3) (inside jj) INTER j = {}` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^2->real^3) jj = j`;
      `IMAGE (f:real^2->real^3) (inside jj) INTER IMAGE f jj =
       IMAGE f (inside jj INTER jj)`;
      `inside jj INTER jj:real^2->bool = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^3) (inside jj) SUBSET d DIFF b`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^2->real^3) k = d`;
      `IMAGE (f:real^2->real^3) (relative_frontier k) = b`;
      `IMAGE (f:real^2->real^3) (inside jj) INTER IMAGE f (relative_frontier k) =
       IMAGE f (inside jj INTER relative_frontier k)`;
      `relative_frontier k INTER inside jj:real^2->bool = {}`;
      `inside jj SUBSET (k:real^2->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^2->real^3) (inside jj) INTER
    (IMAGE f (k INTER outside jj) UNION h) = {}` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^2->real^3) (inside jj) SUBSET d DIFF b`;
      `d INTER h:real^3->bool = b`;
      `IMAGE (f:real^2->real^3) (inside jj) INTER IMAGE f (k INTER outside jj) =
       IMAGE f (inside jj INTER k INTER outside jj)`;
      `inside jj INTER outside jj:real^2->bool = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^2->real^3) (inside jj) UNION
    (IMAGE f (k INTER outside jj) UNION h) = (d UNION h) DIFF j`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^2->real^3) k = d`;
      `IMAGE (f:real^2->real^3) jj = j`;
      `IMAGE (f:real^2->real^3) k DIFF IMAGE f jj = IMAGE f (k DIFF jj)`;
      `(j:real^3->bool) INTER h = {}`;
      `inside jj UNION outside jj = (:real^2) DIFF jj`;
      `inside jj SUBSET (k:real^2->bool)`;
      `inside jj INTER jj:real^2->bool = {}`] THEN
    REWRITE_TAC[IMAGE_UNION] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `open_in (subtopology euclidean d)
                          (IMAGE (f:real^2->real^3) (inside jj))` MP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`g:real^3->real^2`; `k:real^2->bool`] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[homeomorphism]; ALL_TAC] THEN
      REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `inside jj:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `u INTER {z:real^3 | e < z$1 + z$2 + z$3}` THEN
    ASM_SIMP_TAC[OPEN_INTER; MOI_SS2_STD_OPEN_LEVEL] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^2->real^3) (inside jj) = d INTER u`;
      `IMAGE (f:real^2->real^3) (inside jj) SUBSET d DIFF b`;
      `d DIFF b = s0 INTER {z:real^3 | e < z$1 + z$2 + z$3}`;
      `s0 = (d:real^3->bool) UNION h`] THEN
    SET_TAC[];
    SUBGOAL_THEN `compact (j UNION IMAGE (f:real^2->real^3) (inside jj))`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `j UNION IMAGE (f:real^2->real^3) (inside jj) =
                    IMAGE f (jj UNION inside jj)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[IMAGE_UNION]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^2->bool` THEN
      ASM_REWRITE_TAC[UNION_SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `(:real^3) DIFF (j UNION IMAGE (f:real^2->real^3) (inside jj))` THEN
    ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^2->real^3) (inside jj) INTER j = {}`;
      `IMAGE (f:real^2->real^3) (inside jj) INTER
       (IMAGE f (k INTER outside jj) UNION h) = {}`;
      `IMAGE (f:real^2->real^3) (inside jj) UNION
       (IMAGE f (k INTER outside jj) UNION h) = (d UNION h) DIFF j`] THEN
    SET_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^2->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^2->bool` THEN
      REWRITE_TAC[INTER_SUBSET] THEN ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (f:real^2->real^3) (relative_frontier k) = b`;
        `~(relative_frontier k:real^2->bool = {})`;
        `relative_frontier k SUBSET (k:real^2->bool) INTER outside jj`;
        `(b:real^3->bool) SUBSET h`] THEN
      SET_TAC[]];
    ASM_REWRITE_TAC[IN_UNION];
    MP_TAC(ISPECL [`jj UNION inside jj:real^2->bool`; `jj:real^2->bool`;
                   `k:real^2->bool`; `d:real^3->bool`; `f:real^2->real^3`;
                   `g:real^3->real^2`] MOI_SS2_FSA_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[UNION_SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_UNION] THEN
    REWRITE_TAC[GSYM moi_fsa_disk] THEN MESON_TAC[UNION_COMM]]);;

(* ------------------------------------------------------------------------- *)
(* 6. Transport of the two sides through a PL homeomorphism from the       *)
(* boundary of the standard simplex that sends vec 0 to a point q off the  *)
(* circle.                                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_SS2_SIDES_PLH = prove
 (`!(s:real^3->bool) j q (p:real^3->real^3) p'.
     pl_homeomorphism
       (relative_frontier(convex hull {vec 0,basis 1,basis 2,basis 3}),s)
       (p,p') /\
     pl_sphere 1 j /\ j SUBSET s /\ p (vec 0) = q /\ ~(q IN j)
     ==> ?si so. si UNION so = s DIFF j /\ si INTER so = {} /\
                 open_in (subtopology euclidean s) si /\
                 open_in (subtopology euclidean s) so /\
                 connected si /\ connected so /\ q IN so /\
                 moi_fsa_disk (si UNION j) j`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC
   `s0 = relative_frontier(convex hull {vec 0:real^3,basis 1,basis 2,basis 3})` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [homeomorphism] th)) THEN
  MP_TAC(ISPEC `IMAGE (p':real^3->real^3) j` MOI_SS2_SIDES_STD) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_SS2_SPHERE1_IMAGE THEN
      MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `s0:real^3->bool`;
                            `p:real^3->real^3`] THEN
      ASM_REWRITE_TAC[DIMINDEX_3] THEN
      CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (p':real^3->real^3) s = s0`; `(j:real^3->bool) SUBSET s`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`!y:real^3. y IN s ==> (p:real^3->real^3) (p' y) = y`;
        `(p:real^3->real^3) (vec 0) = q`; `~((q:real^3) IN j)`;
        `(j:real^3->bool) SUBSET s`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `si0:real^3->bool` (X_CHOOSE_THEN
    `so0:real^3->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `IMAGE (p:real^3->real^3) si0` THEN
  EXISTS_TAC `IMAGE (p:real^3->real^3) so0` THEN
  SUBGOAL_THEN `(si0:real^3->bool) SUBSET s0 /\ so0 SUBSET s0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `si0 UNION so0 = s0 DIFF IMAGE (p':real^3->real^3) j` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_UNION] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`p:real^3->real^3`; `p':real^3->real^3`; `s0:real^3->bool`;
                   `s0:real^3->bool`; `IMAGE (p':real^3->real^3) j`]
      MOI_SS2_INJ_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL] THEN
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (p':real^3->real^3) s = s0`; `(j:real^3->bool) SUBSET s`] THEN
      SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2)] THEN
    ASM_REWRITE_TAC[GSYM IMAGE_o] THEN
    AP_TERM_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^3. x IN j ==> (f:real^3->real^3) x = x) ==> IMAGE f j = j`) THEN
    REWRITE_TAC[o_THM] THEN
    MAP_EVERY UNDISCH_TAC
     [`!y:real^3. y IN s ==> (p:real^3->real^3) (p' y) = y`;
      `(j:real^3->bool) SUBSET s`] THEN
    SET_TAC[];
    MP_TAC(ISPECL [`p:real^3->real^3`; `p':real^3->real^3`; `s0:real^3->bool`;
                   `si0:real^3->bool`; `so0:real^3->bool`]
      MOI_SS2_INJ_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES];
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`p':real^3->real^3`; `s0:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`p':real^3->real^3`; `s0:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^3` THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`si0 UNION IMAGE (p':real^3->real^3) j`;
                   `IMAGE (p':real^3->real^3) j`; `s0:real^3->bool`;
                   `s:real^3->bool`; `p:real^3->real^3`; `p':real^3->real^3`]
      MOI_SS2_FSA_IMAGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (p':real^3->real^3) s = s0`; `(j:real^3->bool) SUBSET s`;
        `(si0:real^3->bool) SUBSET s0`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(MESON[]
     `(d:real^3->bool) = d' /\ (j:real^3->bool) = j'
      ==> moi_fsa_disk d j ==> moi_fsa_disk d' j'`) THEN
    REWRITE_TAC[IMAGE_UNION; GSYM IMAGE_o] THEN
    SUBGOAL_THEN `IMAGE ((p:real^3->real^3) o p') j = j`
     (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^3. x IN j ==> (f:real^3->real^3) x = x) ==> IMAGE f j = j`) THEN
    MAP_EVERY UNDISCH_TAC
     [`!y:real^3. y IN s ==> (p:real^3->real^3) (p' y) = y`;
      `(j:real^3->bool) SUBSET s`] THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. From the standard simplex to an arbitrary one, and the swap of the    *)
(* two hemispheres (facet and cone) moving a facet point to the vertex.    *)
(* ------------------------------------------------------------------------- *)

let MOI_SS2_AFFINE_ISO = prove
 (`!w a b c:real^3.
     ~affine_dependent {w,a,b,c} /\ ~(w = a) /\ ~(w = b) /\ ~(w = c) /\
     ~(a = b) /\ ~(a = c) /\ ~(b = c)
     ==> ?(l:real^3->real^3) (l':real^3->real^3).
                linear l /\ linear l' /\ (!x. l' (l x) = x) /\
                (!y. l (l' y) = y) /\
                l (basis 1) = a - w /\ l (basis 2) = b - w /\
                l (basis 3) = c - w`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `l = \x:real^3. x$1 % (a - w:real^3) + x$2 % (b - w:real^3) +
                  x$3 % (c - w:real^3)` THEN
  SUBGOAL_THEN `linear (l:real^3->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN
    REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    CONJ_TAC THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^3->real^3) (basis 1) = a - w /\
                l (basis 2) = b - w /\ l (basis 3) = c - w`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REPEAT CONJ_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. ?x. (l:real^3->real^3) x = y` ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim {w:real^3,a,b,c} = &3` ASSUME_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `&(CARD {w:real^3,a,b,c}) - &1:int` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC AFF_DIM_AFFINE_INDEPENDENT THEN FIRST_ASSUM ACCEPT_TAC;
        ALL_TAC] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
               NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
      CONV_TAC INT_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `affine hull {w:real^3,a,b,c} = (:real^3)` MP_TAC THENL
     [ASM_REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3]; ALL_TAC] THEN
    MP_TAC(ISPECL [`w:real^3`; `{a:real^3,b,c}`] AFFINE_HULL_INSERT_SPAN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]; DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN `{x - w | x IN {a:real^3,b,c}} = {a - w,b - w,c - w}`
    SUBST1_TAC THENL
     [REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES]; ALL_TAC] THEN
    REWRITE_TAC[SPAN_3; EXTENSION; IN_UNIV; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w + y:real^3`) THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 MP_TAC
      ASSUME_TAC)) THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `r2:real`
      (X_CHOOSE_THEN `r3:real` ASSUME_TAC))) THEN
    EXISTS_TAC `vector[r1; r2; r3]:real^3` THEN
    EXPAND_TAC "l" THEN REWRITE_TAC[VECTOR_3] THEN
    UNDISCH_TAC `w + y:real^3 = w + v` THEN
    UNDISCH_TAC `v = r1 % (a - w) + r2 % (b - w) + r3 % (c - w:real^3)` THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `l:real^3->real^3` LINEAR_SURJECTIVE_ISOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^3->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`l:real^3->real^3`; `l':real^3->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_SS2_AFFINE_IMAGES = prove
 (`!(l:real^N->real^N) w s.
     linear l /\ (!x y. l x = l y ==> x = y)
     ==> IMAGE (\x. w + l x) (convex hull s) =
         convex hull (IMAGE (\x. w + l x) s) /\
         relative_frontier (IMAGE (\x. w + l x) s) =
         IMAGE (\x. w + l x) (relative_frontier s) /\
         relative_interior (IMAGE (\x. w + l x) s) =
         IMAGE (\x. w + l x) (relative_interior s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t. IMAGE (\x:real^N. w + l x) t =
                    IMAGE (\x. w + x) (IMAGE (l:real^N->real^N) t)`
   (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF]; ALL_TAC] THEN
  REWRITE_TAC[CONVEX_HULL_TRANSLATION; RELATIVE_FRONTIER_TRANSLATION;
              RELATIVE_INTERIOR_TRANSLATION] THEN
  ASM_SIMP_TAC[CONVEX_HULL_LINEAR_IMAGE;
               MATCH_MP RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE
                (CONJ (ASSUME `linear (l:real^N->real^N)`)
                      (ASSUME `!x y:real^N. (l:real^N->real^N) x = l y
                                            ==> x = y`));
               MATCH_MP RELATIVE_INTERIOR_INJECTIVE_LINEAR_IMAGE
                (CONJ (ASSUME `linear (l:real^N->real^N)`)
                      (ASSUME `!x y:real^N. (l:real^N->real^N) x = l y
                                            ==> x = y`))]);;

let MOI_SS2_AFFINE_PLH = prove
 (`!(l:real^N->real^N) l' w.
     linear l /\ linear l' /\ (!x. l' (l x) = x) /\ (!y. l (l' y) = y)
     ==> pl_homeomorphism ((:real^N),(:real^N))
           ((\x. w + l x),(\y. l' (y - w)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\y:real^N. (l':real^N->real^N) (y - w)) =
                (\y. l' y + --(l' w))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN ASM_SIMP_TAC[LINEAR_SUB] THEN
    REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(\x:real^N. w + (l:real^N->real^N) x) = (\x. l x + w)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN REPEAT GEN_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism; IN_UNIV] THEN
  ASM_SIMP_TAC[PL_MAP_ON_AFFINE; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_NEG] THEN
  REWRITE_TAC[VECTOR_ARITH `(x + --a) + a:real^N = x`;
              VECTOR_ARITH `(x + a) + --a:real^N = x`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `y:real^N` THEN
    EXISTS_TAC `(l':real^N->real^N) y + --(l' w)` THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_NEG] THEN VECTOR_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST];
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV] THEN X_GEN_TAC `x:real^N` THEN
    EXISTS_TAC `(l:real^N->real^N) x + w` THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_NEG] THEN VECTOR_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON; CONTINUOUS_ON_CONST]]);;

let MOI_SS2_SIMPLEX_PLH = prove
 (`!w a b c:real^3.
     ~affine_dependent {w,a,b,c} /\ ~(w = a) /\ ~(w = b) /\ ~(w = c) /\
     ~(a = b) /\ ~(a = c) /\ ~(b = c)
     ==> ?(m:real^3->real^3) m'.
           pl_homeomorphism
            (relative_frontier(convex hull {vec 0,basis 1,basis 2,basis 3}),
             relative_frontier(convex hull {w,a,b,c})) (m,m') /\
           m (vec 0) = w /\
           (!q. q IN relative_interior(convex hull {a,b,c})
                ==> m' q IN relative_interior
                              (convex hull {basis 1,basis 2,basis 3}) /\
                    m (m' q) = q)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^3`; `a:real^3`; `b:real^3`; `c:real^3`]
    MOI_SS2_AFFINE_ISO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^3->real^3` (X_CHOOSE_THEN
    `l':real^3->real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x y:real^3. (l:real^3->real^3) x = l y ==> x = y`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^3->real^3`; `l':real^3->real^3`; `w:real^3`]
    MOI_SS2_AFFINE_PLH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^3. w + (l:real^3->real^3) x)
      {vec 0,basis 1,basis 2,basis 3} = {w,a,b,c} /\
    IMAGE (\x:real^3. w + (l:real^3->real^3) x)
      {basis 1,basis 2,basis 3} = {a,b,c}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES;
                MATCH_MP LINEAR_0 (ASSUME `linear (l:real^3->real^3)`)] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `w + (a - w):real^3 = a`; VECTOR_ADD_RID];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^3->real^3`; `w:real^3`;
                 `{vec 0:real^3,basis 1,basis 2,basis 3}`]
    MOI_SS2_AFFINE_IMAGES) THEN
  MP_TAC(ISPECL [`l:real^3->real^3`; `w:real^3`;
                 `convex hull {vec 0:real^3,basis 1,basis 2,basis 3}`]
    MOI_SS2_AFFINE_IMAGES) THEN
  MP_TAC(ISPECL [`l:real^3->real^3`; `w:real^3`;
                 `{basis 1:real^3,basis 2,basis 3}`]
    MOI_SS2_AFFINE_IMAGES) THEN
  MP_TAC(ISPECL [`l:real^3->real^3`; `w:real^3`;
                 `convex hull {basis 1:real^3,basis 2,basis 3}`]
    MOI_SS2_AFFINE_IMAGES) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^3. w + (l:real^3->real^3) x`;
                 `\y:real^3. (l':real^3->real^3) (y - w)`;
                 `relative_frontier(convex hull
                    {vec 0:real^3,basis 1,basis 2,basis 3})`]
    MOI_SCD_PLH_RESTRICT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SA2_POLYTOPE_RF_POLYHEDRON THEN
    MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^3. w + (l:real^3->real^3) x)
      (relative_frontier(convex hull {vec 0,basis 1,basis 2,basis 3})) =
    relative_frontier(convex hull {w,a,b,c})`
  SUBST1_TAC THENL
   [UNDISCH_TAC
     `relative_frontier (IMAGE (\x:real^3. w + (l:real^3->real^3) x)
        (convex hull {vec 0,basis 1,basis 2,basis 3})) =
      IMAGE (\x. w + l x)
        (relative_frontier (convex hull {vec 0,basis 1,basis 2,basis 3}))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^3. w + (l:real^3->real^3) x`;
                        `\y:real^3. (l':real^3->real^3) (y - w)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MATCH_MP LINEAR_0 (ASSUME `linear (l:real^3->real^3)`);
                VECTOR_ADD_RID];
    ALL_TAC] THEN
  X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `w + (y - w):real^3 = y`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(q:real^3) IN IMAGE (\x:real^3. w + (l:real^3->real^3) x)
       (relative_interior (convex hull {basis 1,basis 2,basis 3}))`
  MP_TAC THENL
   [UNDISCH_TAC
     `relative_interior (IMAGE (\x:real^3. w + (l:real^3->real^3) x)
        (convex hull {basis 1,basis 2,basis 3})) =
      IMAGE (\x. w + l x)
        (relative_interior (convex hull {basis 1,basis 2,basis 3}))` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(w + x) - w:real^3 = x`]]);;

(* The facet F0 = conv {e1, e2, e3} seen from vec 0 and from a point of    *)
(* its relative interior.                                                  *)

let MOI_SS2_F0_FACTS = prove
 (`~(vec 0 IN convex hull {basis 1:real^3,basis 2,basis 3}) /\
   (!x y:real^3.
      x IN relative_frontier (convex hull {basis 1,basis 2,basis 3}) /\
      y IN relative_frontier (convex hull {basis 1,basis 2,basis 3}) /\
      y IN segment[vec 0,x] ==> y = x) /\
   polytope (convex hull {basis 1:real^3,basis 2,basis 3}) /\
   convex (convex hull {basis 1:real^3,basis 2,basis 3}) /\
   compact (convex hull {basis 1:real^3,basis 2,basis 3}) /\
   ~(relative_frontier (convex hull {basis 1:real^3,basis 2,basis 3}) = {}) /\
   relative_frontier (convex hull {basis 1:real^3,basis 2,basis 3}) SUBSET
   convex hull {basis 1,basis 2,basis 3} /\
   pl_polyhedron
     (relative_frontier (convex hull {basis 1:real^3,basis 2,basis 3}))`,
  SUBGOAL_THEN `polytope (convex hull {basis 1:real^3,basis 2,basis 3})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier (convex hull {basis 1:real^3,basis 2,basis 3})
                SUBSET convex hull {basis 1,basis 2,basis 3}` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CLOSED];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SA2_POLYTOPE_RF_POLYHEDRON; CONVEX_CONVEX_HULL;
               POLYTOPE_IMP_COMPACT] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_SS2_STD_F0; IN_ELIM_THM; VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN convex hull {basis 1,basis 2,basis 3} /\
                  (y:real^3) IN convex hull {basis 1,basis 2,basis 3}`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(y:real^3) IN segment[vec 0,x]` THEN
    REWRITE_TAC[IN_SEGMENT; MOI_SS2_STD_F0; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_RZERO; VECTOR_ADD_LID;
                    VECTOR_MUL_COMPONENT] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `u = &1` SUBST1_TAC THENL
     [UNDISCH_TAC `u * (x:real^3)$1 + u * x$2 + u * x$3 = &1` THEN
      UNDISCH_TAC `(x:real^3)$1 + x$2 + x$3 = &1` THEN
      CONV_TAC REAL_RING;
      REWRITE_TAC[VECTOR_MUL_LID]];
    MP_TAC(ISPECL [`convex hull {basis 1:real^3,basis 2,basis 3}`; `&2:int`]
      MOI_CON_SIMPLEX_RF_FACTS) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN CONV_TAC INT_REDUCE_CONV THEN
      MESON_TAC[MOI_SS2_STD_NONCOL3];
      SIMP_TAC[]]]);;

(* The swap: a PL homeomorphism of the boundary of the standard simplex   *)
(* exchanging the facet F0 and the cone over its boundary from vec 0,     *)
(* conewise, so that vec 0 goes to a given point of the relative interior *)
(* of F0.                                                                  *)

let MOI_SS2_SWAP = prove
 (`!q0:real^3.
     q0 IN relative_interior (convex hull {basis 1,basis 2,basis 3})
     ==> ?(p:real^3->real^3) p'.
                pl_homeomorphism
                 (relative_frontier(convex hull {vec 0,basis 1,basis 2,basis 3}),
                  relative_frontier(convex hull {vec 0,basis 1,basis 2,basis 3}))
                 (p,p') /\
                p (vec 0) = q0`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC MOI_SS2_F0_FACTS THEN
  MP_TAC(ISPECL [`basis 1:real^3`; `basis 2:real^3`; `basis 3:real^3`;
                 `vec 0:real^3`] MOI_FSA_RF_TETRA) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(INST_TYPE [`:3`,`:N`] AFFINE_INDEPENDENT_STDBASIS) THEN
      REWRITE_TAC[MOI_SS2_STD_SB; INSERT_AC];
      REWRITE_TAC[MOI_SS2_STD_POINTS; VEC_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC
   `(q0:real^3) IN relative_interior (convex hull {basis 1,basis 2,basis 3})` THEN
  ABBREV_TAC `f0 = convex hull {basis 1:real^3,basis 2,basis 3}` THEN
  ABBREV_TAC `r0 = relative_frontier(f0:real^3->bool)` THEN
  ABBREV_TAC `c0 = UNIONS {segment[vec 0:real^3,x] | x IN r0}` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS {segment[q0:real^3,x] | x IN r0} = f0` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `relative_frontier f0 = (r0:real^3->bool)`)) THEN MATCH_MP_TAC MOI_CON_CONE_RF THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((q0:real^3) IN r0) /\ ~((vec 0:real^3) IN r0) /\
                (!x y:real^3. x IN r0 /\ y IN r0 /\ y IN segment[q0,x]
                              ==> y = x)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `relative_frontier f0 = (r0:real^3->bool)`)) THEN
      UNDISCH_TAC `(q0:real^3) IN relative_interior f0` THEN
      REWRITE_TAC[relative_frontier] THEN SET_TAC[];
      ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      MATCH_MP_TAC(ISPECL [`f0:real^3->bool`; `q0:real^3`; `x:real^3`;
                           `y:real^3`] MOI_CON_RF_SEGMENT) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN r0` THEN UNDISCH_TAC `(y:real^3) IN r0` THEN
      SUBST1_TAC(SYM(ASSUME `relative_frontier f0 = (r0:real^3->bool)`)) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism ((r0:real^3->bool),r0) ((\x. x),(\x. x))`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID;
                GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`r0:real^3->bool`; `r0:real^3->bool`; `vec 0:real^3`;
                 `q0:real^3`; `\x:real^3. x`; `\x:real^3. x`]
    MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `aa = moi_con_conemap r0 (vec 0:real^3) q0 (\x:real^3. x)` THEN
  ABBREV_TAC `aa' = moi_con_conemap r0 (q0:real^3) (vec 0) (\x:real^3. x)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^3. x IN r0 ==> (aa':real^3->real^3) x = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXPAND_TAC "aa'" THEN
    MP_TAC(ISPECL [`r0:real^3->bool`; `q0:real^3`; `vec 0:real^3`;
                   `\x:real^3. x`; `x:real^3`] MOI_CON_CONEMAP_ON_BASE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(aa:real^3->real^3) (vec 0) = q0` ASSUME_TAC THENL
   [EXPAND_TAC "aa" THEN MATCH_MP_TAC MOI_CON_CONEMAP_APEX THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism ((f0:real^3->bool),c0)
                  ((aa':real^3->real^3),(aa:real^3->real^3))` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (c0:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f0:real^3->bool`; `c0:real^3->bool`;
                   `aa':real^3->real^3`; `aa:real^3->real^3`]
      MOI_PL2_PL_HOMEO_COMPACT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c0:real^3->bool`; `f0:real^3->bool`; `f0:real^3->bool`;
                 `c0:real^3->bool`; `aa:real^3->real^3`; `aa':real^3->real^3`;
                 `aa':real^3->real^3`; `aa:real^3->real^3`]
    MOI_PL2_PL_HOMEOMORPHISM_UNION) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`f0 INTER c0:real^3->bool = r0`;
        `!x:real^3. x IN r0 ==> (aa:real^3->real^3) x = x`;
        `!x:real^3. x IN r0 ==> (aa':real^3->real^3) x = x`] THEN
      SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`f0 INTER c0:real^3->bool = r0`;
        `!x:real^3. x IN r0 ==> (aa:real^3->real^3) x = x`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`\x:real^3. if x IN c0 then (aa:real^3->real^3) x else aa' x`;
    `\y:real^3. if y IN f0 then (aa':real^3->real^3) y else aa y`] THEN
  CONJ_TAC THENL
   [POP_ASSUM MP_TAC THEN
    MATCH_MP_TAC(MESON[]
     `(s:real^3->bool) = s' /\ (t:real^3->bool) = t'
      ==> pl_homeomorphism (s,t) (f:real^3->real^3,g)
          ==> pl_homeomorphism (s',t') (f,g)`) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(vec 0:real^3) IN c0` (fun th -> ASM_REWRITE_TAC[th]) THEN
    EXPAND_TAC "c0" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    UNDISCH_TAC `~(r0:real^3->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^3`) THEN
    EXISTS_TAC `segment[vec 0:real^3,x]` THEN
    REWRITE_TAC[ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[]]);;

(* The two sides of a PL circle in the boundary of a 3-simplex, seen from  *)
(* a point q of the relative interior of a facet off the circle.           *)

let MOI_SS2_SIDES_FACET = prove
 (`!w a b c j (q:real^3).
     ~affine_dependent {w,a,b,c} /\ ~(w = a) /\ ~(w = b) /\ ~(w = c) /\
     ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
     pl_sphere 1 j /\ j SUBSET relative_frontier(convex hull {w,a,b,c}) /\
     q IN relative_interior(convex hull {a,b,c}) /\ ~(q IN j)
     ==> ?si so.
           si UNION so = relative_frontier(convex hull {w,a,b,c}) DIFF j /\
           si INTER so = {} /\
           open_in (subtopology euclidean
                      (relative_frontier(convex hull {w,a,b,c}))) si /\
           open_in (subtopology euclidean
                      (relative_frontier(convex hull {w,a,b,c}))) so /\
           connected si /\ connected so /\ q IN so /\
           moi_fsa_disk (si UNION j) j`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`w:real^3`; `a:real^3`; `b:real^3`; `c:real^3`]
    MOI_SS2_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^3->real^3` (X_CHOOSE_THEN
    `m':real^3->real^3` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:real^3`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `(m':real^3->real^3) q` MOI_SS2_SWAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^3` (X_CHOOSE_THEN
    `p':real^3->real^3` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_SS2_SIDES_PLH THEN
  MAP_EVERY EXISTS_TAC [`(m:real^3->real^3) o (p:real^3->real^3)`;
                        `(p':real^3->real^3) o (m':real^3->real^3)`] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC
   `relative_frontier(convex hull {vec 0:real^3,basis 1,basis 2,basis 3})` THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 8. Points off the circle in facet interiors (invariance of domain),     *)
(* density of facet interiors, connected sets in a separation.             *)
(* ------------------------------------------------------------------------- *)

let MOI_SS2_FSA_PROPER = prove
 (`!(d:real^N->bool) j. moi_fsa_disk d j ==> ?x. x IN d /\ ~(x IN j)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsa_disk] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->bool` (X_CHOOSE_THEN `f:real^2->real^N`
    (X_CHOOSE_THEN `g:real^N->real^2` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k:real^2->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&2 simplex ({}:real^2->bool)` THEN
    REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (k:real^2->bool) /\ closed k` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLEX_IMP_CONVEX THEN EXISTS_TAC `&2:int` THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC POLYTOPE_IMP_CLOSED THEN
      MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `&2:int` THEN
      FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior (k:real^2->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x0:real^2`) THEN
  EXISTS_TAC `(f:real^2->real^N) x0` THEN
  SUBGOAL_THEN `(x0:real^2) IN k /\ ~(x0 IN relative_frontier k) /\
                relative_frontier k SUBSET k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^2->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `k:real^2->bool` RELATIVE_FRONTIER_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x0:real^2) IN relative_interior k` THEN
    REWRITE_TAC[relative_frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^2->real^N) k = d` THEN
    UNDISCH_TAC `(x0:real^2) IN k` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^N) (relative_frontier k) = j` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^2) IN k` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^2) IN relative_frontier k` THEN
    UNDISCH_TAC `relative_frontier k SUBSET (k:real^2->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `x0:real^2 = y` SUBST_ALL_TAC THENL
   [MP_TAC(MATCH_MP (ASSUME
      `!x:real^2. x IN k ==> (g:real^N->real^2) (f x) = x`)
      (ASSUME `(x0:real^2) IN k`)) THEN
    MP_TAC(MATCH_MP (ASSUME
      `!x:real^2. x IN k ==> (g:real^N->real^2) (f x) = x`)
      (ASSUME `(y:real^2) IN k`)) THEN
    UNDISCH_TAC `(f:real^2->real^N) x0 = f y` THEN MESON_TAC[];
    UNDISCH_TAC `(y:real^2) IN relative_frontier k` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SS2_CONNECTED_IN_SIDE = prove
 (`!(x:real^N->bool) u v c.
     open_in (subtopology euclidean x) u /\
     open_in (subtopology euclidean x) v /\
     u INTER v = {} /\ connected c /\ c SUBSET u UNION v /\
     ~(c INTER u = {})
     ==> c SUBSET u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:real^N->bool) SUBSET x` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; UNION_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  UNDISCH_TAC `open_in (subtopology euclidean x) (u:real^N->bool)` THEN
  UNDISCH_TAC `open_in (subtopology euclidean x) (v:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `tv:real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `tu:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `connected (c:real^N->bool)` THEN
  REWRITE_TAC[CONNECTED_OPEN_IN; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`c INTER tu:real^N->bool`;
                             `c INTER tv:real^N->bool`]) THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  SUBGOAL_THEN `(?t:real^N->bool. open t /\ c INTER tu = c INTER t) /\
                (?t:real^N->bool. open t /\ c INTER tv = c INTER t)`
   (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM SET_TAC[]);;

(* A PL circle contains no relative interior point set of a 2-dimensional *)
(* convex set: invariance of domain sends it into the boundary of a       *)
(* triangle.                                                               *)

let MOI_SS2_NOT_FILL = prove
 (`!(j:real^3->bool) f.
     pl_sphere 1 j /\ convex f /\ ~(f = {}) /\ aff_dim f = &2
     ==> ?q. q IN relative_interior f /\ ~(q IN j)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SET_RULE `(?q:real^3. q IN s /\ ~(q IN t)) <=> ~(s SUBSET t)`] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `pl_sphere 1 (j:real^3->bool)` THEN
  REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN
    `h:real^3->real^3` (X_CHOOSE_THEN `h':real^3->real^3`
    STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_FRONTIER_SUBSET; SIMPLEX_IMP_POLYTOPE;
                  POLYTOPE_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h':real^3->real^3`; `affine hull f:real^3->bool`;
                 `affine hull k:real^3->bool`;
                 `relative_interior f:real^3->bool`]
    INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL;
                OPEN_IN_RELATIVE_INTERIOR] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] AFF_DIM_SIMPLEX) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `k:real^3->bool`]
        HULL_SUBSET) THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    DISCH_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h':real^3->real^3) (relative_interior f) SUBSET relative_interior k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^3. x IN relative_interior f` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h':real^3->real^3) x IN relative_interior k /\
                h' x IN relative_frontier k` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[relative_frontier] THEN SET_TAC[]]);;

(* Every nonempty relatively open subset of the boundary of a simplex meets *)
(* the relative interior of some facet.                                    *)

let MOI_SS2_DENSE_FACET = prove
 (`!(v:real^3->bool) u.
     ~affine_dependent v /\
     open_in (subtopology euclidean (relative_frontier(convex hull v))) u /\
     ~(u = {})
     ==> ?w q. w IN v /\ q IN u /\
               q IN relative_interior(convex hull (v DELETE w))`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^3`) THEN
  SUBGOAL_THEN `FINITE (v:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_IMP_FINITE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `polyhedron (convex hull v:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC POLYTOPE_IMP_POLYHEDRON THEN
    MATCH_MP_TAC POLYTOPE_CONVEX_HULL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `open_in (subtopology euclidean
                 (relative_frontier (convex hull v))) (u:real^3->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN relative_frontier(convex hull v) /\ y IN oo`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN u` THEN
    UNDISCH_TAC `u = relative_frontier (convex hull v) INTER (oo:real^3->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `convex hull v:real^3->bool` RELATIVE_FRONTIER_OF_POLYHEDRON) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `?t:real^3->bool. t facet_of convex hull v /\ y IN t`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN relative_frontier(convex hull v)` THEN
    ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^3->bool) SUBSET relative_frontier(convex hull v)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
     `(x:real^3->bool) IN f ==> x SUBSET UNIONS f`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  UNDISCH_TAC `t facet_of convex hull (v:real^3->bool)` THEN
  MP_TAC(ISPECL [`v:real^3->bool`; `t:real^3->bool`]
    FACET_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `convex (t:real^3->bool) /\ closed t` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONVEX_HULL THEN
    MATCH_MP_TAC FINITE_IMP_COMPACT THEN ASM_SIMP_TAC[FINITE_DELETE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(oo INTER relative_interior (t:real^3->bool) = {})`
  MP_TAC THENL
   [MP_TAC(ISPECL [`oo:real^3->bool`; `relative_interior t:real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    SIMP_TAC[ASSUME `open (oo:real^3->bool)`;
             MATCH_MP CONVEX_CLOSURE_RELATIVE_INTERIOR
               (ASSUME `convex (t:real^3->bool)`);
             MATCH_MP CLOSURE_CLOSED (ASSUME `closed (t:real^3->bool)`)] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `(y:real^3) IN oo` THEN UNDISCH_TAC `(y:real^3) IN t` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`w:real^3`; `q:real^3`] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN t` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(q:real^3) IN relative_interior t` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `u = relative_frontier (convex hull v) INTER (oo:real^3->bool)` THEN
    UNDISCH_TAC `(t:real^3->bool) SUBSET relative_frontier(convex hull v)` THEN
    UNDISCH_TAC `(q:real^3) IN t` THEN UNDISCH_TAC `(q:real^3) IN oo` THEN
    SET_TAC[];
    UNDISCH_TAC `(q:real^3) IN relative_interior t` THEN
    ASM_REWRITE_TAC[]]);;

(* The facet opposite any vertex of {w,a,b,c}.                            *)

let MOI_SS2_FACET_CASES = prove
 (`!w a b c u:real^3.
     ~(w = a) /\ ~(w = b) /\ ~(w = c) /\ ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
     u IN {w,a,b,c}
     ==> ?w' a' b' c'. {w',a',b',c'} = {w,a,b,c} /\
                       {w,a,b,c} DELETE u = {a',b',c'} /\
                       ~(w' = a') /\ ~(w' = b') /\ ~(w' = c') /\
                       ~(a' = b') /\ ~(a' = c') /\ ~(b' = c')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`w:real^3`; `a:real^3`; `b:real^3`; `c:real^3`];
    MAP_EVERY EXISTS_TAC [`a:real^3`; `w:real^3`; `b:real^3`; `c:real^3`];
    MAP_EVERY EXISTS_TAC [`b:real^3`; `w:real^3`; `a:real^3`; `c:real^3`];
    MAP_EVERY EXISTS_TAC [`c:real^3`; `w:real^3`; `a:real^3`; `b:real^3`]] THEN
  REPEAT CONJ_TAC THEN
  (FIRST_ASSUM ACCEPT_TAC ORELSE
   (CONV_TAC(RAND_CONV SYM_CONV) THEN FIRST_ASSUM ACCEPT_TAC) ORELSE
   ASM SET_TAC[]));;

(* ------------------------------------------------------------------------- *)
(* 9. SPHERE_SPLIT.  On the boundary of a 3-simplex: the sides at a facet   *)
(* point q1 off the circle; a facet point q2 on the inner side; the outer  *)
(* side at q2 lies in the inner side at q1, so the inner side at q2 is the *)
(* outer side at q1, and both closures are PL disks bounded by the circle. *)
(* ------------------------------------------------------------------------- *)

let MOI_SS2_SPLIT_T = prove
 (`!(w:real^3) a b c (j:real^3->bool).
     ~affine_dependent {w,a,b,c} /\ ~(w = a) /\ ~(w = b) /\ ~(w = c) /\
     ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
     pl_sphere 1 j /\ j SUBSET relative_frontier(convex hull {w,a,b,c})
     ==> ?d1 d2. moi_fsa_disk d1 j /\ moi_fsa_disk d2 j /\
                 d1 UNION d2 = relative_frontier(convex hull {w,a,b,c}) /\
                 d1 INTER d2 = j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`j:real^3->bool`; `convex hull {a:real^3,b,c}`]
    MOI_SS2_NOT_FILL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY;
                    NOT_INSERT_EMPTY; AFF_DIM_CONVEX_HULL] THEN
    SUBGOAL_THEN `~affine_dependent {a:real^3,b,c}` ASSUME_TAC THENL
     [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
      EXISTS_TAC `{w:real^3,a,b,c}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
             NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC INT_REDUCE_CONV;
    DISCH_THEN(X_CHOOSE_THEN `q1:real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`w:real^3`; `a:real^3`; `b:real^3`; `c:real^3`;
                 `j:real^3->bool`; `q1:real^3`] MOI_SS2_SIDES_FACET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `si1:real^3->bool` (X_CHOOSE_THEN
    `so1:real^3->bool` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `bt = relative_frontier(convex hull {w:real^3,a,b,c})` THEN
  SUBGOAL_THEN `~(si1:real^3->bool = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`si1 UNION j:real^3->bool`; `j:real^3->bool`]
      MOI_SS2_FSA_PROPER) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{w:real^3,a,b,c}`; `si1:real^3->bool`]
    MOI_SS2_DENSE_FACET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `q2:real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`w:real^3`; `a:real^3`; `b:real^3`; `c:real^3`; `u:real^3`]
    MOI_SS2_FACET_CASES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w':real^3` (X_CHOOSE_THEN `a':real^3`
    (X_CHOOSE_THEN `b':real^3` (X_CHOOSE_THEN `c':real^3`
    STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(si1:real^3->bool) SUBSET bt DIFF j /\ so1 SUBSET bt DIFF j`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `si1 UNION so1 = bt DIFF (j:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w':real^3`; `a':real^3`; `b':real^3`; `c':real^3`;
                 `j:real^3->bool`; `q2:real^3`] MOI_SS2_SIDES_FACET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(q2:real^3) IN
         relative_interior (convex hull ({w, a, b, c} DELETE u))` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(si1:real^3->bool) SUBSET bt DIFF j` THEN
      UNDISCH_TAC `(q2:real^3) IN si1` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `si2:real^3->bool` (X_CHOOSE_THEN
    `so2:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(so2:real^3->bool) SUBSET si1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SS2_CONNECTED_IN_SIDE THEN
    MAP_EVERY EXISTS_TAC [`bt:real^3->bool`; `so1:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`si2 UNION so2 = bt DIFF (j:real^3->bool)`;
        `si1 UNION so1 = bt DIFF (j:real^3->bool)`] THEN
      SET_TAC[];
      UNDISCH_TAC `(q2:real^3) IN si1` THEN
      UNDISCH_TAC `(q2:real^3) IN so2` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((si2:real^3->bool) INTER so1 = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`si2 UNION so2 = bt DIFF (j:real^3->bool)`;
      `si1 UNION so1 = bt DIFF (j:real^3->bool)`;
      `si1 INTER so1:real^3->bool = {}`;
      `(so2:real^3->bool) SUBSET si1`;
      `si2 INTER so1:real^3->bool = {}`;
      `(q1:real^3) IN so1`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(si2:real^3->bool) SUBSET so1` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SS2_CONNECTED_IN_SIDE THEN
    MAP_EVERY EXISTS_TAC [`bt:real^3->bool`; `si1:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `si1 INTER so1:real^3->bool = {}` THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`si2 UNION so2 = bt DIFF (j:real^3->bool)`;
        `si1 UNION so1 = bt DIFF (j:real^3->bool)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `si2:real^3->bool = so1` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`si2 UNION so2 = bt DIFF (j:real^3->bool)`;
      `si1 UNION so1 = bt DIFF (j:real^3->bool)`;
      `si1 INTER so1:real^3->bool = {}`;
      `(so2:real^3->bool) SUBSET si1`;
      `(si2:real^3->bool) SUBSET so1`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`si1 UNION j:real^3->bool`; `si2 UNION j:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
  MAP_EVERY UNDISCH_TAC
   [`si1 UNION so1 = bt DIFF (j:real^3->bool)`;
    `si1 INTER so1:real^3->bool = {}`;
    `(j:real^3->bool) SUBSET bt`] THEN
  SET_TAC[]);;

let SPHERE_SPLIT = prove
 (`!s j:real^3->bool.
     pl_sphere 2 s /\ pl_sphere 1 j /\ j SUBSET s
     ==> ?d1 d2. pl_cell_with_boundary 2 d1 j /\ pl_cell_with_boundary 2 d2 j /\
                 d1 UNION d2 = s /\ d1 INTER d2 = j`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `pl_sphere 2 (s:real^3->bool)` THEN
  REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN
    `g:real^3->real^3` (X_CHOOSE_THEN `g':real^3->real^3`
    STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `&3 simplex (k:real^3->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `vv:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(vv:real^3->bool) HAS_SIZE 4` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `(&(CARD (vv:real^3->bool)):int) = &3 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^3` (X_CHOOSE_THEN `a:real^3`
    (X_CHOOSE_THEN `b:real^3` (X_CHOOSE_THEN `c:real^3`
    STRIP_ASSUME_TAC)))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [homeomorphism] th)) THEN
  SUBGOAL_THEN `pl_sphere 1 (IMAGE (g':real^3->real^3) j)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SS2_SPHERE1_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `relative_frontier(convex hull {w:real^3,a,b,c})`;
                          `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN CONJ_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^3`; `a:real^3`; `b:real^3`; `c:real^3`;
                 `IMAGE (g':real^3->real^3) j`] MOI_SS2_SPLIT_T) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (g':real^3->real^3) s = relative_frontier(convex hull {w,a,b,c})`; `(j:real^3->bool) SUBSET s`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^3->bool` (X_CHOOSE_THEN
    `e2:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (g:real^3->real^3) (IMAGE g' j) = j` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^3. x IN j ==> (f:real^3->real^3) x = x) ==> IMAGE f j = j`) THEN
    MAP_EVERY UNDISCH_TAC
     [`!y:real^3. y IN s ==> (g:real^3->real^3) (g' y) = y`;
      `(j:real^3->bool) SUBSET s`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e1:real^3->bool) SUBSET relative_frontier(convex hull {w,a,b,c}) /\
                e2 SUBSET relative_frontier(convex hull {w,a,b,c})` STRIP_ASSUME_TAC
  THENL
   [UNDISCH_TAC `e1 UNION e2 = relative_frontier(convex hull {w:real^3,a,b,c})` THEN SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (g:real^3->real^3) e1`;
                        `IMAGE (g:real^3->real^3) e2`] THEN
  REWRITE_TAC[MOI_SS2_CELL_EQ_FSA] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`e1:real^3->bool`; `IMAGE (g':real^3->real^3) j`;
                   `relative_frontier(convex hull {w:real^3,a,b,c})`; `s:real^3->bool`; `g:real^3->real^3`;
                   `g':real^3->real^3`] MOI_SS2_FSA_IMAGE) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`e2:real^3->bool`; `IMAGE (g':real^3->real^3) j`;
                   `relative_frontier(convex hull {w:real^3,a,b,c})`; `s:real^3->bool`; `g:real^3->real^3`;
                   `g':real^3->real^3`] MOI_SS2_FSA_IMAGE) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[GSYM IMAGE_UNION];
    MP_TAC(ISPECL [`g:real^3->real^3`; `g':real^3->real^3`; `relative_frontier(convex hull {w:real^3,a,b,c})`;
                   `e1:real^3->bool`; `e2:real^3->bool`] MOI_SS2_INJ_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 10. DISK_UNION, PLANE_CELL_HULL, DISK_COMPLEMENT.                         *)
(* ------------------------------------------------------------------------- *)

(* The interior d DIFF j of a PL 2-cell d with boundary j.                 *)

let MOI_SS2_CELL_FACTS = prove
 (`!(d:real^N->bool) j.
     pl_cell_with_boundary 2 d j
     ==> ?(k:real^N->bool) (f:real^N->real^N) (g:real^N->real^N).
                 &2 simplex k /\ pl_homeomorphism (k,d) (f,g) /\
                 j = IMAGE f (relative_frontier k) /\
                 d DIFF j = IMAGE f (relative_interior k) /\
                 j SUBSET d /\ compact d /\ connected (d DIFF j) /\
                 ~(d DIFF j = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                        `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ compact k /\ ~(k = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLEX_IMP_CONVEX THEN EXISTS_TAC `&2:int` THEN
      FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC POLYTOPE_IMP_COMPACT THEN
      MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `&2:int` THEN
      FIRST_ASSUM ACCEPT_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `&2 simplex ({}:real^N->bool)` THEN
      REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_interior k SUBSET (k:real^N->bool) /\
    relative_frontier k SUBSET k /\
    relative_interior k INTER relative_frontier k = {} /\
    relative_interior k UNION relative_frontier k = k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `k:real^N->bool` CLOSURE_CLOSED) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; relative_frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `d DIFF j = IMAGE (f:real^N->real^N) (relative_interior k)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->real^N`; `g:real^N->real^N`; `k:real^N->bool`;
                   `k:real^N->bool`; `relative_frontier k:real^N->bool`]
      MOI_SS2_INJ_IMAGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`relative_interior k INTER relative_frontier k:real^N->bool = {}`;
      `relative_interior k UNION relative_frontier k = (k:real^N->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^N->real^N) k = d`;
      `IMAGE (f:real^N->real^N) (relative_frontier k) = j`;
      `relative_frontier k SUBSET (k:real^N->bool)`] THEN
    SET_TAC[];
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = d` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONVEX_CONNECTED THEN
      ASM_SIMP_TAC[CONVEX_RELATIVE_INTERIOR]];
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]]);;

let DISK_UNION = prove
 (`!d1 d2 j:real^3->bool.
     pl_cell_with_boundary 2 d1 j /\ pl_cell_with_boundary 2 d2 j /\
     d1 INTER d2 = j
     ==> pl_sphere 2 (d1 UNION d2)`,
  REWRITE_TAC[MOI_SS2_CELL_EQ_FSA] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d1:real^3->bool`; `d2:real^3->bool`; `j:real^3->bool`]
    MOI_FSA_TWO_DISKS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:real^(2,1)finite_sum->bool` (X_CHOOSE_THEN
    `f:real^(2,1)finite_sum->real^3` (X_CHOOSE_THEN
    `g:real^3->real^(2,1)finite_sum` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`2`; `relative_frontier kk:real^(2,1)finite_sum->bool`;
                 `d1 UNION d2:real^3->bool`; `f:real^(2,1)finite_sum->real^3`;
                 `g:real^3->real^(2,1)finite_sum`]
    MOI_CMB_PL_SPHERE_TRANSFER) THEN
  DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_2; DIMINDEX_1; DIMINDEX_3] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[]);;

(* A PL 2-cell inside another one with the same boundary is the same cell: *)
(* its interior is open (invariance of domain) and closed in the connected *)
(* interior of the bigger cell.                                            *)

let MOI_SS2_DISK_IN_DISK = prove
 (`!d e j:real^3->bool.
     pl_cell_with_boundary 2 d j /\ pl_cell_with_boundary 2 e j /\
     d SUBSET e
     ==> d = e`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^3->bool` (X_CHOOSE_THEN
    `f1:real^3->real^3` (X_CHOOSE_THEN `g1:real^3->real^3`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN
    `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
    STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> rand(rator(concl th)) = `(k:real^3->bool),(d:real^3->bool)`)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [homeomorphism] th)) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> rand(rator(concl th)) = `(k1:real^3->bool),(e:real^3->bool)`)) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [homeomorphism] th)) THEN
  SUBGOAL_THEN `relative_interior k SUBSET (k:real^3->bool) /\
                k1 SUBSET affine hull (k1:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[RELATIVE_INTERIOR_SUBSET; HULL_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(g1:real^3->real^3) o (f:real^3->real^3)`;
                 `affine hull k:real^3->bool`; `affine hull k1:real^3->bool`;
                 `relative_interior k:real^3->bool`]
    INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL;
                OPEN_IN_RELATIVE_INTERIOR; o_THM; IMAGE_o] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] AFF_DIM_SIMPLEX) THEN
      MP_TAC(ISPECL [`k1:real^3->bool`; `&2:int`] AFF_DIM_SIMPLEX) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `e:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `d DIFF j = IMAGE (f:real^3->real^3) (relative_interior k)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `(d:real^3->bool) SUBSET e` THEN SET_TAC[]];
      UNDISCH_TAC `d DIFF j = IMAGE (f:real^3->real^3) (relative_interior k)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (g1:real^3->real^3) e = k1`;
        `(k1:real^3->bool) SUBSET affine hull k1`;
        `(d:real^3->bool) SUBSET e`] THEN
      SET_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(f:real^3->real^3) x IN e /\ f y IN e` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`d DIFF j = IMAGE (f:real^3->real^3) (relative_interior k)`;
          `(d:real^3->bool) SUBSET e`;
          `(x:real^3) IN relative_interior k`;
          `(y:real^3) IN relative_interior k`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f:real^3->real^3) x = f y` MP_TAC THENL
       [MP_TAC(MATCH_MP (ASSUME
          `!y:real^3. y IN e ==> (f1:real^3->real^3) (g1 y) = y`)
          (ASSUME `(f:real^3->real^3) x IN e`)) THEN
        MP_TAC(MATCH_MP (ASSUME
          `!y:real^3. y IN e ==> (f1:real^3->real^3) (g1 y) = y`)
          (ASSUME `(f:real^3->real^3) y IN e`)) THEN
        UNDISCH_TAC `(g1:real^3->real^3) ((f:real^3->real^3) x) = g1 (f y)` THEN
        MESON_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `g:real^3->real^3`) THEN
      SUBGOAL_THEN `(x:real^3) IN k /\ (y:real^3) IN k` STRIP_ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`relative_interior k SUBSET (k:real^3->bool)`;
          `(x:real^3) IN relative_interior k`;
          `(y:real^3) IN relative_interior k`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN DISCH_TAC THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (e DIFF j))
                        (d DIFF j:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `e:real^3->bool` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `d DIFF j = IMAGE (f1:real^3->real^3)
                     (IMAGE (g1:real^3->real^3)
                        (IMAGE (f:real^3->real^3) (relative_interior k)))`
      SUBST1_TAC THENL
       [UNDISCH_TAC `d DIFF j = IMAGE (f:real^3->real^3) (relative_interior k)` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN
        MAP_EVERY UNDISCH_TAC
         [`!y:real^3. y IN e ==> (f1:real^3->real^3) (g1 y) = y`;
          `(d:real^3->bool) SUBSET e`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`g1:real^3->real^3`; `k1:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
      EXISTS_TAC `affine hull k1:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `d DIFF j = IMAGE (f:real^3->real^3) (relative_interior k)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (g1:real^3->real^3) e = k1`; `(d:real^3->bool) SUBSET e`] THEN
      SET_TAC[];
      UNDISCH_TAC `(d:real^3->bool) SUBSET e` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean (e DIFF j))
                          (d DIFF j:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `d DIFF j = (e DIFF j) INTER (d:real^3->bool)` SUBST1_TAC
    THENL [UNDISCH_TAC `(d:real^3->bool) SUBSET e` THEN SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  UNDISCH_TAC `connected (e DIFF j:real^3->bool)` THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `d DIFF j:real^3->bool`) THEN
  REWRITE_TAC[ASSUME `open_in (subtopology euclidean (e DIFF j))
                        (d DIFF j:real^3->bool)`;
              ASSUME `closed_in (subtopology euclidean (e DIFF j))
                        (d DIFF j:real^3->bool)`;
              ASSUME `~(d DIFF j:real^3->bool = {})`] THEN
  MAP_EVERY UNDISCH_TAC
   [`(d:real^3->bool) SUBSET e`; `(j:real^3->bool) SUBSET d`;
    `(j:real^3->bool) SUBSET e`] THEN
  SET_TAC[]);;

let DISK_COMPLEMENT = prove
 (`!s d j:real^3->bool.
     pl_sphere 2 s /\ pl_cell_with_boundary 2 d j /\ d SUBSET s
     ==> pl_cell_with_boundary 2 ((s DIFF d) UNION j) j`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN
    `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
       STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `pl_sphere 1 (j:real^3->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_frontier k) = j` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOI_SS2_SPHERE1_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `d:real^3->bool`;
                          `g:real^3->real^3`] THEN
    ASM_REWRITE_TAC[DIMINDEX_3] THEN REPEAT CONJ_TAC THENL
     [ARITH_TAC;
      MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
      CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
      MATCH_MP_TAC POLYTOPE_IMP_CLOSED THEN
      MATCH_MP_TAC SIMPLEX_IMP_POLYTOPE THEN EXISTS_TAC `&2:int` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `j:real^3->bool`] SPHERE_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(j:real^3->bool) SUBSET d`; `(d:real^3->bool) SUBSET s`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN
    `d2:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `compact (d1:real^3->bool) /\ compact (d2:real^3->bool) /\
                (j:real^3->bool) SUBSET d1 /\ j SUBSET d2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`d1:real^3->bool`; `j:real^3->bool`] MOI_SS2_CELL_FACTS) THEN
    MP_TAC(ISPECL [`d2:real^3->bool`; `j:real^3->bool`] MOI_SS2_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (d1:real^3->bool) /\ closed (d2:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean s) (d1 DIFF j:real^3->bool) /\
    open_in (subtopology euclidean s) (d2 DIFF j:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_IN_OPEN] THEN CONJ_TAC THENL
     [EXISTS_TAC `(:real^3) DIFF d2` THEN
      ASM_REWRITE_TAC[GSYM closed];
      EXISTS_TAC `(:real^3) DIFF d1` THEN
      ASM_REWRITE_TAC[GSYM closed]] THEN
    MAP_EVERY UNDISCH_TAC
     [`d1 UNION d2:real^3->bool = s`; `d1 INTER d2:real^3->bool = j`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^3->bool) SUBSET d1 \/ d SUBSET d2` MP_TAC THENL
   [ASM_CASES_TAC `(d DIFF j) INTER (d1 DIFF j:real^3->bool) = {}` THENL
     [DISJ2_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`(d DIFF j) INTER (d1 DIFF j:real^3->bool) = {}`;
        `d1 UNION d2:real^3->bool = s`; `(d:real^3->bool) SUBSET s`;
        `d1 INTER d2:real^3->bool = j`] THEN
      SET_TAC[];
      DISJ1_TAC THEN
      SUBGOAL_THEN `d DIFF j SUBSET (d1 DIFF j:real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC MOI_SS2_CONNECTED_IN_SIDE THEN
        MAP_EVERY EXISTS_TAC [`s:real^3->bool`; `d2 DIFF j:real^3->bool`] THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`d1 UNION d2:real^3->bool = s`; `(d:real^3->bool) SUBSET s`;
          `d1 INTER d2:real^3->bool = j`] THEN
        SET_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`d1 INTER d2:real^3->bool = j`] THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `d:real^3->bool = d1` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_SS2_DISK_IN_DISK THEN EXISTS_TAC `j:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s DIFF d1) UNION j:real^3->bool = d2`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    MAP_EVERY UNDISCH_TAC
     [`d1 UNION d2:real^3->bool = s`; `d1 INTER d2:real^3->bool = j`;
      `(j:real^3->bool) SUBSET d2`] THEN
    SET_TAC[];
    SUBGOAL_THEN `d:real^3->bool = d2` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_SS2_DISK_IN_DISK THEN EXISTS_TAC `j:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s DIFF d2) UNION j:real^3->bool = d1`
     (fun th -> ASM_REWRITE_TAC[th]) THEN
    MAP_EVERY UNDISCH_TAC
     [`d1 UNION d2:real^3->bool = s`; `d1 INTER d2:real^3->bool = j`;
      `(j:real^3->bool) SUBSET d1`] THEN
    SET_TAC[]]);;

(* A plane PL 2-cell lies in the convex hull of its boundary: its interior *)
(* is open in the plane (invariance of domain), so its relative frontier   *)
(* lies in the boundary, and a bounded set lies in the convex hull of its  *)
(* relative frontier.                                                      *)

let PLANE_CELL_HULL = prove
 (`!d j:real^3->bool. moi_sch3_plane_cell d j ==> d SUBSET convex hull j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sch3_plane_cell] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `bb:real^3`
    (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))) THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_SS2_CELL_FACTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN
    `f:real^3->real^3` (X_CHOOSE_THEN `g:real^3->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
       STRIP_ASSUME_TAC))))))) THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  ABBREV_TAC `pp = {x:real^3 | bb dot x = r}` THEN
  SUBGOAL_THEN `affine (pp:real^3->bool) /\ aff_dim pp = &2` STRIP_ASSUME_TAC
  THENL
   [EXPAND_TAC "pp" THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
    ASM_SIMP_TAC[AFF_DIM_HYPERPLANE; DIMINDEX_3] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior k SUBSET (k:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `affine hull k:real^3->bool`;
                 `pp:real^3->bool`; `relative_interior k:real^3->bool`]
    INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL;
                    OPEN_IN_RELATIVE_INTERIOR] THEN
    REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] AFF_DIM_SIMPLEX) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`IMAGE (f:real^3->real^3) (relative_interior k) = d DIFF j`;
        `(d:real^3->bool) SUBSET pp`] THEN
      SET_TAC[];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN STRIP_TAC THEN
      MP_TAC(MATCH_MP (ASSUME
        `!x:real^3. x IN k ==> (g:real^3->real^3) (f x) = x`)
        (MATCH_MP (SET_RULE `!x:real^3. s SUBSET k /\ x IN s ==> x IN k`)
          (CONJ (ASSUME `relative_interior k SUBSET (k:real^3->bool)`)
                (ASSUME `(x:real^3) IN relative_interior k`)))) THEN
      MP_TAC(MATCH_MP (ASSUME
        `!x:real^3. x IN k ==> (g:real^3->real^3) (f x) = x`)
        (MATCH_MP (SET_RULE `!x:real^3. s SUBSET k /\ x IN s ==> x IN k`)
          (CONJ (ASSUME `relative_interior k SUBSET (k:real^3->bool)`)
                (ASSUME `(y:real^3) IN relative_interior k`)))) THEN
      UNDISCH_TAC `(f:real^3->real^3) x = f y` THEN MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `affine hull d SUBSET (pp:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `d DIFF j SUBSET relative_interior (d:real^3->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_INTERIOR_MAXIMAL THEN CONJ_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `open_in (subtopology euclidean pp) (d DIFF j:real^3->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `oo:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `d:real^3->bool`]
      HULL_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`d DIFF j = pp INTER (oo:real^3->bool)`;
      `affine hull d SUBSET (pp:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier d SUBSET (j:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    UNDISCH_TAC `d DIFF j SUBSET relative_interior (d:real^3->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `convex hull (relative_frontier d):real^3->bool` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_CONVEX_HULL_RELATIVE_FRONTIER THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    SUBGOAL_THEN `~(j:real^3->bool = {})` MP_TAC THENL
     [UNDISCH_TAC `IMAGE (f:real^3->real^3) (relative_frontier k) = j` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
      MP_TAC(ISPECL [`k:real^3->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`~(d DIFF j:real^3->bool = {})`; `(j:real^3->bool) SUBSET d`] THEN
    SET_TAC[];
    MATCH_MP_TAC HULL_MONO THEN FIRST_ASSUM ACCEPT_TAC]);;

