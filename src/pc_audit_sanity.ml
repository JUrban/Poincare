(* ========================================================================= *)
(* pc_audit_sanity: sanity theorems for the headline statements of           *)
(* poincare_statement.ml (listed in audit/README.md).                        *)
(*                                                                           *)
(* First: restriction lemmas for homeomorphisms; smooth atlases give locally *)
(* Euclidean spaces; simple connectivity implies path connectedness;         *)
(* invariance of the hypotheses under homeomorphism and the converse of the  *)
(* Poincare statement at every carrier type.                                 *)
(* ========================================================================= *)

needs "src/poincare_statement_sanity.ml";;
needs "src/pc_mfd_base.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Restrictions of homeomorphisms.                                           *)
(* ------------------------------------------------------------------------- *)

let AUDSAN_HOMEOMORPHIC_MAP_RESTRICT = prove
 (`!(top:A topology) (top':B topology) f s.
        homeomorphic_map(top,top') f /\ s SUBSET topspace top
        ==> homeomorphic_map(subtopology top s,subtopology top' (IMAGE f s)) f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP) THEN
  ASM SET_TAC[]);;

(* The part of a chart domain mapped into an open subset B of the chart     *)
(* image is open, and homeomorphic to B.                                     *)

let AUDSAN_CHART_PREIMAGE = prove
 (`!(top:A topology) (f:A->real^N) U S B.
        open_in top U /\
        homeomorphic_map (subtopology top U,subtopology euclidean S) f /\
        open B /\ B SUBSET S
        ==> open_in top {y | y IN U /\ f y IN B} /\
            subtopology top {y | y IN U /\ f y IN B} homeomorphic_space
            subtopology euclidean B`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{y | y IN U /\ (f:A->real^N) y IN B} =
      {y | y IN topspace(subtopology top U) /\ f y IN B}`
    SUBST1_TAC THENL
     [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_CONTINUOUS_MAP_PREIMAGE THEN
    EXISTS_TAC `subtopology euclidean (S:real^N->bool)` THEN
    ASM_SIMP_TAC[HOMEOMORPHIC_IMP_CONTINUOUS_MAP] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[GSYM OPEN_IN];
    REWRITE_TAC[HOMEOMORPHIC_SPACE] THEN EXISTS_TAC `f:A->real^N` THEN
    MP_TAC(ISPECL
     [`subtopology top (U:A->bool)`; `subtopology euclidean (S:real^N->bool)`;
      `f:A->real^N`; `{y | y IN U /\ (f:A->real^N) y IN B}`;
      `B:real^N->bool`] HOMEOMORPHIC_MAP_SUBTOPOLOGIES_ALT) THEN
    ASM_REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY; IN_ELIM_THM] THEN
    ANTS_TAC THENL [REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
                    MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(U:A->bool) INTER {y | y IN U /\ (f:A->real^N) y IN B} =
      {y | y IN U /\ f y IN B} /\
      (S:real^N->bool) INTER B = B`
     (fun th -> REWRITE_TAC[th]) THEN
    ASM SET_TAC[]]);;

(* Homotopies with a property are homotopies. *)

let AUDSAN_HOMOTOPIC_WITH_WEAKEN = prove
 (`!P (top:A topology) (top':B topology) f g.
        homotopic_with P (top,top') f g
        ==> homotopic_with (\x. T) (top,top') f g`,
  REWRITE_TAC[homotopic_with] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A smooth atlas makes the space locally Euclidean.                         *)
(* ------------------------------------------------------------------------- *)

let SMOOTH_MANIFOLD_ATLAS_IMP_LOCALLY_EUCLIDEAN = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool).
        smooth_manifold_atlas top atlas ==> locally_euclidean_space (:N) top`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[locally_euclidean_space] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o el 1 o CONJUNCTS o
    GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `(phi:A->real^N) x` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `phi:A->real^N`; `U:A->bool`;
                 `IMAGE (phi:A->real^N) U`; `ball((phi:A->real^N) x,e)`]
                AUDSAN_CHART_PREIMAGE) THEN
  ASM_REWRITE_TAC[OPEN_BALL] THEN STRIP_TAC THEN
  EXISTS_TAC `{y | y IN U /\ (phi:A->real^N) y IN ball(phi x,e)}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL] THEN
  TRANS_TAC HOMEOMORPHIC_SPACE_TRANS
   `subtopology euclidean (ball((phi:A->real^N) x,e))` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC RAND_CONV [GSYM SUBTOPOLOGY_UNIV] THEN
  REWRITE_TAC[HOMEOMORPHIC_SPACE_EUCLIDEAN] THEN
  ASM_SIMP_TAC[HOMEOMORPHIC_BALL_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Simple connectivity implies path connectedness.                           *)
(* ------------------------------------------------------------------------- *)

let SIMPLY_CONNECTED_SPACE_IMP_PATH_CONNECTED_SPACE = prove
 (`!top:A topology. simply_connected_space top ==> path_connected_space top`,
  GEN_TAC THEN
  REWRITE_TAC[simply_connected_space; PATH_CONNECTED_SPACE_IFF_PATH_COMPONENT] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`a:A`; `b:A`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(\t:real. a):real->A`; `(\t:real. b):real->A`]) THEN
  ASM_REWRITE_TAC[PATH_IN_CONST] THEN
  DISCH_THEN(MP_TAC o MATCH_MP AUDSAN_HOMOTOPIC_WITH_WEAKEN) THEN
  REWRITE_TAC[HOMOTOPIC_CONSTANT_MAPS] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; REAL_INTERVAL_EQ_EMPTY] THEN
  REWRITE_TAC[REAL_ARITH `~(&1 < &0)`]);;

(* ------------------------------------------------------------------------- *)
(* Invariance under homeomorphism.                                           *)
(* ------------------------------------------------------------------------- *)

let AUDSAN_LOCALLY_EUCLIDEAN_SPACE_HOMEOMORPHIC_IMP = prove
 (`!(s:N->bool) (top:A topology) (top':B topology).
        top homeomorphic_space top' /\ locally_euclidean_space s top
        ==> locally_euclidean_space s top'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_euclidean_space] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_TAC `f:A->B` o GEN_REWRITE_RULE I [HOMEOMORPHIC_SPACE])
   ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP) THEN
  X_GEN_TAC `y:B` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x:A. x IN topspace top /\ (f:A->B) x = y` STRIP_ASSUME_TAC
  THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  EXISTS_TAC `IMAGE (f:A->B) U` THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HOMEOMORPHIC_MAP_OPENNESS];
    ASM SET_TAC[];
    TRANS_TAC HOMEOMORPHIC_SPACE_TRANS `subtopology top (U:A->bool)` THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SPACE_SYM] THEN
    REWRITE_TAC[HOMEOMORPHIC_SPACE] THEN EXISTS_TAC `f:A->B` THEN
    MATCH_MP_TAC AUDSAN_HOMEOMORPHIC_MAP_RESTRICT THEN ASM_REWRITE_TAC[]]);;

let LOCALLY_EUCLIDEAN_SPACE_HOMEOMORPHIC = prove
 (`!(s:N->bool) (top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (locally_euclidean_space s top <=> locally_euclidean_space s top')`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`s:N->bool`; `top:A topology`; `top':B topology`]
                  AUDSAN_LOCALLY_EUCLIDEAN_SPACE_HOMEOMORPHIC_IMP);
    MP_TAC(ISPECL [`s:N->bool`; `top':B topology`; `top:A topology`]
                  AUDSAN_LOCALLY_EUCLIDEAN_SPACE_HOMEOMORPHIC_IMP)] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SPACE_SYM]);;

let AUDSAN_SIMPLY_CONNECTED_SPACE_HOMEOMORPHIC_IMP = prove
 (`!(top:A topology) (top':B topology).
        top homeomorphic_space top' /\ simply_connected_space top
        ==> simply_connected_space top'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homeomorphic_space; simply_connected_space] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:A->B`; `g:B->A`] THEN
  REWRITE_TAC[homeomorphic_maps] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`p:real->B`; `q:real->B`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`(g:B->A) o (p:real->B)`; `(g:B->A) o (q:real->B)`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[o_THM] THEN CONJ_TAC THEN
    MATCH_MP_TAC PATH_IN_COMPOSE THEN EXISTS_TAC `top':B topology` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  MATCH_MP_TAC HOMOTOPIC_WITH_EQ THEN
  MAP_EVERY EXISTS_TAC
   [`(f:A->B) o (g:B->A) o (p:real->B)`;
    `(f:A->B) o (g:B->A) o (q:real->B)`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_MAP_LEFT THEN
    EXISTS_TAC `\r:real->A. r(&1) = r(&0)` THEN
    EXISTS_TAC `top:A topology` THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[o_THM];
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN
     `(p:real->B) t IN topspace top' /\ (q:real->B) t IN topspace top'`
     STRIP_ASSUME_TAC THENL
     [RULE_ASSUM_TAC(REWRITE_RULE[path_in; continuous_map]) THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY] THEN
    MAP_EVERY X_GEN_TAC [`h:real->B`; `k:real->B`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 IN real_interval[&0,&1] /\ &1 IN real_interval[&0,&1]`
     (fun th -> ASM_SIMP_TAC[th]) THEN
    REWRITE_TAC[IN_REAL_INTERVAL] THEN REAL_ARITH_TAC]);;

let SIMPLY_CONNECTED_SPACE_HOMEOMORPHIC = prove
 (`!(top:A topology) (top':B topology).
        top homeomorphic_space top'
        ==> (simply_connected_space top <=> simply_connected_space top')`,
  REPEAT STRIP_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `top':B topology`]
                  AUDSAN_SIMPLY_CONNECTED_SPACE_HOMEOMORPHIC_IMP);
    MP_TAC(ISPECL [`top':B topology`; `top:A topology`]
                  AUDSAN_SIMPLY_CONNECTED_SPACE_HOMEOMORPHIC_IMP)] THEN
  ASM_MESON_TAC[HOMEOMORPHIC_SPACE_SYM]);;

(* The converse of the Poincare statement holds at every carrier type: a   *)
(* space homeomorphic to S^3 satisfies all the hypotheses.                 *)

let POINCARE_CONVERSE = prove
 (`!top:A topology.
        top homeomorphic_space subtopology euclidean (sphere(vec 0:real^4,&1))
        ==> hausdorff_space top /\ locally_euclidean_space (:3) top /\
            compact_space top /\ ~(topspace top = {}) /\
            simply_connected_space top`,
  GEN_TAC THEN DISCH_TAC THEN MP_TAC POINCARE_HYPOTHESES_SPHERE_3 THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC
   [MATCH_MP HOMEOMORPHIC_HAUSDORFF_SPACE th;
    MATCH_MP LOCALLY_EUCLIDEAN_SPACE_HOMEOMORPHIC th;
    MATCH_MP HOMEOMORPHIC_COMPACT_SPACE th;
    MATCH_MP HOMEOMORPHIC_EMPTY_SPACE th;
    MATCH_MP SIMPLY_CONNECTED_SPACE_HOMEOMORPHIC th]));;

(* ------------------------------------------------------------------------- *)
(* The vacuous instances of the headline statements at the carrier types num *)
(* and 3 (negative controls: why the headline theorems are stated for a type *)
(* variable).  Teeth: each hypothesis of POINCARE_STATEMENT excludes a       *)
(* genuine competitor.                                                       *)
(* ------------------------------------------------------------------------- *)

(* A nonempty locally Euclidean space is uncountable. *)

let AUDSAN_LOCALLY_EUCLIDEAN_SPACE_COUNTABLE = prove
 (`!(s:N->bool) (top:A topology).
        locally_euclidean_space s top /\ COUNTABLE(topspace top)
        ==> topspace top = {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_euclidean_space] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY] THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_SPACE_COUNTABILITY) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN; UNCOUNTABLE_EUCLIDEAN; TOPSPACE_SUBTOPOLOGY] THEN
  MATCH_MP_TAC COUNTABLE_SUBSET THEN EXISTS_TAC `topspace top:A->bool` THEN
  ASM_REWRITE_TAC[INTER_SUBSET]);;

let POINCARE_STATEMENT_NUM = prove
 (`POINCARE_STATEMENT (:num)`,
  REWRITE_TAC[POINCARE_STATEMENT] THEN X_GEN_TAC `top:num topology` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`(:3)`; `top:num topology`]
                AUDSAN_LOCALLY_EUCLIDEAN_SPACE_COUNTABLE) THEN
  ASM_REWRITE_TAC[COUNTABLE_SUBSET_NUM]);;

let POINCARE_SMOOTH_STATEMENT_NUM = prove
 (`POINCARE_SMOOTH_STATEMENT (:num)`,
  REWRITE_TAC[POINCARE_SMOOTH_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC
   [`top:num topology`; `atlas:((num->bool)#(num->real^3))->bool`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `locally_euclidean_space (:3) (top:num topology)` ASSUME_TAC
  THENL
   [MATCH_MP_TAC SMOOTH_MANIFOLD_ATLAS_IMP_LOCALLY_EUCLIDEAN THEN
    EXISTS_TAC `atlas:((num->bool)#(num->real^3))->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:3)`; `top:num topology`]
                AUDSAN_LOCALLY_EUCLIDEAN_SPACE_COUNTABLE) THEN
  ASM_REWRITE_TAC[COUNTABLE_SUBSET_NUM]);;

(* Invariance of domain: a subset of real^N homeomorphic to real^N is open. *)

let AUDSAN_HOMEOMORPHIC_UNIV_IMP_OPEN = prove
 (`!s:real^N->bool. s homeomorphic (:real^N) ==> open s`,
  GEN_TAC THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
  REWRITE_TAC[homeomorphic; homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `s = IMAGE (f:real^N->real^N) (:real^N)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[OPEN_UNIV] THEN
  ASM_MESON_TAC[IN_UNIV]);;

(* Locally Euclidean subsets of real^N of dimension N are open in real^N. *)

let AUDSAN_LOCALLY_EUCLIDEAN_SPACE_EUCLIDEAN_IMP_OPEN = prove
 (`!s:real^N->bool.
        locally_euclidean_space (:N) (subtopology euclidean s) ==> open s`,
  GEN_TAC THEN REWRITE_TAC[LOCALLY_EUCLIDEAN_SPACE_EUCLIDEAN] THEN
  DISCH_TAC THEN ONCE_REWRITE_TAC[OPEN_SUBOPEN] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `U:real^N->bool` THEN
  ASM_SIMP_TAC[AUDSAN_HOMEOMORPHIC_UNIV_IMP_OPEN] THEN
  ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]);;

let POINCARE_EMBEDDED_STATEMENT_3 = prove
 (`POINCARE_EMBEDDED_STATEMENT (:3)`,
  REWRITE_TAC[POINCARE_EMBEDDED_STATEMENT] THEN
  X_GEN_TAC `M:real^3->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (M:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AUDSAN_LOCALLY_EUCLIDEAN_SPACE_EUCLIDEAN_IMP_OPEN THEN
    ASM_REWRITE_TAC[LOCALLY_EUCLIDEAN_SPACE_EUCLIDEAN];
    ALL_TAC] THEN
  MP_TAC(ISPEC `M:real^3->bool` CLOPEN) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  ASM_MESON_TAC[NOT_COMPACT_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Teeth.                                                                    *)
(* ------------------------------------------------------------------------- *)

(* The empty space satisfies every hypothesis except nonemptiness. *)

let POINCARE_NEEDS_NONEMPTY = prove
 (`hausdorff_space (discrete_topology ({}:real^4->bool)) /\
   locally_euclidean_space (:3) (discrete_topology ({}:real^4->bool)) /\
   compact_space (discrete_topology ({}:real^4->bool)) /\
   simply_connected_space (discrete_topology ({}:real^4->bool)) /\
   ~(discrete_topology ({}:real^4->bool) homeomorphic_space
     subtopology euclidean (sphere(vec 0:real^4,&1)))`,
  REWRITE_TAC[HAUSDORFF_SPACE_DISCRETE_TOPOLOGY;
              COMPACT_SPACE_DISCRETE_TOPOLOGY; FINITE_EMPTY] THEN
  REWRITE_TAC[locally_euclidean_space; TOPSPACE_DISCRETE_TOPOLOGY;
              NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[simply_connected_space; path_in] THEN
    SIMP_TAC[CONTINUOUS_MAP_INTO_EMPTY; TOPSPACE_DISCRETE_TOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEANREAL_SUBTOPOLOGY; REAL_INTERVAL_EQ_EMPTY] THEN
    REWRITE_TAC[REAL_ARITH `~(&1 < &0)`];
    SIMP_TAC[HOMEOMORPHIC_EMPTY_SPACE_EQ; TOPSPACE_DISCRETE_TOPOLOGY] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SPHERE_EQ_EMPTY] THEN
    REAL_ARITH_TAC]);;

(* The closed ball (a manifold with boundary) satisfies every hypothesis    *)
(* except local Euclideanness: it fails at the boundary point basis 1.      *)

let POINCARE_NEEDS_NO_BOUNDARY = prove
 (`hausdorff_space (subtopology euclidean (cball(vec 0:real^3,&1))) /\
   compact_space (subtopology euclidean (cball(vec 0:real^3,&1))) /\
   ~(topspace (subtopology euclidean (cball(vec 0:real^3,&1))) = {}) /\
   simply_connected_space (subtopology euclidean (cball(vec 0:real^3,&1))) /\
   ~locally_euclidean_space (:3)
      (subtopology euclidean (cball(vec 0:real^3,&1)))`,
  SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; HAUSDORFF_SPACE_EUCLIDEAN] THEN
  SIMP_TAC[COMPACT_SPACE_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN; COMPACT_CBALL] THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; CBALL_EQ_EMPTY] THEN
  REWRITE_TAC[SIMPLY_CONNECTED_SPACE_EUCLIDEAN] THEN
  SIMP_TAC[CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_CBALL] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[LOCALLY_EUCLIDEAN_SPACE_EUCLIDEAN] THEN
  DISCH_THEN(MP_TAC o SPEC `basis 1:real^3`) THEN
  REWRITE_TAC[IN_CBALL_0; NORM_BASIS_1; REAL_LE_REFL; NOT_EXISTS_THM] THEN
  X_GEN_TAC `U:real^3->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:real^3->bool) SUBSET ball(vec 0,&1)` MP_TAC THENL
   [REWRITE_TAC[GSYM INTERIOR_CBALL] THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN
    ASM_SIMP_TAC[AUDSAN_HOMEOMORPHIC_UNIV_IMP_OPEN] THEN
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    REWRITE_TAC[SUBSET; IN_BALL_0] THEN
    DISCH_THEN(MP_TAC o SPEC `basis 1:real^3`) THEN
    ASM_REWRITE_TAC[NORM_BASIS_1] THEN REAL_ARITH_TAC]);;

(* The 2-sphere (compact and simply connected) is not a 3-manifold. *)

let NOT_LOCALLY_EUCLIDEAN_SPACE_SPHERE_2 = prove
 (`~locally_euclidean_space (:3)
      (subtopology euclidean (sphere(vec 0:real^3,&1)))`,
  DISCH_THEN(MP_TAC o MATCH_MP AUDSAN_LOCALLY_EUCLIDEAN_SPACE_EUCLIDEAN_IMP_OPEN) THEN
  DISCH_THEN(MP_TAC o MATCH_MP INTERIOR_OPEN) THEN
  REWRITE_TAC[INTERIOR_SPHERE] THEN
  REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; NOT_FORALL_THM] THEN
  EXISTS_TAC `basis 1:real^3` THEN
  REWRITE_TAC[IN_SPHERE_0; NORM_BASIS_1]);;

(* Invariance of dimension for nonempty open sets. *)

let AUDSAN_HOMEOMORPHIC_OPEN_DIMINDEX_LE = prove
 (`!(s:real^M->bool) (t:real^N->bool).
        open s /\ ~(s = {}) /\ s homeomorphic t
        ==> dimindex(:M) <= dimindex(:N)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[homeomorphic; homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC INVARIANCE_OF_DIMENSION THEN
  EXISTS_TAC `f:real^M->real^N` THEN EXISTS_TAC `s:real^M->bool` THEN
  ASM_MESON_TAC[]);;

(* The open subsets of a Euclidean chart domain map to open sets. *)

let AUDSAN_HOMEOMORPHIC_MAP_EUCLIDEAN_OPEN_SUBSET = prove
 (`!(top:A topology) U (f:A->real^N) W.
        homeomorphic_map (subtopology top U,euclidean) f /\
        open_in top W /\ W SUBSET U
        ==> open (IMAGE f W) /\
            subtopology top W homeomorphic_space
            subtopology euclidean (IMAGE f W)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology top U) (W:A->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_OPEN_MAP) THEN
    REWRITE_TAC[open_map] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[HOMEOMORPHIC_SPACE] THEN EXISTS_TAC `f:A->real^N` THEN
    MP_TAC(ISPECL [`subtopology top (U:A->bool)`; `euclidean:(real^N)topology`;
                   `f:A->real^N`; `W:A->bool`]
                  AUDSAN_HOMEOMORPHIC_MAP_RESTRICT) THEN
    ASM_SIMP_TAC[OPEN_IN_SUBSET; SUBTOPOLOGY_SUBTOPOLOGY] THEN
    SUBGOAL_THEN `(U:A->bool) INTER W = W` (fun th -> REWRITE_TAC[th]) THEN
    ASM SET_TAC[]]);;

let LOCALLY_EUCLIDEAN_SPACE_DIMENSION_UNIQUE = prove
 (`!top:A topology.
        ~(topspace top = {}) /\ locally_euclidean_space (:3) top
        ==> ~locally_euclidean_space (:4) top`,
  GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; locally_euclidean_space] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `x:A`) (MP_TAC o SPEC `x:A`)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:A->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:A->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `g:A->real^4` o
    GEN_REWRITE_RULE I [HOMEOMORPHIC_SPACE]) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `f:A->real^3` o
    GEN_REWRITE_RULE I [HOMEOMORPHIC_SPACE]) THEN
  MP_TAC(ISPECL [`top:A topology`; `U:A->bool`; `f:A->real^3`;
                 `U INTER V:A->bool`]
                AUDSAN_HOMEOMORPHIC_MAP_EUCLIDEAN_OPEN_SUBSET) THEN
  MP_TAC(ISPECL [`top:A topology`; `V:A->bool`; `g:A->real^4`;
                 `U INTER V:A->bool`]
                AUDSAN_HOMEOMORPHIC_MAP_EUCLIDEAN_OPEN_SUBSET) THEN
  ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET] THEN
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (g:A->real^4) (U INTER V)`;
                 `IMAGE (f:A->real^3) (U INTER V)`]
                AUDSAN_HOMEOMORPHIC_OPEN_DIMINDEX_LE) THEN
  ASM_REWRITE_TAC[DIMINDEX_3; DIMINDEX_4; ARITH; IMAGE_EQ_EMPTY] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[GSYM HOMEOMORPHIC_SPACE_EUCLIDEAN] THEN
  TRANS_TAC HOMEOMORPHIC_SPACE_TRANS `subtopology top (U INTER V:A->bool)` THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SPACE_SYM] THEN
  ASM_REWRITE_TAC[]);;

(* Two disjoint 3-spheres: everything but connectedness, hence not simply  *)
(* connected.                                                               *)

let NOT_SIMPLY_CONNECTED_SPACE_TWO_SPHERES = prove
 (`~simply_connected_space
      (subtopology euclidean
         (sphere(vec 0:real^4,&1) UNION sphere(&3 % basis 1:real^4,&1)))`,
  REWRITE_TAC[SIMPLY_CONNECTED_SPACE_EUCLIDEAN] THEN
  DISCH_THEN(MP_TAC o MATCH_MP SIMPLY_CONNECTED_IMP_CONNECTED) THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC
   [`sphere(vec 0:real^4,&1)`; `sphere(&3 % basis 1:real^4,&1)`] THEN
  REWRITE_TAC[CLOSED_SPHERE; SUBSET_REFL] THEN
  REWRITE_TAC[SET_RULE
   `!s t:real^4->bool. s INTER (s UNION t) = s /\ t INTER (s UNION t) = t /\
                       s INTER t INTER (s UNION t) = s INTER t`] THEN
  REWRITE_TAC[SPHERE_EQ_EMPTY; REAL_ARITH `~(&1 < &0)`] THEN
  SUBGOAL_THEN `norm(&3 % basis 1:real^4) = &3` MP_TAC THENL
   [REWRITE_TAC[NORM_MUL; NORM_BASIS_1] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_SPHERE_0; IN_SPHERE; NOT_IN_EMPTY] THEN
  DISCH_TAC THEN X_GEN_TAC `x:real^4` THEN POP_ASSUM MP_TAC THEN
  CONV_TAC NORM_ARITH);;

(* ------------------------------------------------------------------------- *)
(* No junk in the immersion clause.  The chart images of                     *)
(* overlaps are open; on a chart image a smooth map has its Frechet          *)
(* derivative as a genuine derivative, so the injectivity condition of       *)
(* smooth_immersion_into is about the real derivative; and a constant map    *)
(* on a nonempty manifold is never an immersion.                             *)
(* ------------------------------------------------------------------------- *)

let SMOOTH_MANIFOLD_ATLAS_OPEN_OVERLAP = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U phi V psi.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,psi) IN atlas
        ==> open (IMAGE phi (U INTER V))`,
  MATCH_ACCEPT_TAC CHART_OVERLAP_IMAGE_OPEN);;

let SMOOTH_IMMERSION_DERIVATIVE_WORKS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U phi
    (g:real^N->real^M) y.
        smooth_manifold_atlas top atlas /\ (U,phi) IN atlas /\
        smooth_map_on (IMAGE phi U) g /\ y IN IMAGE phi U
        ==> (g has_derivative frechet_derivative g (at y)) (at y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^N) U`; `g:real^N->real^M`]
                SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let NOT_SMOOTH_IMMERSION_CONST = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) (c:real^M).
        smooth_manifold_atlas top atlas /\ ~(topspace top = {})
        ==> ~smooth_immersion_into atlas (\x:A. c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `x:A`)) THEN
  FIRST_ASSUM(MP_TAC o el 1 o CONJUNCTS o
    GEN_REWRITE_RULE I [smooth_manifold_atlas]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:A`) THEN
  ASM_REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:A->bool`; `phi:A->real^N`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`top:A topology`; `atlas:((A->bool)#(A->real^N))->bool`;
                `U:A->bool`; `phi:A->real^N`] SMOOTH_MANIFOLD_ATLAS_CHART) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[smooth_immersion_into] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`]) THEN
  ASM_REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `g:real^N->real^M` THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `(phi:A->real^N) x` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `frechet_derivative (g:real^N->real^M) (at ((phi:A->real^N) x)) =
    (\h. vec 0)`
  ASSUME_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC FRECHET_DERIVATIVE_AT THEN
    MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
    MAP_EVERY EXISTS_TAC [`(\z:real^N. c:real^M)`; `e:real`] THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_CONST] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN IMAGE (phi:A->real^N) U` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
      ASM_REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM];
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`(phi:A->real^N) x`; `basis 1:real^N`]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  SIMP_TAC[BASIS_NONZERO; DIMINDEX_GE_1; LE_REFL]);;

