(* ========================================================================= *)
(* pc_moi_smo_cf (route M): the combinatorics of surface complexes and of   *)
(* finite combinatorial 3-manifolds.                                        *)
(* C1 MOI_SMO_SURFACE_COMPLEX: a finite simplicial complex whose polyhedron *)
(* is homeomorphic to S^2 has dimension at most 2, is pure, every edge lies *)
(* in exactly two triangles, and the triangles at a vertex form one cycle.  *)
(* Proof by invariance of domain: charts of S^2 (punctured sphere is R^2), *)
(* a book with one page or with three or more pages is not locally R^2,    *)
(* and a vertex whose triangles split into two closed families would have  *)
(* a disconnected punctured neighbourhood.                                  *)
(* C2 MOI_SMO_CF: the same one dimension up for finite combinatorial       *)
(* 3-manifolds, from C1 applied to the vertex links (cone correspondence   *)
(* between simplices at v and simplices of the link of v).                  *)
(* The first part: charts of spaces homeomorphic to S^2 and their           *)
(* consequences.                                                            *)
(* ========================================================================= *)

needs "src/pc_moi_smo_defs.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_real.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_comb.ml";;
needs "src/pc_moi_star.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Every point of a space homeomorphic to S^2 has an open neighbourhood     *)
(* homeomorphic to R^2 (the sphere punctured at the antipode).              *)
(* ------------------------------------------------------------------------- *)

let MOI_SCF_SPHERE_CHART = prove
 (`!X:real^N->bool y.
        X homeomorphic sphere(vec 0:real^3,&1) /\ y IN X
        ==> ?U (phi:real^N->real^2) phi'.
                open_in (subtopology euclidean X) U /\ y IN U /\
                homeomorphism (U,(:real^2)) (phi,phi')`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `h:real^N->real^3` (X_CHOOSE_TAC `h':real^3->real^N`))
    ASSUME_TAC) THEN
  SUBGOAL_THEN `(h:real^N->real^3) y IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `b:real^3 = --((h:real^N->real^3) y)` THEN
  SUBGOAL_THEN `(b:real^3) IN sphere(vec 0,&1) /\
                ~(b = (h:real^N->real^3) y)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "b" THEN
    UNDISCH_TAC `(h:real^N->real^3) y IN sphere(vec 0,&1)` THEN
    REWRITE_TAC[IN_SPHERE_0; NORM_NEG] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `--(z:real^3) = z <=> z = vec 0`] THEN
    DISCH_TAC THEN UNDISCH_TAC `norm((h:real^N->real^3) y) = &1` THEN
    ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(vec 0:real^3,&1)`; `(:real^2)`; `b:real^3`]
    HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[RELATIVE_FRONTIER_CBALL; AFF_DIM_CBALL; AFF_DIM_UNIV;
                DIMINDEX_2; DIMINDEX_3; CONVEX_CBALL; BOUNDED_CBALL;
                AFFINE_UNIV; REAL_OF_NUM_EQ; ARITH_EQ; REAL_LT_01] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    REWRITE_TAC[RELATIVE_FRONTIER_CBALL; REAL_OF_NUM_EQ; ARITH_EQ]] THEN
  REWRITE_TAC[homeomorphic; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^3->real^2`; `k':real^2->real^3`] THEN
  DISCH_TAC THEN
  EXISTS_TAC `IMAGE (h':real^3->real^N) (sphere(vec 0,&1) DELETE b)` THEN
  EXISTS_TAC `(k:real^3->real^2) o (h:real^N->real^3)` THEN
  EXISTS_TAC `(h':real^3->real^N) o (k':real^2->real^3)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `sphere(vec 0:real^3,&1)`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_DELETE THEN REWRITE_TAC[OPEN_IN_REFL];
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
    REWRITE_TAC[IN_IMAGE; IN_DELETE] THEN
    EXISTS_TAC `(h:real^N->real^3) y` THEN ASM_MESON_TAC[];
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `sphere(vec 0:real^3,&1) DELETE b` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `sphere(vec 0:real^3,&1)`] THEN
    ASM_REWRITE_TAC[DELETE_SUBSET] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^3. x)
                                 (sphere(vec 0,&1) DELETE b)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN ASM SET_TAC[]; REWRITE_TAC[IMAGE_ID]]]);;

(* ------------------------------------------------------------------------- *)
(* Consequences of invariance of domain for a space X homeomorphic to S^2.  *)
(* ------------------------------------------------------------------------- *)

(* An injective continuous image of an open subset of R^2 is open in X.     *)

let MOI_SCF_OPEN_IMAGE_R2 = prove
 (`!X:real^N->bool (W:real^2->bool) f.
        X homeomorphic sphere(vec 0:real^3,&1) /\ open W /\
        f continuous_on W /\ IMAGE f W SUBSET X /\
        (!x y. x IN W /\ y IN W /\ f x = f y ==> x = y)
        ==> open_in (subtopology euclidean X) (IMAGE f W)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `(f:real^2->real^N) x`]
    MOI_SCF_SPHERE_CHART) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^2`;
                       `phi':real^2->real^N`] THEN
  STRIP_TAC THEN
  ABBREV_TAC `W' = {z | z IN W /\ (f:real^2->real^N) z IN U}` THEN
  SUBGOAL_THEN `open (W':real^2->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `W:real^2->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "W'" THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE_GEN THEN
    EXISTS_TAC `X:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W':real^2->bool) SUBSET W /\
                IMAGE (f:real^2->real^N) W' SUBSET U /\ x IN W'`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "W'" THEN ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `IMAGE (f:real^2->real^N) W'` THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `U:real^N->bool` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^2->real^N) W' =
                IMAGE (phi':real^2->real^N)
                      (IMAGE ((phi:real^N->real^2) o f) W')`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
  MAP_EVERY EXISTS_TAC [`phi:real^N->real^2`; `(:real^2)`] THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN_GEN THEN
  REWRITE_TAC[LE_REFL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ALL_TAC] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    FIRST_ASSUM ACCEPT_TAC;
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[]]);;

(* A nonempty convex subset of X has dimension at most 2.                   *)

let MOI_SCF_CONVEX_DIM_LE = prove
 (`!X:real^N->bool s.
        X homeomorphic sphere(vec 0:real^3,&1) /\ convex s /\ s SUBSET X
        ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `y:real^N`] MOI_SCF_SPHERE_CHART) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^2`;
                       `phi':real^2->real^N`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN]) THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN v` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `aff_dim(s INTER ball(y:real^N,r)) = aff_dim s`
  (SUBST1_TAC o SYM) THENL
   [MATCH_MP_TAC AFF_DIM_CONVEX_INTER_OPEN THEN
    ASM_REWRITE_TAC[OPEN_BALL; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    ALL_TAC] THEN
  GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [GSYM DIMINDEX_2] THEN
  REWRITE_TAC[GSYM AFF_DIM_UNIV] THEN
  MATCH_MP_TAC INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN THEN
  EXISTS_TAC `phi:real^N->real^2` THEN
  ASM_SIMP_TAC[CONVEX_INTER; CONVEX_BALL; AFFINE_HULL_UNIV; SUBSET_UNIV] THEN
  SUBGOAL_THEN `s INTER ball(y:real^N,r) SUBSET U` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET]; ASM SET_TAC[]]);;

(* A nonempty open subset of X lies in no set of dimension below 2.         *)

let MOI_SCF_OPEN_DIM_GE = prove
 (`!X:real^N->bool V s.
        X homeomorphic sphere(vec 0:real^3,&1) /\
        open_in (subtopology euclidean X) V /\ ~(V = {}) /\ V SUBSET s
        ==> &2 <= aff_dim s`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `y:real^N`] MOI_SCF_SPHERE_CHART) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^2`;
                       `phi':real^2->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (:real^2))
                        (IMAGE (phi:real^N->real^2) (V INTER U))` MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`phi':real^2->real^N`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `X:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET] THEN
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN]] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:real^N->real^2) y`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`phi':real^2->real^N`; `ball((phi:real^N->real^2) y,r)`;
                 `s:real^N->bool`] INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN) THEN
  ASM_REWRITE_TAC[AFF_DIM_BALL; DIMINDEX_2; CONVEX_BALL] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `s:real^N->bool`]
      HULL_SUBSET) THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* An open subset of X inside a set of dimension at most 2 lies in its      *)
(* relative interior.                                                        *)

let MOI_SCF_OPEN_SUBSET_RELINT = prove
 (`!X:real^N->bool V s.
        X homeomorphic sphere(vec 0:real^3,&1) /\
        open_in (subtopology euclidean X) V /\ V SUBSET s /\ aff_dim s <= &2
        ==> V SUBSET relative_interior s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC RELATIVE_INTERIOR_MAXIMAL THEN
  ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `y:real^N`] MOI_SCF_SPHERE_CHART) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^2`;
                       `phi':real^2->real^N`] THEN
  STRIP_TAC THEN EXISTS_TAC `V INTER U:real^N->bool` THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (:real^2))
                        (IMAGE (phi:real^N->real^2) (V INTER U))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`phi':real^2->real^N`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `X:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET] THEN
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `V INTER U:real^N->bool =
                IMAGE (phi':real^2->real^N) (IMAGE phi (V INTER U))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (\x:real^N. x) (V INTER U)` THEN
    CONJ_TAC THENL [REWRITE_TAC[IMAGE_ID]; ALL_TAC] THEN
    MATCH_MP_TAC IMAGE_EQ THEN REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC INVARIANCE_OF_DOMAIN_AFFINE_SETS THEN
  EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[AFFINE_UNIV; AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL;
              AFF_DIM_UNIV; DIMINDEX_2] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `s:real^N->bool`]
      HULL_SUBSET) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC]);;

(* Small punctured neighbourhoods in X can be chosen connected.             *)

let MOI_SCF_PUNCTURED_NBHD = prove
 (`!X:real^N->bool U0 w.
        X homeomorphic sphere(vec 0:real^3,&1) /\
        open_in (subtopology euclidean X) U0 /\ w IN U0
        ==> ?V. open_in (subtopology euclidean X) V /\ w IN V /\
                V SUBSET U0 /\ connected (V DELETE w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`X:real^N->bool`; `w:real^N`] MOI_SCF_SPHERE_CHART) THEN
  ANTS_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^2`;
                       `phi':real^2->real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (:real^2))
                        (IMAGE (phi:real^N->real^2) (U0 INTER U))` MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`phi':real^2->real^N`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `X:real^N->bool` THEN
    ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET] THEN
    ASM_MESON_TAC[OPEN_IN_IMP_SUBSET];
    REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN]] THEN
  REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(phi:real^N->real^2) w`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(phi':real^2->real^N) (phi(w:real^N)) = w` ASSUME_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (phi':real^2->real^N) (ball(phi(w:real^N),r))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `U:real^N->bool` THEN
    CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`phi:real^N->real^2`; `(:real^2)`] THEN
    CONJ_TAC THENL
     [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_BALL]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(phi:real^N->real^2) w` THEN
    ASM_SIMP_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (phi':real^2->real^N) (ball(phi(w:real^N),r)) DELETE w =
    IMAGE phi' (ball(phi w,r) DELETE phi w)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE (phi':real^2->real^N) (ball(phi(w:real^N),r)) DELETE
                phi'(phi w)` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_DELETE_INJ THEN
    RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism; IN_UNIV]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
  SIMP_TAC[CONNECTED_PUNCTURED_BALL; DIMINDEX_2; LE_REFL] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[homeomorphism]) THEN
  ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Open stars in a finite complex of closed sets: the points all of whose   *)
(* carrier simplices satisfy P form an open subset of the polyhedron.       *)
(* ------------------------------------------------------------------------- *)

let MOI_SCF_OPEN_STAR_GEN = prove
 (`!L:(real^N->bool)->bool P.
        FINITE L /\ (!t. t IN L ==> closed t)
        ==> open_in (subtopology euclidean (UNIONS L))
                    {x | x IN UNIONS L /\ !t. t IN L /\ x IN t ==> P t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{x | x IN UNIONS L /\ !t. t IN L /\ x IN t ==> P t} =
    UNIONS L DIFF UNIONS {t:real^N->bool | t IN L /\ ~P t}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_DIFF; IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
  MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSED_UNIONS THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Simplices of a simplicial complex (vertex sets, faces, relative          *)
(* interiors) and the unfolding of two triangles with a common edge.        *)
(* ------------------------------------------------------------------------- *)

let MOI_SCF_SC_VERTICES = prove
 (`!L s:real^N->bool.
        simplicial_complex L /\ s IN L
        ==> ?V. ~affine_dependent V /\ FINITE V /\ s = convex hull V /\
                aff_dim s = &(CARD V) - &1 /\
                (!x. x extreme_point_of s <=> x IN V)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[MOI_CON_SC_SIMPLEX]; ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `V:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `V:real^N->bool` THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE; AFF_DIM_CONVEX_HULL;
               AFF_DIM_AFFINE_INDEPENDENT;
               EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]);;

(* A simplex of the complex that meets the relative interior of s contains  *)
(* s.                                                                         *)

let MOI_SCF_RELINT_SUBSET = prove
 (`!L s t x:real^N.
        simplicial_complex L /\ s IN L /\ t IN L /\
        x IN relative_interior s /\ x IN t
        ==> s SUBSET t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s INTER t:real^N->bool) face_of s` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_CON_SC_INTER]; ALL_TAC] THEN
  ASM_CASES_TAC `s INTER t:real^N->bool = s` THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s INTER t:real^N->bool`; `s:real^N->bool`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_SCF_NOT_SUBSET_RELINT = prove
 (`!L s t:real^N->bool.
        simplicial_complex L /\ s IN L /\ t IN L /\ ~(s SUBSET t)
        ==> t INTER relative_interior s = {}`,
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  MESON_TAC[MOI_SCF_RELINT_SUBSET]);;

let MOI_SCF_SUBSET_FACE = prove
 (`!L s t:real^N->bool.
        simplicial_complex L /\ s IN L /\ t IN L /\ s SUBSET t
        ==> s face_of t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s INTER t:real^N->bool = s` (fun th -> ASM_MESON_TAC[th; MOI_CON_SC_INTER]) THEN
  ASM SET_TAC[]);;

let MOI_SCF_SUBSET_DIM_EQ = prove
 (`!L s t:real^N->bool.
        simplicial_complex L /\ s IN L /\ t IN L /\ s SUBSET t /\
        aff_dim s = aff_dim t
        ==> s = t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) face_of t` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_SUBSET_FACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ASM_MESON_TAC[MOI_CON_SC_CONVEX; INT_LT_REFL]);;

(* Distinct simplices of the same dimension: neither meets the relative      *)
(* interior of the other.                                                     *)

let MOI_SCF_DISTINCT_RELINT = prove
 (`!L s t:real^N->bool.
        simplicial_complex L /\ s IN L /\ t IN L /\ ~(s = t) /\
        aff_dim s = aff_dim t
        ==> t INTER relative_interior s = {}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SCF_NOT_SUBSET_RELINT THEN
  EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MOI_SCF_SUBSET_DIM_EQ]);;

let MOI_SCF_HAS_SIZE_2 = prove
 (`!s:A->bool. s HAS_SIZE 2 <=> ?a b. ~(a = b) /\ s = {a,b}`,
  GEN_TAC THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN REWRITE_TAC[]);;

let MOI_SCF_HAS_SIZE_3 = prove
 (`!s:A->bool. s HAS_SIZE 3 <=>
               ?a b c. ~(a = b) /\ ~(a = c) /\ ~(b = c) /\ s = {a,b,c}`,
  GEN_TAC THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN MESON_TAC[]);;

let MOI_SCF_THIRD = prove
 (`!V a b:A. V HAS_SIZE 3 /\ a IN V /\ b IN V /\ ~(a = b)
             ==> ?c. ~(c = a) /\ ~(c = b) /\ V = {a,b,c}`,
  REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY]) THEN
  REPEAT(FIRST_X_ASSUM DISJ_CASES_TAC) THEN
  REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
  ASM_MESON_TAC[INSERT_AC]);;

(* Edges are segments.                                                       *)

let MOI_SCF_EDGE = prove
 (`!L e:real^N->bool.
        simplicial_complex L /\ e IN L /\ aff_dim e = &1
        ==> ?a b. ~(a = b) /\ e = convex hull {a,b}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(V:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE; GSYM INT_OF_NUM_EQ] THEN ASM_INT_ARITH_TAC;
    REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN ASM_MESON_TAC[]]);;

(* A triangle on the edge with vertices a, b has vertices a, b, c.          *)

let MOI_SCF_TRIANGLE_ON_EDGE = prove
 (`!L a b t:real^N->bool.
        simplicial_complex L /\ t IN L /\ aff_dim t = &2 /\ ~(a = b) /\
        convex hull {a,b} IN L /\ convex hull {a,b} SUBSET t
        ==> ?c. ~(c = a) /\ ~(c = b) /\ ~affine_dependent {a,b,c} /\
                t = convex hull {a,b,c}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(V:real^N->bool) HAS_SIZE 3` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE; GSYM INT_OF_NUM_EQ] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {a:real^N,b} face_of t` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_SUBSET_FACE]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN V /\ b IN V` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(a:real^N) extreme_point_of t /\ b extreme_point_of t`
    MP_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[GSYM FACE_OF_SING] THEN CONJ_TAC THEN
    MATCH_MP_TAC FACE_OF_TRANS THEN
    EXISTS_TAC `convex hull {a:real^N,b}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[FACE_OF_SING] THEN
    SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
             AFFINE_INDEPENDENT_2] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `a:real^N`; `b:real^N`] MOI_SCF_THIRD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `c:real^N` THEN ASM_MESON_TAC[]);;

(* A vertex of the complex lying in a simplex is one of its vertices.        *)

let MOI_SCF_VERTEX_EXTREME = prove
 (`!L t w:real^N.
        simplicial_complex L /\ t IN L /\ {w} IN L /\ w IN t
        ==> w extreme_point_of t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
  MATCH_MP_TAC MOI_SCF_SUBSET_FACE THEN
  EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM SET_TAC[]);;

let MOI_SCF_TWO_OTHERS = prove
 (`!V w:A. V HAS_SIZE 3 /\ w IN V
           ==> ?a b. ~(a = w) /\ ~(b = w) /\ ~(a = b) /\ V = {w,a,b}`,
  REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY]) THEN
  REPEAT(FIRST_X_ASSUM DISJ_CASES_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[INSERT_AC]);;

(* A triangle at a vertex w has vertices w, a, b.                           *)

let MOI_SCF_TRIANGLE_AT_VERTEX = prove
 (`!L t w:real^N.
        simplicial_complex L /\ t IN L /\ aff_dim t = &2 /\ {w} IN L /\ w IN t
        ==> ?a b. ~(a = w) /\ ~(b = w) /\ ~(a = b) /\
                  ~affine_dependent {w,a,b} /\ t = convex hull {w,a,b}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(V:real^N->bool) HAS_SIZE 3` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE; GSYM INT_OF_NUM_EQ] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN V` ASSUME_TAC THENL
   [SUBGOAL_THEN `(w:real^N) extreme_point_of t` MP_TAC THENL
     [ASM_MESON_TAC[MOI_SCF_VERTEX_EXTREME]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `w:real^N`] MOI_SCF_TWO_OTHERS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Barycentric uniqueness in a triangle.                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_SCF_TRI_COORDS = prove
 (`!a b c:real^N x y.
        ~affine_dependent {a,b,c} /\ ~(a = b) /\ ~(a = c) /\ ~(b = c) /\
        x % (b - a) + y % (c - a) = vec 0
        ==> x = &0 /\ y = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `{b:real^N,c}`] DEPENDENT_IMP_AFFINE_DEPENDENT) THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; SIMPLE_IMAGE; IMAGE_CLAUSES] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`b - a:real^N`; `c - a:real^N`; `x:real`; `y:real`]
    INDEPENDENT_2) THEN
  ASM_REWRITE_TAC[independent; VECTOR_ARITH `b - a:real^N = c - a <=> b = c`]);;

(* ------------------------------------------------------------------------- *)
(* Unfolding two triangles a b c1 and a b c2 meeting exactly in the edge a b *)
(* into the plane: an injective continuous map from an open disc of R^2     *)
(* into their union whose image meets the edge.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_SCF_UNFOLD_CONT = prove
 (`!a b c1 c2:real^N s.
     (\p:real^2. a + p$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
                 max (--(p$2)) (&0) % (c2 - a)) continuous_on s`,
  REPEAT GEN_TAC THEN
  REPEAT(MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC) THEN
  REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
  MATCH_MP_TAC CONTINUOUS_ON_VMUL THEN REWRITE_TAC[o_DEF] THEN
  TRY(MATCH_MP_TAC CONTINUOUS_ON_MAX_1 THEN
      REWRITE_TAC[LIFT_NUM; CONTINUOUS_ON_CONST; LIFT_NEG] THEN
      TRY(MATCH_MP_TAC CONTINUOUS_ON_NEG)) THEN
  MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT THEN
  REWRITE_TAC[DIMINDEX_2] THEN ARITH_TAC);;

let MOI_SCF_UNFOLD_IN = prove
 (`!a b c1 c2:real^N p:real^2.
        &0 <= p$1 /\ &0 <= p$2 /\ p$1 + p$2 <= &1
        ==> a + p$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
            max (--(p$2)) (&0) % (c2 - a) IN convex hull {a,b,c1}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `max ((p:real^2)$2) (&0) = p$2 /\ max (--(p$2)) (&0) = &0`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`&1 - (p:real^2)$1 - p$2`; `(p:real^2)$1`;
                        `(p:real^2)$2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let MOI_SCF_UNFOLD_IN2 = prove
 (`!a b c1 c2:real^N p:real^2.
        &0 <= p$1 /\ p$2 <= &0 /\ p$1 - p$2 <= &1
        ==> a + p$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
            max (--(p$2)) (&0) % (c2 - a) IN convex hull {a,b,c2}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `max ((p:real^2)$2) (&0) = &0 /\ max (--(p$2)) (&0) = --(p$2)`
  (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  MAP_EVERY EXISTS_TAC [`&1 - (p:real^2)$1 + p$2`; `(p:real^2)$1`;
                        `--((p:real^2)$2)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let MOI_SCF_UNFOLD_INJ = prove
 (`!a b c1 c2:real^N p q:real^2.
        ~affine_dependent {a,b,c1} /\ ~affine_dependent {a,b,c2} /\
        ~(a = b) /\ ~(c1 = a) /\ ~(c1 = b) /\ ~(c2 = a) /\ ~(c2 = b) /\
        convex hull {a,b,c1} INTER convex hull {a,b,c2} = convex hull {a,b} /\
        &0 <= p$1 /\ abs(p$2) <= &1 - p$1 /\
        &0 <= q$1 /\ abs(q$2) <= &1 - q$1 /\
        a + p$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
        max (--(p$2)) (&0) % (c2 - a) =
        a + q$1 % (b - a) + max (q$2) (&0) % (c1 - a) +
        max (--(q$2)) (&0) % (c2 - a)
        ==> p = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2] THEN
  SUBGOAL_THEN
   `!p:real^2 q:real^2. &0 <= p$1 /\ abs(p$2) <= &1 - p$1 /\
                 &0 <= q$1 /\ abs(q$2) <= &1 - q$1 /\
                 &0 < p$2 /\ q$2 < &0 ==>
                 ~((a:real^N) + p$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
                   max (--(p$2)) (&0) % (c2 - a) =
                   a + q$1 % (b - a) + max (q$2) (&0) % (c1 - a) +
                   max (--(q$2)) (&0) % (c2 - a))`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^2`; `v:real^2`] THEN STRIP_TAC THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c1:real^N`; `c2:real^N`;
                   `u:real^2`] MOI_SCF_UNFOLD_IN) THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c1:real^N`; `c2:real^N`;
                   `v:real^2`] MOI_SCF_UNFOLD_IN2) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ abs y <= &1 - x /\ y < &0
        ==> &0 <= x /\ y <= &0 /\ x - y <= &1`) THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ abs y <= &1 - x /\ &0 < y
        ==> &0 <= x /\ &0 <= y /\ x + y <= &1`) THEN ASM_REWRITE_TAC[];
      DISCH_TAC] THEN
    SUBGOAL_THEN
     `a + (u:real^2)$1 % (b - a) + max (u$2) (&0) % (c1 - a) +
      max (--(u$2)) (&0) % (c2 - a) IN convex hull {a:real^N,b}`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `max ((u:real^2)$2) (&0) = u$2 /\ max (--(u$2)) (&0) = &0`
    (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 < y ==> max y (&0) = y /\ max (--y) (&0) = &0`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CONVEX_HULL_2; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `t:real`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c1:real^N`;
                   `(u:real^2)$1 - t`; `(u:real^2)$2`] MOI_SCF_TRI_COORDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `a + (u:real^2)$1 % (b - a) + u$2 % (c1 - a) + &0 % (c2 - a) =
        r % a + t % (b:real^N)` THEN
      SUBGOAL_THEN `r = &1 - t` SUBST1_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `r + t = &1 ==> r = &1 - t`) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      VECTOR_ARITH_TAC;
      MP_TAC(ASSUME `&0 < (u:real^2)$2`) THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `&0 <= (p:real^2)$2 /\ &0 <= (q:real^2)$2` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN
     `max ((p:real^2)$2) (&0) = p$2 /\ max (--(p$2)) (&0) = &0 /\
      max ((q:real^2)$2) (&0) = q$2 /\ max (--(q$2)) (&0) = &0`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `&0 <= x /\ &0 <= y
        ==> max x (&0) = x /\ max (--x) (&0) = &0 /\
            max y (&0) = y /\ max (--y) (&0) = &0`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c1:real^N`;
                   `(p:real^2)$1 - (q:real^2)$1`; `(p:real^2)$2 - (q:real^2)$2`]
      MOI_SCF_TRI_COORDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `a + (p:real^2)$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
        max (--(p$2)) (&0) % (c2 - a) =
        a + (q:real^2)$1 % (b - a) + max (q$2) (&0) % (c1 - a) +
        max (--(q$2)) (&0) % (c2 - a:real^N)` THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(p:real^2)$2 <= &0 /\ (q:real^2)$2 <= &0` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN
     `max ((p:real^2)$2) (&0) = &0 /\ max (--(p$2)) (&0) = --(p$2) /\
      max ((q:real^2)$2) (&0) = &0 /\ max (--(q$2)) (&0) = --(q$2)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(REAL_ARITH
       `x <= &0 /\ y <= &0
        ==> max x (&0) = &0 /\ max (--x) (&0) = --x /\
            max y (&0) = &0 /\ max (--y) (&0) = --y`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c2:real^N`;
                   `(p:real^2)$1 - (q:real^2)$1`; `(q:real^2)$2 - (p:real^2)$2`]
      MOI_SCF_TRI_COORDS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `a + (p:real^2)$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
        max (--(p$2)) (&0) % (c2 - a) =
        a + (q:real^2)$1 % (b - a) + max (q$2) (&0) % (c1 - a) +
        max (--(q$2)) (&0) % (c2 - a:real^N)` THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&0 < (p:real^2)$2 /\ (q:real^2)$2 < &0) \/
                (&0 < (q:real^2)$2 /\ (p:real^2)$2 < &0)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH
     `~(&0 <= x /\ &0 <= y) /\ ~(x <= &0 /\ y <= &0)
      ==> &0 < x /\ y < &0 \/ &0 < y /\ x < &0`) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:real^2`; `q:real^2`]) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`q:real^2`; `p:real^2`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MOI_SCF_UNFOLD = prove
 (`!a b c1 c2:real^N.
        ~affine_dependent {a,b,c1} /\ ~affine_dependent {a,b,c2} /\
        ~(a = b) /\ ~(c1 = a) /\ ~(c1 = b) /\ ~(c2 = a) /\ ~(c2 = b) /\
        convex hull {a,b,c1} INTER convex hull {a,b,c2} = convex hull {a,b}
        ==> ?(f:real^2->real^N) W.
                open W /\ f continuous_on W /\
                IMAGE f W SUBSET
                  convex hull {a,b,c1} UNION convex hull {a,b,c2} /\
                (!x y. x IN W /\ y IN W /\ f x = f y ==> x = y) /\
                ?x. x IN W /\ f x IN convex hull {a,b}`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\p:real^2. a + p$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
                         max (--(p$2)) (&0) % (c2 - a:real^N)` THEN
  EXISTS_TAC `ball(vector[&1 / &2; &0]:real^2,&1 / &4)` THEN
  REWRITE_TAC[OPEN_BALL; MOI_SCF_UNFOLD_CONT] THEN
  SUBGOAL_THEN
   `!p:real^2. p IN ball(vector[&1 / &2; &0],&1 / &4)
               ==> &1 / &4 <= p$1 /\ abs(p$2) <= &1 / &4 /\
                   p$1 <= &3 / &4`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^2` THEN REWRITE_TAC[IN_BALL; dist] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`vector[&1 / &2; &0] - p:real^2`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`vector[&1 / &2; &0] - p:real^2`; `2`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_2; DIMINDEX_2] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNION] THEN BETA_TAC THEN
    X_GEN_TAC `p:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `p:real^2`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `&0 <= (p:real^2)$2` THENL
     [DISJ1_TAC THEN MATCH_MP_TAC MOI_SCF_UNFOLD_IN THEN ASM_REAL_ARITH_TAC;
      DISJ2_TAC THEN MATCH_MP_TAC MOI_SCF_UNFOLD_IN2 THEN ASM_REAL_ARITH_TAC];
    MAP_EVERY X_GEN_TAC [`p:real^2`; `q:real^2`] THEN STRIP_TAC THEN
    RULE_ASSUM_TAC BETA_RULE THEN
    MATCH_MP_TAC MOI_SCF_UNFOLD_INJ THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `c1:real^N`; `c2:real^N`] THEN
    FIRST_ASSUM(MP_TAC o SPEC `p:real^2`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:real^2`) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REAL_ARITH_TAC;
    EXISTS_TAC `vector[&1 / &2; &0]:real^2` THEN BETA_TAC THEN
    REWRITE_TAC[CENTRE_IN_BALL; VECTOR_2] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[CONVEX_HULL_2; IN_ELIM_THM] THEN
    MAP_EVERY EXISTS_TAC [`&1 / &2`; `&1 / &2`] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* A finite complex L whose polyhedron is homeomorphic to S^2 has dimension *)
(* at most 2, is pure, and every edge lies in exactly two triangles.        *)
(* ------------------------------------------------------------------------- *)

let MOI_SCF_SC_CLOSED = prove
 (`!L t:real^N->bool. simplicial_complex L /\ t IN L ==> closed t`,
  MESON_TAC[MOI_CON_SC_COMPACT; COMPACT_IMP_CLOSED]);;

let MOI_SCF_SC_FINITE = prove
 (`!L:(real^N->bool)->bool. simplicial_complex L ==> FINITE L`,
  SIMP_TAC[simplicial_complex]);;

let MOI_SCF_SC_OPEN_STAR = prove
 (`!L:(real^N->bool)->bool P.
        simplicial_complex L
        ==> open_in (subtopology euclidean (UNIONS L))
                    {x | x IN UNIONS L /\ !t. t IN L /\ x IN t ==> P t}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SCF_OPEN_STAR_GEN THEN
  ASM_MESON_TAC[simplicial_complex; MOI_SCF_SC_CLOSED]);;

let MOI_SCF_SURF_DIM_LE = prove
 (`!L:(real^N->bool)->bool s.
        simplicial_complex L /\
        UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\ s IN L
        ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SCF_CONVEX_DIM_LE THEN
  EXISTS_TAC `UNIONS L:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[MOI_CON_SC_CONVEX]; ASM SET_TAC[]]);;

(* A nonempty maximal simplex has dimension at least 2 (its relative         *)
(* interior is open in the polyhedron).                                      *)

let MOI_SCF_SURF_MAXIMAL = prove
 (`!L:(real^N->bool)->bool t.
        simplicial_complex L /\
        UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\
        t IN L /\ ~(t = {}) /\ (!u. u IN L /\ t SUBSET u ==> u = t)
        ==> &2 <= aff_dim t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_SCF_OPEN_DIM_GE THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS L:real^N->bool`;
    `{x:real^N | x IN UNIONS L /\ !u. u IN L /\ x IN u ==> t SUBSET u}`] THEN
  ASM_SIMP_TAC[MOI_SCF_SC_OPEN_STAR] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `~(relative_interior t:real^N->bool = {})` MP_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MOI_CON_SC_CONVEX];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN EXISTS_TAC `x:real^N` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM_MESON_TAC[MOI_SCF_RELINT_SUBSET]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN ASM_MESON_TAC[SUBSET]]);;

(* Purity: every nonempty simplex lies in a triangle.                         *)

let MOI_SCF_SURF_PURE = prove
 (`!L:(real^N->bool)->bool s.
        simplicial_complex L /\
        UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\
        s IN L /\ ~(s = {})
        ==> ?t. t IN L /\ aff_dim t = &2 /\ s SUBSET t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `!u:real^N->bool. u IN L /\ s SUBSET u
                     ==> aff_dim u <= &1 /\ &0 <= aff_dim u`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `u:real^N->bool`]
      MOI_SCF_SURF_DIM_LE) THEN
    MP_TAC(ISPEC `u:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
    MP_TAC(ISPEC `u:real^N->bool` AFF_DIM_GE) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
    SUBGOAL_THEN `~(u:real^N->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `?t:real^N->bool. t IN L /\ aff_dim t = &1 /\ s SUBSET t` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t:real^N->bool`]
      MOI_SCF_SURF_MAXIMAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t:real^N->bool`; `u:real^N->bool`] AFF_DIM_SUBSET) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_SCF_SURF_MAXIMAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->bool`] AFF_DIM_SUBSET) THEN
      FIRST_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
      UNDISCH_TAC `~(?t:real^N->bool. t IN L /\ aff_dim t = &1 /\ s SUBSET t)` THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN INT_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN INT_ARITH_TAC]]);;

(* An edge in exactly one triangle: the open star of the edge would be an    *)
(* open subset of the polyhedron inside the triangle, hence inside its       *)
(* relative interior, which misses the edge.                                 *)

let MOI_SCF_SURF_EDGE_NOT1 = prove
 (`!L:(real^N->bool)->bool e t1.
        simplicial_complex L /\
        UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\
        e IN L /\ aff_dim e = &1 /\
        {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = {t1}
        ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t1 IN L /\ aff_dim t1 = &2 /\ (e:real^N->bool) SUBSET t1`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC
   `st = {x:real^N | x IN UNIONS L /\ !u. u IN L /\ x IN u ==> e SUBSET u}` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS L)) (st:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN ASM_SIMP_TAC[MOI_SCF_SC_OPEN_STAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(st:real^N->bool) SUBSET t1` ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN GEN_REWRITE_TAC I [SUBSET] THEN
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `u:real^N->bool`]
      MOI_SCF_SURF_PURE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(t:real^N->bool) IN {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t}`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[IN_SING] THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      UNDISCH_TAC `(x:real^N) IN u` THEN
      UNDISCH_TAC `(u:real^N->bool) SUBSET t` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^N. x IN relative_interior e` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `convex(e:real^N->bool) /\ ~(e = {})` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
        EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN st` ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `e:real^N->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ASM_MESON_TAC[MOI_SCF_RELINT_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `st:real^N->bool`;
                 `t1:real^N->bool`] MOI_SCF_OPEN_SUBSET_RELINT) THEN
  ASM_REWRITE_TAC[INT_LE_REFL] THEN
  SUBGOAL_THEN `(e:real^N->bool) INTER relative_interior t1 = {}` MP_TAC THENL
   [MATCH_MP_TAC FACE_OF_DISJOINT_RELATIVE_INTERIOR THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SCF_SUBSET_FACE];
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `e:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  ASM SET_TAC[]);;

(* An edge in three distinct triangles: two of them unfold to an open disc  *)
(* of R^2 whose image is open in the polyhedron (invariance of domain), but  *)
(* the edge is approached by the relative interior of the third.             *)

let MOI_SCF_SURF_EDGE_NOT3 = prove
 (`!L:(real^N->bool)->bool e t1 t2 t3.
        simplicial_complex L /\
        UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\
        e IN L /\ aff_dim e = &1 /\
        t1 IN L /\ aff_dim t1 = &2 /\ e SUBSET t1 /\
        t2 IN L /\ aff_dim t2 = &2 /\ e SUBSET t2 /\
        t3 IN L /\ aff_dim t3 = &2 /\ e SUBSET t3 /\
        ~(t1 = t2) /\ ~(t1 = t3) /\ ~(t2 = t3)
        ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                 `t1:real^N->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                 `t2:real^N->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(c1:real^N = c2)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(t1:real^N->bool = t2)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {a,b,c1} INTER convex hull {a,b,c2} = convex hull {a:real^N,b}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `{a:real^N,b,c1}`;
                   `{a:real^N,b,c2}`] MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c1:real^N`; `c2:real^N`]
    MOI_SCF_UNFOLD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `W:real^2->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `W:real^2->bool`; `f:real^2->real^N`]
    MOI_SCF_OPEN_IMAGE_R2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^N) W SUBSET
                 convex hull {a,b,c1} UNION convex hull {a,b,c2}` THEN
    UNDISCH_TAC `(t1:real^N->bool) IN L` THEN
    UNDISCH_TAC `(t2:real^N->bool) IN L` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^2->real^N) z` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^2->real^N) z IN closure(relative_interior t3)`
  MP_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; MOI_CON_SC_CONVEX;
                 CLOSURE_CLOSED; MOI_SCF_SC_CLOSED] THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t3:real^N->bool`]
      MOI_CON_SC_CONVEX) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t3:real^N->bool`]
      MOI_SCF_SC_CLOSED) THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE (f:real^2->real^N) W` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_INTER; IN_BALL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t3:real^N->bool` THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t3:real^N->bool`;
                 `t1:real^N->bool`] MOI_SCF_DISTINCT_RELINT) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t3:real^N->bool`;
                 `t2:real^N->bool`] MOI_SCF_DISTINCT_RELINT) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^N) W SUBSET
               convex hull {a,b,c1} UNION convex hull {a,b,c2}` THEN
  UNDISCH_TAC `(y:real^N) IN IMAGE (f:real^2->real^N) W` THEN
  UNDISCH_TAC `(y:real^N) IN relative_interior t3` THEN
  SUBGOAL_THEN `~(t3:real^N->bool = t1) /\ ~(t3 = t2)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* Every edge lies in exactly two triangles.                                  *)

let MOI_SCF_SURF_EDGE = prove
 (`!L:(real^N->bool)->bool e.
        simplicial_complex L /\
        UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\
        e IN L /\ aff_dim e = &1
        ==> CARD {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ts = {t:real^N->bool | t IN L /\ aff_dim t = &2 /\ e SUBSET t}` THEN
  SUBGOAL_THEN `FINITE (ts:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_SIMP_TAC[MOI_SCF_SC_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(ts:(real^N->bool)->bool) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN EXPAND_TAC "ts" THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MATCH_MP_TAC MOI_SCF_SURF_PURE THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(ts:(real^N->bool)->bool) = 1)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(ts:(real^N->bool)->bool) HAS_SIZE 1` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_TAC `t1:real^N->bool`) THEN
    MATCH_MP_TAC MOI_SCF_SURF_EDGE_NOT1 THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `e:real^N->bool`;
                          `t1:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(3 <= CARD(ts:(real^N->bool)->bool))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPEC `ts:(real^N->bool)->bool` CHOOSE_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `3`) THEN
    ASM_REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:(real^N->bool)->bool` MP_TAC) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
       (X_CHOOSE_THEN `t3:real^N->bool` STRIP_ASSUME_TAC)))) THEN
    MATCH_MP_TAC MOI_SCF_SURF_EDGE_NOT3 THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `e:real^N->bool`;
      `t1:real^N->bool`; `t2:real^N->bool`; `t3:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(u:(real^N->bool)->bool) SUBSET ts` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "ts" THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The triangles at a vertex w of a surface complex.  Two of them are       *)
(* adjacent when they share an edge (their intersection has dimension 1).   *)
(* Every triangle at w has exactly two neighbours, and the adjacency graph  *)
(* is connected (a separation would disconnect small punctured              *)
(* neighbourhoods of w).                                                    *)
(* ------------------------------------------------------------------------- *)

(* Two distinct triangles sharing two distinct points meet in an edge.      *)

let MOI_SCF_INTER_DIM1 = prove
 (`!L t t' x y:real^N.
        simplicial_complex L /\ t IN L /\ t' IN L /\
        aff_dim t = &2 /\ aff_dim t' = &2 /\ ~(t = t') /\
        x IN t /\ x IN t' /\ y IN t /\ y IN t' /\ ~(x = y)
        ==> aff_dim(t INTER t') = &1`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INT_ARITH `&1 <= x /\ x < &2 ==> x:int = &1`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`{x:real^N,y}`; `t INTER t':real^N->bool`]
      AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[AFF_DIM_2; INSERT_SUBSET; EMPTY_SUBSET; IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t INTER t':real^N->bool) < aff_dim t` MP_TAC THENL
   [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
      EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MOI_CON_SC_INTER];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t:real^N->bool`;
                     `t':real^N->bool`] MOI_SCF_SUBSET_DIM_EQ) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ASM_REWRITE_TAC[]]);;

(* The edges of the triangle w a b through w.                                *)

let MOI_SCF_EDGE_AT_VERTEX = prove
 (`!w a b:real^N f.
        ~affine_dependent {w,a,b} /\ ~(a = w) /\ ~(b = w) /\ ~(a = b) /\
        f face_of convex hull {w,a,b} /\ w IN f /\ aff_dim f = &1
        ==> f = convex hull {w,a} \/ f = convex hull {w,b}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{w:real^N,a,b}`; `f:real^N->bool`]
    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~affine_dependent (C:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN C` ASSUME_TAC THENL
   [SUBGOAL_THEN `(w:real^N) extreme_point_of convex hull C` MP_TAC THENL
     [REWRITE_TAC[GSYM FACE_OF_SING] THEN MATCH_MP_TAC FACE_OF_SUBSET THEN
      EXISTS_TAC `convex hull {w:real^N,a,b}` THEN
      ASM_SIMP_TAC[FACE_OF_SING;
                   EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
                   IN_INSERT] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
      ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(C:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
    UNDISCH_TAC `aff_dim(f:real^N->bool) = &1` THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `C = {w:real^N,a} \/ C = {w,b}`
  (DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [UNDISCH_TAC `(w:real^N) IN C` THEN
    UNDISCH_TAC `(C:real^N->bool) SUBSET {w,a,b}` THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
    ASM_MESON_TAC[INSERT_AC];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

let MOI_SCF_OTHER = prove
 (`!s x:A. s HAS_SIZE 2 /\ x IN s ==> ?y. ~(y = x) /\ s = {x,y}`,
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INSERT; NOT_IN_EMPTY]) THEN
  FIRST_X_ASSUM DISJ_CASES_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_MESON_TAC[INSERT_AC]);;

(* The other triangle at an edge.                                             *)

let MOI_SCF_SURF_OTHER_TRIANGLE = prove
 (`!L:(real^N->bool)->bool e t.
        simplicial_complex L /\
        UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\
        e IN L /\ aff_dim e = &1 /\ t IN L /\ aff_dim t = &2 /\ e SUBSET t
        ==> ?t'. t' IN L /\ aff_dim t' = &2 /\ e SUBSET t' /\ ~(t' = t) /\
                 !s. s IN L /\ aff_dim s = &2 /\ e SUBSET s
                     ==> s = t \/ s = t'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_SCF_SURF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{t:real^N->bool | t IN L /\ aff_dim t = &2 /\ e SUBSET t}`;
                 `t:real^N->bool`] MOI_SCF_OTHER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE; IN_ELIM_THM] THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_SIMP_TAC[MOI_SCF_SC_FINITE];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t':real^N->bool` THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_TAC THEN ASM_MESON_TAC[]);;

(* Every triangle at w has exactly two neighbours among the triangles at w. *)

let MOI_SCF_SURF_NEIGHBOURS = prove
 (`!L:(real^N->bool)->bool w t.
        simplicial_complex L /\
        UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\
        {w} IN L /\ t IN L /\ aff_dim t = &2 /\ w IN t
        ==> ?t1 t2. t1 IN L /\ aff_dim t1 = &2 /\ w IN t1 /\
                    t2 IN L /\ aff_dim t2 = &2 /\ w IN t2 /\ ~(t1 = t2) /\
                    aff_dim(t INTER t1) = &1 /\ aff_dim(t INTER t2) = &1 /\
                    !s. s IN L /\ aff_dim s = &2 /\ w IN s /\
                        aff_dim(t INTER s) = &1
                        ==> s = t1 \/ s = t2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t:real^N->bool`; `w:real^N`]
    MOI_SCF_TRIANGLE_AT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `!x:real^N. x IN {a,b}
               ==> convex hull {w,x} IN L /\ aff_dim(convex hull {w,x}) = &1 /\
                   convex hull {w,x} SUBSET convex hull {w,a,b} /\
                   w IN convex hull {w,x} /\
                   x IN convex hull {w,x} /\ ~(x = w)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `{w:real^N,x} SUBSET {w,a,b} /\ ~(x = w)` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_2] THEN
    SIMP_TAC[HULL_INC; IN_INSERT] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CON_SC_FACE THEN
      EXISTS_TAC `convex hull {w:real^N,a,b}` THEN
      ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `{w:real^N,x}` THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[HULL_MONO]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN {a,b}
               ==> ?tx. tx IN L /\ aff_dim tx = &2 /\
                        convex hull {w,x} SUBSET tx /\
                        ~(tx = convex hull {w,a,b}) /\
                        !s. s IN L /\ aff_dim s = &2 /\
                            convex hull {w,x} SUBSET s
                            ==> s = convex hull {w,a,b} \/ s = tx`
  MP_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_SCF_SURF_OTHER_TRIANGLE THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(fun th ->
    MP_TAC(SPEC `a:real^N` th) THEN MP_TAC(SPEC `b:real^N` th)) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `tb:real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `ta:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `a:real^N` th) THEN MP_TAC(SPEC `b:real^N` th)) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`ta:real^N->bool`; `tb:real^N->bool`] THEN
  SUBGOAL_THEN `(w:real^N) IN ta /\ w IN tb /\ a IN ta /\ b IN tb`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(w:real^N) IN convex hull {w,a,b} /\
                a IN convex hull {w,a,b} /\ b IN convex hull {w,a,b}`
  STRIP_ASSUME_TAC THENL [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `convex hull {w:real^N,a,b} SUBSET tb` ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
      EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MOI_SCF_SUBSET_DIM_EQ]];
    MATCH_MP_TAC MOI_SCF_INTER_DIM1 THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `w:real^N`; `a:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_SCF_INTER_DIM1 THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `w:real^N`; `b:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`w:real^N`; `a:real^N`; `b:real^N`;
                   `convex hull {w,a,b} INTER s:real^N->bool`]
      MOI_SCF_EDGE_AT_VERTEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[MOI_CON_SC_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(s = convex hull {w:real^N,a,b})` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim(convex hull {w:real^N,a,b} INTER
                           convex hull {w,a,b}) = &1` THEN
      ASM_REWRITE_TAC[INTER_IDEMPOT] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN
      SUBGOAL_THEN `s = convex hull {w:real^N,a,b} \/ s = ta` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `ta:real^N->bool`)) (concl th) &&
          is_forall (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_MESON_TAC[]];
      DISJ2_TAC THEN
      SUBGOAL_THEN `s = convex hull {w:real^N,a,b} \/ s = tb` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `tb:real^N->bool`)) (concl th) &&
          is_forall (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_MESON_TAC[]]]]);;

(* Points of the polyhedron near a vertex w, in the relative interior of a  *)
(* given simplex at w.                                                       *)

let MOI_SCF_NEAR_VERTEX = prove
 (`!L:(real^N->bool)->bool w t V.
        simplicial_complex L /\ {w} IN L /\ t IN L /\ w IN t /\ ~(t = {w}) /\
        open_in (subtopology euclidean (UNIONS L)) V /\ w IN V
        ==> ?y. y IN V /\ ~(y = w) /\ y IN relative_interior t`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N) IN closure(relative_interior t)` MP_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t:real^N->bool`]
      MOI_CON_SC_CONVEX) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t:real^N->bool`]
      MOI_SCF_SC_CLOSED) THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[DIST_SYM];
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`{w:real^N}`; `t:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SCF_SUBSET_FACE THEN
        EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM SET_TAC[];
        ASM_MESON_TAC[]];
      ASM SET_TAC[]]]);;

(* A space that is covered by two disjoint relatively open sets meeting it  *)
(* is not connected.                                                         *)

let MOI_SCF_NOT_CONNECTED_OPEN_IN = prove
 (`!X S A1 A2:real^N->bool.
        open_in (subtopology euclidean X) A1 /\
        open_in (subtopology euclidean X) A2 /\
        S SUBSET X /\ S SUBSET A1 UNION A2 /\ A1 INTER A2 = {} /\
        ~(S INTER A1 = {}) /\ ~(S INTER A2 = {})
        ==> ~connected S`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `g1:real^N->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `g2:real^N->bool` STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[connected; NOT_CLAUSES] THEN
  MAP_EVERY EXISTS_TAC [`g1:real^N->bool`; `g2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN ASM SET_TAC[]);;

(* The adjacency graph of the triangles at w is connected.                  *)

let MOI_SCF_SURF_VERTEX_CONNECTED = prove
 (`!L:(real^N->bool)->bool w U.
        simplicial_complex L /\
        UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\ {w} IN L /\
        U SUBSET {t | t IN L /\ aff_dim t = &2 /\ w IN t} /\ ~(U = {}) /\
        (!t t'. t IN U /\ t' IN L /\ aff_dim t' = &2 /\ w IN t' /\
                aff_dim(t INTER t') = &1 ==> t' IN U)
        ==> U = {t | t IN L /\ aff_dim t = &2 /\ w IN t}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "clos")))))) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `U2 = {t | t IN L /\ aff_dim t = &2 /\ w IN t} DIFF
                   (U:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN L /\ aff_dim t = &2 /\ w IN t
                                 ==> t IN U \/ t IN U2`
  (LABEL_TAC "split") THENL
   [EXPAND_TAC "U2" THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN U2 ==> ~(t IN U)` (LABEL_TAC "U2U") THENL
   [EXPAND_TAC "U2" THEN REWRITE_TAC[IN_DIFF] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?t2:real^N->bool. t2 IN U2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U2" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?t1:real^N->bool. t1 IN U` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `t1 IN L /\ aff_dim t1 = &2 /\ (w:real^N) IN t1 /\
    t2 IN L /\ aff_dim t2 = &2 /\ w IN t2 /\ ~(t2 IN U)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U2" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (U:(real^N->bool)->bool) /\
                FINITE (U2:(real^N->bool)->bool) /\
                U SUBSET L /\ U2 SUBSET L`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(U:(real^N->bool)->bool) SUBSET L /\ U2 SUBSET L`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "U2" THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[FINITE_SUBSET; MOI_SCF_SC_FINITE];
    ALL_TAC] THEN
  ABBREV_TAC
   `st = {x:real^N | x IN UNIONS L /\ !t. t IN L /\ x IN t ==> w IN t}` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS L)) (st:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN ASM_SIMP_TAC[MOI_SCF_SC_OPEN_STAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN st` ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN st /\ ~(x = w)
               ==> ?t. t IN L /\ aff_dim t = &2 /\ w IN t /\ x IN t`
  (LABEL_TAC "cover") THENL
   [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "st" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)
      ASSUME_TAC) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `u:real^N->bool`]
      MOI_SCF_SURF_PURE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N t t'. ~(x = w) /\ t IN U /\ t' IN U2 /\ x IN t /\ x IN t'
                    ==> F`
  (LABEL_TAC "disj") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real^N->bool`; `t':real^N->bool`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(t:real^N->bool) IN L /\ aff_dim t = &2 /\ w IN t /\
                  t' IN L /\ aff_dim t' = &2 /\ w IN t' /\ ~(t' IN U)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(t':real^N->bool) IN U2` THEN EXPAND_TAC "U2" THEN
      UNDISCH_TAC `(t:real^N->bool) IN U` THEN
      UNDISCH_TAC `(U:(real^N->bool)->bool) SUBSET
                   {t | t IN L /\ aff_dim t = &2 /\ w IN t}` THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(t:real^N->bool = t')` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((t':real^N->bool) IN U)` THEN REWRITE_TAC[] THEN
    USE_THEN "clos" MATCH_MP_TAC THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SCF_INTER_DIM1 THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `w:real^N`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `A1 = (st DELETE (w:real^N)) INTER UNIONS U` THEN
  ABBREV_TAC `A2 = (st DELETE (w:real^N)) INTER UNIONS U2` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS L)) (A1:real^N->bool) /\
                open_in (subtopology euclidean (UNIONS L)) (A2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `A1 = (st DELETE (w:real^N)) DIFF UNIONS U2 /\
                  A2 = (st DELETE (w:real^N)) DIFF UNIONS U`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [MAP_EVERY EXPAND_TAC ["A1"; "A2"] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_DELETE; IN_UNIONS] THEN
      CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN
      ASM_CASES_TAC `(x:real^N) IN st /\ ~(x = w)` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
      USE_THEN "cover" (MP_TAC o SPEC `x:real^N`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "split" (MP_TAC o SPEC `t:real^N->bool`) THEN
      USE_THEN "disj" (MP_TAC o SPEC `x:real^N`) THEN
      UNDISCH_TAC `(x:real^N) IN t` THEN
      UNDISCH_TAC `~(x:real^N = w)` THEN
      UNDISCH_TAC `(t:real^N->bool) IN L` THEN
      UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
      UNDISCH_TAC `(w:real^N) IN t` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_SIMP_TAC[OPEN_IN_DELETE] THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_SCF_SC_CLOSED; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `st:real^N->bool`; `w:real^N`]
    MOI_SCF_PUNCTURED_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN L /\ aff_dim t = &2 /\ w IN t
                ==> ?y. y IN V /\ ~(y = w) /\ y IN st /\ y IN t`
  (LABEL_TAC "near") THENL
   [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `w:real^N`; `t:real^N->bool`;
                   `V:real^N->bool`] MOI_SCF_NEAR_VERTEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim {w:real^N} = &2` THEN
      REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]] THEN
    EXPAND_TAC "st" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `t:real^N->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) SUBSET u` MP_TAC THENL
       [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
        MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `y:real^N`] THEN
        ASM_REWRITE_TAC[];
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `V DELETE (w:real^N)`;
                 `A1:real^N->bool`; `A2:real^N->bool`]
    MOI_SCF_NOT_CONNECTED_OPEN_IN) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET o check (fun th ->
      can (find_term ((=) `V:real^N->bool`)) (concl th))) THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNION] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN st` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["A1"; "A2"] THEN
    REWRITE_TAC[IN_INTER; IN_DELETE; IN_UNIONS] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "cover" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "split" (MP_TAC o SPEC `t:real^N->bool`) THEN
    UNDISCH_TAC `(x:real^N) IN t` THEN
    UNDISCH_TAC `(t:real^N->bool) IN L` THEN
    UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
    UNDISCH_TAC `(w:real^N) IN t` THEN
    MESON_TAC[];
    MAP_EVERY EXPAND_TAC ["A1"; "A2"] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_DELETE; IN_UNIONS; NOT_IN_EMPTY] THEN
    USE_THEN "disj" MP_TAC THEN MESON_TAC[];
    USE_THEN "near" (MP_TAC o SPEC `t1:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
    EXPAND_TAC "A1" THEN REWRITE_TAC[IN_INTER; IN_DELETE; IN_UNIONS] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `t1:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    USE_THEN "near" (MP_TAC o SPEC `t2:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
    EXPAND_TAC "A2" THEN REWRITE_TAC[IN_INTER; IN_DELETE; IN_UNIONS] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `t2:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* A finite connected graph in which every vertex has exactly two           *)
(* neighbours is one cycle: its vertices can be listed periodically S 0,    *)
(* ..., S (n-1) with consecutive ones adjacent.  Proof: a longest           *)
(* injective path from a vertex closes up at its start, and its vertex set  *)
(* is closed under adjacency.                                               *)
(* ------------------------------------------------------------------------- *)

let moi_scf_path = new_definition
 `moi_scf_path (V:A->bool) (R:A->A->bool) (x0:A) k (W:num->A) <=>
    W 0 = x0 /\ (!i. i <= k ==> W i IN V) /\
    (!i. i < k ==> R (W i) (W(SUC i))) /\
    (!i j. i <= k /\ j <= k /\ ~(i = j) ==> ~(W i = W j))`;;

let MOI_SCF_PATH_BOUND = prove
 (`!(V:A->bool) R x0 k W. FINITE V /\ moi_scf_path V R x0 k W ==> k < CARD V`,
  REWRITE_TAC[moi_scf_path] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`W:num->A`; `{i:num | i <= k}`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_NUMSEG_LE; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[CARD_NUMSEG_LE] THEN DISCH_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (W:num->A) {i:num | i <= k}`; `V:A->bool`]
    CARD_SUBSET) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM];
    ASM_ARITH_TAC]);;

let MOI_SCF_PATH_EXTEND = prove
 (`!(V:A->bool) R x0 k W u.
        moi_scf_path V R x0 k W /\ u IN V /\ R (W k) u /\
        (!i. i <= k ==> ~(W i = u))
        ==> moi_scf_path V R x0 (SUC k) (\i. if i <= k then W i else u)`,
  REWRITE_TAC[moi_scf_path] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[LE_0] THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN COND_CASES_TAC THEN
    ASM_SIMP_TAC[];
    X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `i:num = k` THENL
     [ASM_REWRITE_TAC[LE_REFL; ARITH_RULE `~(SUC k <= k)`];
      SUBGOAL_THEN `i <= k /\ SUC i <= k /\ i < k` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ASM_SIMP_TAC[]]];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `(i:num) <= k` THEN ASM_CASES_TAC `(j:num) <= k` THEN
    ASM_REWRITE_TAC[] THENL
     [ASM_SIMP_TAC[];
      ASM_SIMP_TAC[];
      ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN ASM_SIMP_TAC[];
      ASM_ARITH_TAC]]);;

let MOI_SCF_TWO_NEIGHBOURS = prove
 (`!(V:A->bool) R x a b v.
     (!x. x IN V ==> ?y z. y IN V /\ z IN V /\ ~(y = z) /\ R x y /\ R x z /\
                           !u. u IN V /\ R x u ==> u = y \/ u = z) /\
     x IN V /\ a IN V /\ b IN V /\ ~(a = b) /\ R x a /\ R x b /\
     v IN V /\ R x v
     ==> v = a \/ v = b`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o SPEC `x:A`) STRIP_ASSUME_TAC) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` (X_CHOOSE_THEN `z:A`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "H")))))))) THEN
  SUBGOAL_THEN `(a:A = y \/ a = z) /\ (b = y \/ b = z) /\ (v = y \/ v = z)`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "H" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(a:A = b)` THEN MESON_TAC[]);;

let MOI_SCF_MOD_ADD_SELF = prove
 (`!i n. (i + n) MOD n = i MOD n`,
  REPEAT GEN_TAC THEN
  MP_TAC(SPECL [`1`; `n:num`; `i:num`]
    (CONJUNCT1(CONJUNCT2(CONJUNCT2 MOD_MULT_ADD)))) THEN
  REWRITE_TAC[MULT_CLAUSES]);;

let MOI_SCF_MOD_SUC = prove
 (`!i n. 2 <= n
         ==> (SUC i) MOD n = if i MOD n + 1 < n then i MOD n + 1 else 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `SUC i MOD n = (i MOD n + 1 MOD n) MOD n` SUBST1_TAC THENL
   [REWRITE_TAC[MOD_ADD_MOD; ADD1]; ALL_TAC] THEN
  SUBGOAL_THEN `1 MOD n = 1` SUBST1_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `i MOD n < n` ASSUME_TAC THENL
   [REWRITE_TAC[MOD_LT_EQ] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `i MOD n + 1 = n` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[MOD_REFL]]]);;

(* The longest injective path from x0 closes up: its last vertex is adjacent *)
(* to x0, it has at least three vertices, and its vertex set is closed     *)
(* under adjacency.                                                          *)

let MOI_SCF_CYCLE_PATH = prove
 (`!(V:A->bool) R x0.
     FINITE V /\ x0 IN V /\
     (!x y. R x y ==> R y x) /\
     (!x. x IN V ==> ~R x x) /\
     (!x. x IN V ==> ?y z. y IN V /\ z IN V /\ ~(y = z) /\ R x y /\ R x z /\
                           !u. u IN V /\ R x u ==> u = y \/ u = z)
     ==> ?k W. moi_scf_path V R x0 k W /\ 2 <= k /\ R (W k) (W 0) /\
               !x v. x IN {W j | j <= k} /\ v IN V /\ R x v
                     ==> v IN {W j | j <= k}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sym") (CONJUNCTS_THEN2 (LABEL_TAC "irr")
      (LABEL_TAC "two"))))) THEN
  MP_TAC(ISPEC `\k. ?W:num->A. moi_scf_path V R x0 k W` num_MAX) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `0` THEN EXISTS_TAC `\i:num. (x0:A)` THEN
      REWRITE_TAC[moi_scf_path; LE; LT] THEN ASM_MESON_TAC[];
      EXISTS_TAC `CARD(V:A->bool)` THEN X_GEN_TAC `k:num` THEN
      DISCH_THEN(X_CHOOSE_TAC `W:num->A`) THEN
      MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC MOI_SCF_PATH_BOUND THEN
      MAP_EVERY EXISTS_TAC [`R:A->A->bool`; `x0:A`; `W:num->A`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `W:num->A`) (LABEL_TAC "max"))) THEN
  EXISTS_TAC `k:num` THEN EXISTS_TAC `W:num->A` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_scf_path]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W0") (CONJUNCTS_THEN2
    (LABEL_TAC "WV") (CONJUNCTS_THEN2 (LABEL_TAC "WR") (LABEL_TAC "Winj")))) THEN
  SUBGOAL_THEN `!u:A. u IN V /\ R ((W:num->A) k) u ==> ?i. i <= k /\ W i = u`
  (LABEL_TAC "onpath") THENL
   [X_GEN_TAC `u:A` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o
      REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`]) THEN
    USE_THEN "max" (MP_TAC o SPEC `SUC k`) THEN
    REWRITE_TAC[ARITH_RULE `~(SUC k <= k)`; NOT_CLAUSES; IMP_CLAUSES] THEN
    EXISTS_TAC `\i. if i <= k then (W:num->A) i else u` THEN
    MATCH_MP_TAC MOI_SCF_PATH_EXTEND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(W:num->A) k IN V` ASSUME_TAC THENL
   [USE_THEN "WV" MATCH_MP_TAC THEN REWRITE_TAC[LE_REFL]; ALL_TAC] THEN
  USE_THEN "two" (MP_TAC o SPEC `(W:num->A) k`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:A` (X_CHOOSE_THEN `z:A` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?iy iz. iy <= k /\ (W:num->A) iy = y /\ iz <= k /\ W iz = z`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "onpath" (fun th -> MP_TAC(SPEC `y:A` th) THEN
                                 MP_TAC(SPEC `z:A` th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k = 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `iy = 0 /\ iz = 0` STRIP_ASSUME_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(y:A = z)` THEN
    UNDISCH_TAC `(W:num->A) iy = y` THEN UNDISCH_TAC `(W:num->A) iz = z` THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. 0 < i /\ i <= k ==> R ((W:num->A) i) (W(i - 1))`
  (LABEL_TAC "Wback") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "sym" MATCH_MP_TAC THEN
    SUBGOAL_THEN `(W:num->A) i = W(SUC(i - 1))` SUBST1_TAC THENL
     [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(R:A->A->bool) ((W:num->A) k) (W(k - 1))` ASSUME_TAC THENL
   [USE_THEN "Wback" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `?u:A. u IN V /\ R ((W:num->A) k) u /\ ~(u = W(k - 1))`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `y:A = W(k - 1)` THENL
     [EXISTS_TAC `z:A` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      EXISTS_TAC `y:A` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  USE_THEN "onpath" (MP_TAC o SPEC `u:A`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(i = k) /\ ~(i = k - 1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        concl th = `(W:num->A) k = u`)) THEN
      REMOVE_THEN "irr" (MP_TAC o SPEC `u:A`) THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `~(u:A = W(k - 1))` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `i = 0` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:A->bool`; `R:A->A->bool`; `(W:num->A) i`;
                   `(W:num->A)(i - 1)`; `(W:num->A)(i + 1)`; `(W:num->A) k`]
      MOI_SCF_TWO_NEIGHBOURS) THEN
    ANTS_TAC THENL
     [USE_THEN "two" (fun th -> REWRITE_TAC[th]) THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "Winj" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "Wback" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[GSYM ADD1] THEN USE_THEN "WR" MATCH_MP_TAC THEN
        ASM_ARITH_TAC;
        USE_THEN "sym" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SYM) THEN REWRITE_TAC[IMP_CLAUSES] THEN
      USE_THEN "Winj" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= k` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(R:A->A->bool) ((W:num->A) k) (W 0)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(R:A->A->bool) ((W:num->A) 0) (W k)` ASSUME_TAC THENL
   [USE_THEN "sym" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!j. j <= k ==> ?ja jb. ja <= k /\ jb <= k /\ ~(ja = jb) /\
                           R ((W:num->A) j) (W ja) /\ R (W j) (W jb)`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `j = 0` THENL
     [SUBGOAL_THEN `(R:A->A->bool) ((W:num->A) 0) (W 1)` ASSUME_TAC THENL
       [REWRITE_TAC[ARITH_RULE `1 = SUC 0`] THEN
        USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`1`; `k:num`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[LE_REFL]; ASM_ARITH_TAC;
        UNDISCH_TAC `(R:A->A->bool) ((W:num->A) 0) (W 1)` THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(R:A->A->bool) ((W:num->A) 0) (W k)` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `j:num = k` THENL
     [MAP_EVERY EXISTS_TAC [`k - 1`; `0`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[LE_0]; ASM_ARITH_TAC;
        UNDISCH_TAC `(R:A->A->bool) ((W:num->A) k) (W(k - 1))` THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(R:A->A->bool) ((W:num->A) k) (W 0)` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`j - 1`; `SUC j`] THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_ARITH_TAC;
      USE_THEN "Wback" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:A`; `v:A`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `ja:num` (X_CHOOSE_THEN `jb:num`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V:A->bool`; `R:A->A->bool`; `(W:num->A) j`;
                 `(W:num->A) ja`; `(W:num->A) jb`; `v:A`]
    MOI_SCF_TWO_NEIGHBOURS) THEN
  ANTS_TAC THENL
   [USE_THEN "two" (fun th -> REWRITE_TAC[th]) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [USE_THEN "WV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "WV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "WV" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "Winj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(R:A->A->bool) x v` THEN ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[]]);;

(* The cycle theorem.                                                         *)

let MOI_SCF_CYCLE = prove
 (`!(V:A->bool) R.
     FINITE V /\ ~(V = {}) /\
     (!x y. R x y ==> R y x) /\
     (!x. x IN V ==> ~R x x) /\
     (!x. x IN V ==> ?y z. y IN V /\ z IN V /\ ~(y = z) /\ R x y /\ R x z /\
                           !u. u IN V /\ R x u ==> u = y \/ u = z) /\
     (!U. U SUBSET V /\ ~(U = {}) /\
          (!x y. x IN U /\ y IN V /\ R x y ==> y IN U) ==> U = V)
     ==> ?n S. 3 <= n /\ (!i. S(i + n) = S i) /\
               (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
               (!i. S i IN V /\ R (S i) (S(SUC i))) /\
               (!x. x IN V ==> ?i. i < n /\ x = S i)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "conn")))))) THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x0:A` o GEN_REWRITE_RULE I
    [GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`V:A->bool`; `R:A->A->bool`; `x0:A`] MOI_SCF_CYCLE_PATH) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `W:num->A`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_scf_path] o check (fun th ->
    can (find_term ((=) `W:num->A`)) (concl th) &&
    not (is_forall (concl th)))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W0") (CONJUNCTS_THEN2
    (LABEL_TAC "WV") (CONJUNCTS_THEN2 (LABEL_TAC "WR") (LABEL_TAC "Winj")))) THEN
  SUBGOAL_THEN `{(W:num->A) j | j <= k} = V` (LABEL_TAC "all") THENL
   [USE_THEN "conn" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
      USE_THEN "WV" ACCEPT_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `(W:num->A) 0` THEN EXISTS_TAC `0` THEN REWRITE_TAC[LE_0]];
    ALL_TAC] THEN
  EXISTS_TAC `k + 1` THEN EXISTS_TAC `\i. (W:num->A) (i MOD (k + 1))` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_ARITH_TAC;
    REWRITE_TAC[MOI_SCF_MOD_ADD_SELF];
    MAP_EVERY X_GEN_TAC [`p:num`; `q:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `p MOD (k + 1) = p /\ q MOD (k + 1) = q`
    (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOD_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `(W:num->A) p = W q` THEN REWRITE_TAC[IMP_CLAUSES] THEN
    USE_THEN "Winj" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    X_GEN_TAC `p:num` THEN
    SUBGOAL_THEN `p MOD (k + 1) < k + 1` ASSUME_TAC THENL
     [REWRITE_TAC[MOD_LT_EQ] THEN ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`p:num`; `k + 1`] MOI_SCF_MOD_SUC) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    COND_CASES_TAC THENL
     [SUBGOAL_THEN `p MOD (k + 1) + 1 = SUC(p MOD (k + 1))` SUBST1_TAC THENL
       [ARITH_TAC; ALL_TAC] THEN
      USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `p MOD (k + 1) = k` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:A) IN {(W:num->A) j | j <= k}` MP_TAC THENL
     [USE_THEN "all" (fun th -> ASM_REWRITE_TAC[th]); ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `j:num` THEN
    SUBGOAL_THEN `j MOD (k + 1) = j` (fun th -> ASM_REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* The triangles at a vertex form one cycle, and the theorem C1.            *)
(* ------------------------------------------------------------------------- *)

let MOI_SCF_SURF_VERTEX = prove
 (`!L:(real^N->bool)->bool w.
        simplicial_complex L /\
        UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\ {w} IN L
        ==> ?n S. 3 <= n /\ (!i. S(i + n) = (S:num->real^N->bool) i) /\
                  (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
                  (!i. S i IN L /\ aff_dim(S i) = &2 /\ w IN S i /\
                       aff_dim(S i INTER S(SUC i)) = &1) /\
                  (!t. t IN L /\ aff_dim t = &2 /\ w IN t
                       ==> ?i. i < n /\ t = S i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`{t:real^N->bool | t IN L /\ aff_dim t = &2 /\ w IN t}`;
                 `\s t:real^N->bool. aff_dim(s INTER t) = &1`] MOI_SCF_CYCLE) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_SIMP_TAC[MOI_SCF_SC_FINITE];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `{w:real^N}`]
        MOI_SCF_SURF_PURE) THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET] THEN MESON_TAC[];
      MESON_TAC[INTER_COMM];
      GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[INTER_IDEMPOT] THEN
      INT_ARITH_TAC;
      X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `w:real^N`; `t:real^N->bool`]
        MOI_SCF_SURF_NEIGHBOURS) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN MESON_TAC[];
      X_GEN_TAC `U:(real^N->bool)->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_SCF_SURF_VERTEX_CONNECTED THEN
      RULE_ASSUM_TAC(REWRITE_RULE[GSYM CONJ_ASSOC]) THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[GSYM CONJ_ASSOC] THEN MESON_TAC[]]);;

(* C1: the combinatorics of a simplicial complex whose polyhedron is S^2.   *)

let MOI_SMO_SURFACE_COMPLEX = prove
 (`!u:N->bool. MOI_SMO_SURFACE_COMPLEX_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[MOI_SMO_SURFACE_COMPLEX_STATEMENT] THEN
  X_GEN_TAC `L:(real^N->bool)->bool` THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_SCF_SURF_DIM_LE THEN
    EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_SCF_SURF_PURE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_SCF_SURF_EDGE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_SCF_SURF_VERTEX THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Finite combinatorial 3-manifolds.  The simplices at a vertex v are the   *)
(* cones convex hull (v INSERT s) over the simplices s of the link of v (a  *)
(* simplicial complex whose polyhedron is a PL 2-sphere, hence homeomorphic *)
(* to S^2); C1 for the links gives C2.                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_SCF_LF_SC = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ lf_simplicial_complex c ==> simplicial_complex c`,
  REWRITE_TAC[simplicial_complex; lf_simplicial_complex] THEN MESON_TAC[]);;

let MOI_SCF_LINK_SC = prove
 (`!c (v:real^N).
        simplicial_complex c ==> simplicial_complex (simplicial_link c v)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  REWRITE_TAC[simplicial_complex; simplicial_link; IN_ELIM_THM] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `s:real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^N->bool`
        STRIP_ASSUME_TAC))) ASSUME_TAC) THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
      EXISTS_TAC `t:real^N->bool` THEN ASM_MESON_TAC[FACE_OF_TRANS]];
    ASM_MESON_TAC[]]);;

let MOI_SCF_LINK_SPHERE = prove
 (`!c (v:real^N).
        pl_sphere 2 (UNIONS (simplicial_link c v))
        ==> UNIONS (simplicial_link c v) homeomorphic sphere(vec 0:real^3,&1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC HOMEOMORPHIC_TRANS THEN
  EXISTS_TAC `relative_frontier k:real^N->bool` THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `sphere(vec 0:real^3,&1) = relative_frontier(cball(vec 0,&1))`
    SUBST1_TAC THENL
     [REWRITE_TAC[RELATIVE_FRONTIER_CBALL; REAL_OF_NUM_EQ; ARITH_EQ];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
    REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL; DIMINDEX_3;
                REAL_LT_01] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT;
                  COMPACT_IMP_BOUNDED; AFF_DIM_SIMPLEX]]);;

(* The structure of a finite combinatorial 3-manifold used below.           *)

let MOI_SCF_CM_FACTS = prove
 (`!c:(real^N->bool)->bool.
        FINITE c /\ combinatorial_manifold 3 c
        ==> simplicial_complex c /\
            !v. {v} IN c
                ==> simplicial_complex (simplicial_link c v) /\
                    UNIONS (simplicial_link c v) homeomorphic
                    sphere(vec 0:real^3,&1)`,
  GEN_TAC THEN REWRITE_TAC[combinatorial_manifold] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex(c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LINK_SC THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SCF_LINK_SPHERE THEN ASM_SIMP_TAC[]]);;

(* Every nonempty simplex has a vertex of the complex.                        *)

let MOI_SCF_SC_VERTEX = prove
 (`!c s:real^N->bool.
        simplicial_complex c /\ s IN c /\ ~(s = {})
        ==> ?v. {v} IN c /\ v IN s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[MOI_CON_SC_COMPACT; MOI_CON_SC_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN EXISTS_TAC `v:real^N` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CON_SC_FACE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[FACE_OF_SING];
    ASM_MESON_TAC[extreme_point_of]]);;

(* A simplex of the link: vertex set C, independent together with v.        *)

let MOI_SCF_LINK_VERTS = prove
 (`!c (v:real^N) s.
        simplicial_complex c /\ {v} IN c /\ s IN simplicial_link c v
        ==> ?C. ~affine_dependent (v INSERT C) /\ ~(v IN C) /\
                s = convex hull C /\ convex hull (v INSERT C) IN c`,
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N) IN V` ASSUME_TAC THENL
   [SUBGOAL_THEN `(v:real^N) extreme_point_of t` MP_TAC THENL
     [ASM_MESON_TAC[MOI_SCF_VERTEX_EXTREME]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?C:real^N->bool. C SUBSET V /\ s = convex hull C`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT]; ALL_TAC] THEN
  EXISTS_TAC `C:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((v:real^N) IN C)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `C:real^N->bool`]
      HULL_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `V:real^N->bool` THEN ASM SET_TAC[];
    MATCH_MP_TAC MOI_CON_SC_FACE THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `t = convex hull (V:real^N->bool)` THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `(v:real^N) INSERT C` THEN ASM SET_TAC[]]);;

let MOI_SCF_HULL_INSERT_HULL = prove
 (`!v:real^N s. convex hull (v INSERT convex hull s) =
                convex hull (v INSERT s)`,
  REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[SET_RULE `(v:real^N) INSERT s = {v} UNION s`] THEN
  REWRITE_TAC[GSYM HULL_UNION_RIGHT]);;

(* The cone over a simplex of the link.                                      *)

let MOI_SCF_LINK_JOIN = prove
 (`!c (v:real^N) s.
        simplicial_complex c /\ {v} IN c /\ s IN simplicial_link c v
        ==> convex hull (v INSERT s) IN c /\
            v IN convex hull (v INSERT s) /\
            s SUBSET convex hull (v INSERT s) /\
            aff_dim(convex hull (v INSERT s)) = aff_dim s + &1 /\
            (!x. x extreme_point_of convex hull (v INSERT s) <=>
                 x = v \/ x extreme_point_of s) /\
            ~(v IN s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SCF_LINK_VERTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((v:real^N) IN s)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_SCF_HULL_INSERT_HULL] THEN
  SUBGOAL_THEN `~affine_dependent (C:real^N->bool) /\ FINITE C`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
      EXISTS_TAC `(v:real^N) INSERT C` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE; FINITE_INSERT]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; IN_INSERT;
               AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT;
               CARD_CLAUSES; HULL_INC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC]);;

(* Every simplex at v is such a cone.                                        *)

let MOI_SCF_LINK_OPP = prove
 (`!c (v:real^N) t.
        simplicial_complex c /\ {v} IN c /\ t IN c /\ v IN t
        ==> ?s. s IN simplicial_link c v /\ t = convex hull (v INSERT s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N) IN V` ASSUME_TAC THENL
   [SUBGOAL_THEN `(v:real^N) extreme_point_of t` MP_TAC THENL
     [ASM_MESON_TAC[MOI_SCF_VERTEX_EXTREME]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `convex hull (V DELETE (v:real^N))` THEN CONJ_TAC THENL
   [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    SUBGOAL_THEN `convex hull (V DELETE (v:real^N)) face_of t` ASSUME_TAC THENL
     [UNDISCH_TAC `t = convex hull (V:real^N->bool)` THEN
      DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `V DELETE (v:real^N)` THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CON_SC_FACE THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `~affine_dependent (V:real^N->bool)` THEN
      REWRITE_TAC[affine_dependent] THEN
      MP_TAC(ISPEC `V DELETE (v:real^N)` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[MOI_SCF_HULL_INSERT_HULL] THEN
    ASM_SIMP_TAC[INSERT_DELETE]]);;

(* Inclusion of cones reflects inclusion of their bases.                    *)

let MOI_SCF_LINK_JOIN_SUBSET = prove
 (`!c (v:real^N) s s'.
        simplicial_complex c /\ {v} IN c /\
        s IN simplicial_link c v /\ s' IN simplicial_link c v
        ==> (convex hull (v INSERT s) SUBSET convex hull (v INSERT s') <=>
             s SUBSET s')`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC;
    DISCH_TAC THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull ((v:real^N) INSERT s) face_of
                convex hull (v INSERT s')` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_SUBSET_FACE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x extreme_point_of s ==> x extreme_point_of s'`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
     [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) extreme_point_of convex hull (v INSERT s')`
    MP_TAC THENL
     [MP_TAC(ISPECL [`convex hull ((v:real^N) INSERT s)`;
                     `convex hull ((v:real^N) INSERT s')`; `x:real^N`]
        EXTREME_POINT_OF_FACE) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN simplicial_link c v
                ==> r = convex hull {x | x extreme_point_of r}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
    SUBGOAL_THEN `(r:real^N->bool) IN c` ASSUME_TAC THENL
     [UNDISCH_TAC `(r:real^N->bool) IN simplicial_link c v` THEN
      REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN MESON_TAC[];
      ASM_MESON_TAC[MOI_CON_SC_CONVEX; MOI_CON_SC_COMPACT]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `convex hull {x:real^N | x extreme_point_of s'}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull {x:real^N | x extreme_point_of s}` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[]];
    FIRST_X_ASSUM(MP_TAC o SPEC `s':real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_SCF_LINK_JOIN_INJ = prove
 (`!c (v:real^N) s s'.
        simplicial_complex c /\ {v} IN c /\
        s IN simplicial_link c v /\ s' IN simplicial_link c v /\
        convex hull (v INSERT s) = convex hull (v INSERT s')
        ==> s = s'`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  ASM_MESON_TAC[MOI_SCF_LINK_JOIN_SUBSET; SUBSET_REFL]);;

(* Two distinct simplices of dimension n + 1 containing a common subset of  *)
(* dimension n meet in dimension n.                                          *)

let MOI_SCF_INTER_DIM = prove
 (`!c s t f:real^N->bool n.
        simplicial_complex c /\ s IN c /\ t IN c /\ ~(s = t) /\
        aff_dim s = n + &1 /\ aff_dim t = n + &1 /\
        f SUBSET s INTER t /\ aff_dim f = n
        ==> aff_dim(s INTER t) = n`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(INT_ARITH `n <= x /\ x < n + &1 ==> x:int = n`) THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real^N->bool`; `s INTER t:real^N->bool`]
      AFF_DIM_SUBSET) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(s INTER t:real^N->bool) < aff_dim s` MP_TAC THENL
   [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MOI_CON_SC_INTER];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`;
                     `t:real^N->bool`] MOI_SCF_SUBSET_DIM_EQ) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* C2 from C1 applied to the vertex links, and the theorem C2.              *)
(* ------------------------------------------------------------------------- *)

let MOI_SCF_CM_VERTEX = prove
 (`!c (v:real^N).
        FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c
        ==> simplicial_complex c /\
            simplicial_complex (simplicial_link c v) /\
            UNIONS (simplicial_link c v) homeomorphic sphere(vec 0:real^3,&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_SCF_CM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `v:real^N`)) THEN
  ASM_REWRITE_TAC[]);;

let MOI_SCF_CF_DIM_LE = prove
 (`!c s:real^N->bool.
        FINITE c /\ combinatorial_manifold 3 c /\ s IN c ==> aff_dim s <= &3`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_SCF_CM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_SCF_SC_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_SCF_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s0:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `s0:real^N->bool`]
    MOI_SCF_SURF_DIM_LE) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_SCF_CF_PURE = prove
 (`!c s:real^N->bool.
        FINITE c /\ combinatorial_manifold 3 c /\ s IN c /\ ~(s = {})
        ==> ?tet. tet IN c /\ aff_dim tet = &3 /\ s SUBSET tet`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_SCF_CM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_SCF_SC_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_SCF_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN
   `?t0:real^N->bool. t0 IN simplicial_link c v /\ aff_dim t0 = &2 /\
                      s0 SUBSET t0`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `s0:real^N->bool = {}` THENL
     [SUBGOAL_THEN `?s1:real^N->bool. s1 IN simplicial_link c v /\ ~(s1 = {})`
      STRIP_ASSUME_TAC THENL
       [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        SUBGOAL_THEN `UNIONS (simplicial_link c (v:real^N)) = {}` MP_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        DISCH_THEN(fun th ->
          UNDISCH_TAC `UNIONS (simplicial_link c (v:real^N)) homeomorphic
                       sphere(vec 0:real^3,&1)` THEN REWRITE_TAC[th]) THEN
        REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `s1:real^N->bool`]
        MOI_SCF_SURF_PURE) THEN
      ASM_REWRITE_TAC[EMPTY_SUBSET] THEN MESON_TAC[];
      MATCH_MP_TAC MOI_SCF_SURF_PURE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t0:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
  EXISTS_TAC `convex hull ((v:real^N) INSERT t0)` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [INT_ARITH_TAC; MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]]);;

let MOI_SCF_CF_TRIANGLE = prove
 (`!c t:real^N->bool.
        FINITE c /\ combinatorial_manifold 3 c /\ t IN c /\ aff_dim t = &2
        ==> CARD {tet | tet IN c /\ aff_dim tet = &3 /\ t SUBSET tet} = 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_SCF_CM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_SCF_SC_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_SCF_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e0:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
  SUBGOAL_THEN `aff_dim(e0:real^N->bool) = &1` ASSUME_TAC THENL
   [ASM_INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `{tet | tet IN c /\ aff_dim tet = &3 /\
           convex hull ((v:real^N) INSERT e0) SUBSET tet} =
    IMAGE (\s. convex hull (v INSERT s))
          {s | s IN simplicial_link c v /\ aff_dim s = &2 /\ e0 SUBSET s}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `tet:real^N->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `tet:real^N->bool`]
        MOI_SCF_LINK_OPP) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ASM_INT_ARITH_TAC;
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`;
                       `e0:real^N->bool`; `s:real^N->bool`]
          MOI_SCF_LINK_JOIN_SUBSET) THEN
        ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool`
        (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [INT_ARITH_TAC; MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `e0:real^N->bool`]
    MOI_SCF_SURF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `CARD {s:real^N->bool | s IN simplicial_link c v /\
                                     aff_dim s = &2 /\ e0 SUBSET s}` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN REWRITE_TAC[IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_SCF_LINK_JOIN_INJ THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_SIMP_TAC[MOI_SCF_SC_FINITE]]);;

let MOI_SCF_CF_EDGE = prove
 (`!c e:real^N->bool.
        FINITE c /\ combinatorial_manifold 3 c /\ e IN c /\ aff_dim e = &1
        ==> ?n S. 3 <= n /\ (!i. S(i + n) = (S:num->real^N->bool) i) /\
                  (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
                  (!i. S i IN c /\ aff_dim(S i) = &3 /\ e SUBSET S i /\
                       aff_dim(S i INTER S(SUC i)) = &2) /\
                  (!tet. tet IN c /\ aff_dim tet = &3 /\ e SUBSET tet
                       ==> ?i. i < n /\ tet = S i)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_SCF_CM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_SCF_SC_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SCF_CM_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_SCF_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b0:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `b0:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
  SUBGOAL_THEN `?b:real^N. b0 = {b}` (X_CHOOSE_THEN `b:real^N` SUBST_ALL_TAC)
  THENL [REWRITE_TAC[GSYM AFF_DIM_EQ_0] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `b:real^N`]
    MOI_SCF_SURF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `S:num->real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "Sinj") (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "Sall"))))))) THEN
  SUBGOAL_THEN
   `!i. convex hull ((v:real^N) INSERT (S:num->real^N->bool) i) IN c /\
        aff_dim(convex hull (v INSERT S i)) = &3`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`;
                   `(S:num->real^N->bool) i`] MOI_SCF_LINK_JOIN) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `n:num` THEN
  EXISTS_TAC `\i. convex hull ((v:real^N) INSERT (S:num->real^N->bool) i)` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
    USE_THEN "Sinj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SCF_LINK_JOIN_INJ THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim((S:num->real^N->bool) i) = &2 /\
                  aff_dim(S i INTER S(SUC i)) = &1 /\
                  S i IN simplicial_link c v /\
                  S(SUC i) IN simplicial_link c v`
    STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(S:num->real^N->bool) i INTER S(SUC i) IN
                  simplicial_link c v`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_CON_SC_FACE THEN
      EXISTS_TAC `(S:num->real^N->bool) i` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_CON_SC_INTER];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`;
                   `(S:num->real^N->bool) i INTER S(SUC i)`]
      MOI_SCF_LINK_JOIN) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    MATCH_MP_TAC MOI_SCF_INTER_DIM THEN
    MAP_EVERY EXISTS_TAC
     [`c:(real^N->bool)->bool`;
      `convex hull ((v:real^N) INSERT ((S:num->real^N->bool) i INTER
                                        S(SUC i)))`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(S:num->real^N->bool) i = S(SUC i)` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_SCF_LINK_JOIN_INJ THEN
        MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `aff_dim((S:num->real^N->bool)(SUC i)) = &2` MP_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `aff_dim((S:num->real^N->bool) i INTER S(SUC i)) = &1` THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th ->
        concl th = `(S:num->real^N->bool) i = S(SUC i)`)) THEN
      REWRITE_TAC[INTER_IDEMPOT] THEN INT_ARITH_TAC;
      INT_ARITH_TAC;
      INT_ARITH_TAC;
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    X_GEN_TAC `tet:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `tet:real^N->bool`]
      MOI_SCF_LINK_OPP) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
      MOI_SCF_LINK_JOIN) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `{b:real^N}`;
                   `s:real^N->bool`] MOI_SCF_LINK_JOIN_SUBSET) THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN DISCH_TAC THEN
    USE_THEN "Sall" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SIMP_TAC[]]);;

(* C2: the combinatorics of a finite combinatorial 3-manifold.              *)

let MOI_SMO_CF = prove
 (`!u:N->bool. MOI_SMO_CF_STATEMENT u`,
  GEN_TAC THEN REWRITE_TAC[MOI_SMO_CF_STATEMENT] THEN
  X_GEN_TAC `c:(real^N->bool)->bool` THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_SCF_CF_DIM_LE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_SCF_CF_PURE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_SCF_CF_TRIANGLE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_SCF_CF_EDGE THEN ASM_REWRITE_TAC[]]);;

(* The glue term MOI_SMO_CF_TERM of pc_moi_smo_defs (C1 implies C2) as a    *)
(* theorem.                                                                 *)

let MOI_SCF_CF_TERM_THM = prove
 (MOI_SMO_CF_TERM,
  REWRITE_TAC[MOI_SMO_CF]);;

