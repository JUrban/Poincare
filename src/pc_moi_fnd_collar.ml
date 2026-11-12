(* ========================================================================= *)
(* pc_moi_fnd_collar: collars and two-sidedness for the Moise PL core        *)
(* (Moise, Geometric Topology in Dimensions 2 and 3, GTM 47, Sec 26,         *)
(* pp.191-192, 26.1-26.3).  Main theorems (terms of pc_moi_fnd_stmt.ml):     *)
(*   BOUNDARY_COLLAR                 = MOI_FND_COLLAR                        *)
(*   TWO_SIDED_BOUNDARY_COMPONENTS   = MOI_FND_TWO_SIDED_BOUNDARY            *)
(*   TWO_SIDED_R3                    = MOI_FND_TWO_SIDED_R3                  *)
(* The bicollars SURFACE_BICOLLAR = MOI_FND_BICOLLAR and                     *)
(* SURFACE_BICOLLAR_R3 = MOI_FND_BICOLLAR_R3 are proved in pc_moi_fnd_bicol, *)
(* and CURVE_BICOLLAR_ORIENTABLE = MOI_FND_BICOLLAR_CURVE_2 in               *)
(* pc_moi_fnd_cbicol.                                                        *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_rn.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_cells.ml";;
needs "src/pc_moi_s34_outer.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Invariance of domain for subsets of combinatorial 3-manifolds with        *)
(* boundary, with moi_fmb_mint of pc_moi_fnd_m3b (a neighbourhood            *)
(* homeomorphic to an open subset of real^3), and                            *)
(* TWO_SIDED_BOUNDARY_COMPONENTS (Moise 26.1, p.191).                        *)
(* ========================================================================= *)

let MOI_FCL_OPEN_IN_SUBSET_INTER = prove
 (`!(X:real^N->bool) Y U W.
     Y SUBSET X /\ open_in (subtopology euclidean Y) U /\
     open_in (subtopology euclidean X) W
     ==> open_in (subtopology euclidean U) (U INTER W)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t1:real^N->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `t2:real^N->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `t2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Two neighbourhoods homeomorphic to open subsets of real^3, one in Y and  *)
(* one in X with Y inside X: Y contains a neighbourhood of the point in X. *)

let MOI_FCL_MINT_OPEN = prove
 (`!(X:real^N->bool) Y x.
     Y SUBSET X /\ x IN Y /\ moi_fmb_mint Y x /\ moi_fmb_mint X x
     ==> ?U. open_in (subtopology euclidean X) U /\ x IN U /\ U SUBSET Y`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fmb_mint; homeomorphic] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `U1:real^N->bool` (X_CHOOSE_THEN `V1:real^3->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h1:real^N->real^3`
            (X_CHOOSE_TAC `k1:real^3->real^N`)))))))
      (X_CHOOSE_THEN `U2:real^N->bool` (X_CHOOSE_THEN `V2:real^3->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h2:real^N->real^3`
            (X_CHOOSE_TAC `k2:real^3->real^N`)))))))))) THEN
  EXISTS_TAC `U1 INTER U2:real^N->bool` THEN
  SUBGOAL_THEN `(U1:real^N->bool) SUBSET Y /\ (U2:real^N->bool) SUBSET X`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean U1) (U1 INTER U2:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FCL_OPEN_IN_SUBSET_INTER THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `Y:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (h1:real^N->real^3) (U1 INTER U2))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `V1:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h1:real^N->real^3`; `k1:real^3->real^N`; `U1:real^N->bool`;
                   `V1:real^3->bool`; `U1 INTER U2:real^N->bool`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `homeomorphism (U1:real^N->bool,V1:real^3->bool) (h1,k1)` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  UNDISCH_TAC `homeomorphism (U2:real^N->bool,V2:real^3->bool) (h2,k2)` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (h2:real^N->real^3) (U1 INTER U2))` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (h2:real^N->real^3) (U1 INTER U2) =
      IMAGE ((h2:real^N->real^3) o (k1:real^3->real^N)) (IMAGE h1 (U1 INTER U2))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
      REWRITE_TAC[o_THM; IN_INTER] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `V1:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `U2:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[]];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; o_THM;
                  IN_INTER] THEN
      X_GEN_TAC `x1:real^N` THEN REPEAT DISCH_TAC THEN
      X_GEN_TAC `x2:real^N` THEN REPEAT DISCH_TAC THEN
      AP_TERM_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ALL_TAC; ASM_REWRITE_TAC[IN_INTER]; ASM SET_TAC[]] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `U2:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `U1 INTER U2 =
    {y | y IN U2 /\ (h2:real^N->real^3) y IN IMAGE h2 (U1 INTER U2)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; IN_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `y:real^N = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN ASM_REWRITE_TAC[]]);;

(* A subset Y of |c| with a neighbourhood homeomorphic to an open subset of *)
(* real^3 at x forces x off complex_boundary c (half-space charts).         *)

let MOI_FCL_MINT_NOT_CB = prove
 (`!(c:(real^N->bool)->bool) Y x.
     combinatorial_manifold_with_boundary 3 c /\ Y SUBSET UNIONS c /\ x IN Y /\
     moi_fmb_mint Y x
     ==> ~(x IN complex_boundary c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS c` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FMB_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` (X_CHOOSE_THEN `p:real^N->real^3`
    (X_CHOOSE_THEN `p':real^3->real^N` (X_CHOOSE_THEN `O:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `((p:real^N->real^3) x)$3 = &0` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `moi_fmb_mint Y (x:real^N)` THEN
  REWRITE_TAC[moi_fmb_mint; homeomorphic; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `V:real^3->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h:real^N->real^3`
      (X_CHOOSE_TAC `h':real^3->real^N`))))) THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET Y` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean U) (U INTER W:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FCL_OPEN_IN_SUBSET_INTER THEN
    MAP_EVERY EXISTS_TAC [`UNIONS c:real^N->bool`; `Y:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (h:real^N->real^3) (U INTER W))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:real^N->real^3`; `h':real^3->real^N`; `U:real^N->bool`;
                   `V:real^3->bool`; `U INTER W:real^N->bool`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `homeomorphism (U:real^N->bool,V:real^3->bool) (h,h')` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  UNDISCH_TAC `homeomorphism (W:real^N->bool,IMAGE (p:real^N->real^3) W) (p,p')` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `open (IMAGE (p:real^N->real^3) (U INTER W))` MP_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (p:real^N->real^3) (U INTER W) =
      IMAGE ((p:real^N->real^3) o (h':real^3->real^N)) (IMAGE h (U INTER W))`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN MATCH_MP_TAC IMAGE_EQ THEN
      REWRITE_TAC[o_THM; IN_INTER] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `V:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `W:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN ASM_MESON_TAC[]];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE; o_THM;
                  IN_INTER] THEN
      X_GEN_TAC `x1:real^N` THEN REPEAT DISCH_TAC THEN
      X_GEN_TAC `x2:real^N` THEN REPEAT DISCH_TAC THEN
      AP_TERM_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[open_def] THEN DISCH_THEN(MP_TAC o SPEC `(p:real^N->real^3) x`) THEN
  ANTS_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^N->real^3) x - (e / &2) % basis 3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[dist; VECTOR_ARITH `(a - b) - a:real^N = --b`; NORM_NEG; NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(p:real^N->real^3) x - (e / &2) % basis 3 IN IMAGE p W` MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (y:real^3). y IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `IMAGE (p:real^N->real^3) (U INTER W)` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC);;

(* ========================================================================= *)
(* TWO_SIDED_BOUNDARY_COMPONENTS (Moise 26.1, p.191). A component k of s is  *)
(* a component of Bd m; a connected w near k with k in its relative interior *)
(* splits into its part in |m| - Bd m (open in |c| by invariance of domain;  *)
(* it meets w near a tetrahedron of m) and its part off |m| (it meets w      *)
(* since k misses Bd c).                                                     *)
(* ========================================================================= *)

let MOI_FCL_UNIONS_CLOSED_FINITE = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c ==> closed (UNIONS c)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o
    GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CLOSED]);;

let MOI_FCL_CARD_1_NONEMPTY = prove
 (`!s:A->bool. CARD s = 1 ==> ?a. a IN s`,
  GEN_TAC THEN REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
  DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `CARD({}:A->bool) = 1` THEN REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC);;

let MOI_FCL_CB_TRIANGLES = prove
 (`!c:(real^N->bool)->bool.
     complex_boundary c =
     UNIONS {s | s IN c /\ aff_dim s = &2 /\
                 CARD {r | r IN c /\ aff_dim r = &3 /\ s SUBSET r} = 1}`,
  REWRITE_TAC[complex_boundary]);;

let MOI_FCL_CB_CLOSED = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c ==> closed (complex_boundary c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[complex_boundary] THEN
  MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1 o
      GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CLOSED]]);;

(* A component k of a finite union of closed connected sets: the union     *)
(* minus k is the union of the pieces missing k, hence closed.             *)

let MOI_FCL_COMPONENT_COMPL_CLOSED = prove
 (`!(f:(real^N->bool)->bool) k.
     FINITE f /\ (!t. t IN f ==> closed t /\ connected t) /\
     k IN components (UNIONS f)
     ==> closed (UNIONS f DIFF k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS f DIFF k = UNIONS {t | t IN f /\ DISJOINT t (k:real^N->bool)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[DISJOINT] THEN
      ASM_CASES_TAC `k INTER (t:real^N->bool) = {}` THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(t:real^N->bool) SUBSET k` (fun th -> ASM SET_TAC[th]) THEN
      MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
      EXISTS_TAC `UNIONS f:real^N->bool` THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      CONJ_TAC THENL [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]]];
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[IN_ELIM_THM] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* The interior |m| - Bd m of a finite combinatorial 3-manifold with        *)
(* boundary inside another one is open in the bigger polyhedron.           *)

let MOI_FCL_INTERIOR_OPEN_IN = prove
 (`!(c:(real^N->bool)->bool) m.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     FINITE m /\ combinatorial_manifold_with_boundary 3 m /\
     UNIONS m SUBSET UNIONS c
     ==> open_in (subtopology euclidean (UNIONS c))
                 (UNIONS m DIFF complex_boundary m)`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_fmb_mint (UNIONS m) (y:real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_MINT_CB]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_fmb_mint (UNIONS c) (y:real^N)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `y:real^N`] MOI_FMB_MINT_CB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~a ==> (a <=> ~b) ==> b`) THEN
    MATCH_MP_TAC MOI_FCL_MINT_NOT_CB THEN
    EXISTS_TAC `UNIONS m:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `UNIONS m:real^N->bool`; `y:real^N`]
    MOI_FCL_MINT_OPEN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `U DIFF complex_boundary m:real^N->bool` THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CLOSED_SUBSET THEN
  SUBGOAL_THEN `complex_boundary (m:(real^N->bool)->bool) SUBSET UNIONS c`
    (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[MOI_FMB_CB_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FCL_CB_CLOSED THEN
  ASM_MESON_TAC[combinatorial_manifold_with_boundary]);;

(* A point of Bd m off Bd c has points of |c| - |m| arbitrarily near.     *)

let MOI_FCL_BD_NOT_INTERIOR = prove
 (`!(c:(real^N->bool)->bool) m x U.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     FINITE m /\ combinatorial_manifold_with_boundary 3 m /\
     UNIONS m SUBSET UNIONS c /\
     x IN complex_boundary m /\ ~(x IN complex_boundary c) /\
     open_in (subtopology euclidean (UNIONS c)) U /\ x IN U
     ==> ~(U SUBSET UNIONS m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS m` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_CB_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_fmb_mint (UNIONS c) (x:real^N)` MP_TAC THENL
   [ASM_MESON_TAC[MOI_FMB_MINT_CB; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[moi_fmb_mint; homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `U2:real^N->bool` (X_CHOOSE_THEN `V2:real^3->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h2:real^N->real^3`
        (X_CHOOSE_TAC `k2:real^3->real^N`))))))) THEN
  SUBGOAL_THEN `moi_fmb_mint (UNIONS m) (x:real^N)` MP_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[MOI_FMB_MINT_CB]] THEN
  REWRITE_TAC[moi_fmb_mint] THEN
  MAP_EVERY EXISTS_TAC [`U INTER U2:real^N->bool`;
                        `IMAGE (h2:real^N->real^3) (U INTER U2)`] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c)) (U INTER U2:real^N->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `(U2:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[IN_INTER];
    MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `V2:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h2:real^N->real^3`; `k2:real^3->real^N`; `U2:real^N->bool`;
                   `V2:real^3->bool`; `U INTER U2:real^N->bool`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`h2:real^N->real^3`; `k2:real^3->real^N`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`U2:real^N->bool`; `V2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `homeomorphism (U2:real^N->bool,V2:real^3->bool) (h2,k2)` THEN
    REWRITE_TAC[homeomorphism] THEN SET_TAC[]]);;

let TWO_SIDED_BOUNDARY_COMPONENTS = prove
 (MOI_FND_TWO_SIDED_BOUNDARY,

  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `m:(real^N->bool)->bool`;
                       `s:real^N->bool`] THEN
  STRIP_TAC THEN REWRITE_TAC[two_sided_in] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool) /\
                lf_simplicial_complex (m:(real^N->bool)->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `complex_boundary (m:(real^N->bool)->bool) SUBSET UNIONS m`
  ASSUME_TAC THENL [REWRITE_TAC[MOI_FMB_CB_SUBSET]; ALL_TAC] THEN
  (* k is a component of the boundary of m *)
  SUBGOAL_THEN `(k:real^N->bool) IN components (complex_boundary m)` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [IN_COMPONENTS_MAXIMAL]) THEN
    MP_TAC(ISPECL [`complex_boundary (m:(real^N->bool)->bool)`; `k:real^N->bool`]
      EXISTS_COMPONENT_SUPERSET) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `K:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(K:real^N->bool) SUBSET s` ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `K:real^N->bool = k` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k:real^N->bool = {}) /\ k SUBSET complex_boundary m`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_SUBSET];
                          ALL_TAC] THEN
  (* the rest of the boundary of m is closed *)
  SUBGOAL_THEN `closed (complex_boundary m DIFF k:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `(k:real^N->bool) IN components (complex_boundary m)` THEN
    REWRITE_TAC[MOI_FCL_CB_TRIANGLES] THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FCL_COMPONENT_COMPL_CLOSED THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `m:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
      FIRST_ASSUM(MP_TAC o SPEC `t:real^N->bool` o CONJUNCT1 o
        GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
      ASM_REWRITE_TAC[] THEN
      MESON_TAC[SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED]];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS c DIFF (complex_boundary m DIFF k):real^N->bool` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL] THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^N->bool` THEN STRIP_TAC THEN
  (* a point of k with a ball inside w *)
  SUBGOAL_THEN
   `?x e. (x:real^N) IN k /\ &0 < e /\ !y. y IN UNIONS c /\ dist(x,y) < e ==> y IN w`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(k:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN EXISTS_TAC `x:real^N` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^N) IN (subtopology euclidean (UNIONS c)) interior_of w`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[interior_of; IN_ELIM_THM; OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [open_def]) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_OPEN_IN] THEN
  MAP_EVERY EXISTS_TAC
   [`(w DIFF k) INTER (UNIONS m DIFF complex_boundary m):real^N->bool`;
    `(w DIFF k) DIFF UNIONS m:real^N->bool`] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `m:(real^N->bool)->bool`]
      MOI_FCL_INTERIOR_OPEN_IN) THEN
    ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `(:real^N) DIFF UNIONS m` THEN
    REWRITE_TAC[GSYM closed] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FCL_UNIONS_CLOSED_FINITE THEN ASM_REWRITE_TAC[]; SET_TAC[]];
    ASM SET_TAC[];
    SET_TAC[];
    (* the part in the interior of m is nonempty *)
    SUBGOAL_THEN
     `?t r. (t:real^N->bool) IN m /\ (x:real^N) IN t /\ r IN m /\
            aff_dim r = &3 /\ t SUBSET r`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(x:real^N) IN complex_boundary m` MP_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_FCL_CARD_1_NONEMPTY) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `r:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex (r:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN closure(relative_interior r)` MP_TAC THENL
     [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR] THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
    SUBGOAL_THEN `(y:real^N) IN r` ASSUME_TAC THENL
     [ASM_MESON_TAC[REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN UNIONS m` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((y:real^N) IN complex_boundary m)` ASSUME_TAC THENL
     [REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `r:real^N->bool`; `q:real^N->bool`;
                     `y:real^N`] MOI_FRN_RELINT_SUBSET) THEN
      ASM_SIMP_TAC[MOI_FRN_LF_BAR_COMPLEX] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`r:real^N->bool`; `q:real^N->bool`] AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
      ASM_MESON_TAC[SUBSET]];
    (* the part off m is nonempty *)
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN complex_boundary m /\ ~(x IN complex_boundary c) /\
                  x IN UNIONS c` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET];
        ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET; IN_DISJOINT];
        ASM_MESON_TAC[SUBSET]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `m:(real^N->bool)->bool`; `x:real^N`;
                   `UNIONS c INTER ball(x:real^N,e)`] MOI_FCL_BD_NOT_INTERIOR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN
      MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN X_GEN_TAC `y:real^N` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN w` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(w DIFF k) DIFF UNIONS m = {}:real^N->bool` THEN
    UNDISCH_TAC `(y:real^N) IN w` THEN
    UNDISCH_TAC `(k:real^N->bool) SUBSET complex_boundary m` THEN
    UNDISCH_TAC `complex_boundary (m:(real^N->bool)->bool) SUBSET UNIONS m` THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* Components of finite combinatorial 2-manifolds, and TWO_SIDED_R3 (from    *)
(* MOISE_266, Moise 26.6: a connected closed polyhedral surface in real^3    *)
(* has two complementary components, both with frontier the surface).        *)
(* ========================================================================= *)

let MOI_FCL_CM2_COMPONENT = prove
 (`!(s:(real^N->bool)->bool) k.
     FINITE s /\ combinatorial_manifold 2 s /\ k IN components (UNIONS s)
     ==> FINITE {t | t IN s /\ t SUBSET k} /\
         combinatorial_manifold 2 {t | t IN s /\ t SUBSET k} /\
         UNIONS {t | t IN s /\ t SUBSET k} = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (s:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN s ==> connected t` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN s /\ ~(t INTER k = {}) ==> t SUBSET k`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `UNIONS s:real^N->bool` THEN ASM_SIMP_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `s:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC;
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS s` MP_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]] THEN
  REWRITE_TAC[combinatorial_manifold] THEN CONJ_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (s:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex; IN_ELIM_THM] THEN
    STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `t:real^N->bool`] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
      ASM_MESON_TAC[];
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
        is_forall(concl th) &&
        can (find_term (fun t -> try fst(dest_const t) = "FINITE"
                                 with Failure _ -> false)) (concl th))) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `simplicial_link {t | t IN s /\ t SUBSET k} (v:real^N) = simplicial_link s v`
  SUBST1_TAC THENL
   [REWRITE_TAC[simplicial_link; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `f:real^N->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) SUBSET k` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS];
        EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]]];
    ASM_MESON_TAC[combinatorial_manifold]]);;

let TWO_SIDED_R3 = prove
 (MOI_FND_TWO_SIDED_R3,
  DISCH_TAC THEN
  X_GEN_TAC `s:(real^3->bool)->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[two_sided_in] THEN X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:(real^3->bool)->bool`; `k:real^3->bool`] MOI_FCL_CM2_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k:real^3->bool = {}) /\ connected k /\ k SUBSET UNIONS s`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; IN_COMPONENTS_CONNECTED;
                  IN_COMPONENTS_SUBSET];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `{t | t IN s /\ t SUBSET (k:real^3->bool)}` o
    REWRITE_RULE[MOISE_266_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `lf_simplicial_complex (s:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS s DIFF (k:real^3->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FCL_COMPONENT_COMPL_CLOSED THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?n. n simplex (t:real^3->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN `b IN components ((:real^3) DIFF k) /\
                outside k IN components ((:real^3) DIFF k)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (k:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CLOSED_IN_COMPONENT; CLOSED_IN_CLOSED_TRANS;
                  MOI_FCL_UNIONS_CLOSED_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (b:real^3->bool) /\ open (outside k:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC OPEN_COMPONENTS THEN
    EXISTS_TAC `(:real^3) DIFF k` THEN
    ASM_REWRITE_TAC[GSYM closed];
    ALL_TAC] THEN
  SUBGOAL_THEN `b INTER outside k = {}:real^3->bool` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
  SUBGOAL_THEN `(:real^3) DIFF k = b UNION outside k` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^3) DIFF k` UNIONS_COMPONENTS) THEN
    ASM_REWRITE_TAC[UNIONS_2];
    ALL_TAC] THEN
  EXISTS_TAC `(:real^3) DIFF (UNIONS s DIFF k)` THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; EUCLIDEAN_INTERIOR_OF] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[GSYM closed];
    ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `w:real^3->bool` THEN STRIP_TAC THEN
  UNDISCH_TAC `~(k:real^3->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^3`) THEN
  SUBGOAL_THEN `?e. &0 < e /\ ball(x:real^3,e) SUBSET w` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^3) IN interior w` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTERIOR];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^3->bool. frontier c = k ==> ?y. y IN c /\ y IN ball(x,e)`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN closure c` MP_TAC THENL
     [ASM_MESON_TAC[frontier; IN_DIFF]; ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[IN_BALL] THEN MESON_TAC[DIST_SYM];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_OPEN_IN] THEN
  MAP_EVERY EXISTS_TAC [`(w DIFF k) INTER b:real^3->bool`;
                        `(w DIFF k) INTER outside k:real^3->bool`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `b:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^3` THEN
    ASM SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `outside k:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^3` THEN
    ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Generic cell tools.  Injective PL maps on compact sets are PL             *)
(* homeomorphisms; full-dimensional polytopes are PL cells bounded by their  *)
(* frontier (generic form of MOI_S5C_POLYTOPE_CELL of pc_moi_s35_minc and    *)
(* MOI_S5A_POLYTOPE_CELL of pc_moi_s35_approx, which are not in this load    *)
(* closure; proofs adapted and generalised); the relative frontier of a cone *)
(* simplex; cones over PL cells.                                             *)
(* ========================================================================= *)

let MOI_FCL_PLH_COMPACT = prove
 (`!(s:real^M->bool) (f:real^M->real^N).
     compact s /\ pl_map_on s f /\
     (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y)
     ==> ?g. pl_homeomorphism (s,IMAGE f s) (f,g)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?g. homeomorphism (s,IMAGE (f:real^M->real^N) s) (f,g)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
    ALL_TAC] THEN
  EXISTS_TAC `g:real^N->real^M` THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[]);;

(* The same as MOI_S5C_CONVEX_CONE_RF (pc_moi_s35_minc.ml). *)

let MOI_FCL_CONVEX_CONE_RF = prove
 (`!t (b:real^N).
     convex t /\ compact t /\ b IN relative_interior t /\ ~(t = {b})
     ==> ~(b IN relative_frontier t) /\
         (!x y. x IN relative_frontier t /\ y IN relative_frontier t /\
                y IN segment[b,x] ==> y = x) /\
         UNIONS {segment[b,x] | x IN relative_frontier t} = t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[MOI_CON_RF_SEGMENT];
    REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ; SUBSET; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `segment[b:real^N,x] SUBSET t` MP_TAC THENL
       [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; relative_frontier;
                      IN_DIFF; COMPACT_IMP_CLOSED; CLOSURE_CLOSED];
        ASM SET_TAC[]];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`t:real^N->bool`; `b:real^N`; `y:real^N`]
        SEGMENT_TO_RELATIVE_FRONTIER) THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN MESON_TAC[]]]);;

(* The same as MOI_S5C_STAR_RF0 (pc_moi_s35_minc.ml). *)

let MOI_FCL_STAR_RF0 = prove
 (`!P:real^N->bool.
     polytope P /\ vec 0 IN interior P
     ==> pl_sphere (dimindex(:N) - 1) (relative_frontier P)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CMB_STAR_SHAPED_PL_SPHERE_0 THEN
  SUBGOAL_THEN `(vec 0:real^N) IN relative_interior P` ASSUME_TAC THENL
   [ASM_MESON_TAC[INTERIOR_SUBSET_RELATIVE_INTERIOR; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `convex(P:real^N->bool) /\ bounded P` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_BOUNDED]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`P:real^N->bool`; `vec 0:real^N`; `u:real^N`]
        RAY_TO_RELATIVE_FRONTIER) THEN
      ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN ANTS_TAC THENL
       [MATCH_MP_TAC(SET_RULE `s = UNIV ==> (x:real^N) IN s`) THEN
        MATCH_MP_TAC AFFINE_HULL_NONEMPTY_INTERIOR THEN ASM SET_TAC[];
        MESON_TAC[]];
      MAP_EVERY X_GEN_TAC [`r1:real`; `r2:real`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`P:real^N->bool`; `r1 % u:real^N`; `r2 % u:real^N`; `r1 / r2`]
        MOI_CMB_RAY_FRONTIER_UNIQUE) THEN
      ASM_SIMP_TAC[REAL_LT_DIV; VECTOR_MUL_ASSOC; REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN
      ASM_SIMP_TAC[REAL_EQ_LDIV_EQ; REAL_MUL_LID]]]);;

(* A full-dimensional polytope of real^N is a PL cell bounded by its      *)
(* relative frontier (= frontier).  Generalised from MOI_S5C_POLYTOPE_CELL. *)

let MOI_FCL_POLYTOPE_CELL = prove
 (`!P:real^N->bool.
     polytope P /\ ~(interior P = {})
     ==> pl_cell_with_boundary (dimindex(:N)) P (relative_frontier P)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `m:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `pl_sphere (dimindex(:N) - 1) (relative_frontier P:real^N->bool)` MP_TAC THENL
   [MP_TAC(ISPEC `IMAGE (\x:real^N. --m + x) P` MOI_FCL_STAR_RF0) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[POLYTOPE_TRANSLATION_EQ; INTERIOR_TRANSLATION] THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `m:real^N` THEN
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[RELATIVE_FRONTIER_TRANSLATION] THEN DISCH_TAC THEN
    MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (\x:real^N. --m + x) (relative_frontier P)`;
                          `(\x:real^N. m + x)`; `(\x:real^N. --m + x)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CMB_TRANSLATION_PL_HOMEOMORPHISM THEN
    MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `dimindex(:N) - 1 + 1 = dimindex(:N)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:N)` DIMINDEX_GE_1) THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[pl_sphere] THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&(dimindex(:N)):int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LE; DIMINDEX_GE_1]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`P:real^N->bool`; `m:real^N`] MOI_FCL_CONVEX_CONE_RF) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[INTERIOR_SUBSET_RELATIVE_INTERIOR; SUBSET];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(m:real^N) IN interior {m}` THEN
      REWRITE_TAC[INTERIOR_SING; NOT_IN_EMPTY]];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier k:real^N->bool`; `relative_frontier P:real^N->bool`;
                 `simplex_barycentre (k:real^N->bool)`; `m:real^N`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`;
    `moi_con_conemap (relative_frontier k) (simplex_barycentre k) (m:real^N)
       (f:real^N->real^N)`;
    `moi_con_conemap (relative_frontier P) (m:real^N) (simplex_barycentre k)
       (g:real^N->real^N)`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_homeomorphism (relative_frontier k:real^N->bool,
                                 relative_frontier P:real^N->bool) (f:real^N->real^N,g)` THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  TRANS_TAC EQ_TRANS `IMAGE (f:real^N->real^N) (relative_frontier k)` THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC IMAGE_EQ THEN ASM_SIMP_TAC[]);;

(* The relative frontier of the cone simplex over an n-simplex, n >= 1.    *)

let MOI_FCL_RF_CONE_SIMPLEX = prove
 (`!k (w:real^N) n.
     n simplex k /\ &1 <= n /\ ~(w IN affine hull k)
     ==> relative_frontier (convex hull (w INSERT k)) =
         k UNION UNIONS {segment[w,x] | x IN relative_frontier k}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC o
    GEN_REWRITE_RULE I [simplex]) THEN
  SUBGOAL_THEN `FINITE (c:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `~((w:real^N) IN c)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((w:real^N) IN affine hull k)` THEN
    ASM_REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN ASM_MESON_TAC[HULL_INC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent ((w:real^N) INSERT c)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((w:real^N) IN affine hull k)` THEN
    ASM_REWRITE_TAC[AFFINE_HULL_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= CARD(c:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    UNDISCH_TAC `&(CARD(c:real^N->bool)):int = n + &1` THEN
    UNDISCH_TAC `&1:int <= n` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^N. a IN c ==> ~(c DELETE a = {})` ASSUME_TAC THENL
   [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^N`; `c:real^N->bool`] CARD_DELETE) THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN
    UNDISCH_TAC `2 <= CARD(c:real^N->bool)` THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull ((w:real^N) INSERT k) = convex hull (w INSERT c)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SET_RULE `(a:real^N) INSERT s = {a} UNION s`] THEN
    REWRITE_TAC[GSYM HULL_UNION_RIGHT];
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_CONVEX_HULL] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_INSERT] THEN
  SUBGOAL_THEN `((w:real^N) INSERT c) DELETE w = c` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE; EXISTS_IN_GSPEC] THEN
  X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(y:real^N) IN convex hull ((w INSERT c) DELETE a)` THEN
    SUBGOAL_THEN `((w:real^N) INSERT c) DELETE a = w INSERT (c DELETE a)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONVEX_HULL_INSERT_SEGMENTS] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((w:real^N) INSERT c) DELETE a = w INSERT (c DELETE a)` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONVEX_HULL_INSERT_SEGMENTS] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]]);;

(* The cone map carries the cone over a subset onto the cone over its image. *)

let MOI_FCL_CONEMAP_IMAGE_CONE = prove
 (`!a b (u:real^M) (v:real^N) f.
     ~(u IN a) /\
     (!x y. x IN a /\ y IN a /\ y IN segment[u,x] ==> y = x) /\
     b SUBSET a
     ==> IMAGE (moi_con_conemap a u v f) (UNIONS {segment[u,x] | x IN b}) =
         UNIONS {segment[v,y] | y IN IMAGE f b}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `q:real^N` THEN
  REWRITE_TAC[IN_IMAGE; MOI_CON_IN_CONE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `p:real^M` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `x:real^M` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)))) THEN
    MAP_EVERY EXISTS_TAC [`(f:real^M->real^N) x`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_CON_CONEMAP_EQ THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `r:real`
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC)
        STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `u + r % (x - u):real^M` THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC MOI_CON_CONEMAP_EQ THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`x:real^M`; `r:real`] THEN ASM_REWRITE_TAC[]]]);;

(* A cone over a PL n-cell (n >= 1) is a PL (n+1)-cell bounded by the base  *)
(* and the cone over the boundary of the base.                             *)

let MOI_FCL_CONE_CELL = prove
 (`!n (X:real^N->bool) bX v.
     1 <= n /\ n + 1 <= dimindex(:N) /\
     pl_cell_with_boundary n X bX /\ ~(v IN X) /\
     (!x y. x IN X /\ y IN X /\ y IN segment[v,x] ==> y = x)
     ==> pl_cell_with_boundary (n + 1) (UNIONS {segment[v,x] | x IN X})
                               (X UNION UNIONS {segment[v,x] | x IN bX})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_cell_with_boundary n (X:real^N->bool) bX` THEN
  REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?v':real^N. ~(v' IN affine hull k)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(s = (:real^N)) ==> ?x. ~(x IN s)`) THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_AFFINE_HULL) THEN
    ASM_REWRITE_TAC[AFF_DIM_UNIV] THEN
    UNDISCH_TAC `&n simplex (k:real^N->bool)` THEN
    REWRITE_TAC[simplex] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    UNDISCH_TAC `n + 1 <= dimindex(:N)` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_ADD] THEN
    UNDISCH_TAC `&(CARD (c:real^N->bool)):int = &n + &1` THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k:real^N->bool = {}) /\ convex k /\ polytope k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_EMPTY; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYTOPE;
                  INT_ARITH `~(&n:int = -- &1)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v':real^N) IN k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN k /\ y IN k /\ y IN segment[v',x] ==> y = x:real^N`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(y:real^N) IN segment[v',x]` THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `u = &1` THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~((v':real^N) IN affine hull k)` THEN
    MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
    SUBGOAL_THEN `~(&1 - u = &0)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(&1 - u) % v' = y - u % x:real^N` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `v':real^N = inv(&1 - u) % y + (--(inv(&1 - u) * u)) % x`
    SUBST1_TAC THENL
     [SUBGOAL_THEN `v':real^N = inv(&1 - u) % ((&1 - u) % v')` MP_TAC THENL
       [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_LINV] THEN
        REWRITE_TAC[VECTOR_MUL_LID];
        ALL_TAC] THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      REWRITE_TAC[ASSUME `(&1 - u) % v' = y - u % x:real^N`] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
    ASM_SIMP_TAC[HULL_INC] THEN
    UNDISCH_TAC `~(&1 - u = &0)` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `X:real^N->bool`; `v':real^N`; `v:real^N`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON]; STRIP_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull ((v':real^N) INSERT k)`;
    `moi_con_conemap k (v':real^N) v (f:real^N->real^N)`;
    `moi_con_conemap X (v:real^N) v' (g:real^N->real^N)`] THEN
  SUBGOAL_THEN `convex hull ((v':real^N) INSERT k) = UNIONS {segment[v',x] | x IN k}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONVEX_HULL_INSERT_SEGMENTS] THEN
    SUBGOAL_THEN `convex hull k = k:real^N->bool` (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EQ];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
    MATCH_MP_TAC MOI_CON_CONE_SIMPLEX THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `v':real^N`; `&n:int`] MOI_FCL_RF_CONE_SIMPLEX) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IMAGE_UNION] THEN BINOP_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!(h:real^N->real^N) f k X. (!x. x IN k ==> h x = f x) /\ IMAGE f k = X
                                ==> X = IMAGE h k`) THEN
    EXISTS_TAC `f:real^N->real^N` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `pl_homeomorphism (k:real^N->bool,X) (f:real^N->real^N,g)` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `relative_frontier k:real^N->bool`; `v':real^N`;
                 `v:real^N`; `f:real^N->real^N`] MOI_FCL_CONEMAP_IMAGE_CONE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[relative_frontier] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> s DIFF u SUBSET t`) THEN
    ASM_MESON_TAC[CLOSURE_CLOSED; SIMPLEX_IMP_CLOSED; SUBSET_REFL];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Sections of cones.  For a simplicial complex K, a point v with the        *)
(* segment condition over UNIONS K and factors 0 < g z <= 1 at the vertices, *)
(* the simplexwise affine map taking each vertex z to the point v + g z % (z *)
(* - v) of its ray is a PL homeomorphism of UNIONS K onto the union of the   *)
(* lifted simplices (ABSTRACT_REALIZATIONS_PL_HOMEOMORPHIC).                 *)
(* ========================================================================= *)

let MOI_FCL_VEC_DIV = prove
 (`!a b (u:real^N) w. &0 < a /\ a % u = b % w ==> u = (b / a) % w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `u:real^N = inv a % (a % u)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[VECTOR_MUL_ASSOC; real_div] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC]);;

let MOI_FCL_AFF_COORDS_UNIQUE = prove
 (`!S (a:real^N->real) b.
     FINITE S /\ ~affine_dependent S /\ sum S a = &1 /\ sum S b = &1 /\
     vsum S (\x. a x % x) = vsum S (\x. b x % x)
     ==> !x. x IN S ==> a x = b x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `~affine_dependent (S:real^N->bool)` THEN
  ASM_SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT_FINITE] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `\y:real^N. a y - b y`) THEN
  REWRITE_TAC[VECTOR_SUB_RDISTRIB] THEN
  ASM_SIMP_TAC[SUM_SUB; VSUM_SUB; REAL_SUB_REFL; VECTOR_SUB_REFL] THEN
  MESON_TAC[REAL_SUB_0]);;

let MOI_FCL_LIFT_INJ = prove
 (`!S (v:real^N) g.
     FINITE S /\ ~affine_dependent (v INSERT S) /\ ~(v IN S) /\
     (!z. z IN S ==> &0 < g z)
     ==> !x y. x IN S /\ y IN S /\ v + g x % (x - v) = v + g y % (y - v)
               ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:real^N = y` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(x:real^N = v) /\ ~(v = y)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THEN UNDISCH_TAC `~((v:real^N) IN S)` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real) y % (y - v) = g x % (x - v)` ASSUME_TAC THENL
   [UNDISCH_TAC `v + g x % (x - v) = v + (g:real^N->real) y % (y - v)` THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < (g:real^N->real) y` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~affine_dependent ((v:real^N) INSERT S)` THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  MATCH_MP_TAC AFFINE_DEPENDENT_MONO THEN EXISTS_TAC `{x:real^N,v,y}` THEN
  CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
  MP_TAC(ISPECL [`x:real^N`; `v:real^N`; `y:real^N`]
    COLLINEAR_3_EQ_AFFINE_DEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[COLLINEAR_3; COLLINEAR_LEMMA] THEN
  REPEAT DISJ2_TAC THEN EXISTS_TAC `(g:real^N->real) x / g y` THEN
  MATCH_MP_TAC MOI_FCL_VEC_DIV THEN ASM_REWRITE_TAC[]);;

let MOI_FCL_LIFT_NOT_V = prove
 (`!S (v:real^N) g.
     ~(v IN S) /\ (!z. z IN S ==> &0 < g z)
     ==> ~(v IN IMAGE (\z. v + g z % (z - v)) S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `v = v + (g:real^N->real) z % (z - v)` THEN
  REWRITE_TAC[VECTOR_ARITH `v = v + x <=> x = vec 0:real^N`; VECTOR_MUL_EQ_0] THEN
  REWRITE_TAC[VECTOR_SUB_EQ] THEN
  SUBGOAL_THEN `~((g:real^N->real) z = &0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[REAL_LT_IMP_NZ]; ASM_MESON_TAC[]]);;

let MOI_FCL_LIFT_AFF_INDEP = prove
 (`!S (v:real^N) g.
     FINITE S /\ ~affine_dependent (v INSERT S) /\ ~(v IN S) /\
     (!z. z IN S ==> &0 < g z)
     ==> ~affine_dependent (v INSERT IMAGE (\z. v + g z % (z - v)) S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `v:real^N`; `g:real^N->real`] MOI_FCL_LIFT_INJ) THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `v:real^N`; `g:real^N->real`] MOI_FCL_LIFT_NOT_V) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT_FINITE; FINITE_INSERT; FINITE_IMAGE;
           ASSUME `FINITE (S:real^N->bool)`] THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `u:real^N->real` THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_IMAGE; ASSUME `FINITE (S:real^N->bool)`;
           ASSUME `~((v:real^N) IN IMAGE (\z. v + g z % (z - v)) S)`] THEN
  MP_TAC(ISPECL [`\z:real^N. v + (g:real^N->real) z % (z - v)`; `u:real^N->real`;
                 `S:real^N->bool`] SUM_IMAGE) THEN
  MP_TAC(ISPECL [`\z:real^N. v + (g:real^N->real) z % (z - v)`;
                 `\p:real^N. (u:real^N->real) p % p`; `S:real^N->bool`] VSUM_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[o_DEF] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_forall(concl th) &&
    is_imp(snd(strip_forall(concl th))) &&
    is_eq(rand(snd(strip_forall(concl th)))))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  REWRITE_TAC[IN_INSERT; EXISTS_IN_IMAGE; RIGHT_OR_DISTRIB; EXISTS_OR_THM;
              UNWIND_THM2] THEN
  DISCH_TAC THEN
  UNDISCH_TAC `~affine_dependent ((v:real^N) INSERT S)` THEN
  SIMP_TAC[AFFINE_DEPENDENT_EXPLICIT_FINITE; FINITE_INSERT;
           ASSUME `FINITE (S:real^N->bool)`] THEN
  EXISTS_TAC
   `\p:real^N. if p = v
               then u v + sum S (\z. u(v + g z % (z - v)) * (&1 - g z))
               else u(v + g p % (p - v)) * g p` THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; ASSUME `FINITE (S:real^N->bool)`;
           ASSUME `~((v:real^N) IN S)`] THEN
  SUBGOAL_THEN
   `sum S (\p:real^N. if p = v
                     then u v + sum S (\z. u(v + g z % (z - v)) * (&1 - g z))
                     else u(v + g p % (p - v)) * g p) =
    sum S (\z. u(v + g z % (z - v)) * g z) /\
    vsum S (\p:real^N. (if p = v
                       then u v + sum S (\z. u(v + g z % (z - v)) * (&1 - g z))
                       else u(v + g p % (p - v)) * g p) % p) =
    vsum S (\z. (u(v + g z % (z - v)) * g z) % z)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(z:real^N = v)` (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(z:real^N = v)` (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `u v + sum S (\x:real^N. u (v + g x % (x - v))) = &0` THEN
    REWRITE_TAC[GSYM REAL_ADD_ASSOC] THEN
    SIMP_TAC[GSYM SUM_ADD; ASSUME `FINITE (S:real^N->bool)`] THEN
    REWRITE_TAC[REAL_ARITH `a * (&1 - b) + a * b = a`] THEN
    DISCH_THEN ACCEPT_TAC;
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [ASM_CASES_TAC `!z:real^N. z IN S ==> u(v + g z % (z - v)) = &0` THENL
       [EXISTS_TAC `v:real^N` THEN REWRITE_TAC[IN_INSERT] THEN
        SUBGOAL_THEN `sum S (\z:real^N. u(v + g z % (z - v)) * (&1 - g z)) = &0`
          (fun th -> ASM_REWRITE_TAC[th; REAL_ADD_RID]) THEN
        MATCH_MP_TAC SUM_EQ_0 THEN ASM_SIMP_TAC[REAL_MUL_LZERO];
        FIRST_X_ASSUM(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC o
          REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
        EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
        COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
        ASM_MESON_TAC[REAL_LT_IMP_NZ]];
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[IN_INSERT] THEN
      COND_CASES_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[REAL_ENTIRE; DE_MORGAN_THM] THEN
      ASM_MESON_TAC[REAL_LT_IMP_NZ]];
    UNDISCH_TAC `u v % v + vsum S (\x:real^N. u (v + g x % (x - v)) % (v + g x % (x - v))) =
                 vec 0` THEN
    SUBGOAL_THEN
     `vsum S (\x:real^N. u (v + g x % (x - v)) % (v + g x % (x - v))) =
      sum S (\z. u (v + g z % (z - v)) * (&1 - g z)) % v +
      vsum S (\z. (u (v + g z % (z - v)) * g z) % z)` SUBST1_TAC THENL
     [SIMP_TAC[GSYM VSUM_RMUL; GSYM VSUM_ADD; ASSUME `FINITE (S:real^N->bool)`] THEN
      MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC;
                  REAL_SUB_LDISTRIB; REAL_MUL_RID; VECTOR_SUB_RDISTRIB] THEN
      VECTOR_ARITH_TAC;
      VECTOR_ARITH_TAC]]);;

let MOI_FCL_LIFT_COMB = prove
 (`!S (v:real^N) g (l:real^N->real).
     FINITE S /\ sum S l = &1
     ==> vsum S (\z. l z % (v + g z % (z - v))) =
         (&1 - sum S (\z. l z * g z)) % v + vsum S (\z. (l z * g z) % z)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `vsum S (\z:real^N. l z % (v + g z % (z - v))) =
    vsum S (\z. (l z - l z * g z) % v) + vsum S (\z. (l z * g z) % z)`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[GSYM VSUM_ADD] THEN MATCH_MP_TAC VSUM_EQ THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC;
                VECTOR_SUB_RDISTRIB] THEN
    VECTOR_ARITH_TAC;
    REWRITE_TAC[VSUM_RMUL] THEN ASM_SIMP_TAC[SUM_SUB]]);;

(* A point of a lifted simplex lying in the cone over a face lies in the  *)
(* lifted face (uniqueness of barycentric coordinates in v INSERT S).      *)

let MOI_FCL_LIFT_FACE = prove
 (`!S Q (v:real^N) g x.
     FINITE S /\ ~affine_dependent (v INSERT S) /\ ~(v IN S) /\ Q SUBSET S /\
     (!z. z IN S ==> &0 < g z) /\
     x IN convex hull (IMAGE (\z. v + g z % (z - v)) S) /\
     x IN convex hull (v INSERT Q)
     ==> x IN convex hull (IMAGE (\z. v + g z % (z - v)) Q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (Q:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN Q)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `x IN convex hull (IMAGE (\z:real^N. v + g z % (z - v)) S)` THEN
  ASM_SIMP_TAC[CONVEX_HULL_FINITE_IMAGE_EXPLICIT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(x:real^N) IN convex hull (v INSERT Q)` THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `m (v:real^N) + sum Q m = &1 /\ m v % v + vsum Q (\p. m p % p) = x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `sum ((v:real^N) INSERT Q) m = &1` THEN
    UNDISCH_TAC `vsum ((v:real^N) INSERT Q) (\x. m x % x) = x` THEN
    ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(&1 - sum S (\z. l z * g z)) % v + vsum S (\z. (l z * g z) % z) = x:real^N`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^N->bool`; `v:real^N`; `g:real^N->real`; `l:real^N->real`]
      MOI_FCL_LIFT_COMB) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(v:real^N) INSERT S`;
                 `\p:real^N. if p = v then &1 - sum S (\z. l z * g z) else l p * g p`;
                 `\p:real^N. if p IN v INSERT Q then m p else &0`]
    MOI_FCL_AFF_COORDS_UNIQUE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FINITE_INSERT] THEN
    SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; ASSUME `FINITE (S:real^N->bool)`;
             ASSUME `~((v:real^N) IN S)`] THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `sum S (\p:real^N. if p = v then &1 - sum S (\z. l z * g z) else l p * g p) =
      sum S (\z. l z * g z) /\
      vsum S (\p:real^N. (if p = v then &1 - sum S (\z. l z * g z) else l p * g p) % p) =
      vsum S (\z. (l z * g z) % z)`
    (fun th -> REWRITE_TAC[th]) THENL
     [CONJ_TAC THENL [MATCH_MP_TAC SUM_EQ; MATCH_MP_TAC VSUM_EQ] THEN
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(z:real^N = v)` (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `sum S (\p:real^N. if p IN v INSERT Q then m p else &0) = sum Q m /\
      vsum S (\p:real^N. (if p IN v INSERT Q then m p else &0) % p) =
      vsum Q (\p. m p % p)`
    (fun th -> REWRITE_TAC[th; IN_INSERT]) THENL
     [CONJ_TAC THENL
       [TRANS_TAC EQ_TRANS `sum Q (\p:real^N. if p IN v INSERT Q then m p else &0)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC SUM_SUPERSET THEN
          ASM_REWRITE_TAC[IN_INSERT] THEN
          REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
          ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
          MATCH_MP_TAC SUM_EQ THEN SIMP_TAC[IN_INSERT]];
        TRANS_TAC EQ_TRANS
          `vsum Q (\p:real^N. (if p IN v INSERT Q then m p else &0) % p)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC VSUM_SUPERSET THEN
          ASM_REWRITE_TAC[IN_INSERT] THEN
          REPEAT STRIP_TAC THEN COND_CASES_TAC THEN
          ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN ASM_MESON_TAC[];
          MATCH_MP_TAC VSUM_EQ THEN SIMP_TAC[IN_INSERT]]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `!z:real^N. z IN S /\ ~(z IN Q) ==> l z = &0` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN
    SUBGOAL_THEN `~(z:real^N = v)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[REAL_ENTIRE] THEN ASM_MESON_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_FINITE_IMAGE_EXPLICIT; IN_ELIM_THM] THEN
  EXISTS_TAC `l:real^N->real` THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET];
    TRANS_TAC EQ_TRANS `sum S (l:real^N->real)` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC SUM_SUPERSET THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[]];
    TRANS_TAC EQ_TRANS `vsum S (\a:real^N. l a % (v + g a % (a - v)))` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
      ASM_SIMP_TAC[VECTOR_MUL_LZERO];
      ASM_REWRITE_TAC[]]]);;

(* The vertex sets of K: their points are vertices of K.                     *)

let MOI_FCL_VERTEX_SETS_VERTEX = prove
 (`!(K:(real^N->bool)->bool) S z.
     simplicial_complex K /\ S IN moi_real_vertex_sets K /\ z IN S
     ==> {z} IN K`,
  REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN REPEAT STRIP_TAC THEN
  UNDISCH_TAC `simplicial_complex (K:(real^N->bool)->bool)` THEN
  REWRITE_TAC[simplicial_complex] THEN
  DISCH_THEN(MATCH_MP_TAC o el 2 o CONJUNCTS) THEN
  EXISTS_TAC `convex hull S:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(z:real^N) extreme_point_of convex hull S` MP_TAC THENL
   [ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT];
    REWRITE_TAC[FACE_OF_SING]]);;

let MOI_FCL_SING_VERTEX_SET = prove
 (`!(K:(real^N->bool)->bool) z.
     {z} IN K ==> {z} IN moi_real_vertex_sets K`,
  REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS; CONVEX_HULL_SING; AFFINE_INDEPENDENT_1;
              NOT_INSERT_EMPTY]);;

let MOI_FCL_LIFT_IN_CONE = prove
 (`!S (v:real^N) g.
     (!z. z IN S ==> &0 <= g z /\ g z <= &1)
     ==> convex hull (IMAGE (\z. v + g z % (z - v)) S) SUBSET
         convex hull (v INSERT S)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN
  REWRITE_TAC[CONVEX_CONVEX_HULL; SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `v + (g:real^N->real) z % (z - v) = (&1 - g z) % v + g z % z`
  SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[convex] CONVEX_CONVEX_HULL) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[IN_INSERT];
    ASM_SIMP_TAC[REAL_SUB_LE];
    ASM_SIMP_TAC[];
    REAL_ARITH_TAC]);;

let MOI_FCL_LIFT_REALIZES = prove
 (`!(K:(real^N->bool)->bool) v g.
     simplicial_complex K /\ ~(v IN UNIONS K) /\
     (!x y. x IN UNIONS K /\ y IN UNIONS K /\ y IN segment[v,x] ==> y = x) /\
     (!z. {z} IN K ==> &0 < g z /\ g z <= &1)
     ==> abstract_realizes (\z. v + g z % (z - v)) (moi_real_vertex_sets K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!S. S IN moi_real_vertex_sets K
        ==> FINITE S /\ ~affine_dependent ((v:real^N) INSERT S) /\ ~(v IN S) /\
            (!z. z IN S ==> &0 < g z /\ g z <= &1) /\
            S SUBSET UNIONS K /\ convex hull S IN K /\ ~affine_dependent S`
  (LABEL_TAC "vs") THENL
   [X_GEN_TAC `S:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `!z:real^N. z IN S ==> {z} IN K` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FCL_VERTEX_SETS_VERTEX]; ALL_TAC] THEN
    SUBGOAL_THEN `(S:real^N->bool) SUBSET UNIONS K` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `z:real^N` THEN
      DISCH_TAC THEN EXISTS_TAC `{z:real^N}` THEN ASM_SIMP_TAC[IN_SING];
      ALL_TAC] THEN
    UNDISCH_TAC `(S:real^N->bool) IN moi_real_vertex_sets K` THEN
    REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~affine_dependent ((v:real^N) INSERT S)` ASSUME_TAC THENL
     [MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[GSYM AFFINE_HULL_CONVEX_HULL] THEN
      MATCH_MP_TAC MOI_CON_SC_NOT_IN_AFFINE_HULL THEN
      EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((v:real^N) IN S)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[abstract_realizes] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `S:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "vs" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(S:real^N->bool) IN moi_real_vertex_sets K`)) THEN
    MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `(v:real^N) INSERT IMAGE (\z. v + g z % (z - v)) S` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
    MATCH_MP_TAC MOI_FCL_LIFT_AFF_INDEP THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `S1:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `S2:real^N->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC)) THEN
    USE_THEN "vs" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(S1:real^N->bool) IN moi_real_vertex_sets K`)) THEN
    USE_THEN "vs" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(S2:real^N->bool) IN moi_real_vertex_sets K`)) THEN
    MP_TAC(ISPECL [`UNIONS K:real^N->bool`; `v:real^N`; `x:real^N`; `y:real^N`;
                   `(g:real^N->real) x`; `(g:real^N->real) y`] MOI_CON_RAY_UNIQUE) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < (g:real^N->real) x` (fun th -> MESON_TAC[th; REAL_LT_IMP_NZ]) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`S:real^N->bool`; `T1:real^N->bool`] THEN STRIP_TAC THEN
    USE_THEN "vs" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(S:real^N->bool) IN moi_real_vertex_sets K`)) THEN
    USE_THEN "vs" (STRIP_ASSUME_TAC o C MATCH_MP
      (ASSUME `(T1:real^N->bool) IN moi_real_vertex_sets K`)) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN
      SET_TAC[]] THEN
    REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FCL_LIFT_FACE THEN
    EXISTS_TAC `S:real^N->bool` THEN ASM_SIMP_TAC[INTER_SUBSET] THEN
    SUBGOAL_THEN `convex hull S INTER convex hull T1 = convex hull (S INTER T1:real^N->bool)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL THEN
      EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`UNIONS K:real^N->bool`; `v:real^N`; `convex hull S:real^N->bool`;
                   `convex hull T1:real^N->bool`] MOI_CON_CONE_INTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM HULL_INSERT] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_INTER] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`S:real^N->bool`; `v:real^N`; `g:real^N->real`]
        MOI_FCL_LIFT_IN_CONE);
      MP_TAC(ISPECL [`T1:real^N->bool`; `v:real^N`; `g:real^N->real`]
        MOI_FCL_LIFT_IN_CONE)] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN ASM SET_TAC[]]);;

(* The section lemma: over a finite simplicial complex K seen from v with  *)
(* unique rays, the simplexwise affine map with vertex values               *)
(* v + g z % (z - v), 0 < g z <= 1, is a PL homeomorphism of UNIONS K onto *)
(* the union of the lifted simplices.                                      *)

let MOI_FCL_SECTION = prove
 (`!(K:(real^N->bool)->bool) v g.
     simplicial_complex K /\ ~(v IN UNIONS K) /\
     (!x y. x IN UNIONS K /\ y IN UNIONS K /\ y IN segment[v,x] ==> y = x) /\
     (!z. {z} IN K ==> &0 < g z /\ g z <= &1)
     ==> ?h h'. pl_homeomorphism
                  (UNIONS K,
                   UNIONS {convex hull (IMAGE (\z. v + g z % (z - v)) S) |
                           S IN moi_real_vertex_sets K}) (h,h') /\
                (!z. {z} IN K ==> h z = v + g z % (z - v)) /\
                (!S. S IN moi_real_vertex_sets K
                     ==> IMAGE h (convex hull S) =
                         convex hull (IMAGE (\z. v + g z % (z - v)) S))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^N. x`; `\z:real^N. v + g z % (z - v)`;
                 `moi_real_vertex_sets (K:(real^N->bool)->bool)`]
    ABSTRACT_REALIZATIONS_PL_HOMEOMORPHIC) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN `FINITE (K:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_REAL_VERTEX_SETS_FINITE; MOI_REAL_VERTEX_SETS_ABSTRACT_COMPLEX;
                 MOI_REAL_VERTEX_SETS_REALIZES] THEN
    MATCH_MP_TAC MOI_FCL_LIFT_REALIZES THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_REAL_VERTEX_SETS_UNIONS; IMAGE_ID] THEN
  REWRITE_TAC[abstract_realization; UNIONS_INSERT; UNION_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `h':real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `h':real^N->real^N`] THEN
  ASM_SIMP_TAC[] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `UNIONS (moi_real_vertex_sets (K:(real^N->bool)->bool))`))
        (concl th))) THEN
  REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{z:real^N}` THEN
  ASM_SIMP_TAC[MOI_FCL_SING_VERTEX_SET; IN_SING]);;

(* ========================================================================= *)
(* The labelled cell assembly with targets in real^M: the MOI_CEL_ON_ lemmas *)
(* and MOISE_CELL_ASSEMBLY_ON of pc_moi_cells.ml (whose targets are in       *)
(* real^3), with the target type generalised.                                *)
(* ========================================================================= *)

let MOI_FCL_ON_BOUNDARY_PLH = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (b:L->real^M->bool) (d:L->num)
    (face:L->L->bool) (f:real^N->real^M) l.
     (!l. l IN lab ==> face l l) /\
     (!l m. l IN lab /\ face l m ==> m IN lab /\ (m = l \/ d m < d l)) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (a l)
                         (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. l IN lab /\ m IN lab
            ==> b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!x. x IN UNIONS {a l | l IN lab}
          ==> ?w. open w /\ x IN w /\
                  FINITE {l | l IN lab /\ ~(a l INTER w = {})}) /\
     (!m. m IN lab /\ d m < d l
          ==> pl_map_on (a m) f /\ IMAGE f (a m) = b m /\
              (!x y. x IN a m /\ y IN a m /\ f x = f y ==> x = y)) /\
     l IN lab
     ==> ?g. pl_homeomorphism (UNIONS {a m | m | face l m /\ ~(m = l)},
                               UNIONS {b m | m | face l m /\ ~(m = l)})
                              (f,g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!m:L. (face:L->L->bool) l m /\ ~(m = l)
                      ==> m IN lab /\ (d:L->num) m < d l`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!m:L. m IN lab ==> closed ((a:L->real^N->bool) m)`
  ASSUME_TAC THENL
   [X_GEN_TAC `m:L` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `pl_cell_with_boundary ((d:L->num) m) ((a:L->real^N->bool) m)
        (UNIONS {a n | n | (face:L->L->bool) m n /\ ~(n = m)})`
    (fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_CEL_CELL_COMPACT th)) THENL
     [ASM_MESON_TAC[]; ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary ((d:L->num) l) ((a:L->real^N->bool) l)
      (UNIONS {a m | m | (face:L->L->bool) l m /\ ~(m = l)})`
  (fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_CEL_CELL_COMPACT th)) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on (UNIONS {(a:L->real^N->bool) m | m |
                       (face:L->L->bool) l m /\ ~(m = l)})
              (f:real^N->real^M)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CEL_ON_PL_MAP_ON_UNIONS_LF_INDEXED THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS {(a:L->real^N->bool) l | l IN lab}`
    (fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th)) THENL
     [UNDISCH_TAC
       `(x:real^N) IN UNIONS {(a:L->real^N->bool) m | m |
                              (face:L->L->bool) l m /\ ~(m = l)}` THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{m:L | m IN lab /\ ~((a:L->real^N->bool) m INTER w = {})}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^N->real^M)
      (UNIONS {(a:L->real^N->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}) =
    UNIONS {(b:L->real^M->bool) m | m | face l m /\ ~(m = l)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CEL_IMAGE_UNIONS THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y. x IN UNIONS {(a:L->real^N->bool) m | m |
                       (face:L->L->bool) l m /\ ~(m = l)} /\
          y IN UNIONS {a m | m | face l m /\ ~(m = l)} /\
          (f:real^N->real^M) x = f y
          ==> x = y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CEL_INJ_SUBSET THEN
    EXISTS_TAC
     `UNIONS {(a:L->real^N->bool) m | m IN lab /\ (d:L->num) m < d l}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^M->bool`;
                   `face:L->L->bool`; `f:real^N->real^M`;
                   `\m:L. (d:L->num) m < d l`]
      MOI_CEL_ON_INJECTIVE_UNIONS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[LT_TRANS];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`UNIONS {(a:L->real^N->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}`;
    `f:real^N->real^M`;
    `UNIONS {(b:L->real^M->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}`]
   HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^N` THEN
  DISCH_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 5. The extension over one cell of lab.                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_FCL_ON_EXTEND_ONE = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (b:L->real^M->bool) (d:L->num)
    (face:L->L->bool) (f:real^N->real^M) l.
     (!l. l IN lab ==> face l l) /\
     (!l m. l IN lab /\ face l m ==> m IN lab /\ (m = l \/ d m < d l)) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (a l)
                         (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (b l)
                         (UNIONS {b m | m | face l m /\ ~(m = l)})) /\
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. l IN lab /\ m IN lab
            ==> b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!x. x IN UNIONS {a l | l IN lab}
          ==> ?w. open w /\ x IN w /\
                  FINITE {l | l IN lab /\ ~(a l INTER w = {})}) /\
     (!m. m IN lab /\ d m < d l
          ==> pl_map_on (a m) f /\ IMAGE f (a m) = b m /\
              (!x y. x IN a m /\ y IN a m /\ f x = f y ==> x = y)) /\
     l IN lab
     ==> ?g. pl_map_on (a l) g /\ IMAGE g (a l) = b l /\
             (!x y. x IN a l /\ y IN a l /\ g x = g y ==> x = y) /\
             (!n x. face l n /\ ~(n = l) /\ x IN a n ==> g x = f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^M->bool`;
                 `d:L->num`; `face:L->L->bool`; `f:real^N->real^M`; `l:L`]
    MOI_FCL_ON_BOUNDARY_PLH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `g0:real^M->real^N`) THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary ((d:L->num) l) ((a:L->real^N->bool) l)
      (UNIONS {a m | m | (face:L->L->bool) l m /\ ~(m = l)}) /\
    pl_cell_with_boundary (d l) ((b:L->real^M->bool) l)
      (UNIONS {b m | m | face l m /\ ~(m = l)})`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`(d:L->num) l`; `(a:L->real^N->bool) l`;
    `UNIONS {(a:L->real^N->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}`;
    `(b:L->real^M->bool) l`;
    `UNIONS {(b:L->real^M->bool) m | m | (face:L->L->bool) l m /\ ~(m = l)}`;
    `f:real^N->real^M`; `g0:real^M->real^N`] MOI_CEL_CELL_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` (X_CHOOSE_THEN
    `g':real^M->real^N` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `g:real^N->real^M` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism] o
    check (fun th -> rand(concl th) = `(g:real^N->real^M,g':real^M->real^N)`))
  THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 6. Gluing the extensions over the cells of lab of dimension k.           *)
(* ------------------------------------------------------------------------- *)

let MOI_FCL_ON_GLUE_STEP = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (b:L->real^M->bool) (d:L->num)
    (face:L->L->bool) k (f:real^N->real^M) (ff:L->real^N->real^M).
     (!l m. l IN lab /\ face l m ==> m IN lab /\ (m = l \/ d m < d l)) /\
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l. l IN lab /\ d l < k
          ==> pl_map_on (a l) f /\ IMAGE f (a l) = b l /\
              (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y)) /\
     (!l. l IN lab /\ d l = k
          ==> pl_map_on (a l) (ff l) /\ IMAGE (ff l) (a l) = b l /\
              (!x y. x IN a l /\ y IN a l /\ ff l x = ff l y ==> x = y) /\
              (!n x. face l n /\ ~(n = l) /\ x IN a n ==> ff l x = f x))
     ==> ?g:real^N->real^M.
           !l. l IN lab /\ d l < SUC k
               ==> pl_map_on (a l) g /\ IMAGE g (a l) = b l /\
                   (!x y. x IN a l /\ y IN a l /\ g x = g y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `face:L->L->bool`]
    MOI_CEL_ON_INTER_FACES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!l m x. l IN lab /\ m IN lab /\ (d:L->num) l = k /\ d m < k /\
            (x:real^N) IN (a:L->real^N->bool) l /\ x IN a m
            ==> (ff:L->real^N->real^M) l x = (f:real^N->real^M) x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `?n:L. (face:L->L->bool) l n /\ face m n /\
            (x:real^N) IN (a:L->real^N->bool) n`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(n:L = l)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(l:L) = m \/ (d:L->num) l < d m` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      STRIP_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!l l' x. l IN lab /\ l' IN lab /\ (d:L->num) l = k /\ d l' = k /\
             (x:real^N) IN (a:L->real^N->bool) l /\ x IN a l'
             ==> (ff:L->real^N->real^M) l x = ff l' x`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_CASES_TAC `l':L = l` THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?n:L. (face:L->L->bool) l n /\ face l' n /\
            (x:real^N) IN (a:L->real^N->bool) n`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(n:L = l) /\ ~(n = l')` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
       [SUBGOAL_THEN `(d:L->num) l < d l'` MP_TAC THENL
         [ASM_MESON_TAC[]; ASM_ARITH_TAC];
        SUBGOAL_THEN `(d:L->num) l' < d l` MP_TAC THENL
         [ASM_MESON_TAC[]; ASM_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?lb:real^N->L.
      !x. (?l. l IN lab /\ (d:L->num) l = k /\ x IN (a:L->real^N->bool) l)
          ==> lb x IN lab /\ d (lb x) = k /\ x IN a (lb x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?g:real^N->real^M.
      (!m x. m IN lab /\ (d:L->num) m < k /\ x IN (a:L->real^N->bool) m
             ==> g x = (f:real^N->real^M) x) /\
      (!l x. l IN lab /\ d l = k /\ x IN a l
             ==> g x = (ff:L->real^N->real^M) l x)`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC
     `\x:real^N. if ?l:L. l IN lab /\ (d:L->num) l = k /\
                          x IN (a:L->real^N->bool) l
                 then (ff:L->real^N->real^M) ((lb:real^N->L) x) x
                 else (f:real^N->real^M) x` THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT STRIP_TAC THEN
    COND_CASES_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `g:real^N->real^M` THEN X_GEN_TAC `l:L` THEN
  REWRITE_TAC[LT] THEN STRIP_TAC THEN MATCH_MP_TAC MOI_CEL_TRANSFER THENL
   [EXISTS_TAC `(ff:L->real^N->real^M) l`;
    EXISTS_TAC `f:real^N->real^M`] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 7. The induction over the skeleta of lab.                                *)
(* ------------------------------------------------------------------------- *)

let MOI_FCL_ON_STEP = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (b:L->real^M->bool) (d:L->num)
    (face:L->L->bool) k.
     (!l. l IN lab ==> face l l) /\
     (!l m. l IN lab /\ face l m ==> m IN lab /\ (m = l \/ d m < d l)) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (a l)
                         (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (b l)
                         (UNIONS {b m | m | face l m /\ ~(m = l)})) /\
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. l IN lab /\ m IN lab
            ==> b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!x. x IN UNIONS {a l | l IN lab}
          ==> ?w. open w /\ x IN w /\
                  FINITE {l | l IN lab /\ ~(a l INTER w = {})})
     ==> (?f:real^N->real^M.
            !l. l IN lab /\ d l < k
                ==> pl_map_on (a l) f /\ IMAGE f (a l) = b l /\
                    (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y))
         ==> (?f:real^N->real^M.
                !l. l IN lab /\ d l < SUC k
                    ==> pl_map_on (a l) f /\ IMAGE f (a l) = b l /\
                        (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  DISCH_THEN(X_CHOOSE_TAC `f:real^N->real^M`) THEN
  SUBGOAL_THEN
   `!l. ?g:real^N->real^M.
      l IN lab /\ (d:L->num) l = k
      ==> pl_map_on ((a:L->real^N->bool) l) g /\ IMAGE g (a l) = b l /\
          (!x y. x IN a l /\ y IN a l /\ g x = g y ==> x = y) /\
          (!n x. (face:L->L->bool) l n /\ ~(n = l) /\ x IN a n
                 ==> g x = (f:real^N->real^M) x)`
  MP_TAC THENL
   [X_GEN_TAC `l:L` THEN
    ASM_CASES_TAC `(l:L) IN lab` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(d:L->num) l = k` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^M->bool`;
                   `d:L->num`; `face:L->L->bool`; `f:real^N->real^M`; `l:L`]
      MOI_FCL_ON_EXTEND_ONE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `ff:L->real^N->real^M`) THEN
  MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^M->bool`;
                 `d:L->num`; `face:L->L->bool`; `k:num`; `f:real^N->real^M`;
                 `ff:L->real^N->real^M`] MOI_FCL_ON_GLUE_STEP) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FCL_ON_ALL_SKELETA = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (b:L->real^M->bool) (d:L->num)
    (face:L->L->bool).
     (!l. l IN lab ==> face l l) /\
     (!l m. l IN lab /\ face l m ==> m IN lab /\ (m = l \/ d m < d l)) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (a l)
                         (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
     (!l. l IN lab ==> pl_cell_with_boundary (d l) (b l)
                         (UNIONS {b m | m | face l m /\ ~(m = l)})) /\
     (!l m. l IN lab /\ m IN lab
            ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
     (!l m. l IN lab /\ m IN lab
            ==> b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
     (!x. x IN UNIONS {a l | l IN lab}
          ==> ?w. open w /\ x IN w /\
                  FINITE {l | l IN lab /\ ~(a l INTER w = {})})
     ==> !k. ?f:real^N->real^M.
               !l. l IN lab /\ d l < k
                   ==> pl_map_on (a l) f /\ IMAGE f (a l) = b l /\
                       (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[LT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^M->bool`;
                 `d:L->num`; `face:L->L->bool`; `k:num`] MOI_FCL_ON_STEP) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 8. The assembly in set form.                                              *)
(* ------------------------------------------------------------------------- *)

(* The assembly in set form (MOISE_CELL_ASSEMBLY_ON with real^M targets).   *)

let MOI_FCL_ASSEMBLY = prove
 (`!(lab:L->bool) (a:L->real^N->bool) (b:L->real^M->bool) (d:L->num)
    (face:L->L->bool).
        (!l. l IN lab ==> d l <= 3 /\ face l l) /\
        (!l m. l IN lab /\ face l m ==> m IN lab /\ (m = l \/ d m < d l)) /\
        (!l. l IN lab ==> pl_cell_with_boundary (d l) (a l)
                            (UNIONS {a m | m | face l m /\ ~(m = l)})) /\
        (!l. l IN lab ==> pl_cell_with_boundary (d l) (b l)
                            (UNIONS {b m | m | face l m /\ ~(m = l)})) /\
        (!l m. l IN lab /\ m IN lab
               ==> a l INTER a m = UNIONS {a n | n | face l n /\ face m n}) /\
        (!l m. l IN lab /\ m IN lab
               ==> b l INTER b m = UNIONS {b n | n | face l n /\ face m n}) /\
        (!x. x IN UNIONS {a l | l IN lab}
             ==> ?w. open w /\ x IN w /\
                     FINITE {l | l IN lab /\ ~(a l INTER w = {})}) /\
        (!y. y IN UNIONS {b l | l IN lab}
             ==> ?w. open w /\ y IN w /\
                     FINITE {l | l IN lab /\ ~(b l INTER w = {})})
        ==> ?f. pl_map_on (UNIONS {a l | l IN lab}) f /\
                (!x y. x IN UNIONS {a l | l IN lab} /\
                       y IN UNIONS {a l | l IN lab} /\ f x = f y ==> x = y) /\
                (!l. l IN lab ==> IMAGE f (a l) = b l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!l:L. l IN lab ==> (face:L->L->bool) l l` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^M->bool`;
                 `d:L->num`; `face:L->L->bool`] MOI_FCL_ON_ALL_SKELETA) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `4`) THEN
  DISCH_THEN(X_CHOOSE_TAC `f:real^N->real^M`) THEN
  SUBGOAL_THEN
   `!l. l IN lab
        ==> pl_map_on ((a:L->real^N->bool) l) (f:real^N->real^M) /\
            IMAGE f (a l) = (b:L->real^M->bool) l /\
            (!x y. x IN a l /\ y IN a l /\ f x = f y ==> x = y)`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:L` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[ARITH_RULE `n <= 3 ==> n < 4`];
    ALL_TAC] THEN
  SUBGOAL_THEN `!l:L. l IN lab ==> closed ((a:L->real^N->bool) l)`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:L` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `pl_cell_with_boundary ((d:L->num) l) ((a:L->real^N->bool) l)
        (UNIONS {a m | m | (face:L->L->bool) l m /\ ~(m = l)})`
    (fun th -> STRIP_ASSUME_TAC(MATCH_MP MOI_CEL_CELL_COMPACT th)) THENL
     [ASM_MESON_TAC[]; ASM_SIMP_TAC[COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  EXISTS_TAC `f:real^N->real^M` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CEL_ON_PL_MAP_ON_UNIONS_LF_INDEXED THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; FIRST_ASSUM ACCEPT_TAC];
    MP_TAC(ISPECL [`lab:L->bool`; `a:L->real^N->bool`; `b:L->real^M->bool`;
                   `face:L->L->bool`; `f:real^N->real^M`; `\l:L. T`]
      MOI_CEL_ON_INJECTIVE_UNIONS) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;


(* ========================================================================= *)
(* Products with polytopes.  PL maps and PL homeomorphisms times the         *)
(* identity of a polytope, transfer of PL cells between spaces along PL      *)
(* homeomorphisms, and prisms over PL cells of dimension at most 2.          *)
(* ========================================================================= *)

let MOI_FCL_LP_PCROSS = prove
 (`!(s:real^M->bool) (t:real^P->bool).
     locally_polyhedral s /\ polytope t ==> locally_polyhedral (s PCROSS t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_polyhedral] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS] THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `y:real^P`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool` (X_CHOOSE_THEN `u:real^M->bool`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `IMAGE (\k:real^M->bool. k PCROSS (t:real^P->bool)) c` THEN
  EXISTS_TAC `(u:real^M->bool) PCROSS (:real^P)` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; OPEN_PCROSS; OPEN_UNIV; PASTECART_IN_PCROSS; IN_UNIV;
               FORALL_IN_IMAGE] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_PASTECART; IN_INTER; PASTECART_IN_PCROSS; IN_UNIV;
                IN_UNIONS; EXISTS_IN_IMAGE] THEN
    MAP_EVERY X_GEN_TAC [`a:real^M`; `b:real^P`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^M) IN UNIONS c` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `k:real^M->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS];
    X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_PCROSS THEN ASM_SIMP_TAC[];
      MATCH_MP_TAC PCROSS_MONO THEN ASM_SIMP_TAC[SUBSET_REFL]]]);;

let MOI_FCL_PL_PCROSS_ID = prove
 (`!(s:real^M->bool) (f:real^M->real^N) (t:real^P->bool).
     pl_map_on s f /\ polytope t
     ==> pl_map_on (s PCROSS t) (\z. pastecart (f (fstcart z)) (sndcart z))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `locally_polyhedral ((s:real^M->bool) PCROSS (t:real^P->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FCL_LP_PCROSS THEN
    ASM_MESON_TAC[PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL];
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_PASTECART THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `(\z:real^(M,P)finite_sum. (f:real^M->real^N) (fstcart z)) = f o fstcart`
    SUBST1_TAC THENL [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `s:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `\z:real^(M,P)finite_sum. fstcart z + vec 0` THEN
      CONJ_TAC THENL
       [REWRITE_TAC[VECTOR_ADD_RID];
        MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[LINEAR_FSTCART]];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS; FSTCART_PASTECART] THEN
      SIMP_TAC[]];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^(M,P)finite_sum. sndcart z + vec 0` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_RID];
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[LINEAR_SNDCART]]]);;

let MOI_FCL_PLH_PCROSS_ID = prove
 (`!(s:real^M->bool) (s':real^N->bool) f g (t:real^P->bool).
     pl_homeomorphism (s,s') (f,g) /\ polytope t
     ==> pl_homeomorphism (s PCROSS t,s' PCROSS t)
           ((\z. pastecart (f (fstcart z)) (sndcart z)),
            (\z. pastecart (g (fstcart z)) (sndcart z)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FCL_PL_PCROSS_ID] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
      ASM_SIMP_TAC[MOI_FCL_PL_PCROSS_ID] THEN NO_TAC) THEN
  TRY(REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART] THEN
      ASM_SIMP_TAC[] THEN NO_TAC) THEN
  REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PASTECART; EXISTS_PASTECART;
              PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
              PASTECART_INJ] THEN
  ASM SET_TAC[]);;

(* PL cells move along PL homeomorphisms, also into other spaces.           *)

let MOI_FCL_CELL_TRANSFER = prove
 (`!n (X:real^M->bool) bX (Y:real^P->bool) h h'.
     pl_cell_with_boundary n X bX /\ pl_homeomorphism (X,Y) (h,h') /\
     n <= dimindex(:P)
     ==> pl_cell_with_boundary n Y (IMAGE h bX)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `f:real^M->real^M`
     (X_CHOOSE_THEN `g:real^M->real^M` STRIP_ASSUME_TAC))) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `&n:int` (INST_TYPE [`:P`,`:N`] CHOOSE_SIMPLEX)) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[INT_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_TAC `k':real^P->bool`)] THEN
  MP_TAC(ISPECL [`k':real^P->bool`; `k:real^M->bool`; `&n:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^P->real^M` (X_CHOOSE_THEN `q:real^M->real^P`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`k':real^P->bool`; `(h:real^M->real^P) o (f:real^M->real^M) o (p:real^P->real^M)`;
    `((q:real^M->real^P) o (g:real^M->real^M)) o (h':real^P->real^M)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `X:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^M->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  UNDISCH_TAC `pl_homeomorphism (relative_frontier k',relative_frontier k)
                 (p:real^P->real^M,q)` THEN
  SIMP_TAC[pl_homeomorphism; homeomorphism]);;

let MOI_FCL_UNIT_INTERVAL = prove
 (`interior(interval[vec 0:real^1,vec 1]) = interval(vec 0,vec 1) /\
   ~(interval(vec 0:real^1,vec 1) = {}) /\
   relative_interior(interval[vec 0:real^1,vec 1]) = interval(vec 0,vec 1) /\
   aff_dim(interval[vec 0:real^1,vec 1]) = &1 /\
   polytope(interval[vec 0:real^1,vec 1]) /\
   closed(interval[vec 0:real^1,vec 1]) /\
   ~(interval[vec 0:real^1,vec 1] = {})`,
  SUBGOAL_THEN `~(interval(vec 0:real^1,vec 1) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; POLYTOPE_INTERVAL; CLOSED_INTERVAL] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM INTERIOR_CLOSED_INTERVAL] THEN
    MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR THEN
    ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPEC `interval[vec 0:real^1,vec 1]` AFF_DIM_NONEMPTY_INTERIOR) THEN
    ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; DIMINDEX_1];
    REWRITE_TAC[INTERVAL_EQ_EMPTY_1; DROP_VEC] THEN REAL_ARITH_TAC]);;

let MOI_FCL_RF_PRISM = prove
 (`!k:real^N->bool.
     convex k /\ closed k /\ ~(k = {})
     ==> relative_frontier (k PCROSS interval[vec 0:real^1,vec 1]) =
         (k PCROSS {vec 0,vec 1}) UNION
         (relative_frontier k PCROSS interval[vec 0,vec 1])`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[relative_frontier; CLOSURE_PCROSS; RELATIVE_INTERIOR_PCROSS] THEN
  ASM_SIMP_TAC[CLOSURE_CLOSED; CLOSED_INTERVAL; MOI_FCL_UNIT_INTERVAL] THEN
  REWRITE_TAC[EXTENSION; FORALL_PASTECART; IN_DIFF; IN_UNION; PASTECART_IN_PCROSS;
              IN_INSERT; NOT_IN_EMPTY; IN_INTERVAL_1; GSYM DROP_EQ; DROP_VEC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real^1`] THEN
  ASM_CASES_TAC `(x:real^N) IN relative_interior k` THEN
  ASM_CASES_TAC `(x:real^N) IN k` THEN ASM_REWRITE_TAC[] THEN
  TRY REAL_ARITH_TAC THEN
  ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]);;

let MOI_FCL_IMAGE_PCROSS_ID = prove
 (`!(f:real^M->real^N) s (t:real^P->bool).
     IMAGE (\z. pastecart (f (fstcart z)) (sndcart z)) (s PCROSS t) =
     (IMAGE f s) PCROSS t`,
  REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PASTECART; EXISTS_PASTECART;
              PASTECART_IN_PCROSS; FSTCART_PASTECART; SNDCART_PASTECART;
              PASTECART_INJ] THEN
  MESON_TAC[]);;

(* Prisms over PL cells of dimension at most 2.                             *)

let MOI_FCL_PRISM_CELL = prove
 (`!n (X:real^N->bool) bX.
     pl_cell_with_boundary n X bX /\ n <= 2
     ==> pl_cell_with_boundary (n + 1) (X PCROSS interval[vec 0:real^1,vec 1])
           ((X PCROSS {vec 0,vec 1}) UNION (bX PCROSS interval[vec 0,vec 1]))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary])
    ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ closed k /\ ~(k = {}) /\ polytope k /\
                aff_dim k = &n` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_POLYTOPE;
                  AFF_DIM_SIMPLEX; SIMPLEX_EMPTY; INT_ARITH `~(&n:int = -- &1)`];
    ALL_TAC] THEN
  ABBREV_TAC `P = (k:real^N->bool) PCROSS interval[vec 0:real^1,vec 1]` THEN
  SUBGOAL_THEN `polytope (P:real^(N,1)finite_sum->bool) /\ aff_dim P = &(n + 1)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN
    ASM_SIMP_TAC[POLYTOPE_PCROSS; MOI_FCL_UNIT_INTERVAL; AFF_DIM_PCROSS] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_ADD];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary (n + 1) (P:real^(N,1)finite_sum->bool)
                  (relative_frontier P)` ASSUME_TAC THENL
   [UNDISCH_TAC `n <= 2` THEN
    REWRITE_TAC[ARITH_RULE `n <= 2 <=> n = 0 \/ n = 1 \/ n = 2`] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN CONV_TAC NUM_REDUCE_CONV THENL
     [MATCH_MP_TAC MOI_S4A_POLY_CELL_1; MATCH_MP_TAC MOI_S4A_POLY_CELL_2;
      MATCH_MP_TAC MOI_S4A_POLY_CELL_3] THEN
    RULE_ASSUM_TAC(CONV_RULE NUM_REDUCE_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n + 1`; `P:real^(N,1)finite_sum->bool`;
                 `relative_frontier P:real^(N,1)finite_sum->bool`;
                 `(X:real^N->bool) PCROSS interval[vec 0:real^1,vec 1]`;
                 `\z:real^(N,1)finite_sum.
                    pastecart ((f:real^N->real^N) (fstcart z)) (sndcart z)`;
                 `\z:real^(N,1)finite_sum.
                    pastecart ((g:real^N->real^N) (fstcart z)) (sndcart z)`]
    MOI_FCL_CELL_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "P" THEN MATCH_MP_TAC MOI_FCL_PLH_PCROSS_ID THEN
      ASM_REWRITE_TAC[MOI_FCL_UNIT_INTERVAL];
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1; LE_ADD_RCANCEL] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
      UNDISCH_TAC `aff_dim (k:real^N->bool) = &n` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[AFF_DIM_LE_UNIV]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  EXPAND_TAC "P" THEN ASM_SIMP_TAC[MOI_FCL_RF_PRISM] THEN
  REWRITE_TAC[IMAGE_UNION; MOI_FCL_IMAGE_PCROSS_ID] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  ASM_REWRITE_TAC[]);;

(* Slices of PL cells.                                                      *)

let MOI_FCL_SLICE_CELL = prove
 (`!n (X:real^N->bool) bX (a:real^1).
     pl_cell_with_boundary n X bX
     ==> pl_cell_with_boundary n (X PCROSS {a}) (bX PCROSS {a})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary]) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `locally_polyhedral (X:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL THEN
    EXISTS_TAC `g:real^N->real^N` THEN ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (k:real^N->bool) = &n` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (X:real^N->bool) (\x. pastecart x (a:real^1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^N. (\x:real^N. pastecart x (vec 0:real^1)) x +
                           pastecart (vec 0) (a:real^1)` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[PASTECART_ADD; VECTOR_ADD_LID; VECTOR_ADD_RID];
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[linear; PASTECART_ADD; GSYM PASTECART_CMUL; VECTOR_ADD_LID;
                  VECTOR_MUL_RZERO]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on ((X:real^N->bool) PCROSS {a:real^1}) fstcart`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\z:real^(N,1)finite_sum. fstcart z + vec 0` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_RID];
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN REWRITE_TAC[LINEAR_FSTCART] THEN
      MATCH_MP_TAC MOI_FCL_LP_PCROSS THEN ASM_REWRITE_TAC[POLYTOPE_SING]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `X:real^N->bool`; `bX:real^N->bool`;
                 `(X:real^N->bool) PCROSS {a:real^1}`;
                 `\x:real^N. pastecart x (a:real^1)`;
                 `fstcart:real^(N,1)finite_sum->real^N`] MOI_FCL_CELL_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[DIMINDEX_FINITE_SUM; DIMINDEX_1] THEN
      REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_ADD] THEN
      MATCH_MP_TAC(INT_ARITH `x <= y ==> x <= y + &1:int`) THEN
      UNDISCH_TAC `aff_dim (k:real^N->bool) = &n` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[AFF_DIM_LE_UNIV]] THEN
    ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FSTCART_PASTECART];
      REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                  PASTECART_INJ; IN_SING] THEN MESON_TAC[];
      MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_PCROSS; FSTCART_PASTECART; IN_SING] THEN SIMP_TAC[];
      REWRITE_TAC[EXTENSION; IN_IMAGE; EXISTS_PASTECART; PASTECART_IN_PCROSS;
                  FSTCART_PASTECART; IN_SING] THEN MESON_TAC[];
      SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_FSTCART]];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                PASTECART_INJ; IN_SING] THEN MESON_TAC[]]);;

(* ========================================================================= *)
(* Dual cells in the first barycentric subdivision.  For a simplex s of c,   *)
(* moi_fcl_dual c s is the union of the derived simplices spanned by the     *)
(* barycentres of chains of simplices containing s; moi_fcl_ldual c s uses   *)
(* chains of simplices properly containing s (the link of the barycentre of  *)
(* s in the dual cell).  Moise Sec 26 / DG DualCell.                         *)
(* ========================================================================= *)

let moi_fcl_dual = new_definition
 `moi_fcl_dual (c:(real^N->bool)->bool) (s:real^N->bool) =
    UNIONS {convex hull (IMAGE simplex_barycentre f) | f |
            moi_bar_chain c f /\ ~(f = {}) /\ !t. t IN f ==> s SUBSET t}`;;

let moi_fcl_ldual = new_definition
 `moi_fcl_ldual (c:(real^N->bool)->bool) (s:real^N->bool) =
    UNIONS {convex hull (IMAGE simplex_barycentre f) | f |
            moi_bar_chain c f /\ ~(f = {}) /\
            !t. t IN f ==> s SUBSET t /\ ~(t = s)}`;;

let MOI_FCL_IN_DUAL = prove
 (`!(c:(real^N->bool)->bool) s x.
     (x IN moi_fcl_dual c s <=>
      ?f. moi_bar_chain c f /\ ~(f = {}) /\ (!t. t IN f ==> s SUBSET t) /\
          x IN convex hull (IMAGE simplex_barycentre f)) /\
     (x IN moi_fcl_ldual c s <=>
      ?f. moi_bar_chain c f /\ ~(f = {}) /\
          (!t. t IN f ==> s SUBSET t /\ ~(t = s)) /\
          x IN convex hull (IMAGE simplex_barycentre f))`,
  REWRITE_TAC[moi_fcl_dual; moi_fcl_ldual; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let MOI_FCL_DUAL_MONO = prove
 (`!(c:(real^N->bool)->bool) s u.
     (s SUBSET u ==> moi_fcl_dual c u SUBSET moi_fcl_dual c s) /\
     moi_fcl_ldual c s SUBSET moi_fcl_dual c s`,
  REWRITE_TAC[SUBSET; MOI_FCL_IN_DUAL] THEN MESON_TAC[SUBSET_TRANS]);;

let MOI_FCL_DUAL_INTER = prove
 (`!(c:(real^N->bool)->bool) s s'.
     moi_bar_complex c
     ==> moi_fcl_dual c s INTER moi_fcl_dual c s' =
         UNIONS {moi_fcl_dual c u | u |
                 u IN c /\ ~(u = {}) /\ s SUBSET u /\ s' SUBSET u}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; SUBSET_INTER] THEN
    X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[MOI_FCL_DUAL_MONO]] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER g))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((f:(real^N->bool)->bool) INTER g = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER g))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain c ((f:(real^N->bool)->bool) INTER g)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_CHAIN_INTER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(f:(real^N->bool)->bool) INTER g`]
    MOI_FTA_CHAIN_MIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `moi_fcl_dual c (INTERS ((f:(real^N->bool)->bool) INTER g))` THEN
  CONJ_TAC THENL
   [EXISTS_TAC `INTERS ((f:(real^N->bool)->bool) INTER g)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `INTERS ((f:(real^N->bool)->bool) INTER g) IN f INTER g` THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `INTERS ((f:(real^N->bool)->bool) INTER g)`]
      MOI_BAR_CHAIN_ELEMENT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `!t:real^N->bool. t IN f ==> s SUBSET t` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `!t:real^N->bool. t IN g ==> s' SUBSET t` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    EXISTS_TAC `(f:(real^N->bool)->bool) INTER g` THEN ASM_REWRITE_TAC[]]);;

let MOI_FCL_LDUAL_EQ = prove
 (`!(c:(real^N->bool)->bool) s.
     moi_fcl_ldual c s =
     UNIONS {moi_fcl_dual c u | u | u IN c /\ ~(u = {}) /\ s SUBSET u /\ ~(u = s)}`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_FCL_IN_DUAL; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
      MOI_FTA_CHAIN_MIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `moi_fcl_dual c (INTERS (f:(real^N->bool)->bool))` THEN
    CONJ_TAC THENL
     [EXISTS_TAC `INTERS (f:(real^N->bool)->bool)` THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
      REPEAT CONJ_TAC THEN ASM_MESON_TAC[SUBSET];
      REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[SUBSET; MOI_FCL_IN_DUAL; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `(x:real^N) IN w` THEN ASM_REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `f:(real^N->bool)->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^N->bool` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(u:real^N->bool) SUBSET t` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[]]]);;

(* The dual cell is the cone from the barycentre of s over its link part. *)

let MOI_FCL_DUAL_CONE = prove
 (`!(c:(real^N->bool)->bool) s.
     moi_bar_complex c /\ s IN c /\ ~(s = {}) /\ ~(moi_fcl_ldual c s = {})
     ==> moi_fcl_dual c s =
         UNIONS {segment[simplex_barycentre s,y] | y | y IN moi_fcl_ldual c s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    GEN_REWRITE_TAC LAND_CONV [CONJUNCT1(SPEC_ALL MOI_FCL_IN_DUAL)] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(s:real^N->bool) IN f` THENL
     [ALL_TAC;
      EXISTS_TAC `segment[simplex_barycentre (s:real^N->bool),x]` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `x:real^N` THEN
      REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] THEN
    SUBGOAL_THEN
     `IMAGE simplex_barycentre (f:(real^N->bool)->bool) =
      simplex_barycentre s INSERT IMAGE simplex_barycentre (f DELETE s)`
    SUBST_ALL_TAC THENL
     [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [GSYM(MATCH_MP INSERT_DELETE th)]) THEN REWRITE_TAC[IMAGE_CLAUSES];
      ALL_TAC] THEN
    ASM_CASES_TAC `(f:(real^N->bool)->bool) DELETE s = {}` THENL
     [UNDISCH_TAC `(x:real^N) IN convex hull (simplex_barycentre s INSERT
                     IMAGE simplex_barycentre ((f:(real^N->bool)->bool) DELETE s))` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING] THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `~(moi_fcl_ldual c (s:real^N->bool) = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
      EXISTS_TAC `segment[simplex_barycentre (s:real^N->bool),y]` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `y:real^N` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN convex hull (simplex_barycentre s INSERT
                   IMAGE simplex_barycentre ((f:(real^N->bool)->bool) DELETE s))` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_INSERT_SEGMENTS; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `w:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    EXISTS_TAC `(f:(real^N->bool)->bool) DELETE s` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[DELETE_SUBSET];
      REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `(y:real^N) IN moi_fcl_ldual c s` THEN REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `(s:real^N->bool) INSERT g` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_MESON_TAC[];
      REWRITE_TAC[NOT_INSERT_EMPTY];
      REWRITE_TAC[FORALL_IN_INSERT; SUBSET_REFL] THEN ASM_MESON_TAC[];
      UNDISCH_TAC `(x:real^N) IN w` THEN ASM_REWRITE_TAC[] THEN
      SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT];
        MATCH_MP_TAC(SET_RULE `!s t (y:real^N). y IN s /\ s SUBSET t ==> y IN t`) THEN
        EXISTS_TAC `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]]]);;

(* A segment from a point off an affine set meets it in one end only.    *)

let MOI_FCL_SEG_OFF_AFFINE = prove
 (`!A (v:real^N) x y.
     affine A /\ ~(v IN A) /\ x IN A /\ y IN A /\ y IN segment[v,x] ==> y = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN segment[v,x]` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `u = &1` THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~((v:real^N) IN A)` THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  SUBGOAL_THEN `~(&1 - u = &0)` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - u) % v = y - u % x:real^N` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `v:real^N = inv(&1 - u) % y + (--(inv(&1 - u) * u)) % x`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `v:real^N = inv(&1 - u) % ((&1 - u) % v)` MP_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_LINV] THEN
      REWRITE_TAC[VECTOR_MUL_LID];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    REWRITE_TAC[ASSUME `(&1 - u) % v = y - u % x:real^N`] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `affine (A:real^N->bool)` THEN REWRITE_TAC[affine] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(&1 - u = &0)` THEN CONV_TAC REAL_FIELD);;

(* Unique rays from the barycentre of s over the link part of its dual cell. *)

let MOI_FCL_LDUAL_RAYS = prove
 (`!(c:(real^N->bool)->bool) s.
     moi_bar_complex c /\ s IN c /\ ~(s = {})
     ==> ~(simplex_barycentre s IN moi_fcl_ldual c s) /\
         (!x y. x IN moi_fcl_ldual c s /\ y IN moi_fcl_ldual c s /\
                y IN segment[simplex_barycentre s,x] ==> y = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `s:real^N->bool`] MOI_FTA_BARY_IN_HULL) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC)
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC)) THEN
  SUBGOAL_THEN `moi_bar_chain c ((s:real^N->bool) INSERT f)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(y:real^N) IN convex hull (IMAGE simplex_barycentre ((s:real^N->bool) INSERT f))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t (y:real^N). y IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `segment[simplex_barycentre (s:real^N->bool),x]` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT];
      MATCH_MP_TAC(SET_RULE `!s t (y:real^N). y IN s /\ s SUBSET t ==> y IN t`) THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(y:real^N) IN convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(s:real^N->bool) INSERT f`;
                   `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((s:real^N->bool) IN g)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `!t:real^N->bool. t IN g ==> s SUBSET t /\ ~(t = s)` THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `((s:real^N->bool) INSERT f) INTER g = f INTER g` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t (y:real^N). y IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                  ((f:(real^N->bool)->bool) INTER g))` THEN
    CONJ_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FCL_SEG_OFF_AFFINE THEN
  MAP_EVERY EXISTS_TAC
   [`affine hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))`;
    `simplex_barycentre (s:real^N->bool)`] THEN
  ASM_SIMP_TAC[AFFINE_AFFINE_HULL;
               REWRITE_RULE[SUBSET] CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
  SUBGOAL_THEN
   `~(simplex_barycentre (s:real^N->bool) IN IMAGE simplex_barycentre f)`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
      STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(s:real^N->bool) INSERT f`;
                   `s:real^N->bool`; `t:real^N->bool`]
      MOI_BAR_CHAIN_BARYCENTRE_INJ) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(s:real^N->bool) INSERT f`]
    MOI_BAR_CHAIN_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[affine_dependent; IMAGE_CLAUSES; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `simplex_barycentre (s:real^N->bool)`) THEN
  REWRITE_TAC[IN_INSERT] THEN
  ASM_SIMP_TAC[SET_RULE `~((a:real^N) IN s) ==> (a INSERT s) DELETE a = s`]);;

(* The dual cell of s in a subcomplex l is its part in UNIONS l.          *)

let MOI_FCL_DUAL_SUB = prove
 (`!(c:(real^N->bool)->bool) l s.
     moi_bar_complex c /\ simplicial_subcomplex l c
     ==> moi_fcl_dual c s INTER UNIONS l = moi_fcl_dual l s /\
         moi_fcl_ldual c s INTER UNIONS l = moi_fcl_ldual l s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_complex (c:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) c` THEN
    REWRITE_TAC[moi_bar_complex; simplicial_subcomplex] THEN
    REWRITE_TAC[SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f. moi_bar_chain l f /\ ~(f = {})
        ==> convex hull (IMAGE simplex_barycentre f) SUBSET UNIONS (l:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS (f:(real^N->bool)->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_HULL_SUBSET_MAX THEN
      EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
        MOI_BAR_CHAIN_MAX) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a:A->bool b. a IN b ==> a SUBSET UNIONS b`) THEN
      ASM_MESON_TAC[moi_bar_chain; SUBSET]];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_INTER] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [CONJUNCT1(SPEC_ALL MOI_FCL_IN_DUAL)] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:(real^N->bool)->bool`
      STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `(f:(real^N->bool)->bool) INTER l` THEN
    SUBGOAL_THEN
     `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER l))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_HULL_SUBCOMPLEX THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain] THEN SIMP_TAC[FINITE_INTER; IN_INTER] THEN
      SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER l))` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[MOI_FCL_IN_DUAL] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `f:(real^N->bool)->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_fcl_dual; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      ASM_SIMP_TAC[]];
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_INTER] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [CONJUNCT2(SPEC_ALL MOI_FCL_IN_DUAL)] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `f:(real^N->bool)->bool`
      STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `(f:(real^N->bool)->bool) INTER l` THEN
    SUBGOAL_THEN
     `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER l))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_HULL_SUBCOMPLEX THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain] THEN SIMP_TAC[FINITE_INTER; IN_INTER] THEN
      SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER l))` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
      REWRITE_TAC[MOI_FCL_IN_DUAL] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `f:(real^N->bool)->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_fcl_ldual; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      ASM_SIMP_TAC[]]]);;

(* ========================================================================= *)
(* Vertex links in the first barycentric subdivision are link parts of dual  *)
(* cells; the boundary complex of the first derived of a combinatorial       *)
(* 3-manifold with boundary is the first derived of its boundary complex;    *)
(* the cells at boundary vertices.                                           *)
(* ========================================================================= *)

let MOI_FCL_LINK_BARY = prove
 (`!(c:(real^N->bool)->bool) v.
     moi_bar_complex c /\ {v} IN c
     ==> UNIONS (simplicial_link (barycentric_subdivision c) v) =
         moi_fcl_ldual c {v}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; simplicial_link; IN_ELIM_THM] THEN
    X_GEN_TAC `r:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC))) THEN
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(q:real^N->bool) IN barycentric_subdivision c` THEN
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`; `v:real^N`]
      MOI_FTA_VERTEX_IN_HULL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `(f:(real^N->bool)->bool) SUBSET g` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_HULL_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
      ALL_TAC] THEN
    ASM_CASES_TAC `(f:(real^N->bool)->bool) = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; EMPTY_SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN GEN_REWRITE_TAC I [SUBSET] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SING_SUBSET] THEN ASM SET_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~((v:real^N) IN r)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[MOI_FTA_BARY_SING]];
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`; `v:real^N`]
        MOI_FTA_VERTEX_IN_HULL) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                   ({v:real^N} INSERT (f:(real^N->bool)->bool)))` THEN
      SUBGOAL_THEN `moi_bar_chain c ({v:real^N} INSERT (f:(real^N->bool)->bool))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
        EXISTS_TAC `{v:real^N} INSERT (f:(real^N->bool)->bool)` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE; IN_INSERT] THEN
        EXISTS_TAC `{v:real^N}` THEN REWRITE_TAC[MOI_FTA_BARY_SING];
        MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
        EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
        SET_TAC[]]]]);;

(* The boundary complex of the first derived. *)

let MOI_FCL_BC_BARY = prove
 (`!c:(real^N->bool)->bool.
     combinatorial_manifold_with_boundary 3 c
     ==> boundary_complex (barycentric_subdivision c) =
         barycentric_subdivision (boundary_complex c)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` COMBINATORIAL_WB_BARYCENTRIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FM3_BC_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`]
    MOI_FTA_SUB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC LAND_CONV [boundary_complex] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:real^N->bool` THEN
  EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC MOI_FTA_BS_FULL THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    ASM_MESON_TAC[extreme_point_of; SUBSET];
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
      SUBGOAL_THEN
       `(r:real^N->bool) SUBSET UNIONS (barycentric_subdivision (boundary_complex c))`
      MP_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]]]);;

(* Basic facts on the first derived of a combinatorial 3-manifold with     *)
(* boundary and its boundary complex.                                       *)

let MOI_FCL_CMWB_SETUP = prove
 (`!c:(real^N->bool)->bool.
     combinatorial_manifold_with_boundary 3 c
     ==> lf_simplicial_complex c /\ moi_bar_complex c /\
         simplicial_subcomplex (boundary_complex c) c /\
         UNIONS (boundary_complex c) = complex_boundary c /\
         lf_simplicial_complex (boundary_complex c) /\
         moi_bar_complex (boundary_complex c) /\
         combinatorial_manifold 2 (boundary_complex c) /\
         combinatorial_manifold_with_boundary 3 (barycentric_subdivision c) /\
         complex_boundary (barycentric_subdivision c) = complex_boundary c /\
         lf_simplicial_complex (barycentric_subdivision c) /\
         boundary_complex (barycentric_subdivision c) =
         barycentric_subdivision (boundary_complex c)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` COMBINATORIAL_WB_BARYCENTRIC) THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FM3_BC_SUBCOMPLEX) THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_SIMP_TAC[MOI_FCL_BC_BARY; MOI_FTA_LF_BAR] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[combinatorial_manifold_with_boundary; MOI_FTA_LF_BAR]);;

let MOI_FCL_VERTEX_LDUAL = prove
 (`!(c:(real^N->bool)->bool) v.
     combinatorial_manifold_with_boundary 3 c /\ {v} IN c /\
     v IN complex_boundary c
     ==> {v} IN boundary_complex c /\
         pl_cell_with_boundary 2 (moi_fcl_ldual c {v})
                                 (moi_fcl_ldual (boundary_complex c) {v}) /\
         pl_sphere 1 (moi_fcl_ldual (boundary_complex c) {v}) /\
         3 <= dimindex(:N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  SUBGOAL_THEN `{v:real^N} IN boundary_complex c` ASSUME_TAC THENL
   [REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N} IN barycentric_subdivision c` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FRN_SING_IN_BARY]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_ball 2 (UNIONS (simplicial_link (barycentric_subdivision c) (v:real^N)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision c:(real^N->bool)->bool`; `v:real^N`]
      MOI_FM3_CB_VERTEX_CLASSIFY) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `simplicial_link (barycentric_subdivision c) (v:real^N)`
    MOI_FM3_DISK_PL) THEN
  ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
  ASM_SIMP_TAC[GSYM MOI_FM3_BC_LINK] THEN
  ASM_SIMP_TAC[MOI_FCL_LINK_BARY] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[pl_cell_with_boundary] THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FRN_BALL_LINK_DIM THEN
    MAP_EVERY EXISTS_TAC [`barycentric_subdivision c:(real^N->bool)->bool`; `v:real^N`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FCL_LDUAL_SUB_MONO = prove
 (`!(c:(real^N->bool)->bool) l s.
     l SUBSET c ==> moi_fcl_ldual l s SUBSET moi_fcl_ldual c s /\
                    moi_fcl_dual l s SUBSET moi_fcl_dual c s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; MOI_FCL_IN_DUAL] THEN
  REPEAT STRIP_TAC THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
  ASM_MESON_TAC[MOI_BAR_CHAIN_MONO]);;

let MOI_FCL_VERTEX_CELLS = prove
 (`!(c:(real^N->bool)->bool) v.
     combinatorial_manifold_with_boundary 3 c /\ {v} IN c /\
     v IN complex_boundary c
     ==> moi_fcl_dual (boundary_complex c) {v} =
           UNIONS {segment[v,y] | y | y IN moi_fcl_ldual (boundary_complex c) {v}} /\
         moi_fcl_dual c {v} =
           UNIONS {segment[v,y] | y | y IN moi_fcl_ldual c {v}} /\
         pl_cell_with_boundary 2 (moi_fcl_dual (boundary_complex c) {v})
                                 (moi_fcl_ldual (boundary_complex c) {v}) /\
         pl_cell_with_boundary 3 (moi_fcl_dual c {v})
           (moi_fcl_ldual c {v} UNION moi_fcl_dual (boundary_complex c) {v})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FCL_VERTEX_LDUAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(boundary_complex c:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_fcl_ldual (boundary_complex c) {v:real^N} = {}) /\
                ~(moi_fcl_ldual c {v:real^N} = {})` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s t:real^N->bool. ~(s = {}) /\ s SUBSET t
                                ==> ~(s = {}) /\ ~(t = {})`) THEN
    ASM_SIMP_TAC[MOI_FCL_LDUAL_SUB_MONO] THEN
    ASM_MESON_TAC[MOI_FTA_PL_SPHERE_NONEMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`boundary_complex c:(real^N->bool)->bool`; `{v:real^N}`]
    MOI_FCL_DUAL_CONE) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{v:real^N}`] MOI_FCL_DUAL_CONE) THEN
  MP_TAC(ISPECL [`boundary_complex c:(real^N->bool)->bool`; `{v:real^N}`]
    MOI_FCL_LDUAL_RAYS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{v:real^N}`] MOI_FCL_LDUAL_RAYS) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY; MOI_FTA_BARY_SING] THEN
  REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`1`; `moi_fcl_ldual (boundary_complex c) {v:real^N}`; `v:real^N`]
      MOI_FTA_CONE_CELL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]];
    MP_TAC(ISPECL [`2`; `moi_fcl_ldual c {v:real^N}`;
                   `moi_fcl_ldual (boundary_complex c) {v:real^N}`; `v:real^N`]
      MOI_FCL_CONE_CELL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];
      CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The cells at boundary edges.  The link part of the dual cell of a         *)
(* boundary edge e is an arc between the barycentres of the two boundary     *)
(* triangles at e: in the closed star C of a vertex u of e in the first      *)
(* derived (a PL 3-cell), the link of the barycentre of e in the boundary    *)
(* complex of C is a PL circle, made of that link part and the two segments  *)
(* from u to the triangle barycentres (MOI_FTA_S2LINK's method).             *)
(* ========================================================================= *)

let MOI_FCL_CSTAR_BARY = prove
 (`!(c:(real^N->bool)->bool) u.
     moi_bar_complex c /\ {u} IN c
     ==> (!r. r IN moi_fm3_cstar (barycentric_subdivision c) u <=>
              ?f. moi_bar_chain c f /\ (!t. t IN f ==> u IN t) /\
                  r = convex hull (IMAGE simplex_barycentre f)) /\
         UNIONS (moi_fm3_cstar (barycentric_subdivision c) u) = moi_fcl_dual c {u}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. r IN moi_fm3_cstar (barycentric_subdivision c) u <=>
        ?f. moi_bar_chain c f /\ (!t. t IN f ==> (u:real^N) IN t) /\
            r = convex hull (IMAGE simplex_barycentre f)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN REWRITE_TAC[moi_fm3_cstar; IN_ELIM_THM] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(q:real^N->bool) IN barycentric_subdivision c` THEN
      REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`; `u:real^N`]
        MOI_FTA_VERTEX_IN_HULL) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `(r:real^N->bool) face_of q` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
        MOI_BAR_CHAIN_AFFINE_INDEPENDENT) THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; SUBSET_IMAGE] THEN
      DISCH_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC)
        SUBST1_TAC)) THEN
      EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                   ({u:real^N} INSERT (f:(real^N->bool)->bool)))` THEN
      SUBGOAL_THEN `moi_bar_chain c ({u:real^N} INSERT (f:(real^N->bool)->bool))`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
        ASM_MESON_TAC[SING_SUBSET];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
        EXISTS_TAC `{u:real^N} INSERT (f:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE; IN_INSERT] THEN
        EXISTS_TAC `{u:real^N}` THEN REWRITE_TAC[MOI_FTA_BARY_SING];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
        EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_UNIONS; MOI_FCL_IN_DUAL] THEN
  X_GEN_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN
    UNDISCH_TAC `(x:real^N) IN r` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN
    DISCH_TAC THEN UNDISCH_TAC
     `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SING_SUBSET]]);;

(* A chain at u whose derived simplex lies in the boundary of the star is a *)
(* chain of the subcomplex l (the derived simplices are full).              *)

let MOI_FCL_CSTAR_BD_CHAIN = prove
 (`!(c:(real^N->bool)->bool) l u g.
     moi_bar_complex c /\ simplicial_subcomplex l c /\ {u} IN c /\
     moi_bar_chain c g /\ {u} IN g /\
     convex hull (IMAGE simplex_barycentre g) SUBSET
       moi_fcl_ldual c {u} UNION moi_fcl_dual l {u}
     ==> g SUBSET l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?x:real^N. x IN relative_interior (convex hull (IMAGE simplex_barycentre g))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; CONVEX_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY;
             IMAGE_EQ_EMPTY] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre g)` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN moi_fcl_ldual c {u} \/ x IN moi_fcl_dual l {u}`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN moi_fcl_ldual c {u}` THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `g':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`;
                   `g':(real^N->bool)->bool`; `x:real^N`] MOI_FTA_RI_SUBCHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `{u:real^N} IN g'` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `!t. t IN g' ==> {u:real^N} SUBSET t /\ ~(t = {u})` THEN
    DISCH_THEN(MP_TAC o SPEC `{u:real^N}`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS l` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `{u:real^N}`]
      MOI_FCL_DUAL_SUB) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `g:(real^N->bool)->bool`] MOI_FRN_FULL_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`;
                 `(g:(real^N->bool)->bool) INTER l`; `x:real^N`] MOI_FTA_RI_SUBCHAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FTA_CHAIN_INTER];
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER]];
    SET_TAC[]]);;

(* The link of the barycentre of e in the boundary complex of the star of u. *)

let MOI_FCL_EDGE_STAR_LINK = prove
 (`!(c:(real^N->bool)->bool) l u e.
     moi_bar_complex c /\ simplicial_subcomplex l c /\ {u} IN c /\
     e IN l /\ u IN e /\ ~(e = {u}) /\
     (!t. t IN c /\ t SUBSET e /\ u IN t ==> t = {u} \/ t = e) /\
     ~(moi_fcl_ldual l e = {})
     ==> UNIONS (simplicial_link
                  {s | s IN moi_fm3_cstar (barycentric_subdivision c) u /\
                       s SUBSET moi_fcl_ldual c {u} UNION moi_fcl_dual l {u}}
                  (simplex_barycentre e)) =
         moi_fcl_ldual c e UNION
         UNIONS {segment[u,y] | y | y IN moi_fcl_ldual l e}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N`] MOI_FCL_CSTAR_BARY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET c /\ e IN c /\ ~(e:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN l` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) c` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[FACE_OF_SING] THEN
    SUBGOAL_THEN `?n. n simplex (e:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
    UNDISCH_TAC `!t:real^N->bool. t IN c /\ t SUBSET e /\ u IN t ==> t = {u} \/ t = e` THEN
    DISCH_THEN(K ALL_TAC) THEN
    SUBGOAL_THEN `{u:real^N} face_of e` MP_TAC THENL
     [UNDISCH_TAC `moi_bar_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`{u:real^N}`; `e:real^N->bool`] o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `{u:real^N} INTER e = {u}` (fun th -> SIMP_TAC[th]) THEN
      ASM SET_TAC[];
      REWRITE_TAC[FACE_OF_SING]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; simplicial_link; IN_ELIM_THM] THEN
    X_GEN_TAC `r:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `(r:real^N->bool) IN moi_fm3_cstar (barycentric_subdivision c) u` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(q:real^N->bool) IN moi_fm3_cstar (barycentric_subdivision c) u` THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(e:real^N->bool) IN g` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`;
                     `e:real^N->bool`] MOI_FTA_BARY_IN_HULL) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:(real^N->bool)->bool) SUBSET g` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_HULL_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((e:real^N->bool) IN f)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(simplex_barycentre (e:real^N->bool) IN r)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!t:real^N->bool. t IN f ==> t = {u} \/ (e SUBSET t /\ ~(t = e))`
    ASSUME_TAC THENL
     [X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) SUBSET e \/ e SUBSET t` MP_TAC THENL
       [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
      STRIP_TAC THENL
       [DISJ1_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool` o check (fun th ->
          is_forall(concl th) &&
          can (find_term ((=) `{u:real^N}`)) (concl th) &&
          can (find_term ((=) `e:real^N->bool`)) (concl th))) THEN
        ANTS_TAC THENL [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ASM_MESON_TAC[]];
        DISJ2_TAC THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `{u:real^N} IN f` THENL
     [ALL_TAC;
      MATCH_MP_TAC(SET_RULE `!s t u:real^N->bool. s SUBSET t ==> s SUBSET t UNION u`) THEN
      ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `(f:(real^N->bool)->bool) = {}` THENL
       [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; EMPTY_SUBSET]; ALL_TAC] THEN
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]] THEN
    SUBGOAL_THEN `(g:(real^N->bool)->bool) SUBSET l` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FCL_CSTAR_BD_CHAIN THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `u:real^N`] THEN
      ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s t u:real^N->bool. s SUBSET u ==> s SUBSET t UNION u`) THEN
    SUBGOAL_THEN
     `IMAGE simplex_barycentre (f:(real^N->bool)->bool) =
      u INSERT IMAGE simplex_barycentre (f DELETE {u})`
    ASSUME_TAC THENL
     [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
        [GSYM(MATCH_MP INSERT_DELETE th)]) THEN
      REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(f:(real^N->bool)->bool) DELETE {u} = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; SING_SUBSET] THEN
      UNDISCH_TAC `~(moi_fcl_ldual l (e:real^N->bool) = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
      EXISTS_TAC `segment[u:real^N,y]` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[CONVEX_HULL_INSERT_SEGMENTS; IMAGE_EQ_EMPTY] THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s:A->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `z:real^N` THEN REWRITE_TAC[] THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    EXISTS_TAC `(f:(real^N->bool)->bool) DELETE {u}` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
      REWRITE_TAC[DELETE_SUBSET] THEN
      UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain] THEN ASM SET_TAC[];
      REWRITE_TAC[IN_DELETE] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_bar_chain c ((e:real^N->bool) INSERT f)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!s t u:real^N->bool. s SUBSET t ==> s SUBSET t UNION u`) THEN
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(e:real^N->bool) SUBSET t /\ ~(t = e)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[]];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                     `e:real^N->bool`] MOI_FTA_BARY_IN_HULL) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                   ((e:real^N->bool) INSERT f))` THEN
      REPEAT CONJ_TAC THENL
       [EXISTS_TAC `(e:real^N->bool) INSERT f` THEN ASM_REWRITE_TAC[FORALL_IN_INSERT] THEN
        ASM SET_TAC[];
        MATCH_MP_TAC(SET_RULE `!s t u:real^N->bool. s SUBSET t ==> s SUBSET t UNION u`) THEN
        GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
        REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `(e:real^N->bool) INSERT f` THEN
        ASM_REWRITE_TAC[NOT_INSERT_EMPTY; FORALL_IN_INSERT] THEN
        REWRITE_TAC[SING_SUBSET] THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
        X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(e:real^N->bool) SUBSET t /\ ~(t = e)` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[]];
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT];
        MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
        EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain l ((e:real^N->bool) INSERT f) /\
                moi_bar_chain l ({u:real^N} INSERT e INSERT f) /\
                moi_bar_chain l ({u:real^N} INSERT f)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_bar_chain l ((e:real^N->bool) INSERT f)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_bar_chain l ({u:real^N} INSERT e INSERT f)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FTA_CHAIN_INSERT THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
      REWRITE_TAC[FORALL_IN_INSERT] THEN ASM_REWRITE_TAC[SING_SUBSET] THEN
      ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `{u:real^N} INSERT e INSERT f` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain c ({u:real^N} INSERT e INSERT f) /\
                moi_bar_chain c ({u:real^N} INSERT f)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_MONO]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre ({u:real^N} INSERT f))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE; IN_INSERT] THEN
      EXISTS_TAC `{u:real^N}` THEN REWRITE_TAC[MOI_FTA_BARY_SING];
      MATCH_MP_TAC(SET_RULE `!s t (y:real^N). y IN s /\ s SUBSET t ==> y IN t`) THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `!s:A->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
  ASM_REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `{u:real^N} INSERT f` THEN ASM_REWRITE_TAC[FORALL_IN_INSERT; IN_SING] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE `!s t u:real^N->bool. s SUBSET u ==> s SUBSET t UNION u`) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `{u:real^N} INSERT f` THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; FORALL_IN_INSERT; SUBSET_REFL] THEN
    ASM SET_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{u:real^N} INSERT f`;
                   `e:real^N->bool`] MOI_FTA_BARY_IN_HULL) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[];
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                 ({u:real^N} INSERT e INSERT f))` THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `{u:real^N} INSERT e INSERT f` THEN
      ASM_REWRITE_TAC[FORALL_IN_INSERT; IN_SING] THEN ASM SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!s t u:real^N->bool. s SUBSET u ==> s SUBSET t UNION u`) THEN
      GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
      REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `{u:real^N} INSERT e INSERT f` THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY; FORALL_IN_INSERT; SUBSET_REFL] THEN
      ASM SET_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT];
      MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]]);;

(* PL circles are images of simple closed PL paths; PL arcs are 1-cells.   *)

let MOI_FCL_CIRCLE_PATH = prove
 (`!Z:real^N->bool.
     pl_sphere 1 Z
     ==> ?g. simple_path g /\ pathfinish g = pathstart g /\
             pl_map_on (interval[vec 0,vec 1]) g /\ path_image g = Z`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `h:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `&2 simplex (k:real^N->bool)` THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c:real^N`] MOI_PL2_TRIANGLE_POLYGON) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_homeomorphism (relative_frontier (convex hull {a,b,c}),Z)
                 (f:real^N->real^N,h)` THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE] THEN
  REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
  EXISTS_TAC `(f:real^N->real^N) o polygonal_path[a;b;c;a:real^N]` THEN
  ASM_REWRITE_TAC[PATHSTART_COMPOSE; PATHFINISH_COMPOSE; PATH_IMAGE_COMPOSE] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SIMPLE_PATH_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `segment[a,b] UNION segment[b,c] UNION segment[c,a:real^N]` THEN
    ASM_REWRITE_TAC[MOI_PL2_PL_POLYGONAL_PATH] THEN
    REWRITE_TAC[GSYM path_image] THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

let MOI_FCL_UNIT_RF = prove
 (`relative_frontier(interval[vec 0:real^1,vec 1]) = {vec 0,vec 1}`,
  REWRITE_TAC[relative_frontier; MOI_FCL_UNIT_INTERVAL] THEN
  SIMP_TAC[CLOSURE_CLOSED; CLOSED_INTERVAL] THEN
  REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTERVAL_1; IN_INSERT; NOT_IN_EMPTY;
              GSYM DROP_EQ; DROP_VEC] THEN
  REAL_ARITH_TAC);;

let MOI_FCL_ARC_CELL = prove
 (`!g:real^1->real^N.
     arc g /\ pl_map_on (interval[vec 0,vec 1]) g
     ==> pl_cell_with_boundary 1 (path_image g) {pathstart g,pathfinish g}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `g:real^1->real^N` MOI_PL2_ARC_PL_HOMEOMORPHISM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `h:real^N->real^1`) THEN
  MP_TAC(ISPECL [`1`; `interval[vec 0:real^1,vec 1]`;
                 `relative_frontier(interval[vec 0:real^1,vec 1])`;
                 `path_image (g:real^1->real^N)`; `g:real^1->real^N`;
                 `h:real^N->real^1`] MOI_FCL_CELL_TRANSFER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_GE_1] THEN MATCH_MP_TAC MOI_S4A_POLY_CELL_1 THEN
    REWRITE_TAC[MOI_FCL_UNIT_INTERVAL];
    MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
    REWRITE_TAC[MOI_FCL_UNIT_RF; IMAGE_CLAUSES; pathstart; pathfinish]]);;

(* An edge of a complex: its ends are vertices, and its faces through one  *)
(* end are that end and the edge.                                           *)

let MOI_FCL_EDGE_SEGMENT = prove
 (`!(c:(real^N->bool)->bool) e.
     moi_bar_complex c /\ e IN c /\ aff_dim e = &1
     ==> ?u w. ~(u = w) /\ e = segment[u,w] /\ {u} IN c /\ {w} IN c /\
               (!t. t IN c /\ t SUBSET e /\ u IN t ==> t = {u} \/ t = e)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&1 simplex (e:real^N->bool)` MP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`]
      MOI_BAR_COMPLEX_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `u:real^N` THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!t:real^N->bool. t face_of segment[u,w] ==> t IN c` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `moi_bar_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    EXISTS_TAC `segment[u:real^N,w]` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^N->bool) face_of segment[u,w]` MP_TAC THENL
   [UNDISCH_TAC `moi_bar_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`t:real^N->bool`; `e:real^N->bool`] o
      CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(t:real^N->bool) INTER segment[u,w] = t` (fun th -> SIMP_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(u:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(u:real^N) IN d` THEN ASM_CASES_TAC `(w:real^N) IN d` THENL
   [DISCH_TAC THEN DISJ2_TAC THEN AP_TERM_TAC THEN ASM SET_TAC[];
    DISCH_TAC THEN DISJ1_TAC THEN
    SUBGOAL_THEN `d = {u:real^N}` SUBST1_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[CONVEX_HULL_SING]];
    SUBGOAL_THEN `d = {w:real^N}` SUBST1_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN ASM_MESON_TAC[]];
    SUBGOAL_THEN `d:real^N->bool = {}` SUBST1_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY]]]);;

(* A boundary edge lies in exactly two boundary triangles; the link part of *)
(* its dual cell in the boundary complex is their two barycentres.         *)

let MOI_FCL_EDGE_TRIANGLES = prove
 (`!(l:(real^N->bool)->bool) e.
     FINITE l /\ combinatorial_manifold 2 l /\ e IN l /\ aff_dim e = &1
     ==> ?s1 s2. ~(s1 = s2) /\
                 {t | t IN l /\ aff_dim t = &2 /\ e SUBSET t} = {s1,s2} /\
                 s1 IN l /\ s2 IN l /\ aff_dim s1 = &2 /\ aff_dim s2 = &2 /\
                 e SUBSET s1 /\ e SUBSET s2 /\
                 ~(simplex_barycentre s1 = simplex_barycentre s2) /\
                 moi_fcl_ldual l e = {simplex_barycentre s1,simplex_barycentre s2}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FRN_SA_CM_EDGE2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `{t | t IN l /\ aff_dim t = &2 /\ (e:real^N->bool) SUBSET t} HAS_SIZE 2`
  MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
  SUBGOAL_THEN
   `(s1:real^N->bool) IN l /\ s2 IN l /\ aff_dim s1 = &2 /\ aff_dim s2 = &2 /\
    e SUBSET s1 /\ e SUBSET s2`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(s1:real^N->bool = s2)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FTA_BARY_INJ THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
    ASM_MESON_TAC[INT_ARITH `~(--(&1):int = &2)`];
    ALL_TAC] THEN
  (* the members of the chains strictly above e are s1 or s2 *)
  SUBGOAL_THEN
   `!t:real^N->bool. t IN l /\ e SUBSET t /\ ~(t = e) ==> t = s1 \/ t = s2`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `t IN {t | t IN l /\ aff_dim t = &2 /\ (e:real^N->bool) SUBSET t}`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(INT_ARITH `a <= &2 /\ &1 < a ==> a:int = &2`) THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FRN_SA_CM_DIM]; ALL_TAC] THEN
      UNDISCH_TAC `aff_dim (e:real^N->bool) = &1` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_CONVEX];
        UNDISCH_TAC `moi_bar_complex (l:(real^N->bool)->bool)` THEN
        REWRITE_TAC[moi_bar_complex] THEN
        DISCH_THEN(MP_TAC o SPECL [`e:real^N->bool`; `t:real^N->bool`] o
          CONJUNCT2 o CONJUNCT2) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(e:real^N->bool) INTER t = e` (fun th -> SIMP_TAC[th]) THEN
        ASM SET_TAC[]];
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((s1:real^N->bool) SUBSET s2) /\ ~(s2 SUBSET s1)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`s1:real^N->bool`; `s2:real^N->bool`] FACE_OF_AFF_DIM_LT);
      MP_TAC(ISPECL [`s2:real^N->bool`; `s1:real^N->bool`] FACE_OF_AFF_DIM_LT)] THEN
    ASM_REWRITE_TAC[INT_LT_REFL] THEN
    ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_CONVEX; moi_bar_complex;
                  SET_RULE `(a:real^N->bool) SUBSET b ==> a INTER b = a /\ b INTER a = a`];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(f:(real^N->bool)->bool) SUBSET {s1,s2}` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `s1:real^N->bool`)) (concl th) &&
        is_imp(snd(strip_forall(concl th))))) THEN
      ASM_MESON_TAC[moi_bar_chain; SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `f = {s1:real^N->bool} \/ f = {s2}` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `~((s1:real^N->bool) IN f /\ s2 IN f)` MP_TAC THENL
       [STRIP_TAC THEN
        SUBGOAL_THEN `(s1:real^N->bool) SUBSET s2 \/ s2 SUBSET s1` MP_TAC THENL
         [ASM_MESON_TAC[moi_bar_chain]; ASM_REWRITE_TAC[]];
        ASM SET_TAC[]];
      UNDISCH_TAC `(x:real^N) IN convex hull IMAGE simplex_barycentre f` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING; IN_INSERT] THEN
      MESON_TAC[];
      UNDISCH_TAC `(x:real^N) IN convex hull IMAGE simplex_barycentre f` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING; IN_INSERT] THEN
      MESON_TAC[]];
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; MOI_FCL_IN_DUAL] THEN CONJ_TAC THENL
     [EXISTS_TAC `{s1:real^N->bool}`; EXISTS_TAC `{s2:real^N->bool}`] THEN
    REWRITE_TAC[NOT_INSERT_EMPTY; IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING;
                FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN ASM_REWRITE_TAC[] THEN
       DISCH_THEN SUBST_ALL_TAC THEN
       RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
       ASM_MESON_TAC[INT_ARITH `~(--(&1):int = &2)`];
       DISCH_THEN SUBST_ALL_TAC THEN
       RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
       ASM_MESON_TAC[INT_ARITH `~(&1:int = &2)`]])]);;

let MOI_FCL_CHAIN_PAIR = prove
 (`!(c:(real^N->bool)->bool) s t.
     s IN c /\ t IN c /\ ~(s = {}) /\ ~(t = {}) /\ s SUBSET t
     ==> moi_bar_chain c {s,t}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT; FINITE_EMPTY;
              IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[SUBSET_REFL]);;

(* The link part of the dual cell of a boundary edge is an arc between the  *)
(* barycentres of the two boundary triangles at the edge.                   *)

let MOI_FCL_EDGE_LDUAL_ARC = prove
 (`!(c:(real^N->bool)->bool) e.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     e IN boundary_complex c /\ aff_dim e = &1
     ==> ?s1 s2.
           ~(s1 = s2) /\
           {t | t IN boundary_complex c /\ aff_dim t = &2 /\ e SUBSET t} = {s1,s2} /\
           ~(simplex_barycentre s1 = simplex_barycentre s2) /\
           moi_fcl_ldual (boundary_complex c) e =
             {simplex_barycentre s1,simplex_barycentre s2} /\
           pl_cell_with_boundary 1 (moi_fcl_ldual c e)
             {simplex_barycentre s1,simplex_barycentre s2}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  ABBREV_TAC `l = boundary_complex (c:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool) /\ l SUBSET c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) c` THEN
    SIMP_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) IN c /\ e SUBSET complex_boundary c`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(e:real^N->bool) IN l` THEN EXPAND_TAC "l" THEN
    REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCL_EDGE_TRIANGLES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCL_EDGE_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` MP_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (ASSUME_TAC o SYM)
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(u:real^N) IN e /\ (w:real^N) IN e` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th ->
      let th' = check (fun t -> is_eq(concl t) && rhs(concl t) = `e:real^N->bool`) th in
      REWRITE_TAC[SYM th']) THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `e:real^N->bool`)) THEN
  SUBGOAL_THEN `(u:real^N) IN complex_boundary c /\ ~(e = {u:real^N}) /\
                ~(e SUBSET {u:real^N}) /\ ~(e:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]; ASM SET_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s1:real^N->bool) IN c /\ s2 IN c` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(s1:real^N->bool = {}) /\ ~(s2:real^N->bool = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
    ASM_MESON_TAC[INT_ARITH `~(--(&1):int = &2)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s1:real^N->bool = {u}) /\ ~(s2:real^N->bool = {u})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_SING]) THEN
    ASM_MESON_TAC[INT_ARITH `~(&0:int = &2)`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s1:real^N->bool = e) /\ ~(s2:real^N->bool = e)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_MESON_TAC[INT_ARITH `~(&1:int = &2)`];
    ALL_TAC] THEN
  (* the closed star of u in the first derived *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N`] MOI_FCL_VERTEX_CELLS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o last o CONJUNCTS) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N`] MOI_FCL_CSTAR_BARY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `{u:real^N} IN barycentric_subdivision c` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_SING_IN_BARY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE (moi_fm3_cstar (barycentric_subdivision c) (u:real^N)) /\
    lf_simplicial_complex (moi_fm3_cstar (barycentric_subdivision c) u)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision c:(real^N->bool)->bool`; `u:real^N`]
      MOI_FTA_CSTAR_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM moi_fta_cstar; moi_fm3_cstar] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fm3_cstar (barycentric_subdivision c) (u:real^N)`;
                 `moi_fcl_ldual c {u:real^N} UNION moi_fcl_dual l {u}`]
    PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `{simplex_barycentre (e:real^N->bool)} IN
    boundary_complex (moi_fm3_cstar (barycentric_subdivision c) u)`
  ASSUME_TAC THENL
   [REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN
    SUBGOAL_THEN `moi_bar_chain c {e:real^N->bool} /\ moi_bar_chain l {e:real^N->bool}`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N`] MOI_FCL_CSTAR_BARY) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(fun th -> REWRITE_TAC[CONJUNCT1 th]) THEN
      EXISTS_TAC `{e:real^N->bool}` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; FORALL_IN_INSERT; NOT_IN_EMPTY];
      ASM_REWRITE_TAC[SING_SUBSET; IN_UNION] THEN DISJ2_TAC THEN
      REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `{e:real^N->bool}` THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY; IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING;
                      FORALL_IN_INSERT; NOT_IN_EMPTY; SING_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_sphere 1 (UNIONS (simplicial_link
      (boundary_complex (moi_fm3_cstar (barycentric_subdivision c) u))
      (simplex_barycentre (e:real^N->bool))))`
  MP_TAC THENL
   [MP_TAC(ISPEC `moi_fm3_cstar (barycentric_subdivision c) (u:real^N)`
      BOUNDARY_COMPLEX_SURFACE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o el 3 o CONJUNCTS) THEN
    REWRITE_TAC[combinatorial_manifold] THEN
    DISCH_THEN(MP_TAC o SPEC `simplex_barycentre (e:real^N->bool)` o CONJUNCT2) THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[boundary_complex] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `u:real^N`;
                 `e:real^N->bool`] MOI_FCL_EDGE_STAR_LINK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    UNDISCH_TAC `!t:real^N->bool. t IN c /\ t SUBSET e /\ u IN t ==> t = {u} \/ t = e` THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_2] THEN
  ABBREV_TAC `b1 = simplex_barycentre (s1:real^N->bool)` THEN
  ABBREV_TAC `b2 = simplex_barycentre (s2:real^N->bool)` THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FCL_CIRCLE_PATH) THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^1->real^N` STRIP_ASSUME_TAC) THEN
  (* the arc b1 -- u -- b2 *)
  SUBGOAL_THEN `~(b1:real^N = u) /\ ~(b2 = u)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s1:real^N->bool`; `{u:real^N}`]
        MOI_FTA_BARY_INJ);
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s2:real^N->bool`; `{u:real^N}`]
        MOI_FTA_BARY_INJ)] THEN
    ASM_REWRITE_TAC[MOI_FTA_BARY_SING; NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} SUBSET s1 /\ {u} SUBSET s2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(u:real^N) IN e` THEN UNDISCH_TAC `(e:real^N->bool) SUBSET s1` THEN
    UNDISCH_TAC `(e:real^N->bool) SUBSET s2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_bar_chain c {{u:real^N},s1} /\ moi_bar_chain c {{u:real^N},s2}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FCL_CHAIN_PAIR THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[b1:real^N,u] INTER segment[u,b2] = {u}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{{u:real^N},s1}`;
                   `{{u:real^N},s2}`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING] THEN
    SUBGOAL_THEN `{{u:real^N},s1} INTER {{u},s2} = {{u}}` SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `t:real^N->bool` THEN
      ASM_CASES_TAC `t = {u:real^N}` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `t:real^N->bool = s1` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING; CONVEX_HULL_SING] THEN
      REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN MESON_TAC[SEGMENT_SYM]];
    ALL_TAC] THEN
  ABBREV_TAC `h = linepath(b1:real^N,u) ++ linepath(u,b2)` THEN
  SUBGOAL_THEN
   `arc (h:real^1->real^N) /\ pl_map_on (interval[vec 0,vec 1]) h /\
    pathstart h = b1 /\ pathfinish h = b2 /\
    path_image h = segment[b1,u] UNION segment[u,b2]`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "h" THEN
    SIMP_TAC[ARC_JOIN_EQ; PATHSTART_LINEPATH; PATHFINISH_LINEPATH; PATHSTART_JOIN;
             PATHFINISH_JOIN; PATH_IMAGE_JOIN; PATH_IMAGE_LINEPATH] THEN
    ASM_SIMP_TAC[ARC_LINEPATH] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[SUBSET_REFL];
      EXPAND_TAC "h" THEN MATCH_MP_TAC MOI_PL2_PL_JOINPATHS THEN
      REWRITE_TAC[PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
      CONJ_TAC THEN MATCH_MP_TAC MOI_PL2_PL_LINEPATH THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN
      REWRITE_TAC[POLYTOPE_INTERVAL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^1->real^N`; `h:real^1->real^N`] MOI_PL2_ARC_IN_LOOP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[ISPECL [`u:real^N`; `b1:real^N`] (CONJUNCT1 SEGMENT_SYM)] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^1->real^N` STRIP_ASSUME_TAC) THEN
  (* the link part meets the two segments only at b1, b2 *)
  SUBGOAL_THEN
   `moi_fcl_ldual c e INTER (segment[b1:real^N,u] UNION segment[u,b2]) = {b1,b2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC;
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_INTER; IN_UNION; ENDS_IN_SEGMENT] THEN
      REWRITE_TAC[MOI_FCL_IN_DUAL] THEN CONJ_TAC THENL
       [EXISTS_TAC `{s1:real^N->bool}`; EXISTS_TAC `{s2:real^N->bool}`] THEN
      ASM_SIMP_TAC[NOT_INSERT_EMPTY; IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING;
                   FORALL_IN_INSERT; NOT_IN_EMPTY; MOI_FTA_CHAIN_SING]] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_UNION] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~({u:real^N} IN f)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `!t:real^N->bool. t IN f ==> e SUBSET t /\ ~(t = e)` THEN
      DISCH_THEN(MP_TAC o SPEC `{u:real^N}`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                     `{{u:real^N},s1}`] MOI_BAR_CHAIN_HULL_INTER) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING] THEN
      REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(y:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER {{u},s1}))`
      MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN
        ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f:(real^N->bool)->bool) INTER {{u},s1} SUBSET {s1}` MP_TAC THENL
       [UNDISCH_TAC `~({u:real^N} IN f)` THEN SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `simplex_barycentre:(real^N->bool)->real^N`
        IMAGE_SUBSET)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `convex:(real^N->bool)->bool` HULL_MONO)) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING] THEN SET_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                     `{{u:real^N},s2}`] MOI_BAR_CHAIN_HULL_INTER) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FTA_BARY_SING] THEN
      REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(y:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER {{u},s2}))`
      MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN
        ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f:(real^N->bool)->bool) INTER {{u},s2} SUBSET {s2}` MP_TAC THENL
       [UNDISCH_TAC `~({u:real^N} IN f)` THEN SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `simplex_barycentre:(real^N->bool)->real^N`
        IMAGE_SUBSET)) THEN
      DISCH_THEN(MP_TAC o MATCH_MP (ISPEC `convex:(real^N->bool)->bool` HULL_MONO)) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fcl_ldual c e = path_image (k:real^1->real^N)` SUBST1_TAC THENL
   [UNDISCH_TAC `path_image (g:real^1->real^N) =
                 moi_fcl_ldual c e UNION segment[u,b1] UNION segment[u,b2]` THEN
    REWRITE_TAC[ISPECL [`u:real^N`; `b1:real^N`] (CONJUNCT1 SEGMENT_SYM)] THEN
    UNDISCH_TAC `path_image (h:real^1->real^N) UNION path_image k = path_image g` THEN
    UNDISCH_TAC `path_image (h:real^1->real^N) INTER path_image k =
                 {pathstart h,pathfinish h}` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `moi_fcl_ldual c e INTER (segment[b1:real^N,u] UNION segment[u,b2]) = {b1,b2}` THEN
    REWRITE_TAC[ISPECL [`u:real^N`; `b1:real^N`] (CONJUNCT1 SEGMENT_SYM);
                ISPECL [`b2:real^N`; `u:real^N`] (CONJUNCT1 SEGMENT_SYM)] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `k:real^1->real^N` MOI_FCL_ARC_CELL) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[INSERT_AC]);;

(* ========================================================================= *)
(* The cells at boundary triangles and the boundary cells at boundary edges. *)
(* ========================================================================= *)

let MOI_FCL_TRIANGLE_FACTS = prove
 (`!(c:(real^N->bool)->bool) s.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     s IN boundary_complex c /\ aff_dim s = &2
     ==> ?r. r IN c /\ aff_dim r = &3 /\ s SUBSET r /\
             (!t. t IN c /\ s SUBSET t /\ ~(t = s) ==> t = r) /\
             moi_fcl_ldual c s = {simplex_barycentre r} /\
             moi_fcl_ldual (boundary_complex c) s = {} /\
             moi_fcl_dual (boundary_complex c) s = {simplex_barycentre s}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  ABBREV_TAC `l = boundary_complex (c:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool) /\ l SUBSET c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) c` THEN
    SIMP_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN c /\ s SUBSET complex_boundary c`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(s:real^N->bool) IN l` THEN EXPAND_TAC "l" THEN
    REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN c /\ s SUBSET t /\ ~(t = s) ==> aff_dim t = &3`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(INT_ARITH `a <= &3 /\ &2 < a ==> a:int = &3`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[CM_WB_DIM]; ALL_TAC] THEN
    UNDISCH_TAC `aff_dim (s:real^N->bool) = &2` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_CONVEX];
      MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {r | r IN c /\ aff_dim r = &3 /\ (s:real^N->bool) SUBSET r} = 1`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `~(relative_interior (s:real^N->bool) = {})` MP_TAC THENL
     [SUBGOAL_THEN `convex (s:real^N->bool) /\ ~(s = {})` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_CONVEX];
          DISCH_THEN SUBST_ALL_TAC THEN
          RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
          ASM_MESON_TAC[INT_ARITH `~(--(&1):int = &2)`]];
        ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
    SUBGOAL_THEN `(x:real^N) IN complex_boundary c` MP_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[MOI_FCL_CB_TRIANGLES; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET t` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FRN_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `t:real^N->bool = s` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `!t:real^N->bool. t IN c /\ s SUBSET t /\ ~(t = s) ==> aff_dim t = &3` THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {r | r IN c /\ aff_dim r = &3 /\ (s:real^N->bool) SUBSET r}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{r | r IN c /\ aff_dim r = &3 /\ (s:real^N->bool) SUBSET r}`
    MOI_FM3_CARD_EQ_1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `r:real^N->bool`) THEN EXISTS_TAC `r:real^N->bool` THEN
  SUBGOAL_THEN `(r:real^N->bool) IN c /\ aff_dim r = &3 /\ s SUBSET r` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    DISCH_THEN(MP_TAC o SPEC `r:real^N->bool`) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN c /\ s SUBSET t /\ ~(t = s) ==> t = r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `t IN {r | r IN c /\ aff_dim r = &3 /\ (s:real^N->bool) SUBSET r}`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ASM_REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((r:real^N->bool) IN l) /\ ~(r:real^N->bool = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `r:real^N->bool`] MOI_FRN_SA_CM_DIM) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
      ASM_MESON_TAC[INT_ARITH `~(--(&1):int = &3)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r:real^N->bool = s)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim (r:real^N->bool) = &3` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim (s:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:(real^N->bool)->bool. moi_bar_chain c f /\ ~(f = {}) /\
        (!t. t IN f ==> s SUBSET t /\ ~(t = s)) ==> f = {r}`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:(real^N->bool)->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!f a:A. ~(f = {}) /\ (!t. t IN f ==> t = a) ==> f = {a}`) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC `!t:real^N->bool. t IN c /\ s SUBSET t /\ ~(t = s) ==> t = r` THEN
    DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `!t:real^N->bool. t IN f ==> s SUBSET t /\ ~(t = s)` THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:(real^N->bool)->bool. moi_bar_chain l f /\ ~(f = {}) /\
        (!t. t IN f ==> s SUBSET t) ==> f = {s}`
  ASSUME_TAC THENL
   [X_GEN_TAC `f:(real^N->bool)->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!f a:A. ~(f = {}) /\ (!t. t IN f ==> t = a) ==> f = {a}`) THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(t:real^N->bool) IN l` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_bar_chain l (f:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain; SUBSET] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `t:real^N->bool = r` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `!t:real^N->bool. t IN c /\ s SUBSET t /\ ~(t = s) ==> t = r` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[]];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN
      REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `f = {r:real^N->bool}` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `{r:real^N->bool}`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(y:real^N) IN convex hull IMAGE simplex_barycentre {r}` THEN
        REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING]];
      REWRITE_TAC[SING_SUBSET; MOI_FCL_IN_DUAL] THEN EXISTS_TAC `{r:real^N->bool}` THEN
      REWRITE_TAC[NOT_INSERT_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                  IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN ASM_REWRITE_TAC[]];
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[NOT_IN_EMPTY; MOI_FCL_IN_DUAL] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `f = {r:real^N->bool}` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `{r:real^N->bool}`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
      EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_bar_chain l (f:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[moi_bar_chain; SING_SUBSET];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN
      REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `f = {s:real^N->bool}` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term ((=) `{s:real^N->bool}`)) (concl th))) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(y:real^N) IN convex hull IMAGE simplex_barycentre {s}` THEN
        REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING]];
      REWRITE_TAC[SING_SUBSET; MOI_FCL_IN_DUAL] THEN EXISTS_TAC `{s:real^N->bool}` THEN
      REWRITE_TAC[NOT_INSERT_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY; SUBSET_REFL;
                  IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING] THEN
      MATCH_MP_TAC MOI_FTA_CHAIN_SING THEN ASM_REWRITE_TAC[]]]);;

let MOI_FCL_PL_SPHERE_0 = prove
 (`!p q:real^N. ~(p = q) ==> pl_sphere 0 {p,q}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  MAP_EVERY EXISTS_TAC [`segment[p:real^N,q]`; `\x:real^N. x`; `\x:real^N. x`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_PL2_SIMPLEX_1] THEN MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier(segment[p:real^N,q]) = {p,q}` SUBST1_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SIMP_TAC[RELATIVE_FRONTIER_OF_CONVEX_HULL; AFFINE_INDEPENDENT_2] THEN
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_2] THEN
    ASM_SIMP_TAC[SET_RULE `~(p:real^N = q) ==> {p,q} DELETE p = {q} /\ {p,q} DELETE q = {p}`;
                 CONVEX_HULL_SING] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{{p:real^N},{q}}` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
              POLYTOPE_SING; UNIONS_2] THEN
  SET_TAC[]);;

(* The boundary cell at a boundary edge: two segments from the barycentre  *)
(* of the edge to the barycentres of the two boundary triangles.           *)

let MOI_FCL_EDGE_BD_CELL = prove
 (`!(c:(real^N->bool)->bool) e s1 s2.
     combinatorial_manifold_with_boundary 3 c /\ e IN boundary_complex c /\
     ~(e = {}) /\
     ~(simplex_barycentre s1 = simplex_barycentre s2) /\
     moi_fcl_ldual (boundary_complex c) e =
       {simplex_barycentre s1,simplex_barycentre s2}
     ==> moi_fcl_dual (boundary_complex c) e =
           UNIONS {segment[simplex_barycentre e,y] | y |
                   y IN {simplex_barycentre s1,simplex_barycentre s2}} /\
         pl_cell_with_boundary 1 (moi_fcl_dual (boundary_complex c) e)
           {simplex_barycentre s1,simplex_barycentre s2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPECL [`boundary_complex c:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FCL_DUAL_CONE) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`boundary_complex c:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FCL_LDUAL_RAYS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`0`; `{simplex_barycentre s1,simplex_barycentre (s2:real^N->bool)}`;
                 `simplex_barycentre (e:real^N->bool)`] MOI_FTA_CONE_CELL) THEN
  ASM_SIMP_TAC[MOI_FCL_PL_SPHERE_0] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]);;

(* ========================================================================= *)
(* The level pieces of the dual cells.  With the weight sigma of the         *)
(* subcomplex l (moi_frn_sig: simplexwise affine on the first derived, 1 at  *)
(* the barycentres of simplices of l, 0 at the others), the collar piece     *)
(* over s is W(s) = D(s) INTER {sigma >= 1/2} and its top is T(s) = D(s)     *)
(* INTER {sigma = 1/2}.                                                      *)
(* ========================================================================= *)

let moi_fcl_wc = new_definition
 `moi_fcl_wc (c:(real^N->bool)->bool) (h:real^N->real^1) s =
    moi_fcl_dual c s INTER {x | &1 / &2 <= drop(h x)}`;;

let moi_fcl_tc = new_definition
 `moi_fcl_tc (c:(real^N->bool)->bool) (h:real^N->real^1) s =
    moi_fcl_dual c s INTER {x | drop(h x) = &1 / &2}`;;

let moi_fcl_gc = new_definition
 `moi_fcl_gc (c:(real^N->bool)->bool) (h:real^N->real^1) s =
    moi_fcl_tc c h s UNION (moi_fcl_wc c h s INTER moi_fcl_ldual c s)`;;

(* The weight at a barycentre. *)

let MOI_FCL_SIG_BARY = prove
 (`!(c:(real^N->bool)->bool) l h t.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h /\
     t IN c /\ ~(t = {})
     ==> drop(h(simplex_barycentre t)) = if t IN l then &1 else &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(simplex_barycentre t:real^N) IN UNIONS l <=> t IN l` ASSUME_TAC THENL
   [EQ_TAC THENL
     [DISCH_TAC THEN MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`;
                            `simplex_barycentre t:real^N`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
      ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX];
      DISCH_TAC THEN REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
      ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]];
    ALL_TAC] THEN
  COND_CASES_TAC THENL
   [MATCH_MP_TAC MOI_FRN_SIG_ONE THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `{simplex_barycentre t:real^N}`;
                 `simplex_barycentre t:real^N`] MOI_FRN_SIG_SIMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_SING] THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `{t:real^N->bool}` THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; IMAGE_CLAUSES; CONVEX_HULL_SING];
    ALL_TAC] THEN
  REWRITE_TAC[EXTREME_POINT_OF_SING] THEN
  SUBGOAL_THEN `{v:real^N | v = simplex_barycentre t /\ v IN UNIONS l} = {}`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUM_CLAUSES] THEN MESON_TAC[]);;

(* On the derived simplex of a chain the weight is the global affine        *)
(* function with the same vertex values.                                    *)

let MOI_FCL_SIG_AFFINE_FN = prove
 (`!(c:(real^N->bool)->bool) l h f.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h /\
     moi_bar_chain c f /\ ~(f = {})
     ==> ?Fl. (!x y u. Fl((&1 - u) % x + u % y) = (&1 - u) * Fl x + u * Fl y) /\
             (!t. t IN f ==> Fl(simplex_barycentre t) = if t IN l then &1 else &0) /\
             (!x. x IN convex hull (IMAGE simplex_barycentre f) ==> Fl x = drop(h x))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE simplex_barycentre (f:(real^N->bool)->bool)`;
                 `\a:real^N. a IN UNIONS l`] MOI_FTA_LEVEL_FN) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fl:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!t. t IN f ==> (Fl:real^N->real)(simplex_barycentre t) = drop(h(simplex_barycentre t)) /\
                   Fl(simplex_barycentre t) = if t IN l then &1 else &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `t:real^N->bool`] MOI_BAR_CHAIN_ELEMENT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_TAC `n:int`))) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `t:real^N->bool`] MOI_FCL_SIG_BARY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(simplex_barycentre t:real^N) IN UNIONS l <=> t IN l`
    ASSUME_TAC THENL
     [EQ_TAC THENL
       [DISCH_TAC THEN MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
        MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`;
                              `simplex_barycentre t:real^N`] THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
        EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
        EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `simplex_barycentre t:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `UNIONS (l:(real^N->bool)->bool)`)) (concl th))) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `Fl:real^N->real` THEN ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool)) SUBSET
    {x | x IN convex hull (IMAGE simplex_barycentre f) /\
         (Fl:real^N->real) x = drop(h x)}`
  (fun th -> MP_TAC th THEN SET_TAC[]) THEN
  MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Fl:real^N->real`)) (concl th) &&
        can (find_term ((=) `h:real^N->real^1`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(ACCEPT_TAC o CONJUNCT1)];
    ALL_TAC] THEN
  REWRITE_TAC[CONVEX_ALT; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`; `u:real`] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] CONVEX_CONVEX_HULL) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
  MATCH_MP_TAC MOI_FRN_SIG_AFF THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                        `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))`] THEN
  ASM_REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[]);;

(* The weight vanishes on the dual cells of simplices outside l. *)

let MOI_FCL_SIG_ZERO_DUAL = prove
 (`!(c:(real^N->bool)->bool) l h u x.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h /\
     u IN c /\ ~(u IN l) /\ x IN moi_fcl_dual c u
     ==> drop(h x) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN moi_fcl_dual c u` THEN REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `f:(real^N->bool)->bool`] MOI_FCL_SIG_AFFINE_FN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fl:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN f ==> ~(t IN l)` ASSUME_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN REPEAT STRIP_TAC THEN
    UNDISCH_TAC `~((u:real^N->bool) IN l)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) c` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain; SUBSET] THEN ASM_MESON_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM(MATCH_MP th
    (ASSUME `(x:real^N) IN convex hull IMAGE simplex_barycentre f`))]) THEN
  MP_TAC(ISPECL [`Fl:real^N->real`; `&0`;
                 `IMAGE simplex_barycentre (f:(real^N->bool)->bool)`]
    MOI_FTA_LEVEL_HULL) THEN
  ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN ANTS_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN ASM_SIMP_TAC[];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_FCL_WC_EMPTY = prove
 (`!(c:(real^N->bool)->bool) l h u.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h /\
     u IN c /\ ~(u IN l)
     ==> moi_fcl_wc c h u = {} /\ moi_fcl_tc c h u = {}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_fcl_wc; moi_fcl_tc; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `(x:real^N) IN moi_fcl_dual c u` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `u:real^N->bool`; `x:real^N`]
    MOI_FCL_SIG_ZERO_DUAL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The link part of W(s) is the union of the W(t) for t in l above s. *)

let MOI_FCL_LEVEL_LDUAL = prove
 (`!(c:(real^N->bool)->bool) l h s Q.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h /\
     (!x. x IN Q ==> ~(drop(h x) = &0))
     ==> (moi_fcl_dual c s INTER Q) INTER moi_fcl_ldual c s =
           UNIONS {moi_fcl_dual c t INTER Q | t |
                   t IN l /\ ~(t = {}) /\ s SUBSET t /\ ~(t = s)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  REWRITE_TAC[MOI_FCL_LDUAL_EQ] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (X_CHOOSE_THEN `w:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    SUBGOAL_THEN `(x:real^N) IN moi_fcl_dual c u` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^N->bool) IN l` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:real^N->real^1`; `u:real^N->bool`; `x:real^N`]
        MOI_FCL_SIG_ZERO_DUAL) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `moi_fcl_dual c u INTER (Q:real^N->bool)` THEN
    REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `u:real^N->bool`]
        MOI_FCL_DUAL_MONO) THEN ASM SET_TAC[];
      EXISTS_TAC `moi_fcl_dual c (u:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `u:real^N->bool` THEN ASM SET_TAC[]]]);;

let MOI_FCL_WC_LDUAL = prove
 (`!(c:(real^N->bool)->bool) l h s.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h
     ==> moi_fcl_wc c h s INTER moi_fcl_ldual c s =
           UNIONS {moi_fcl_wc c h t | t | t IN l /\ ~(t = {}) /\ s SUBSET t /\ ~(t = s)} /\
         moi_fcl_tc c h s INTER moi_fcl_ldual c s =
           UNIONS {moi_fcl_tc c h t | t | t IN l /\ ~(t = {}) /\ s SUBSET t /\ ~(t = s)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_fcl_wc; moi_fcl_tc] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^1`; `s:real^N->bool`;
      `{x:real^N | &1 / &2 <= drop(h x)}`] MOI_FCL_LEVEL_LDUAL);
    MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
      `h:real^N->real^1`; `s:real^N->bool`;
      `{x:real^N | drop(h x) = &1 / &2}`] MOI_FCL_LEVEL_LDUAL)] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REAL_ARITH_TAC);;

(* W(s) is the cone from the barycentre of s over Gamma(s). *)

let MOI_FCL_WC_CONE = prove
 (`!(c:(real^N->bool)->bool) l h s.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h /\
     s IN l /\ ~(s = {}) /\ ~(moi_fcl_ldual c s = {})
     ==> (!y. y IN moi_fcl_ldual c s
              ==> ?!r. &0 < r /\ r <= &1 /\
                       simplex_barycentre s + r % (y - simplex_barycentre s) IN
                       moi_fcl_gc c h s) /\
         ~(simplex_barycentre s IN moi_fcl_gc c h s) /\
         (!x y. x IN moi_fcl_gc c h s /\ y IN moi_fcl_gc c h s /\
                y IN segment[simplex_barycentre s,x] ==> y = x) /\
         moi_fcl_wc c h s =
         UNIONS {segment[simplex_barycentre s,x] | x | x IN moi_fcl_gc c h s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_LDUAL_RAYS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_DUAL_CONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_fcl_gc] THEN
  MATCH_MP_TAC MOI_FTA_CONE_FROM_RAYS THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_fcl_wc] THEN ASM SET_TAC[];
    REWRITE_TAC[moi_fcl_tc] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  UNDISCH_TAC `(y:real^N) IN moi_fcl_ldual c s` THEN REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain c ((s:real^N->bool) INSERT g)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain c (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; FINITE_INSERT] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `(s:real^N->bool) INSERT g`] MOI_FCL_SIG_AFFINE_FN) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fl:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(Fl:real^N->real)(simplex_barycentre s) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `!t:real^N->bool. t IN s INSERT g
                   ==> (Fl:real^N->real)(simplex_barycentre t) =
                       (if t IN l then &1 else &0)` THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE simplex_barycentre ((s:real^N->bool) INSERT g)) SUBSET
    moi_fcl_dual c s`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `(s:real^N->bool) INSERT g` THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; FORALL_IN_INSERT; SUBSET_REFL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull (IMAGE simplex_barycentre ((s:real^N->bool) INSERT g))`;
    `Fl:real^N->real`] THEN
  ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT];
    MP_TAC(ISPECL [`convex:(real^N->bool)->bool`;
                   `IMAGE simplex_barycentre (g:(real^N->bool)->bool)`;
                   `IMAGE simplex_barycentre ((s:real^N->bool) INSERT g)`] HULL_MONO) THEN
    ANTS_TAC THENL [REWRITE_TAC[IMAGE_CLAUSES] THEN SET_TAC[]; ASM SET_TAC[]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN moi_fcl_dual c s /\ (Fl:real^N->real) x = drop(h x)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[moi_fcl_wc; IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN moi_fcl_dual c s /\ (Fl:real^N->real) x = drop(h x)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    REWRITE_TAC[moi_fcl_tc; IN_INTER; IN_ELIM_THM] THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The level-derived complex of a dual cell.  lcx c s: the simplices of the  *)
(* first derived in the link part of the dual cell of s; kcx c l s: its      *)
(* derived subdivision with the level points moi_fta_lev l                   *)
(* (MOI_FTA_DERIVED_HOMEO of pc_moi_fnd_tubea), a finite simplicial complex  *)
(* covering the link part of the dual cell.                                  *)
(* ========================================================================= *)

(* Points chosen in the relative interiors of the members of a chain are    *)
(* affinely independent (generalises MOI_BAR_CHAIN_AFFINE_INDEPENDENT).     *)

let MOI_FCL_RELINT_CHAIN_INDEP = prove
 (`!c f (d:(real^N->bool)->real^N).
        moi_bar_complex c /\ moi_bar_chain c f /\
        (!t. t IN f ==> d t IN relative_interior t)
        ==> ~affine_dependent (IMAGE d f)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN
  WF_INDUCT_TAC `CARD(f:(real^N->bool)->bool)` THEN STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; AFFINE_INDEPENDENT_EMPTY] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(f:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (d:(real^N->bool)->real^N) f =
    d (UNIONS f) INSERT IMAGE d (f DELETE UNIONS f)`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [GSYM(MATCH_MP INSERT_DELETE th)]) THEN
    REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_bar_chain c ((f:(real^N->bool)->bool) DELETE UNIONS f)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[DELETE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    ASM_SIMP_TAC[IN_DELETE; CARD_DELETE] THEN
    MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n - 1 < n`) THEN
    ASM_SIMP_TAC[CARD_EQ_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `(f:(real^N->bool)->bool) DELETE UNIONS f = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; AFFINE_HULL_EMPTY; NOT_IN_EMPTY] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `(f:(real^N->bool)->bool) DELETE UNIONS f`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `affine hull (IMAGE (d:(real^N->bool)->real^N) (f DELETE UNIONS f)) SUBSET
    affine hull (UNIONS ((f:(real^N->bool)->bool) DELETE UNIONS f))`
  MP_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real^N->bool` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(d:(real^N->bool)->real^N) t IN t` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `~((x:real^N) IN t) ==> s SUBSET t ==> ~(x IN s)`) THEN
  SUBGOAL_THEN `?n. n simplex (UNIONS f:real^N->bool)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `UNIONS f:real^N->bool`] MOI_BAR_CHAIN_ELEMENT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS f:real^N->bool`;
                 `UNIONS ((f:(real^N->bool)->bool) DELETE UNIONS f)`]
    AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SIMPLEX_IMP_CONVEX THEN EXISTS_TAC `n:int` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_BAR_CHAIN_FACE_OF_MAX THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `!x s a:real^N->bool. x IN s DELETE a ==> x IN s`) THEN
      EXISTS_TAC `UNIONS f:real^N->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC(MESON[IN_DELETE]
        `!x s a:real^N->bool. x IN s DELETE a ==> ~(x = a)`) THEN
      EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  DISCH_THEN(MP_TAC o SPEC `(d:(real^N->bool)->real^N) (UNIONS f)`) THEN
  ASM_SIMP_TAC[]);;

(* The first-derived simplices of the link part of the dual cell of s.     *)

let moi_fcl_lcx = new_definition
 `moi_fcl_lcx (c:(real^N->bool)->bool) (s:real^N->bool) =
    {convex hull (IMAGE simplex_barycentre g) | g |
     moi_bar_chain c g /\ !t. t IN g ==> s SUBSET t /\ ~(t = s)}`;;

let MOI_FCL_LCX_FACTS = prove
 (`!(c:(real^N->bool)->bool) s.
     FINITE c /\ moi_bar_complex c
     ==> FINITE (moi_fcl_lcx c s) /\ moi_bar_complex (moi_fcl_lcx c s) /\
         moi_fcl_lcx c s SUBSET barycentric_subdivision c /\
         UNIONS (moi_fcl_lcx c s) = moi_fcl_ldual c s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_fcl_lcx c (s:real^N->bool) SUBSET barycentric_subdivision c`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; moi_fcl_lcx; FORALL_IN_GSPEC; MOI_BAR_IN_SUBDIVISION] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (c:(real^N->bool)->bool))`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_COMPLEX]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; MOI_BAR_SUBDIVISION_FINITE];
    REWRITE_TAC[moi_bar_complex] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SUBSET];
      MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `m:real^N->bool`] THEN
      REWRITE_TAC[moi_fcl_lcx; IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
        MOI_BAR_CHAIN_AFFINE_INDEPENDENT) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `{t:real^N->bool | t IN g /\ simplex_barycentre t IN q}` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
        ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM SET_TAC[]];
      MAP_EVERY X_GEN_TAC [`m:real^N->bool`; `m':real^N->bool`] THEN STRIP_TAC THEN
      UNDISCH_TAC `moi_bar_complex (barycentric_subdivision (c:(real^N->bool)->bool))` THEN
      REWRITE_TAC[moi_bar_complex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN ASM SET_TAC[]];
    REWRITE_TAC[moi_fcl_lcx; moi_fcl_ldual] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(x:real^N) IN m` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      MESON_TAC[]]]);;

(* The level-derived subdivision of lcx c s. *)

let moi_fcl_kcx = new_definition
 `moi_fcl_kcx (c:(real^N->bool)->bool) (l:(real^N->bool)->bool) (s:real^N->bool) =
    {convex hull (IMAGE (moi_fta_lev l) fs) | fs |
     moi_bar_chain (moi_fcl_lcx c s) fs}`;;

let MOI_FCL_KCX_COMPLEX = prove
 (`!(c:(real^N->bool)->bool) l s.
     FINITE c /\ moi_bar_complex c
     ==> simplicial_complex (moi_fcl_kcx c l s) /\
         UNIONS (moi_fcl_kcx c l s) = moi_fcl_ldual c s /\
         (!fs. moi_bar_chain (moi_fcl_lcx c s) fs
               ==> ~affine_dependent (IMAGE (moi_fta_lev l) fs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_LCX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `L = moi_fcl_lcx c (s:real^N->bool)` THEN
  SUBGOAL_THEN
   `!m:real^N->bool. m IN L /\ ~(m = {}) ==> moi_fta_lev l m IN relative_interior m`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?n. n simplex (m:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FTA_LEV_RELINT THEN EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!fs. moi_bar_chain (L:(real^N->bool)->bool) fs ==> ~affine_dependent (IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) fs)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FCL_RELINT_CHAIN_INDEP THEN
    EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `moi_bar_chain (L:(real^N->bool)->bool) (fs:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `moi_fta_lev (l:(real^N->bool)->bool)`]
    MOI_FTA_DERIVED_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `th:real^N->real^N` (X_CHOOSE_THEN `th':real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(!x. x IN UNIONS L ==> (th':real^N->real^N) (th x) = x) /\
    IMAGE (th:real^N->real^N) (UNIONS L) = UNIONS L`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!fs. moi_bar_chain (L:(real^N->bool)->bool) fs
         ==> convex hull (IMAGE simplex_barycentre fs) SUBSET UNIONS (L:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPEC `L:(real^N->bool)->bool` MOI_BAR_UNIONS_SUBDIVISION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `fs:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!fs fs'. moi_bar_chain (L:(real^N->bool)->bool) fs /\ moi_bar_chain (L:(real^N->bool)->bool) fs'
             ==> convex hull (IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) fs) INTER
                 convex hull (IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) fs') =
                 convex hull (IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) (fs INTER fs'))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `moi_bar_chain (L:(real^N->bool)->bool) ((fs:(real^N->bool)->bool) INTER fs')` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `fs:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `fs:(real^N->bool)->bool`;
                   `fs':(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `convex hull (IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) fs) =
      IMAGE (th:real^N->real^N) (convex hull (IMAGE simplex_barycentre fs)) /\
      convex hull (IMAGE (moi_fta_lev l) fs') =
      IMAGE th (convex hull (IMAGE simplex_barycentre fs')) /\
      convex hull (IMAGE (moi_fta_lev l) (fs INTER fs')) =
      IMAGE th (convex hull (IMAGE simplex_barycentre (fs INTER fs')))`
    (fun th0 -> REWRITE_TAC[th0]) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE
     `!(f:real^N->real^N) g A B U.
        (!x. x IN U ==> g (f x) = x) /\ A SUBSET U /\ B SUBSET U
        ==> IMAGE f A INTER IMAGE f B = IMAGE f (A INTER B)`) THEN
    MAP_EVERY EXISTS_TAC [`th':real^N->real^N`; `UNIONS L:real^N->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!fs fs'. moi_bar_chain (L:(real^N->bool)->bool) fs /\ fs' SUBSET fs
             ==> convex hull (IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) fs') face_of
                 convex hull (IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) (fs:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~affine_dependent (IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) fs)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) (fs':(real^N->bool)->bool)` THEN
    ASM_SIMP_TAC[IMAGE_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fcl_kcx c l (s:real^N->bool) =
                IMAGE (IMAGE (th:real^N->real^N)) (barycentric_subdivision L)`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_fcl_kcx] THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N->bool` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; MOI_BAR_IN_SUBDIVISION] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `fs:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre (fs:(real^N->bool)->bool))` THEN
      ASM_SIMP_TAC[] THEN EXISTS_TAC `fs:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` (CONJUNCTS_THEN2 SUBST1_TAC
        (X_CHOOSE_THEN `fs:(real^N->bool)->bool` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `fs:(real^N->bool)->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[GSYM IMAGE_UNIONS] THEN
    ASM_SIMP_TAC[MOI_BAR_UNIONS_SUBDIVISION] THEN ASM_MESON_TAC[]] THEN
  REWRITE_TAC[MOI_BAR_SIMPLICIAL_COMPLEX] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[moi_bar_complex] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_fcl_kcx; FORALL_IN_GSPEC] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `fs:(real^N->bool)->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `&(CARD(IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) (fs:(real^N->bool)->bool))) - &1:int` THEN
    REWRITE_TAC[simplex] THEN
    EXISTS_TAC `IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) (fs:(real^N->bool)->bool)` THEN
    ASM_SIMP_TAC[] THEN INT_ARITH_TAC;
    MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `m:real^N->bool`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `fs:(real^N->bool)->bool` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~affine_dependent (IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) fs)`
    ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{t:real^N->bool | t IN fs /\ moi_fta_lev l t IN q}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `fs:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN ASM SET_TAC[]];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `fs:(real^N->bool)->bool` THEN DISCH_TAC THEN
    X_GEN_TAC `fs':(real^N->bool)->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `convex hull (IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) fs) INTER
      convex hull (IMAGE (moi_fta_lev l) fs') =
      convex hull (IMAGE (moi_fta_lev l) (fs INTER fs'))`
    SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[INTER_SUBSET]]);;

(* The vertex sets of the level-derived complex are the level images of    *)
(* nonempty chains.                                                         *)

let MOI_FCL_KCX_VSETS = prove
 (`!(c:(real^N->bool)->bool) l s S.
     FINITE c /\ moi_bar_complex c /\ S IN moi_real_vertex_sets (moi_fcl_kcx c l s)
     ==> ?fs. moi_bar_chain (moi_fcl_lcx c s) fs /\ ~(fs = {}) /\
              S = IMAGE (moi_fta_lev l) fs`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_FCL_KCX_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `S IN moi_real_vertex_sets (moi_fcl_kcx c l (s:real^N->bool))` THEN
  REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  REWRITE_TAC[moi_fcl_kcx; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `fs:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `S = IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) fs` ASSUME_TAC THENL
   [MP_TAC(ISPEC `S:real^N->bool` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    MP_TAC(ISPEC `IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) fs`
      EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `fs:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `~(S:real^N->bool = {})` THEN ASM_REWRITE_TAC[IMAGE_CLAUSES]);;

(* ========================================================================= *)
(* The base Gamma(s) = moi_fcl_gc c h s of the cone W(s) is PL homeomorphic  *)
(* to the link part of the dual cell of s, by the section lemma              *)
(* MOI_FCL_SECTION on the level-derived complex, with lift factor 1 at       *)
(* points of weight >= 1/2 and 1/2 elsewhere; the homeomorphism maps the     *)
(* boundary part (in l) onto itself.                                         *)
(* ========================================================================= *)

let MOI_FCL_BARY_IN_L = prove
 (`!(c:(real^N->bool)->bool) l t.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ t IN c /\ ~(t = {})
     ==> (simplex_barycentre t IN UNIONS l <=> t IN l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`;
                          `simplex_barycentre t:real^N`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX];
    DISCH_TAC THEN REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
    ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]]);;

(* Along a chain of faces of a simplex with 0/1 vertex values, the level    *)
(* points have values 0, 1/2 or 1, all on one side of 1/2.                 *)

let MOI_FCL_CHAIN_LEV_SIDE = prove
 (`!l (Fl:real^N->real) V fs.
     ~affine_dependent V /\
     (!x y u. Fl((&1 - u) % x + u % y) = (&1 - u) * Fl x + u * Fl y) /\
     (!a. a IN V ==> Fl a = if a IN UNIONS l then &1 else &0) /\
     moi_bar_chain {r | r face_of convex hull V} fs
     ==> (!r. r IN fs ==> Fl(moi_fta_lev l r) = &0 \/
                          Fl(moi_fta_lev l r) = &1 / &2 \/
                          Fl(moi_fta_lev l r) = &1) /\
         ((!r. r IN fs ==> &1 / &2 <= Fl(moi_fta_lev l r)) \/
          (!r. r IN fs ==> Fl(moi_fta_lev l r) <= &1 / &2))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. r IN fs
        ==> Fl(moi_fta_lev l r) =
            if (?a. a extreme_point_of r /\ a IN UNIONS l) /\
               (?b. b extreme_point_of r /\ ~(b IN UNIONS l))
            then &1 / &2
            else if (?a:real^N. a extreme_point_of r /\ a IN UNIONS l) then &1 else &0`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FTA_FACE_LEV_VALUE THEN EXISTS_TAC `V:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_bar_chain {r | r face_of convex hull V} (fs:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    REPEAT COND_CASES_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?r1:real^N->bool. r1 IN fs /\ ~(?a. a extreme_point_of r1 /\ a IN UNIONS l)`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `r1:real^N->bool` STRIP_ASSUME_TAC) THEN
    DISJ2_TAC THEN X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC `?a:real^N. a extreme_point_of r /\ a IN UNIONS l` THEN
    ASM_REWRITE_TAC[] THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    SUBGOAL_THEN `?b:real^N. b extreme_point_of r /\ ~(b IN UNIONS l)`
      (fun th -> REWRITE_TAC[th]) THENL [ALL_TAC; REAL_ARITH_TAC] THEN
    MATCH_MP_TAC MOI_FTA_CHAIN_EXT_UP THEN
    MAP_EVERY EXISTS_TAC [`convex hull V:real^N->bool`;
                          `fs:(real^N->bool)->bool`; `r1:real^N->bool`] THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
    MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
    ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
    DISJ1_TAC THEN X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `?a:real^N. a extreme_point_of r /\ a IN UNIONS l`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC]);;

(* The lift factor: 1 at points of weight >= 1/2, 1/2 elsewhere. *)

let moi_fcl_gf = new_definition
 `moi_fcl_gf (h:real^N->real^1) (z:real^N) =
    if &1 / &2 <= drop(h z) then &1 else &1 / &2`;;

let MOI_FCL_GF_RANGE = prove
 (`!(h:real^N->real^1) z. &0 < moi_fcl_gf h z /\ moi_fcl_gf h z <= &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fcl_gf] THEN COND_CASES_TAC THEN
  REAL_ARITH_TAC);;

(* Every ray from v through a point of a simplex meets its lift. *)

let MOI_FCL_LIFT_RAY = prove
 (`!S (v:real^N) g y.
     FINITE S /\ y IN convex hull S /\ (!z. z IN S ==> &0 < g z /\ g z <= &1)
     ==> ?r. &0 < r /\ r <= &1 /\
             v + r % (y - v) IN convex hull (IMAGE (\z. v + g z % (z - v)) S)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN convex hull S` THEN
  GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [CONVEX_HULL_FINITE] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `Q = sum S (\z:real^N. u z / g z)` THEN
  SUBGOAL_THEN `&1 <= Q` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `sum S (u:real^N->real)` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    EXPAND_TAC "Q" THEN MATCH_MP_TAC SUM_LE THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `&0 < (g:real^N->real) z /\ g z <= &1 /\ &0 <= u z`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN
    GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_RID] THEN
    MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `inv Q` THEN
  ASM_SIMP_TAC[REAL_LT_INV; REAL_INV_LE_1; REAL_ARITH `&1 <= Q ==> &0 < Q`] THEN
  SUBGOAL_THEN
   `v + inv Q % (y - v) =
    vsum S (\z:real^N. (inv Q * u z / g z) % (v + g z % (z - v)))`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`S:real^N->bool`; `v:real^N`; `g:real^N->real`;
                   `\z:real^N. inv Q * u z / g z`] MOI_FCL_LIFT_COMB) THEN
    BETA_TAC THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[SUM_LMUL] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN UNDISCH_TAC `&1 <= Q` THEN REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    SUBGOAL_THEN
     `sum S (\z:real^N. (inv Q * u z / g z) * g z) = inv Q /\
      vsum S (\z:real^N. ((inv Q * u z / g z) * g z) % z) = inv Q % y`
    (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `!z:real^N. z IN S ==> (inv Q * u z / g z) * g z = inv Q * u z`
      ASSUME_TAC THENL
       [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
        SUBGOAL_THEN `&0 < (g:real^N->real) z` MP_TAC THENL
         [ASM_MESON_TAC[]; CONV_TAC REAL_FIELD];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [TRANS_TAC EQ_TRANS `sum S (\z:real^N. inv Q * u z)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[];
          ASM_REWRITE_TAC[SUM_LMUL; REAL_MUL_RID]];
        TRANS_TAC EQ_TRANS `vsum S (\z:real^N. inv Q % (u z % z))` THEN CONJ_TAC THENL
         [MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[VECTOR_MUL_ASSOC];
          ASM_REWRITE_TAC[VSUM_LMUL]]];
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC CONVEX_VSUM THEN ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[SUM_LMUL] THEN
    MATCH_MP_TAC REAL_MUL_LINV THEN UNDISCH_TAC `&1 <= Q` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < (g:real^N->real) z /\ &0 <= u z` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN
    ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LE_DIV; REAL_LT_IMP_LE;
                 REAL_ARITH `&1 <= Q ==> &0 <= Q`];
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[]]);;

(* A lifted simplex of the level-derived complex lies in Gamma(s). *)

let MOI_FCL_LIFT_SUB_GC = prove
 (`!(c:(real^N->bool)->bool) l h s S.
     FINITE c /\ lf_simplicial_complex c /\ simplicial_subcomplex l c /\
     moi_frn_sig c l h /\ s IN l /\ ~(s = {}) /\
     S IN moi_real_vertex_sets (moi_fcl_kcx c l s)
     ==> convex hull (IMAGE (\z. simplex_barycentre s +
                                 moi_fcl_gf h z % (z - simplex_barycentre s)) S)
         SUBSET moi_fcl_gc c h s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `s:real^N->bool`; `S:real^N->bool`] MOI_FCL_KCX_VSETS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fs:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    concl th = `S = IMAGE (moi_fta_lev (l:(real^N->bool)->bool)) fs`)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_LCX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_fcl_lcx c (s:real^N->bool)`; `fs:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS fs IN moi_fcl_lcx c (s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain (moi_fcl_lcx c s) (fs:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g. moi_bar_chain c g /\ ~(g = {}) /\
        (!t. t IN g ==> (s:real^N->bool) SUBSET t /\ ~(t = s)) /\
        UNIONS fs = convex hull (IMAGE simplex_barycentre g)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS fs IN moi_fcl_lcx c (s:real^N->bool)` THEN
    REWRITE_TAC[moi_fcl_lcx; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:(real^N->bool)->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `moi_bar_chain (moi_fcl_lcx c s) (fs:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN
    UNDISCH_TAC `UNIONS fs IN (fs:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain c ((s:real^N->bool) INSERT g)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain c (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; FINITE_INSERT] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_INSERT] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `(s:real^N->bool) INSERT g`] MOI_FCL_SIG_AFFINE_FN) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fl:real^N->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `M = convex hull (IMAGE simplex_barycentre ((s:real^N->bool) INSERT g))` THEN
  SUBGOAL_THEN `(Fl:real^N->real)(simplex_barycentre s) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `!t:real^N->bool. t IN s INSERT g
                   ==> (Fl:real^N->real)(simplex_barycentre t) =
                       (if t IN l then &1 else &0)` THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `M SUBSET moi_fcl_dual c (s:real^N->bool) /\ simplex_barycentre s IN M /\
                convex M /\ UNIONS fs SUBSET M`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN REWRITE_TAC[CONVEX_CONVEX_HULL] THEN REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      EXISTS_TAC `(s:real^N->bool) INSERT g` THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY; FORALL_IN_INSERT; SUBSET_REFL] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IMAGE_CLAUSES; IN_INSERT];
      REWRITE_TAC[ASSUME `UNIONS fs =
                   convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))`] THEN
      MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[IMAGE_CLAUSES] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN M ==> Fl x = drop(h x)` ASSUME_TAC THENL
   [EXPAND_TAC "M" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS fs SUBSET moi_fcl_ldual c (s:real^N->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `UNIONS (moi_fcl_lcx c (s:real^N->bool)) = moi_fcl_ldual c s`)) THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (UNIONS fs:real^N->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_CONVEX_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^N->bool) SUBSET UNIONS fs` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `r:real^N->bool` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `moi_fta_lev l r IN (r:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[SUBSET] RELATIVE_INTERIOR_SUBSET) THEN
      MATCH_MP_TAC MOI_FTA_LEV_RELINT THEN
      SUBGOAL_THEN `(r:real^N->bool) IN moi_fcl_lcx c s /\ ~(r = {})` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `moi_bar_chain (moi_fcl_lcx c s) (fs:(real^N->bool)->bool)` THEN
        REWRITE_TAC[moi_bar_chain; SUBSET] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `Fl:real^N->real`;
                 `IMAGE simplex_barycentre (g:(real^N->bool)->bool)`;
                 `fs:(real^N->bool)->bool`] MOI_FCL_CHAIN_LEV_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) IN c /\ ~(t = {})` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `moi_bar_chain c (g:(real^N->bool)->bool)` THEN
        UNDISCH_TAC `(t:real^N->bool) IN g` THEN
        REWRITE_TAC[moi_bar_chain] THEN MESON_TAC[SUBSET];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `t:real^N->bool`] MOI_FCL_BARY_IN_L) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `!t:real^N->bool. t IN s INSERT g
                     ==> (Fl:real^N->real)(simplex_barycentre t) =
                         (if t IN l then &1 else &0)` THEN
      DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[IN_INSERT];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `UNIONS fs = convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))`)) THEN
      SUBGOAL_THEN `!r. r IN fs ==> r face_of UNIONS (fs:(real^N->bool)->bool)`
      ASSUME_TAC THENL
       [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
        MATCH_MP_TAC MOI_BAR_CHAIN_FACE_OF_MAX THEN
        EXISTS_TAC `moi_fcl_lcx c (s:real^N->bool)` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `moi_bar_chain (moi_fcl_lcx c s) (fs:(real^N->bool)->bool)` THEN
      UNDISCH_TAC `!r. r IN fs ==> r face_of UNIONS (fs:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "vals") (LABEL_TAC "side")) THEN
  SUBGOAL_THEN `!z:real^N. z IN S ==> z IN M /\ (Fl z = &0 \/ Fl z = &1 / &2 \/ Fl z = &1)`
  (LABEL_TAC "zs") THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(z:real^N) IN S` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "vals" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "side" STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (\z. simplex_barycentre s + moi_fcl_gf h z % (z - simplex_barycentre s))
            (S:real^N->bool) = S`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(!x:real^N. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
      X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[moi_fcl_gf] THEN
      SUBGOAL_THEN `&1 / &2 <= drop((h:real^N->real^1) z)` (fun th -> REWRITE_TAC[th]) THENL
       [SUBGOAL_THEN `z IN (M:real^N->bool) /\ &1 / &2 <= (Fl:real^N->real) z` MP_TAC THENL
         [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
          UNDISCH_TAC `(z:real^N) IN S` THEN EXPAND_TAC "S" THEN
          REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
          ASM_MESON_TAC[]];
        VECTOR_ARITH_TAC];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS fs` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `S:real^N->bool`;
                     `UNIONS fs:real^N->bool`] HULL_MINIMAL) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 / &2 <= (Fl:real^N->real) x` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`Fl:real^N->real`; `&1 / &2`; `S:real^N->bool`]
        MOI_FTA_LEVEL_HULL_GE) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [EXPAND_TAC "S" THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Fl:real^N->real) x = drop(h x)` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_fcl_gc; moi_fcl_wc; IN_UNION; IN_INTER; IN_ELIM_THM] THEN
    DISJ2_TAC THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[]; ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z:real^N. z IN S
        ==> simplex_barycentre s + moi_fcl_gf h z % (z - simplex_barycentre s) IN M /\
            (Fl:real^N->real)
              (simplex_barycentre s + moi_fcl_gf h z % (z - simplex_barycentre s)) =
            &1 / &2`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN M` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(Fl:real^N->real) z <= &1 / &2` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^N) IN S` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Fl:real^N->real) z = drop(h z)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_fcl_gf] THEN
    USE_THEN "zs" (STRIP_ASSUME_TAC o C MATCH_MP (ASSUME `(z:real^N) IN S`)) THENL
     [SUBGOAL_THEN `~(&1 / &2 <= drop((h:real^N->real^1) z))` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH `b + &1 / &2 % (z - b):real^N =
                                (&1 - &1 / &2) % b + &1 / &2 % z`] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] (ASSUME `convex (M:real^N->bool)`)) THEN
        ASM_REWRITE_TAC[] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
      SUBGOAL_THEN `&1 / &2 <= drop((h:real^N->real^1) z)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH `b + &1 % (z - b):real^N = z`] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN M` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex:(real^N->bool)->bool`;
     `IMAGE (\z. simplex_barycentre s + moi_fcl_gf h z % (z - simplex_barycentre s))
            (S:real^N->bool)`; `M:real^N->bool`] HULL_MINIMAL) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Fl:real^N->real) x = &1 / &2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`Fl:real^N->real`; `&1 / &2`;
     `IMAGE (\z. simplex_barycentre s + moi_fcl_gf h z % (z - simplex_barycentre s))
            (S:real^N->bool)`] MOI_FTA_LEVEL_HULL) THEN
    ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN ANTS_TAC THENL
     [ASM_MESON_TAC[]; DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fcl_gc; moi_fcl_tc; IN_UNION; IN_INTER; IN_ELIM_THM] THEN
  DISJ1_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]);;

(* The boundary part of the link of the dual cell is covered by simplices   *)
(* of the level-derived complex with all vertices in |l|.                   *)

let MOI_FCL_KCX_LCOVER = prove
 (`!(c:(real^N->bool)->bool) l s x.
     FINITE c /\ lf_simplicial_complex c /\ simplicial_subcomplex l c /\
     x IN moi_fcl_ldual l s
     ==> ?S. S IN moi_real_vertex_sets (moi_fcl_kcx c l s) /\ x IN convex hull S /\
             convex hull S SUBSET moi_fcl_ldual l s /\ S SUBSET UNIONS l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN moi_fcl_ldual l s` THEN REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain c (g:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain l (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  ABBREV_TAC `m = convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
  SUBGOAL_THEN `(m:real^N->bool) IN moi_fcl_lcx c s` ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN REWRITE_TAC[moi_fcl_lcx; IN_ELIM_THM] THEN
    EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(&(CARD(g:(real^N->bool)->bool)) - &1) simplex (m:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN MATCH_MP_TAC MOI_BAR_CHAIN_SIMPLEX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `&(CARD(g:(real^N->bool)->bool)) - &1:int`;
                 `m:real^N->bool`; `x:real^N`] MOI_FTA_LEV_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fs:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_LCX_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_chain (moi_fcl_lcx c s) (fs:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_fcl_lcx c (s:real^N->bool)`; `m:real^N->bool`]
      MOI_BAR_FACES_SUBSET_COMPLEX) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_bar_chain {r | r face_of m} (fs:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN fs ==> moi_fta_lev l r IN (m:real^N->bool)` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `&(CARD(g:(real^N->bool)->bool)) - &1:int`;
                   `m:real^N->bool`; `fs:(real^N->bool)->bool`; `r:real^N->bool`]
      MOI_FTA_FACE_CHAIN_ELT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (IMAGE (moi_fta_lev l) fs) SUBSET (m:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    EXPAND_TAC "m" THEN REWRITE_TAC[CONVEX_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N->bool) SUBSET moi_fcl_ldual l s` ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N->bool) SUBSET UNIONS l` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_bar_chain l (g:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain] THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (moi_fta_lev l) (fs:(real^N->bool)->bool)` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `(x:real^N) IN convex hull IMAGE (moi_fta_lev l) fs` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `s:real^N->bool`] MOI_FCL_KCX_COMPLEX) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_fcl_kcx; IN_ELIM_THM] THEN
      EXISTS_TAC `fs:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ASM SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `convex hull (IMAGE (moi_fta_lev l) (fs:(real^N->bool)->bool))` THEN
    REWRITE_TAC[HULL_SUBSET] THEN ASM SET_TAC[]]);;

(* The union of the lifted simplices is Gamma(s). *)

let MOI_FCL_LIFTS_GC = prove
 (`!(c:(real^N->bool)->bool) l h s.
     FINITE c /\ lf_simplicial_complex c /\ simplicial_subcomplex l c /\
     moi_frn_sig c l h /\ s IN l /\ ~(s = {}) /\ ~(moi_fcl_ldual c s = {})
     ==> UNIONS {convex hull (IMAGE (\z. simplex_barycentre s +
                                         moi_fcl_gf h z % (z - simplex_barycentre s)) S) |
                 S | S IN moi_real_vertex_sets (moi_fcl_kcx c l s)} =
         moi_fcl_gc c h s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `S:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FCL_LIFT_SUB_GC THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `s:real^N->bool`] MOI_FCL_WC_CONE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "uniq") (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))) THEN
  SUBGOAL_THEN `(x:real^N) IN moi_fcl_dual c s` MP_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN moi_fcl_gc c h s` THEN
    REWRITE_TAC[moi_fcl_gc; moi_fcl_tc; moi_fcl_wc; IN_UNION; IN_INTER] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_DUAL_CONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FTA_IN_CONE) THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(r = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(x:real^N) IN moi_fcl_gc c h s` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?S. S IN moi_real_vertex_sets (moi_fcl_kcx c l s) /\ (y:real^N) IN convex hull S`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `s:real^N->bool`] MOI_FCL_KCX_COMPLEX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `moi_fcl_kcx c l (s:real^N->bool)` MOI_REAL_VERTEX_SETS_UNIONS) THEN
    ASM_REWRITE_TAC[abstract_realization; UNIONS_INSERT; UNION_EMPTY; IMAGE_ID] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N` o GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (S:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `S IN moi_real_vertex_sets (moi_fcl_kcx c l (s:real^N->bool))` THEN
    REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^N->bool`; `simplex_barycentre s:real^N`;
                 `moi_fcl_gf (h:real^N->real^1)`; `y:real^N`] MOI_FCL_LIFT_RAY) THEN
  ASM_REWRITE_TAC[MOI_FCL_GF_RANGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `r':real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `s:real^N->bool`; `S:real^N->bool`]
    MOI_FCL_LIFT_SUB_GC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `r':real = r` SUBST_ALL_TAC THENL
   [USE_THEN "uniq" (MP_TAC o C MATCH_MP (ASSUME `(y:real^N) IN moi_fcl_ldual c s`)) THEN
    REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `simplex_barycentre s + r' % (y - simplex_barycentre s) IN
                  moi_fcl_gc c h (s:real^N->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!x:real^N s t. x IN s /\ s SUBSET t ==> x IN t`) THEN
      EXISTS_TAC `convex hull (IMAGE (\z. simplex_barycentre s +
                    moi_fcl_gf h z % (z - simplex_barycentre s)) (S:real^N->bool))` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `simplex_barycentre s + r % (y - simplex_barycentre s) IN
                  moi_fcl_gc c h (s:real^N->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN moi_fcl_gc c h s` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `convex hull (IMAGE (\z. simplex_barycentre s +
                 moi_fcl_gf h z % (z - simplex_barycentre s)) (S:real^N->bool))` THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* Gamma(s) is PL homeomorphic to the link part of the dual cell of s, by a *)
(* homeomorphism mapping the boundary part onto itself.                     *)

let MOI_FCL_GC_PLH = prove
 (`!(c:(real^N->bool)->bool) l h s.
     FINITE c /\ lf_simplicial_complex c /\ simplicial_subcomplex l c /\
     moi_frn_sig c l h /\ s IN l /\ ~(s = {}) /\ ~(moi_fcl_ldual c s = {})
     ==> ?f f'. pl_homeomorphism (moi_fcl_ldual c s,moi_fcl_gc c h s) (f,f') /\
                IMAGE f (moi_fcl_ldual l s) = moi_fcl_ldual l s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_FCL_KCX_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_LDUAL_RAYS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `s:real^N->bool`] MOI_FCL_LIFTS_GC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_fcl_kcx c l (s:real^N->bool)`; `simplex_barycentre s:real^N`;
                 `moi_fcl_gf (h:real^N->real^1)`] MOI_FCL_SECTION) THEN
  ASM_REWRITE_TAC[MOI_FCL_GF_RANGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` (X_CHOOSE_THEN `f':real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `f':real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!S. S IN moi_real_vertex_sets (moi_fcl_kcx c l s) /\ S SUBSET UNIONS l
        ==> IMAGE (f:real^N->real^N) (convex hull S) = convex hull S`
  (LABEL_TAC "fixS") THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^N. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN REWRITE_TAC[moi_fcl_gf] THEN
    SUBGOAL_THEN `drop((h:real^N->real^1) z) = &1` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC MOI_FRN_SIG_ONE THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(S:real^N->bool) SUBSET UNIONS l` THEN
      UNDISCH_TAC `(z:real^N) IN S` THEN SET_TAC[];
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THENL
   [REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `s:real^N->bool`; `x0:real^N`] MOI_FCL_KCX_LCOVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^N) IN IMAGE (f:real^N->real^N) (convex hull S)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "fixS" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ
      (ASSUME `S IN moi_real_vertex_sets (moi_fcl_kcx c l (s:real^N->bool))`)
      (ASSUME `(S:real^N->bool) SUBSET UNIONS l`))]) THEN
    UNDISCH_TAC `convex hull S SUBSET moi_fcl_ldual l (s:real^N->bool)` THEN
    UNDISCH_TAC `(x:real^N) = (f:real^N->real^N) x0` THEN SET_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `s:real^N->bool`; `x:real^N`] MOI_FCL_KCX_LCOVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^N) IN IMAGE (f:real^N->real^N) (convex hull S)` MP_TAC THENL
     [USE_THEN "fixS" (fun th -> REWRITE_TAC[MATCH_MP th (CONJ
        (ASSUME `S IN moi_real_vertex_sets (moi_fcl_kcx c l (s:real^N->bool))`)
        (ASSUME `(S:real^N->bool) SUBSET UNIONS l`))]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `convex hull S SUBSET moi_fcl_ldual l (s:real^N->bool)` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* The cells Gamma(s) and W(s).  For boundary vertices and edges Gamma(s) is *)
(* a PL copy of the link part of the dual cell (above) and W(s) is the cone  *)
(* over it; for boundary triangles everything is explicit on the segment     *)
(* from the barycentre of s to that of its tetrahedron.                      *)
(* ========================================================================= *)

(* The same as MOI_S4G_POINT_CELL (pc_moi_s34_recoga.ml, which is not       *)
(* loaded here).                                                            *)

let MOI_FCL_POINT_CELL = prove
 (`!p:real^N. pl_cell_with_boundary 0 {p} {}`,
  GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`{p:real^N}`; `\x:real^N. x`; `\x:real^N. x`] THEN
  REWRITE_TAC[RELATIVE_FRONTIER_SING; IMAGE_CLAUSES; pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_SING] THEN
  REWRITE_TAC[simplex] THEN EXISTS_TAC `{p:real^N}` THEN
  REWRITE_TAC[AFFINE_INDEPENDENT_1; CONVEX_HULL_SING; CARD_SING] THEN INT_ARITH_TAC);;

let MOI_FCL_SEGMENT_CELL = prove
 (`!a b:real^N. ~(a = b) ==> pl_cell_with_boundary 1 (segment[a,b]) {a,b}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_cell_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`segment[a:real^N,b]`; `\x:real^N. x`; `\x:real^N. x`] THEN
  REWRITE_TAC[IMAGE_ID; pl_homeomorphism; HOMEOMORPHISM_ID] THEN
  REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_SEGMENT] THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  SIMP_TAC[RELATIVE_FRONTIER_OF_CONVEX_HULL; AFFINE_INDEPENDENT_2] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[simplex] THEN EXISTS_TAC `{a:real^N,b}` THEN
    REWRITE_TAC[AFFINE_INDEPENDENT_2] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_SING; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
    REWRITE_TAC[SIMPLE_IMAGE; IMAGE_CLAUSES; UNIONS_2] THEN
    SUBGOAL_THEN `{a:real^N,b} DELETE a = {b} /\ {a,b} DELETE b = {a}`
      (fun th -> REWRITE_TAC[th; CONVEX_HULL_SING]) THENL
     [ASM SET_TAC[]; SET_TAC[]]]);;

(* Level sets of an affine function going from 1 to 0 along a segment. *)

let MOI_FCL_SEG_LEVEL = prove
 (`!(Fl:real^N->real) a b.
     (!x y u. Fl((&1 - u) % x + u % y) = (&1 - u) * Fl x + u * Fl y) /\
     Fl a = &1 /\ Fl b = &0
     ==> {x | x IN segment[a,b] /\ Fl x = &1 / &2} = {midpoint(a,b)} /\
         {x | x IN segment[a,b] /\ &1 / &2 <= Fl x} = segment[a,midpoint(a,b)]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!u. (Fl:real^N->real)((&1 - u) % a + u % b) = &1 - u` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[midpoint] THEN CONJ_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_ELIM_THM; IN_SING; IN_SEGMENT] THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `u = &1 / &2` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `&1 / &2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC;
      REWRITE_TAC[VECTOR_ARITH `inv(&2) % (a + b):real^N =
                                (&1 - &1 / &2) % a + &1 / &2 % b`] THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) MP_TAC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN EXISTS_TAC `&2 * u` THEN
    REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    DISCH_THEN(X_CHOOSE_THEN `v:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `x:real^N = (&1 - v / &2) % a + (v / &2) % b` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `v / &2` THEN REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC]]);;

(* Gamma(s) and W(s) are cells when the link part of the dual cell is a    *)
(* cell bounded by its boundary part.                                      *)

let MOI_FCL_GW_CELLS = prove
 (`!(c:(real^N->bool)->bool) l h s n.
     FINITE c /\ lf_simplicial_complex c /\ simplicial_subcomplex l c /\
     moi_frn_sig c l h /\ s IN l /\ ~(s = {}) /\ ~(moi_fcl_ldual l s = {}) /\
     1 <= n /\ n + 1 <= dimindex(:N) /\
     pl_cell_with_boundary n (moi_fcl_ldual c s) (moi_fcl_ldual l s)
     ==> pl_cell_with_boundary n (moi_fcl_gc c h s) (moi_fcl_ldual l s) /\
         pl_cell_with_boundary (n + 1) (moi_fcl_wc c h s)
           (moi_fcl_gc c h s UNION moi_fcl_dual l s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool) /\
                moi_bar_complex (l:(real^N->bool)->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR; MOI_FTA_BAR_SUB]; ALL_TAC] THEN
  SUBGOAL_THEN `~(moi_fcl_ldual c (s:real^N->bool) = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `s:real^N->bool`] MOI_FCL_LDUAL_SUB_MONO) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[simplicial_subcomplex]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `s:real^N->bool`] MOI_FCL_GC_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->real^N` (X_CHOOSE_THEN `f':real^N->real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `pl_cell_with_boundary n (moi_fcl_gc c h s) (moi_fcl_ldual l (s:real^N->bool))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `moi_fcl_ldual c (s:real^N->bool)`;
                   `moi_fcl_ldual l (s:real^N->bool)`; `moi_fcl_gc c h (s:real^N->bool)`;
                   `f:real^N->real^N`; `f':real^N->real^N`] MOI_FCL_CELL_TRANSFER) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `s:real^N->bool`] MOI_FCL_WC_CONE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_DUAL_CONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`n:num`; `moi_fcl_gc c h (s:real^N->bool)`;
                 `moi_fcl_ldual l (s:real^N->bool)`; `simplex_barycentre s:real^N`]
    MOI_FCL_CONE_CELL) THEN
  ASM_REWRITE_TAC[]);;

(* At a simplex s of l whose link part is a single barycentre b(r), r not   *)
(* in l (a boundary triangle and its tetrahedron), the level pieces are     *)
(* explicit on the segment from b(s) to b(r).                               *)

let MOI_FCL_TRI_LEVEL = prove
 (`!(c:(real^N->bool)->bool) l h s r.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h /\
     s IN l /\ ~(s = {}) /\ r IN c /\ ~(r IN l) /\ s SUBSET r /\
     moi_fcl_ldual c s = {simplex_barycentre r}
     ==> moi_fcl_dual c s = segment[simplex_barycentre s,simplex_barycentre r] /\
         moi_fcl_tc c h s =
           {midpoint(simplex_barycentre s,simplex_barycentre r)} /\
         moi_fcl_wc c h s =
           segment[simplex_barycentre s,
                   midpoint(simplex_barycentre s,simplex_barycentre r)] /\
         moi_fcl_gc c h s =
           {midpoint(simplex_barycentre s,simplex_barycentre r)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN c /\ ~(r:real^N->bool = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fcl_dual c (s:real^N->bool) =
    segment[simplex_barycentre s,simplex_barycentre r]`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_DUAL_CONE) THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[SET_RULE `!f (a:real^N). {f y | y | y IN {a}} = {(f:real^N->real^N->bool) a}`;
                UNIONS_1];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain c {s:real^N->bool,r}` ASSUME_TAC THENL
   [REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT;
                FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `{s:real^N->bool,r}`] MOI_FCL_SIG_AFFINE_FN) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                  IMAGE_CLAUSES; GSYM SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fl:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `moi_fcl_tc c h (s:real^N->bool) =
      {x | x IN segment[simplex_barycentre s,simplex_barycentre r] /\
           (Fl:real^N->real) x = &1 / &2} /\
    moi_fcl_wc c h (s:real^N->bool) =
      {x | x IN segment[simplex_barycentre s,simplex_barycentre r] /\
           &1 / &2 <= (Fl:real^N->real) x}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_fcl_tc; moi_fcl_wc] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_CASES_TAC `(x:real^N) IN segment[simplex_barycentre s,simplex_barycentre r]` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`Fl:real^N->real`; `simplex_barycentre s:real^N`;
                 `simplex_barycentre r:real^N`] MOI_FCL_SEG_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lev1") (LABEL_TAC "lev2")) THEN
  SUBGOAL_THEN
   `~(simplex_barycentre r IN
      segment[simplex_barycentre s,
              midpoint(simplex_barycentre s,simplex_barycentre r:real^N)])`
  ASSUME_TAC THENL
   [USE_THEN "lev2" (MP_TAC o SPEC `simplex_barycentre r:real^N` o
      GEN_REWRITE_RULE I [EXTENSION]) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; ENDS_IN_SEGMENT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_fcl_gc] THEN
  USE_THEN "lev1" (fun th -> REWRITE_TAC[th]) THEN
  USE_THEN "lev2" (fun th -> REWRITE_TAC[th]) THEN
  UNDISCH_TAC
   `~(simplex_barycentre r IN
      segment[simplex_barycentre s,
              midpoint(simplex_barycentre s,simplex_barycentre r:real^N)])` THEN
  SET_TAC[]);;

(* The cells at a boundary triangle. *)

let MOI_FCL_TRI_CELLS = prove
 (`!(c:(real^N->bool)->bool) h s.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_frn_sig c (boundary_complex c) h /\
     s IN boundary_complex c /\ aff_dim s = &2
     ==> moi_fcl_dual (boundary_complex c) s = {simplex_barycentre s} /\
         moi_fcl_ldual (boundary_complex c) s = {} /\
         pl_cell_with_boundary 0 (moi_fcl_tc c h s) {} /\
         moi_fcl_tc c h s INTER moi_fcl_ldual c s = {} /\
         pl_cell_with_boundary 1 (moi_fcl_wc c h s)
           (moi_fcl_gc c h s UNION moi_fcl_dual (boundary_complex c) s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_TRIANGLE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((r:real^N->bool) IN boundary_complex c)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`boundary_complex c:(real^N->bool)->bool`; `r:real^N->bool`]
      MOI_FRN_SA_CM_DIM) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_subcomplex];
      INT_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `s:real^N->bool`; `r:real^N->bool`]
    MOI_FCL_TRI_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[MOI_FCL_POINT_CELL] THEN
  SUBGOAL_THEN `~(simplex_barycentre s:real^N = simplex_barycentre r)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `r:real^N->bool`]
      MOI_FTA_BARY_INJ) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(s:real^N->bool) IN c /\ ~(r:real^N->bool = {})` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ASM SET_TAC[]];
      ASM_REWRITE_TAC[]] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim(r:real^N->bool) = &3` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN
    ASM_CASES_TAC `x = midpoint(simplex_barycentre s:real^N,simplex_barycentre r)` THEN
    ASM_REWRITE_TAC[MIDPOINT_EQ_ENDPOINT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{midpoint(simplex_barycentre s:real^N,simplex_barycentre r)} UNION
    {simplex_barycentre s} =
    {simplex_barycentre s,midpoint(simplex_barycentre s,simplex_barycentre r)}`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FCL_SEGMENT_CELL THEN
  ASM_REWRITE_TAC[MIDPOINT_EQ_ENDPOINT]);;

(* ========================================================================= *)
(* The data of the cell assembly.  Labels are pairs (s,i), s a nonempty      *)
(* simplex of l, i = 0 (bottom), 1 (top), 2 (prism).  Source cells           *)
(* moi_fcl_src l (s,i) = D_l(s) PCROSS I_i, target cells moi_fcl_tgt c l h   *)
(* (s,i) = D_c(s) INTER L_i with the level sets L_i of the weight; (t,j) is  *)
(* a face of (s,i) when s SUBSET t and (i = j or i = 2).  Generic            *)
(* intersection identities for three nested levels.                          *)
(* ========================================================================= *)

let moi_fcl_ival = new_definition
 `moi_fcl_ival (i:num) =
    if i = 0 then {vec 0:real^1} else if i = 1 then {vec 1}
    else interval[vec 0,vec 1]`;;

let moi_fcl_lv = new_definition
 `moi_fcl_lv (l:(real^N->bool)->bool) (h:real^N->real^1) (i:num) =
    if i = 0 then UNIONS l
    else if i = 1 then {x | drop(h x) = &1 / &2}
    else {x | &1 / &2 <= drop(h x)}`;;

let moi_fcl_src = new_definition
 `moi_fcl_src (l:(real^N->bool)->bool) (p:(real^N->bool)#num) =
    moi_fcl_dual l (FST p) PCROSS moi_fcl_ival (SND p)`;;

let moi_fcl_tgt = new_definition
 `moi_fcl_tgt (c:(real^N->bool)->bool) l (h:real^N->real^1)
              (p:(real^N->bool)#num) =
    moi_fcl_dual c (FST p) INTER moi_fcl_lv l h (SND p)`;;

let moi_fcl_face = new_definition
 `moi_fcl_face (l:(real^N->bool)->bool) (p:(real^N->bool)#num)
               (q:(real^N->bool)#num) <=>
    FST q IN l /\ ~(FST q = {}) /\ FST p SUBSET FST q /\ SND q <= 2 /\
    (SND p = SND q \/ SND p = 2)`;;

let moi_fcl_dim = new_definition
 `moi_fcl_dim (p:(real^N->bool)#num) =
    num_of_int(&2 - aff_dim (FST p)) + (if SND p = 2 then 1 else 0)`;;

(* Three nested levels: L 0 and L 1 disjoint inside L 2. *)

let MOI_FCL_LV3_INTER = prove
 (`!(L:num->A->bool) i j.
     L 0 INTER L 1 = {} /\ L 0 SUBSET L 2 /\ L 1 SUBSET L 2 /\ i <= 2 /\ j <= 2
     ==> L i INTER L j =
         UNIONS {L k | k | k <= 2 /\ (i = k \/ i = 2) /\ (j = k \/ j = 2)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:A. ~(x IN L 0 /\ x IN L 1) /\ (x IN L 0 ==> x IN L 2) /\
          (x IN L 1 ==> x IN L 2)`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:A` THEN
  REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  SUBGOAL_THEN
   `(?t. (?k. (k <= 2 /\ (i = k \/ i = 2) /\ (j = k \/ j = 2)) /\ t = L k) /\
         (x:A) IN t) <=>
    (?k. (k <= 2 /\ (i = k \/ i = 2) /\ (j = k \/ j = 2)) /\ x IN L k)`
  SUBST1_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `k <= 2 <=> k = 0 \/ k = 1 \/ k = 2`] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; LEFT_OR_DISTRIB; EXISTS_OR_THM;
              GSYM CONJ_ASSOC; UNWIND_THM2] THEN
  UNDISCH_TAC `i <= 2` THEN UNDISCH_TAC `j <= 2` THEN
  REWRITE_TAC[ARITH_RULE `n <= 2 <=> n = 0 \/ n = 1 \/ n = 2`] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[ARITH_EQ] THEN ASM_MESON_TAC[]);;

let MOI_FCL_IVAL_LEVELS = prove
 (`moi_fcl_ival 0 INTER moi_fcl_ival 1 = {} /\
   moi_fcl_ival 0 SUBSET moi_fcl_ival 2 /\ moi_fcl_ival 1 SUBSET moi_fcl_ival 2`,
  REWRITE_TAC[moi_fcl_ival; ARITH_EQ] THEN
  REWRITE_TAC[SING_SUBSET; ENDS_IN_UNIT_INTERVAL] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; NOT_IN_EMPTY] THEN
  MESON_TAC[VEC_EQ; ARITH_RULE `~(0 = 1)`]);;

let MOI_FCL_LV_LEVELS = prove
 (`!(c:(real^N->bool)->bool) l h.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h
     ==> moi_fcl_lv l h 0 INTER moi_fcl_lv l h 1 = {} /\
         moi_fcl_lv l h 0 SUBSET moi_fcl_lv l h 2 /\
         moi_fcl_lv l h 1 SUBSET moi_fcl_lv l h 2 /\
         (!i x. x IN moi_fcl_lv l h i ==> ~(drop(h x) = &0))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^N. x IN UNIONS l ==> drop(h x) = &1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_SIG_ONE THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fcl_lv; ARITH_EQ] THEN
  REWRITE_TAC[EXTENSION; SUBSET; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `(x:real^N) IN UNIONS l` THEN
    ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
    REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN REPEAT COND_CASES_TAC THEN REWRITE_TAC[IN_ELIM_THM] THENL
     [DISCH_TAC THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      REAL_ARITH_TAC]]);;

(* Intersections of source cells. *)

let MOI_FCL_SRC_INTER = prove
 (`!(c:(real^N->bool)->bool) l p q.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\
     SND p <= 2 /\ SND q <= 2
     ==> moi_fcl_src l p INTER moi_fcl_src l q =
         UNIONS {moi_fcl_src l r | r | moi_fcl_face l p r /\ moi_fcl_face l q r}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR; MOI_FTA_BAR_SUB]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `FST(p:(real^N->bool)#num)`;
                 `FST(q:(real^N->bool)#num)`] MOI_FCL_DUAL_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_fcl_ival`; `SND(p:(real^N->bool)#num)`;
                 `SND(q:(real^N->bool)#num)`] MOI_FCL_LV3_INTER) THEN
  ASM_REWRITE_TAC[MOI_FCL_IVAL_LEVELS] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_fcl_src; INTER_PCROSS] THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIONS; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^1`] THEN
  REWRITE_TAC[moi_fcl_face; EXISTS_PAIR_THM; FST; SND] THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `X:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))
      (X_CHOOSE_THEN `Y:real^1->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN ASSUME_TAC)) ASSUME_TAC))) THEN
    EXISTS_TAC `moi_fcl_dual l (u:real^N->bool) PCROSS moi_fcl_ival k` THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `k:num`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `Z:real^(N,1)finite_sum->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `k:num`
        (CONJUNCTS_THEN ASSUME_TAC)))
      MP_TAC)) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN STRIP_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `moi_fcl_dual l (u:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `moi_fcl_ival k` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[]]]);;

(* Intersections of target cells. *)

let MOI_FCL_TGT_INTER = prove
 (`!(c:(real^N->bool)->bool) l h p q.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h /\
     SND p <= 2 /\ SND q <= 2
     ==> moi_fcl_tgt c l h p INTER moi_fcl_tgt c l h q =
         UNIONS {moi_fcl_tgt c l h r | r |
                 moi_fcl_face l p r /\ moi_fcl_face l q r}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`] MOI_FCL_LV_LEVELS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `FST(p:(real^N->bool)#num)`;
                 `FST(q:(real^N->bool)#num)`] MOI_FCL_DUAL_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_fcl_lv (l:(real^N->bool)->bool) (h:real^N->real^1)`;
                 `SND(p:(real^N->bool)#num)`;
                 `SND(q:(real^N->bool)#num)`] MOI_FCL_LV3_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[moi_fcl_tgt] THEN
  REWRITE_TAC[SET_RULE `(a INTER b) INTER (c INTER d) =
                        (a INTER c) INTER (b INTER d:real^N->bool)`] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
  REWRITE_TAC[moi_fcl_face; EXISTS_PAIR_THM; FST; SND] THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `X:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `u:real^N->bool` (CONJUNCTS_THEN ASSUME_TAC)) ASSUME_TAC))
      (X_CHOOSE_THEN `Y:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN ASSUME_TAC)) ASSUME_TAC))) THEN
    SUBGOAL_THEN `(x:real^N) IN moi_fcl_dual c u /\ x IN moi_fcl_lv l h k`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^N->bool) IN l` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:real^N->real^1`; `u:real^N->bool`; `x:real^N`]
        MOI_FCL_SIG_ZERO_DUAL) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `moi_fcl_dual c (u:real^N->bool) INTER moi_fcl_lv l h k` THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `k:num`] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `Z:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `k:num`
        (CONJUNCTS_THEN ASSUME_TAC)))
      MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `moi_fcl_dual c (u:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `u:real^N->bool` THEN ASM_MESON_TAC[SUBSET];
      EXISTS_TAC `moi_fcl_lv l (h:real^N->real^1) k` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `k:num` THEN ASM_MESON_TAC[]]]);;

(* Boundaries of the source cells. *)

let MOI_FCL_SRC_BD01 = prove
 (`!(c:(real^N->bool)->bool) l s i.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ i <= 1
     ==> UNIONS {moi_fcl_src l m | m | moi_fcl_face l (s,i) m /\ ~(m = (s,i))} =
         moi_fcl_ldual l s PCROSS moi_fcl_ival i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_FCL_LDUAL_EQ] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIONS; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^1`] THEN
  REWRITE_TAC[moi_fcl_face; moi_fcl_src; EXISTS_PAIR_THM; FST; SND; PAIR_EQ] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `Z:real^(N,1)finite_sum->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `j:num`
        (CONJUNCTS_THEN ASSUME_TAC))) MP_TAC)) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `j:num = i` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `i <= 1 ==> ~(i = 2)`]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `moi_fcl_dual l (t:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_MESON_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `X:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN ASSUME_TAC)) ASSUME_TAC))
      ASSUME_TAC) THEN
    EXISTS_TAC `moi_fcl_dual l (t:real^N->bool) PCROSS moi_fcl_ival i` THEN
    REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `i:num`] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let MOI_FCL_IVAL_CASES = prove
 (`moi_fcl_ival 0 = {vec 0} /\ moi_fcl_ival 1 = {vec 1} /\
   moi_fcl_ival 2 = interval[vec 0,vec 1] /\
   (!j. j <= 2 ==> moi_fcl_ival j SUBSET interval[vec 0,vec 1])`,
  REWRITE_TAC[moi_fcl_ival; ARITH_EQ] THEN GEN_TAC THEN DISCH_TAC THEN
  REPEAT COND_CASES_TAC THEN
  REWRITE_TAC[SUBSET_REFL; SING_SUBSET; ENDS_IN_UNIT_INTERVAL]);;

let MOI_FCL_SRC_BD2 = prove
 (`!(c:(real^N->bool)->bool) l s.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ s IN l /\ ~(s = {})
     ==> UNIONS {moi_fcl_src l m | m | moi_fcl_face l (s,2) m /\ ~(m = (s,2))} =
         (moi_fcl_dual l s PCROSS {vec 0,vec 1}) UNION
         (moi_fcl_ldual l s PCROSS interval[vec 0,vec 1])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_FCL_LDUAL_EQ] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIONS; IN_ELIM_THM;
              IN_UNION] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^1`] THEN
  REWRITE_TAC[moi_fcl_face; moi_fcl_src; EXISTS_PAIR_THM; FST; SND; PAIR_EQ] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `Z:real^(N,1)finite_sum->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `j:num`
        (CONJUNCTS_THEN ASSUME_TAC))) MP_TAC)) THEN
    ASM_REWRITE_TAC[PASTECART_IN_PCROSS] THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    ASM_CASES_TAC `t:real^N->bool = s` THENL
     [DISJ1_TAC THEN
      SUBGOAL_THEN `j = 0 \/ j = 1` ASSUME_TAC THENL
       [ASM_MESON_TAC[ARITH_RULE `j <= 2 /\ ~(j = 2) ==> j = 0 \/ j = 1`];
        ALL_TAC] THEN
      UNDISCH_TAC `(y:real^1) IN moi_fcl_ival j` THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC) THEN
      REWRITE_TAC[MOI_FCL_IVAL_CASES; IN_SING; IN_INSERT] THEN
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN ASM_MESON_TAC[];
      DISJ2_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `moi_fcl_dual l (t:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `t:real^N->bool` THEN ASM_MESON_TAC[];
        ASM_MESON_TAC[MOI_FCL_IVAL_CASES; SUBSET]]];
    STRIP_TAC THENL
     [EXISTS_TAC `moi_fcl_dual l (s:real^N->bool) PCROSS
                  moi_fcl_ival (if (y:real^1) = vec 0 then 0 else 1)` THEN
      REWRITE_TAC[PASTECART_IN_PCROSS] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `if y = vec 0:real^1 then 0 else 1`] THEN
        ASM_REWRITE_TAC[SUBSET_REFL] THEN COND_CASES_TAC THEN ARITH_TAC;
        UNDISCH_TAC `(y:real^1) IN {vec 0,vec 1}` THEN
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
        COND_CASES_TAC THEN ASM_REWRITE_TAC[MOI_FCL_IVAL_CASES; IN_SING]];
      EXISTS_TAC `moi_fcl_dual l (u:real^N->bool) PCROSS moi_fcl_ival 2` THEN
      REWRITE_TAC[PASTECART_IN_PCROSS; MOI_FCL_IVAL_CASES] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `2`] THEN
        ASM_REWRITE_TAC[MOI_FCL_IVAL_CASES; LE_REFL];
        ASM_MESON_TAC[]]]]);;

(* Boundaries of the target cells. *)

let MOI_FCL_TGT_BD01 = prove
 (`!(c:(real^N->bool)->bool) l h s i.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h /\
     i <= 1
     ==> UNIONS {moi_fcl_tgt c l h m | m |
                 moi_fcl_face l (s,i) m /\ ~(m = (s,i))} =
         moi_fcl_ldual c s INTER moi_fcl_lv l h i`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`] MOI_FCL_LV_LEVELS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[MOI_FCL_LDUAL_EQ] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
  REWRITE_TAC[moi_fcl_face; moi_fcl_tgt; EXISTS_PAIR_THM; FST; SND; PAIR_EQ;
              IN_INTER] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `Z:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `t:real^N->bool` (X_CHOOSE_THEN `j:num`
        (CONJUNCTS_THEN ASSUME_TAC))) MP_TAC)) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `j:num = i` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `i <= 1 ==> ~(i = 2)`]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `moi_fcl_dual c (t:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_MESON_TAC[SUBSET];
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `X:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN ASSUME_TAC)) ASSUME_TAC))
      ASSUME_TAC) THEN
    SUBGOAL_THEN `(t:real^N->bool) IN l` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:real^N->real^1`; `t:real^N->bool`; `x:real^N`]
        MOI_FCL_SIG_ZERO_DUAL) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `moi_fcl_dual c (t:real^N->bool) INTER moi_fcl_lv l h i` THEN
    REWRITE_TAC[IN_INTER] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `i:num`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[ARITH_RULE `i <= 1 ==> i <= 2`]]);;

let MOI_FCL_TGT_BD2 = prove
 (`!(c:(real^N->bool)->bool) l h s.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h /\
     s IN l /\ ~(s = {})
     ==> UNIONS {moi_fcl_tgt c l h m | m |
                 moi_fcl_face l (s,2) m /\ ~(m = (s,2))} =
         moi_fcl_gc c h s UNION moi_fcl_dual l s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET c /\
                moi_bar_complex (c:(real^N->bool)->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; MOI_FTA_LF_BAR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`] MOI_FCL_LV_LEVELS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j. j <= 2 ==> moi_fcl_lv l (h:real^N->real^1) j SUBSET moi_fcl_lv l h 2`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ARITH_RULE `j <= 2 <=> j = 0 \/ j = 1 \/ j = 2`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fcl_dual c s INTER moi_fcl_lv l (h:real^N->real^1) 0 =
                moi_fcl_dual l s`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_fcl_lv; ARITH_EQ] THEN ASM_MESON_TAC[MOI_FCL_DUAL_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fcl_dual c s INTER moi_fcl_lv l (h:real^N->real^1) 1 =
                moi_fcl_tc c h s /\
                moi_fcl_dual c s INTER moi_fcl_lv l (h:real^N->real^1) 2 =
                moi_fcl_wc c h s`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_fcl_lv; moi_fcl_tc; moi_fcl_wc; ARITH_EQ]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; FORALL_PAIR_THM; moi_fcl_face;
                FST; SND; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `j:num`] THEN STRIP_TAC THEN
    REWRITE_TAC[moi_fcl_tgt] THEN
    ASM_CASES_TAC `t:real^N->bool = s` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
      SUBGOAL_THEN `j = 0 \/ j = 1` MP_TAC THENL
       [ASM_ARITH_TAC;
        DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
        ASM_REWRITE_TAC[moi_fcl_gc] THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_fcl_dual c t SUBSET moi_fcl_ldual c (s:real^N->bool) /\
                  moi_fcl_ldual c s SUBSET moi_fcl_dual c s`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MOI_FCL_DUAL_MONO] THEN
      REWRITE_TAC[MOI_FCL_LDUAL_EQ] THEN
      MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_fcl_lv l (h:real^N->real^1) j SUBSET moi_fcl_lv l h 2`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `moi_fcl_dual c s INTER moi_fcl_lv l (h:real^N->real^1) 2 =
                 moi_fcl_wc c h s` THEN
    REWRITE_TAC[moi_fcl_gc] THEN
    UNDISCH_TAC `moi_fcl_dual c t SUBSET moi_fcl_ldual c (s:real^N->bool)` THEN
    UNDISCH_TAC `moi_fcl_ldual c s SUBSET moi_fcl_dual c (s:real^N->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `s:real^N->bool`] MOI_FCL_WC_LDUAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_fcl_gc; UNION_SUBSET] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `(s:real^N->bool),1` THEN
    ASM_REWRITE_TAC[moi_fcl_face; moi_fcl_tgt; FST; SND; PAIR_EQ; SUBSET_REFL] THEN
    ARITH_TAC;
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `(t:real^N->bool),2` THEN
    ASM_REWRITE_TAC[moi_fcl_face; moi_fcl_tgt; FST; SND; PAIR_EQ; LE_REFL] THEN
    REWRITE_TAC[moi_fcl_wc; moi_fcl_lv; ARITH_EQ];
    MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `(s:real^N->bool),0` THEN
    ASM_REWRITE_TAC[moi_fcl_face; moi_fcl_tgt; FST; SND; PAIR_EQ; SUBSET_REFL] THEN
    ARITH_TAC]);;

(* ========================================================================= *)
(* The generic assembly over a face-closed set of labels: given the source   *)
(* and target cells of each label, MOI_FCL_ASSEMBLY yields a PL embedding of *)
(* the union of the source cells onto the union of the target cells          *)
(* respecting labels.                                                        *)
(* ========================================================================= *)

let moi_fcl_lab = new_definition
 `moi_fcl_lab (l:(real^N->bool)->bool) =
    {p:(real^N->bool)#num | FST p IN l /\ ~(FST p = {}) /\ SND p <= 2}`;;

let MOI_FCL_LAB_FINITE = prove
 (`!l:(real^N->bool)->bool. FINITE l ==> FINITE (moi_fcl_lab l)`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{(s:real^N->bool),(i:num) | s IN l /\ i IN {0,1,2}}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    REWRITE_TAC[SUBSET; moi_fcl_lab; FORALL_PAIR_THM; IN_ELIM_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `i:num`] THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `i:num`] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_ARITH_TAC]);;

(* Proper faces in a subcomplex of a locally finite complex have smaller   *)
(* dimension.                                                               *)

let MOI_FCL_PROPER_DIM_LT = prove
 (`!(c:(real^N->bool)->bool) s t.
     lf_simplicial_complex c /\ s IN c /\ t IN c /\ s SUBSET t /\ ~(s = t)
     ==> aff_dim s < aff_dim t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX];
    MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_FCL_DIM_FACTS = prove
 (`!(c:(real^N->bool)->bool) l p q.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\
     (!s. s IN l ==> aff_dim s <= &2) /\ p IN moi_fcl_lab l
     ==> moi_fcl_dim p <= 3 /\ moi_fcl_face l p p /\
         (moi_fcl_face l p q ==> q IN moi_fcl_lab l /\
                                 (q = p \/ moi_fcl_dim q < moi_fcl_dim p))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_fcl_lab; IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN l /\ ~(s = {})
                  ==> &0 <= aff_dim s /\ aff_dim s <= &2 /\
                      &(num_of_int(&2 - aff_dim s)) = &2 - aff_dim s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= aff_dim(s:real^N->bool) /\ aff_dim s <= &2` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[AFF_DIM_POS_LE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INT_OF_NUM_OF_INT THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[moi_fcl_dim; moi_fcl_face] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `FST(p:(real^N->bool)#num)`) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_ADD] THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `FST(q:(real^N->bool)#num) = FST(p:(real^N->bool)#num)` THENL
   [ASM_CASES_TAC `SND(q:(real^N->bool)#num) = SND(p:(real^N->bool)#num)` THENL
     [DISJ1_TAC THEN
      ONCE_REWRITE_TAC[GSYM PAIR] THEN ASM_REWRITE_TAC[PAIR_EQ];
      DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `SND(p:(real^N->bool)#num) = 2 /\ ~(SND(q:(real^N->bool)#num) = 2)`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    DISJ2_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `FST(p:(real^N->bool)#num)`;
                   `FST(q:(real^N->bool)#num)`] MOI_FCL_PROPER_DIM_LT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[SUBSET]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `&(num_of_int(&2 - aff_dim(FST(q:(real^N->bool)#num)))) <
      &(num_of_int(&2 - aff_dim(FST(p:(real^N->bool)#num)))):int`
    MP_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `FST(p:(real^N->bool)#num)`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `FST(q:(real^N->bool)#num)`) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `FST(q:(real^N->bool)#num) IN l /\ ~(FST q = {})`
        (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[INT_OF_NUM_LT] THEN
    SUBGOAL_THEN `SND(q:(real^N->bool)#num) = 2 ==> SND(p:(real^N->bool)#num) = 2`
    MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ARITH_TAC]);;

(* The generic assembly over a face-closed set of labels. *)

let MOI_FCL_ASM_GEN = prove
 (`!(c:(real^N->bool)->bool) l h lab.
     FINITE c /\ lf_simplicial_complex c /\ simplicial_subcomplex l c /\
     moi_frn_sig c l h /\ (!s. s IN l ==> aff_dim s <= &2) /\
     lab SUBSET moi_fcl_lab l /\
     (!p q. p IN lab /\ moi_fcl_face l p q ==> q IN lab) /\
     (!p. p IN lab
          ==> pl_cell_with_boundary (moi_fcl_dim p) (moi_fcl_src l p)
                (UNIONS {moi_fcl_src l q | q | moi_fcl_face l p q /\ ~(q = p)})) /\
     (!p. p IN lab
          ==> pl_cell_with_boundary (moi_fcl_dim p) (moi_fcl_tgt c l h p)
                (UNIONS {moi_fcl_tgt c l h q | q | moi_fcl_face l p q /\ ~(q = p)}))
     ==> ?f. pl_map_on (UNIONS {moi_fcl_src l p | p IN lab}) f /\
             (!x y. x IN UNIONS {moi_fcl_src l p | p IN lab} /\
                    y IN UNIONS {moi_fcl_src l p | p IN lab} /\ f x = f y
                    ==> x = y) /\
             (!p. p IN lab ==> IMAGE f (moi_fcl_src l p) = moi_fcl_tgt c l h p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (lab:(real^N->bool)#num->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `moi_fcl_lab (l:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FCL_LAB_FINITE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `!p:(real^N->bool)#num. p IN lab ==> SND p <= 2` ASSUME_TAC THENL
   [UNDISCH_TAC `lab SUBSET moi_fcl_lab (l:(real^N->bool)->bool)` THEN
    REWRITE_TAC[SUBSET; moi_fcl_lab; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FCL_ASSEMBLY THEN
  MAP_EVERY EXISTS_TAC [`moi_fcl_dim:(real^N->bool)#num->num`;
                        `moi_fcl_face (l:(real^N->bool)->bool)`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `p:(real^N->bool)#num` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `p:(real^N->bool)#num`; `p:(real^N->bool)#num`]
      MOI_FCL_DIM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`p:(real^N->bool)#num`; `q:(real^N->bool)#num`] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `p:(real^N->bool)#num`; `q:(real^N->bool)#num`]
      MOI_FCL_DIM_FACTS) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`p:(real^N->bool)#num`; `q:(real^N->bool)#num`] THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_FCL_SRC_INTER THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`p:(real^N->bool)#num`; `q:(real^N->bool)#num`] THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_FCL_TGT_INTER THEN ASM_SIMP_TAC[];
    X_GEN_TAC `x:real^(N,1)finite_sum` THEN DISCH_TAC THEN
    EXISTS_TAC `(:real^(N,1)finite_sum)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `lab:(real^N->bool)#num->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `lab:(real^N->bool)#num->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* The cell conditions of the assembly, label by label. *)

let MOI_FCL_SRC_CELL = prove
 (`!(c:(real^N->bool)->bool) l s i.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\
     s IN l /\ ~(s = {}) /\ aff_dim s <= &2 /\ i <= 2 /\
     pl_cell_with_boundary (num_of_int(&2 - aff_dim s)) (moi_fcl_dual l s)
                           (moi_fcl_ldual l s)
     ==> pl_cell_with_boundary (moi_fcl_dim (s,i)) (moi_fcl_src l (s,i))
           (UNIONS {moi_fcl_src l q | q | moi_fcl_face l (s,i) q /\ ~(q = (s,i))})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `num_of_int(&2 - aff_dim(s:real^N->bool)) <= 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `&0 <= aff_dim(s:real^N->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[AFF_DIM_POS_LE]; ALL_TAC] THEN
    MP_TAC(ISPEC `&2 - aff_dim(s:real^N->bool)` INT_OF_NUM_OF_INT) THEN
    ANTS_TAC THENL [ASM_INT_ARITH_TAC; DISCH_TAC] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `i <= 2` THEN REWRITE_TAC[ARITH_RULE `i <= 2 <=> i <= 1 \/ i = 2`] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `s:real^N->bool`; `i:num`] MOI_FCL_SRC_BD01) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[moi_fcl_dim; moi_fcl_src; FST; SND] THEN
    ASM_SIMP_TAC[ARITH_RULE `i <= 1 ==> ~(i = 2)`; ADD_CLAUSES] THEN
    UNDISCH_TAC `i <= 1` THEN REWRITE_TAC[ARITH_RULE `i <= 1 <=> i = 0 \/ i = 1`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[moi_fcl_ival; ARITH_EQ] THEN
    MATCH_MP_TAC MOI_FCL_SLICE_CELL THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `s:real^N->bool`] MOI_FCL_SRC_BD2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[moi_fcl_dim; moi_fcl_src; FST; SND; moi_fcl_ival; ARITH_EQ] THEN
    MATCH_MP_TAC MOI_FCL_PRISM_CELL THEN ASM_REWRITE_TAC[]]);;

let MOI_FCL_TGT_CELL = prove
 (`!(c:(real^N->bool)->bool) l h s i.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h /\
     s IN l /\ ~(s = {}) /\ i <= 2 /\
     (i = 0 ==> pl_cell_with_boundary (num_of_int(&2 - aff_dim s))
                  (moi_fcl_dual l s) (moi_fcl_ldual l s)) /\
     (i = 1 ==> pl_cell_with_boundary (num_of_int(&2 - aff_dim s))
                  (moi_fcl_tc c h s) (moi_fcl_tc c h s INTER moi_fcl_ldual c s)) /\
     (i = 2 ==> pl_cell_with_boundary (num_of_int(&2 - aff_dim s) + 1)
                  (moi_fcl_wc c h s) (moi_fcl_gc c h s UNION moi_fcl_dual l s))
     ==> pl_cell_with_boundary (moi_fcl_dim (s,i)) (moi_fcl_tgt c l h (s,i))
           (UNIONS {moi_fcl_tgt c l h q | q |
                    moi_fcl_face l (s,i) q /\ ~(q = (s,i))})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_FCL_DUAL_SUB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `i <= 2` THEN
  REWRITE_TAC[ARITH_RULE `i <= 2 <=> i = 0 \/ i = 1 \/ i = 2`] THEN
  STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `s:real^N->bool`; `0`] MOI_FCL_TGT_BD01) THEN
    ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_REWRITE_TAC[moi_fcl_dim; moi_fcl_tgt; moi_fcl_lv; FST; SND; ARITH_EQ;
                    ADD_CLAUSES];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `s:real^N->bool`; `1`] MOI_FCL_TGT_BD01) THEN
    ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[moi_fcl_dim; moi_fcl_tgt; FST; SND; ARITH_EQ; ADD_CLAUSES] THEN
    SUBGOAL_THEN
     `moi_fcl_dual c s INTER moi_fcl_lv l h 1 = moi_fcl_tc c h (s:real^N->bool) /\
      moi_fcl_ldual c s INTER moi_fcl_lv l h 1 =
      moi_fcl_tc c h s INTER moi_fcl_ldual c s`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    REWRITE_TAC[moi_fcl_lv; moi_fcl_tc; ARITH_EQ] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `s:real^N->bool`]
      MOI_FCL_DUAL_MONO) THEN SET_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `s:real^N->bool`] MOI_FCL_TGT_BD2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[moi_fcl_dim; moi_fcl_tgt; FST; SND; moi_fcl_lv; ARITH_EQ] THEN
    REWRITE_TAC[GSYM moi_fcl_wc] THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The cells of the assembly for a finite combinatorial 3-manifold with      *)
(* boundary c, l = boundary_complex c: boundary dual cells, the cells W(s)   *)
(* (dimension 3 - dim s), and the arcs T(e) at boundary edges.               *)
(* ========================================================================= *)

let MOI_FCL_BD_AFF_DIM = prove
 (`!(c:(real^N->bool)->bool) s.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     s IN boundary_complex c
     ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MATCH_MP_TAC MOI_FRN_SA_CM_DIM THEN
  EXISTS_TAC `boundary_complex c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
  ASM_MESON_TAC[simplicial_subcomplex]);;

let MOI_FCL_BD_VERTEX = prove
 (`!(c:(real^N->bool)->bool) v.
     {v} IN boundary_complex c ==> {v} IN c /\ v IN complex_boundary c`,
  REWRITE_TAC[boundary_complex; IN_ELIM_THM; SING_SUBSET] THEN MESON_TAC[]);;

let MOI_FCL_DIM3 = prove
 (`!(c:(real^N->bool)->bool) s.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     s IN boundary_complex c /\ ~(s = {})
     ==> 3 <= dimindex(:N)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  SUBGOAL_THEN `?v:real^N. {v} IN boundary_complex c` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
    UNDISCH_TAC `n simplex (s:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?v:real^N. v IN k` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(s:real^N->bool = {})` THEN ASM_REWRITE_TAC[CONVEX_HULL_EMPTY];
      ALL_TAC] THEN
    EXISTS_TAC `v:real^N` THEN
    UNDISCH_TAC `simplicial_subcomplex (boundary_complex c) (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(v:real^N) extreme_point_of s` MP_TAC THENL
     [ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]; ALL_TAC] THEN
    REWRITE_TAC[FACE_OF_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FCL_VERTEX_LDUAL) THEN
  ASM_MESON_TAC[MOI_FCL_BD_VERTEX]);;

(* The boundary dual cells. *)

let MOI_FCL_BD_DUAL_CELL = prove
 (`!(c:(real^N->bool)->bool) s.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     s IN boundary_complex c /\ ~(s = {})
     ==> pl_cell_with_boundary (num_of_int(&2 - aff_dim s))
           (moi_fcl_dual (boundary_complex c) s)
           (moi_fcl_ldual (boundary_complex c) s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_BD_AFF_DIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &0 \/ aff_dim s = &1 \/ aff_dim s = &2`
  MP_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `v:real^N` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [AFF_DIM_EQ_0]) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FCL_VERTEX_CELLS) THEN
    ASM_MESON_TAC[MOI_FCL_BD_VERTEX];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_EDGE_LDUAL_ARC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`;
                   `s1:real^N->bool`; `s2:real^N->bool`] MOI_FCL_EDGE_BD_CELL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_TRIANGLE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[MOI_FCL_POINT_CELL]]);;

(* The cells W(s). *)

let MOI_FCL_BD_W_CELL = prove
 (`!(c:(real^N->bool)->bool) h s.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_frn_sig c (boundary_complex c) h /\
     s IN boundary_complex c /\ ~(s = {})
     ==> pl_cell_with_boundary (num_of_int(&2 - aff_dim s) + 1) (moi_fcl_wc c h s)
           (moi_fcl_gc c h s UNION moi_fcl_dual (boundary_complex c) s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_BD_AFF_DIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_DIM3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &0 \/ aff_dim s = &1 \/ aff_dim s = &2`
  MP_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
    ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN CONV_TAC NUM_REDUCE_CONV THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `v:real^N` SUBST_ALL_TAC o
      GEN_REWRITE_RULE I [AFF_DIM_EQ_0]) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FCL_VERTEX_LDUAL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_FCL_BD_VERTEX]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `{v:real^N}`; `2`] MOI_FCL_GW_CELLS) THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[MOI_FTA_PL_SPHERE_NONEMPTY];
      CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_EDGE_LDUAL_ARC) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `s:real^N->bool`; `1`] MOI_FCL_GW_CELLS) THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    ANTS_TAC THENL
     [CONV_TAC NUM_REDUCE_CONV THEN ASM_ARITH_TAC;
      CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[]];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^N->real^1`; `s:real^N->bool`]
      MOI_FCL_TRI_CELLS) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

(* Dual cells of a finite complex are compact; level sets in them closed. *)

let MOI_FCL_DUAL_COMPACT = prove
 (`!(c:(real^N->bool)->bool) s.
     FINITE c /\ moi_bar_complex c
     ==> compact (moi_fcl_dual c s) /\ compact (moi_fcl_ldual c s) /\
         moi_fcl_dual c s SUBSET UNIONS c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!P. FINITE {convex hull (IMAGE simplex_barycentre f) | f |
                moi_bar_chain (c:(real^N->bool)->bool) f /\ ~(f = {}) /\ P f} /\
        (!f. moi_bar_chain c f ==> compact(convex hull (IMAGE simplex_barycentre f)) /\
             convex hull (IMAGE simplex_barycentre f) SUBSET UNIONS c)`
  ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `{convex hull (IMAGE simplex_barycentre f) | f |
         moi_bar_chain c f /\ ~(f = {}) /\ P f} =
        IMAGE (\f. convex hull (IMAGE simplex_barycentre f))
              {f | f SUBSET (c:(real^N->bool)->bool) /\
                   moi_bar_chain c f /\ ~(f = {}) /\ P f}`
      SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN
        MESON_TAC[moi_bar_chain];
        MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{f | f SUBSET (c:(real^N->bool)->bool)}` THEN
        ASM_SIMP_TAC[FINITE_POWERSET] THEN SET_TAC[]];
      X_GEN_TAC `f:(real^N->bool)->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_CONVEX_HULL THEN MATCH_MP_TAC FINITE_IMP_COMPACT THEN
        MATCH_MP_TAC FINITE_IMAGE THEN ASM_MESON_TAC[moi_bar_chain];
        ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
        ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; EMPTY_SUBSET] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS f:real^N->bool` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MOI_BAR_CHAIN_HULL_SUBSET_MAX THEN
          EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC SUBSET_UNIONS THEN ASM_MESON_TAC[moi_bar_chain]]]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fcl_dual; moi_fcl_ldual] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[FORALL_IN_GSPEC] THEN
    ASM_MESON_TAC[];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN ASM_MESON_TAC[]]);;

let MOI_FCL_LEVEL_CLOSED = prove
 (`!(X:real^N->bool) (h:real^N->real^1) a.
     closed X /\ h continuous_on X
     ==> closed (X INTER {x | drop(h x) = a}) /\
         closed (X INTER {x | a <= drop(h x)})`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`h:real^N->real^1`; `X:real^N->bool`; `{lift a}`]
      CONTINUOUS_CLOSED_PREIMAGE) THEN
    ASM_REWRITE_TAC[CLOSED_SING] THEN
    MATCH_MP_TAC(TAUT `p = q ==> p ==> q`) THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING] THEN
    REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP];
    MP_TAC(ISPECL [`h:real^N->real^1`; `X:real^N->bool`; `{y:real^1 | y$1 >= a}`]
      CONTINUOUS_CLOSED_PREIMAGE) THEN
    ASM_REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE] THEN
    MATCH_MP_TAC(TAUT `p = q ==> p ==> q`) THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; drop; real_ge]]);;

(* The proper cofaces in l of a boundary edge are its two triangles. *)

let MOI_FCL_EDGE_COFACES = prove
 (`!(c:(real^N->bool)->bool) e.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     e IN boundary_complex c /\ aff_dim e = &1
     ==> ?s1 s2. ~(s1 = s2) /\ s1 IN boundary_complex c /\ s2 IN boundary_complex c /\
                 aff_dim s1 = &2 /\ aff_dim s2 = &2 /\ e SUBSET s1 /\ e SUBSET s2 /\
                 {t | t IN boundary_complex c /\ ~(t = {}) /\ e SUBSET t /\ ~(t = e)} =
                 {s1,s2}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCL_EDGE_LDUAL_ARC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION] o check (fun th ->
    can (find_term ((=) `{s1:real^N->bool,s2}`)) (concl th) &&
    can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th))) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(s1:real^N->bool) IN boundary_complex c /\ aff_dim s1 = &2 /\ e SUBSET s1 /\
    (s2:real^N->bool) IN boundary_complex c /\ aff_dim s2 = &2 /\ e SUBSET s2`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `aff_dim(t:real^N->bool) = &2` (fun th -> ASM_MESON_TAC[th]) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `t:real^N->bool`]
      MOI_FCL_PROPER_DIM_LT) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FCL_BD_AFF_DIM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(e:real^N->bool) IN c /\ t IN c` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [DISCH_THEN SUBST_ALL_TAC THEN
       RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN ASM_INT_ARITH_TAC;
       DISCH_THEN SUBST_ALL_TAC THEN ASM_INT_ARITH_TAC])]);;

(* The top piece at a boundary triangle is the midpoint of the segment to   *)
(* the barycentre of its tetrahedron.                                       *)

let MOI_FCL_TRI_TC_SING = prove
 (`!(c:(real^N->bool)->bool) h s.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_frn_sig c (boundary_complex c) h /\
     s IN boundary_complex c /\ aff_dim s = &2
     ==> ?r. r IN c /\ ~(r IN boundary_complex c) /\ s SUBSET r /\ ~(r = s) /\
             moi_fcl_tc c h s =
             {midpoint(simplex_barycentre s,simplex_barycentre r)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_TRIANGLE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim({}:real^N->bool) = &2` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((r:real^N->bool) IN boundary_complex c)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`] MOI_FCL_BD_AFF_DIM) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `s:real^N->bool`; `r:real^N->bool`]
    MOI_FCL_TRI_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* Top pieces of distinct boundary triangles are disjoint. *)

let MOI_FCL_TC_DISJOINT = prove
 (`!(c:(real^N->bool)->bool) h s1 s2.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_frn_sig c (boundary_complex c) h /\
     s1 IN boundary_complex c /\ s2 IN boundary_complex c /\
     aff_dim s1 = &2 /\ aff_dim s2 = &2 /\ ~(s1 = s2)
     ==> moi_fcl_tc c h s1 INTER moi_fcl_tc c h s2 = {}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `(s1:real^N->bool),1`; `(s2:real^N->bool),1`]
    MOI_FCL_TGT_INTER) THEN
  ASM_REWRITE_TAC[ARITH] THEN
  REWRITE_TAC[moi_fcl_tgt; moi_fcl_lv; moi_fcl_tc; FST; SND; ARITH_EQ] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[EMPTY_UNIONS; FORALL_IN_GSPEC; FORALL_PAIR_THM; moi_fcl_face;
              FST; SND] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `k:num`] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(u:real^N->bool) IN boundary_complex c /\ s1 SUBSET u /\ s2 SUBSET u`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN boundary_complex c /\ aff_dim s = &2 /\
                                 s SUBSET u ==> s = u`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `u:real^N->bool`]
      MOI_FCL_PROPER_DIM_LT) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`] MOI_FCL_BD_AFF_DIM) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(s:real^N->bool) IN c /\ u IN c` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* The top piece at a boundary edge has a point off the link part. *)

let MOI_FCL_TC_OFF_LINK = prove
 (`!(c:(real^N->bool)->bool) h e.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_frn_sig c (boundary_complex c) h /\
     e IN boundary_complex c /\ aff_dim e = &1
     ==> ?x. x IN moi_fcl_tc c h e /\ ~(x IN moi_fcl_ldual c e)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCL_EDGE_COFACES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^N->real^1`; `s1:real^N->bool`]
    MOI_FCL_TRI_TC_SING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(e:real^N->bool = {}) /\ e IN c /\ ~(r:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN ASM_INT_ARITH_TAC;
      ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) SUBSET r /\ ~(r = e)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((e:real^N->bool) IN boundary_complex c)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre r IN moi_fcl_ldual c (e:real^N->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `{r:real^N->bool}` THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY; FORALL_IN_INSERT;
                 NOT_IN_EMPTY; IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCL_LDUAL_RAYS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCL_DUAL_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain c {e:real^N->bool,r}` ASSUME_TAC THENL
   [REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT;
                FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `{e:real^N->bool,r}`] MOI_FCL_SIG_AFFINE_FN) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                  IMAGE_CLAUSES; GSYM SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fl:real^N->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Fl:real^N->real`; `simplex_barycentre e:real^N`;
                 `simplex_barycentre r:real^N`] MOI_FCL_SEG_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `midpoint(simplex_barycentre e,simplex_barycentre r:real^N)` o
    GEN_REWRITE_RULE I [EXTENSION] o CONJUNCT1) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN STRIP_TAC THEN
  EXISTS_TAC `midpoint(simplex_barycentre e,simplex_barycentre r:real^N)` THEN
  SUBGOAL_THEN `midpoint(simplex_barycentre e,simplex_barycentre r:real^N) IN
                segment[simplex_barycentre e,simplex_barycentre r]`
  ASSUME_TAC THENL [REWRITE_TAC[MIDPOINT_IN_SEGMENT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_fcl_tc; IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `segment[simplex_barycentre e,simplex_barycentre r:real^N]` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `simplex_barycentre r:real^N` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    DISCH_TAC THEN
    SUBGOAL_THEN `midpoint(simplex_barycentre e,simplex_barycentre r:real^N) =
                  simplex_barycentre r` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[MIDPOINT_EQ_ENDPOINT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `r:real^N->bool`]
      MOI_FTA_BARY_INJ) THEN
    ASM_REWRITE_TAC[]]);;

(* The top piece at a boundary edge is an arc bounded by the top points of  *)
(* its two triangles: it is the complement, in the boundary circle of W(e), *)
(* of the arc formed by the bottom cell and the sides W(s1), W(s2).        *)

let MOI_FCL_EDGE_T_ARC = prove
 (`!(c:(real^N->bool)->bool) h e.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_frn_sig c (boundary_complex c) h /\
     e IN boundary_complex c /\ aff_dim e = &1
     ==> pl_cell_with_boundary 1 (moi_fcl_tc c h e)
           (moi_fcl_tc c h e INTER moi_fcl_ldual c e)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  SUBGOAL_THEN `~(e:real^N->bool = {}) /\ e IN c` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN ASM_INT_ARITH_TAC;
      ASM_MESON_TAC[simplicial_subcomplex; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FCL_EDGE_COFACES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `s2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^N->real^1`; `s1:real^N->bool`]
    MOI_FCL_TRI_TC_SING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^N->real^1`; `s2:real^N->bool`]
    MOI_FCL_TRI_TC_SING) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real^N->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `m1 = midpoint(simplex_barycentre s1,simplex_barycentre r1:real^N)` THEN
  ABBREV_TAC `m2 = midpoint(simplex_barycentre s2,simplex_barycentre r2:real^N)` THEN
  SUBGOAL_THEN `~(m1:real^N = m2)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^N->real^1`;
                   `s1:real^N->bool`; `s2:real^N->bool`] MOI_FCL_TC_DISJOINT) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the link part of the top piece *)
  SUBGOAL_THEN `moi_fcl_tc c h e INTER moi_fcl_ldual c e = {m1:real^N,m2}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `e:real^N->bool`] MOI_FCL_WC_LDUAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN
     `{moi_fcl_tc c h t | t | t IN boundary_complex c /\ ~(t = {}) /\
                              e SUBSET t /\ ~(t = e)} =
      {moi_fcl_tc c h (s1:real^N->bool),moi_fcl_tc c h s2}`
    SUBST1_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION] o check (fun th ->
        can (find_term ((=) `{s1:real^N->bool,s2}`)) (concl th) &&
        is_eq (concl th))) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN DISCH_TAC THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      REWRITE_TAC[UNIONS_2] THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* the boundary circle of W(e) *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^N->real^1`; `e:real^N->bool`]
    MOI_FCL_BD_W_CELL) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `2 = 1 + 1`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S4O_CELL_SPHERE) THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_S4O_CIRCLE_ARC THEN
  MAP_EVERY EXISTS_TAC
   [`moi_fcl_gc c h e UNION moi_fcl_dual (boundary_complex c) (e:real^N->bool)`;
    `(moi_fcl_wc c h e INTER moi_fcl_ldual c e) UNION moi_fcl_dual (boundary_complex c) (e:real^N->bool)`]
  THEN ASM_REWRITE_TAC[] THEN
  (* facts on levels and closedness *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                 `h:real^N->real^1`] MOI_FCL_LV_LEVELS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_fcl_dual (boundary_complex c) (e:real^N->bool) SUBSET UNIONS (boundary_complex c)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                   `e:real^N->bool`] MOI_FCL_DUAL_SUB) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fcl_tc c h e INTER moi_fcl_dual (boundary_complex c) (e:real^N->bool) = {}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fcl_lv (boundary_complex c) (h:real^N->real^1) 0 INTER
                 moi_fcl_lv (boundary_complex c) h 1 = {}` THEN
    REWRITE_TAC[moi_fcl_lv; moi_fcl_tc; ARITH_EQ] THEN
    UNDISCH_TAC `moi_fcl_dual (boundary_complex c) (e:real^N->bool) SUBSET UNIONS (boundary_complex c)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fcl_tc c h e SUBSET moi_fcl_wc c h (e:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fcl_tc; moi_fcl_wc] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact (moi_fcl_dual c (e:real^N->bool)) /\ compact (moi_fcl_ldual c e) /\
    moi_fcl_dual c e SUBSET UNIONS c /\ compact (moi_fcl_dual (boundary_complex c) e)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FCL_DUAL_COMPACT] THEN
    MP_TAC(ISPECL [`boundary_complex c:(real^N->bool)->bool`; `e:real^N->bool`]
      MOI_FCL_DUAL_COMPACT) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^1) continuous_on moi_fcl_dual c e` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_MESON_TAC[moi_frn_sig];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fcl_dual c (e:real^N->bool)`; `h:real^N->real^1`; `&1 / &2`]
    MOI_FCL_LEVEL_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  REWRITE_TAC[GSYM moi_fcl_tc; GSYM moi_fcl_wc] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_fcl_gc] THEN ASM SET_TAC[];
    MATCH_MP_TAC CLOSED_UNION THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_INTER];
    ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    (* A is not inside {m1,m2}: the barycentre of e *)
    SUBGOAL_THEN `simplex_barycentre e IN moi_fcl_dual (boundary_complex c) (e:real^N->bool)` MP_TAC THENL
     [REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `{e:real^N->bool}` THEN
      ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY; FORALL_IN_INSERT;
                   NOT_IN_EMPTY; IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING;
                   SUBSET_REFL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(m1:real^N) IN moi_fcl_tc c h e /\ m2 IN moi_fcl_tc c h e`
    MP_TAC THENL
     [UNDISCH_TAC `moi_fcl_tc c h e INTER moi_fcl_ldual c e = {m1:real^N,m2}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_fcl_tc c h e INTER moi_fcl_dual (boundary_complex c) (e:real^N->bool) = {}` THEN
    SET_TAC[];
    (* B is not inside {m1,m2}: a point off the link part *)
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^N->real^1`; `e:real^N->bool`]
      MOI_FCL_TC_OFF_LINK) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `moi_fcl_tc c h e INTER moi_fcl_ldual c e = {m1:real^N,m2}` THEN
    UNDISCH_TAC `~((x:real^N) IN moi_fcl_ldual c e)` THEN
    UNDISCH_TAC `(x:real^N) IN moi_fcl_tc c h e` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* The first assembly stage (all labels except the top and prism of boundary *)
(* vertices) and its consequences: the boundary J(v) of the top piece at a   *)
(* boundary vertex v is a PL circle, and T(v) is a PL disk by                *)
(* MOI_S4O_SPHERE_PIECE in the boundary 2-sphere of W(v).                    *)
(* ========================================================================= *)

(* The midpoint of the segment from b(s) to b(r), r a simplex above s not  *)
(* in l, is a point of the top piece T(s) off the link part.               *)

let MOI_FCL_TC_OFF_LINK_GEN = prove
 (`!(c:(real^N->bool)->bool) l h s r.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h /\
     s IN l /\ ~(s = {}) /\ r IN c /\ ~(r IN l) /\ s SUBSET r
     ==> midpoint(simplex_barycentre s,simplex_barycentre r) IN moi_fcl_tc c h s /\
         ~(midpoint(simplex_barycentre s,simplex_barycentre r) IN moi_fcl_ldual c s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN c /\ ~(r:real^N->bool = {}) /\ ~(r = s)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
      ASM SET_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre r IN moi_fcl_ldual c (s:real^N->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `{r:real^N->bool}` THEN
    ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY; FORALL_IN_INSERT;
                 NOT_IN_EMPTY; IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_LDUAL_RAYS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FCL_DUAL_CONE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain c {s:real^N->bool,r}` ASSUME_TAC THENL
   [REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT;
                FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `{s:real^N->bool,r}`] MOI_FCL_SIG_AFFINE_FN) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
                  IMAGE_CLAUSES; GSYM SEGMENT_CONVEX_HULL] THEN
  DISCH_THEN(X_CHOOSE_THEN `Fl:real^N->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`Fl:real^N->real`; `simplex_barycentre s:real^N`;
                 `simplex_barycentre r:real^N`] MOI_FCL_SEG_LEVEL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `midpoint(simplex_barycentre s,simplex_barycentre r:real^N)` o
    GEN_REWRITE_RULE I [EXTENSION] o CONJUNCT1) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN STRIP_TAC THEN
  SUBGOAL_THEN `midpoint(simplex_barycentre s,simplex_barycentre r:real^N) IN
                segment[simplex_barycentre s,simplex_barycentre r]`
  ASSUME_TAC THENL [REWRITE_TAC[MIDPOINT_IN_SEGMENT]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[moi_fcl_tc; IN_INTER; IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `segment[simplex_barycentre s,simplex_barycentre r:real^N]` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `simplex_barycentre r:real^N` THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    DISCH_TAC THEN
    SUBGOAL_THEN `midpoint(simplex_barycentre s,simplex_barycentre r:real^N) =
                  simplex_barycentre r` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[MIDPOINT_EQ_ENDPOINT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `r:real^N->bool`]
      MOI_FTA_BARY_INJ) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* A boundary vertex lies in a tetrahedron, which is not in the boundary.  *)

let MOI_FCL_VERTEX_TET = prove
 (`!(c:(real^N->bool)->bool) v.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     {v} IN boundary_complex c
     ==> ?r. r IN c /\ ~(r IN boundary_complex c) /\ {v} SUBSET r`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FCL_BD_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(v:real^N) IN complex_boundary c` THEN
  REWRITE_TAC[MOI_FCL_CB_TRIANGLES; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:real^N->bool) IN boundary_complex c` ASSUME_TAC THENL
   [REWRITE_TAC[boundary_complex; IN_ELIM_THM; MOI_FCL_CB_TRIANGLES] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FCL_TRIANGLE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`] MOI_FCL_BD_AFF_DIM) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ASM SET_TAC[]]);;

(* Stage one: labels other than the top and prism of boundary vertices. *)

let moi_fcl_lab1 = new_definition
 `moi_fcl_lab1 (l:(real^N->bool)->bool) =
    {p:(real^N->bool)#num | p IN moi_fcl_lab l /\
                            (~(aff_dim (FST p) = &0) \/ SND p = 0)}`;;

let MOI_FCL_LAB1_CLOSED = prove
 (`!(c:(real^N->bool)->bool) l p q.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\
     (!s. s IN l ==> aff_dim s <= &2) /\
     p IN moi_fcl_lab1 l /\ moi_fcl_face l p q
     ==> q IN moi_fcl_lab1 l`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fcl_lab1; IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `p:(real^N->bool)#num`; `q:(real^N->bool)#num`] MOI_FCL_DIM_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN
    UNDISCH_TAC `moi_fcl_face l (p:(real^N->bool)#num) q` THEN
    UNDISCH_TAC `p IN moi_fcl_lab (l:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_fcl_face; moi_fcl_lab; IN_ELIM_THM] THEN STRIP_TAC THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`FST(p:(real^N->bool)#num)`; `FST(q:(real^N->bool)#num)`]
      AFF_DIM_SUBSET) THEN
    MP_TAC(ISPEC `FST(p:(real^N->bool)#num)` AFF_DIM_POS_LE) THEN
    ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
    UNDISCH_TAC `moi_fcl_face l (p:(real^N->bool)#num) q` THEN
    REWRITE_TAC[moi_fcl_face] THEN ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let MOI_FCL_STAGE1 = prove
 (`!(c:(real^N->bool)->bool) h.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_frn_sig c (boundary_complex c) h
     ==> ?f. pl_map_on (UNIONS {moi_fcl_src (boundary_complex c) p |
                                p | p IN moi_fcl_lab1 (boundary_complex c)}) f /\
             (!x y. x IN UNIONS {moi_fcl_src (boundary_complex c) p |
                                 p | p IN moi_fcl_lab1 (boundary_complex c)} /\
                    y IN UNIONS {moi_fcl_src (boundary_complex c) p |
                                 p | p IN moi_fcl_lab1 (boundary_complex c)} /\
                    f x = f y ==> x = y) /\
             (!p. p IN moi_fcl_lab1 (boundary_complex c)
                  ==> IMAGE f (moi_fcl_src (boundary_complex c) p) =
                      moi_fcl_tgt c (boundary_complex c) h p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN boundary_complex c ==> aff_dim s <= &2`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FCL_BD_AFF_DIM]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FCL_ASM_GEN THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_fcl_lab1] THEN SET_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FCL_LAB1_CLOSED THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `p:(real^N->bool)#num`] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[FORALL_PAIR_THM; moi_fcl_lab1; moi_fcl_lab; IN_ELIM_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `i:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FCL_SRC_CELL THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FCL_BD_DUAL_CELL];
    REWRITE_TAC[FORALL_PAIR_THM; moi_fcl_lab1; moi_fcl_lab; IN_ELIM_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `i:num`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FCL_TGT_CELL THEN
    ASM_SIMP_TAC[MOI_FCL_BD_DUAL_CELL; MOI_FCL_BD_W_CELL] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ARITH_EQ]) THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &2` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) = &1 \/ aff_dim s = &2` MP_TAC THENL
     [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN
      ASM_SIMP_TAC[] THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM] THENL
     [MATCH_MP_TAC MOI_FCL_EDGE_T_ARC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^N->real^1`; `s:real^N->bool`]
        MOI_FCL_TRI_CELLS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]]]);;

(* The slice map y |-> (y,a). *)

let MOI_FCL_SLICE_MAP = prove
 (`!(X:real^N->bool) (a:real^1).
     locally_polyhedral X
     ==> pl_map_on X (\y. pastecart y a) /\
         IMAGE (\y. pastecart y a) X = X PCROSS {a} /\
         (!x y:real^N. pastecart x a = pastecart y a ==> x = y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_PASTECART THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID; ETA_AX];
      MATCH_MP_TAC PL_MAP_ON_CONST THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[EXTENSION; IN_IMAGE; FORALL_PASTECART; PASTECART_IN_PCROSS;
                PASTECART_INJ; IN_SING] THEN MESON_TAC[];
    REWRITE_TAC[PASTECART_INJ] THEN MESON_TAC[]]);;

(* The circle J(v) at a boundary vertex. *)

let MOI_FCL_JV_CIRCLE = prove
 (`!(c:(real^N->bool)->bool) h v.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_frn_sig c (boundary_complex c) h /\ {v} IN boundary_complex c
     ==> pl_sphere 1 (moi_fcl_tc c h {v} INTER moi_fcl_ldual c {v})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^N->real^1`] MOI_FCL_STAGE1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(N,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FCL_VERTEX_LDUAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_FCL_BD_VERTEX]; STRIP_TAC] THEN
  ABBREV_TAC `L = moi_fcl_ldual (boundary_complex c) {v:real^N}` THEN
  SUBGOAL_THEN `locally_polyhedral (L:real^N->bool) /\ compact L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      ASM_MESON_TAC[MOI_S4O_SPHERE_POLY];
      EXPAND_TAC "L" THEN
      MP_TAC(ISPECL [`boundary_complex c:(real^N->bool)->bool`; `{v:real^N}`]
        MOI_FCL_DUAL_COMPACT) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[simplicial_subcomplex]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->bool`; `vec 1:real^1`] MOI_FCL_SLICE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the slice of the circle is the union of the stage-one tops above v *)
  SUBGOAL_THEN
   `UNIONS {moi_fcl_src (boundary_complex c) m | m |
            moi_fcl_face (boundary_complex c) ({v:real^N},1) m /\ ~(m = ({v},1))} =
    L PCROSS {vec 1:real^1}`
  (LABEL_TAC "slice") THENL
   [EXPAND_TAC "L" THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                   `{v:real^N}`; `1`] MOI_FCL_SRC_BD01) THEN
    ASM_REWRITE_TAC[ARITH] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[moi_fcl_ival; ARITH_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. moi_fcl_face (boundary_complex c) ({v:real^N},1) m /\ ~(m = ({v},1))
        ==> m IN moi_fcl_lab1 (boundary_complex c)`
  ASSUME_TAC THENL
   [REWRITE_TAC[FORALL_PAIR_THM; moi_fcl_face; moi_fcl_lab1; moi_fcl_lab;
                IN_ELIM_THM; FST; SND; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `j:num`] THEN
    DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
    SUBGOAL_THEN `j = 1 /\ ~(t:real^N->bool = {v})` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[ARITH_RULE `~(1 = 2)`]; ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(t:real^N->bool) = &0)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{v:real^N}`; `t:real^N->bool`]
        MOI_FCL_PROPER_DIM_LT) THEN
      REWRITE_TAC[AFF_DIM_SING] THEN
      ANTS_TAC THENL [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; INT_ARITH_TAC];
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^(N,1)finite_sum->real^N) (L PCROSS {vec 1}) =
    moi_fcl_tc c h {v} INTER moi_fcl_ldual c {v}`
  ASSUME_TAC THENL
   [USE_THEN "slice" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[IMAGE_UNIONS] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `{v:real^N}`; `1`] MOI_FCL_TGT_BD01) THEN
    ASM_REWRITE_TAC[ARITH] THEN
    SUBGOAL_THEN
     `moi_fcl_ldual c {v} INTER moi_fcl_lv (boundary_complex c) h 1 =
      moi_fcl_tc c h {v:real^N} INTER moi_fcl_ldual c {v}`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_fcl_lv; moi_fcl_tc; ARITH_EQ] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{v:real^N}`; `{v:real^N}`]
        MOI_FCL_DUAL_MONO) THEN SET_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM)] THEN
    AP_TERM_TAC THEN
    REWRITE_TAC[SET_RULE
     `!(g:real^(N,1)finite_sum->real^N) (f:(real^N->bool)#num->real^(N,1)finite_sum->bool) P.
        IMAGE (IMAGE g) {f m | m | P m} = {IMAGE g (f m) | m | P m}`] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(L:real^N->bool) PCROSS {vec 1} SUBSET
    UNIONS {moi_fcl_src (boundary_complex c) p | p |
            p IN moi_fcl_lab1 (boundary_complex c)}`
  ASSUME_TAC THENL
   [USE_THEN "slice" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `m:(real^N->bool)#num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(SET_RULE `(x:real^(N,1)finite_sum->bool) IN s ==> x SUBSET UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `m:(real^N->bool)#num` THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->bool`;
                 `(f:real^(N,1)finite_sum->real^N) o (\y:real^N. pastecart y (vec 1:real^1))`]
    MOI_FCL_PLH_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
      EXISTS_TAC `UNIONS {moi_fcl_src (boundary_complex c) p | p |
                          p IN moi_fcl_lab1 (boundary_complex (c:(real^N->bool)->bool))}` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `pastecart (x:real^N) (vec 1:real^1)`)) (concl th))) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `(f:real^(N,1)finite_sum->real^N) x`)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(L:real^N->bool) PCROSS {vec 1} SUBSET
                   UNIONS {moi_fcl_src (boundary_complex c) p | p |
                           p IN moi_fcl_lab1 (boundary_complex c)}` THEN
      REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_SING] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `g:real^N->real^N`) THEN
  MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
  MAP_EVERY EXISTS_TAC [`L:real^N->bool`;
    `(f:real^(N,1)finite_sum->real^N) o (\y:real^N. pastecart y (vec 1:real^1))`;
    `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `IMAGE ((f:real^(N,1)finite_sum->real^N) o (\y:real^N. pastecart y (vec 1:real^1))) L =
    moi_fcl_tc c h {v} INTER moi_fcl_ldual c {v}`
  (fun th -> ASM_MESON_TAC[th]) THEN
  ASM_REWRITE_TAC[IMAGE_o]);;

(* The top piece at a boundary vertex is a disk bounded by J(v). *)

let MOI_FCL_VERTEX_T_DISK = prove
 (`!(c:(real^N->bool)->bool) h v.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_frn_sig c (boundary_complex c) h /\ {v} IN boundary_complex c
     ==> pl_cell_with_boundary 2 (moi_fcl_tc c h {v})
           (moi_fcl_tc c h {v} INTER moi_fcl_ldual c {v})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  SUBGOAL_THEN `{v:real^N} IN c /\ ~({v:real^N} = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FCL_BD_VERTEX; NOT_INSERT_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^N->real^1`; `{v:real^N}`]
    MOI_FCL_BD_W_CELL) THEN
  ASM_REWRITE_TAC[AFF_DIM_SING] THEN CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
  REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[ARITH_RULE `3 = 2 + 1`] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S4O_CELL_SPHERE) THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_S4O_SPHERE_PIECE THEN
  EXISTS_TAC `moi_fcl_gc c h {v} UNION moi_fcl_dual (boundary_complex c) {v:real^N}` THEN
  ASM_SIMP_TAC[MOI_FCL_JV_CIRCLE; INTER_SUBSET] THEN
  (* levels, closedness *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                 `h:real^N->real^1`] MOI_FCL_LV_LEVELS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_fcl_dual (boundary_complex c) {v:real^N} SUBSET
                UNIONS (boundary_complex c)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                   `{v:real^N}`] MOI_FCL_DUAL_SUB) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fcl_tc c h {v} INTER
                moi_fcl_dual (boundary_complex c) {v:real^N} = {}`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fcl_lv (boundary_complex c) (h:real^N->real^1) 0 INTER
                 moi_fcl_lv (boundary_complex c) h 1 = {}` THEN
    REWRITE_TAC[moi_fcl_lv; moi_fcl_tc; ARITH_EQ] THEN
    UNDISCH_TAC `moi_fcl_dual (boundary_complex c) {v:real^N} SUBSET
                 UNIONS (boundary_complex c)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fcl_tc c h {v} SUBSET moi_fcl_wc c h {v:real^N}` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fcl_tc; moi_fcl_wc] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[REAL_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `compact (moi_fcl_dual c {v:real^N}) /\ compact (moi_fcl_ldual c {v}) /\
    moi_fcl_dual c {v} SUBSET UNIONS c /\
    compact (moi_fcl_dual (boundary_complex c) {v})`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FCL_DUAL_COMPACT] THEN
    MP_TAC(ISPECL [`boundary_complex c:(real^N->bool)->bool`; `{v:real^N}`]
      MOI_FCL_DUAL_COMPACT) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^1) continuous_on moi_fcl_dual c {v}` ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_MESON_TAC[moi_frn_sig];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fcl_dual c {v:real^N}`; `h:real^N->real^1`; `&1 / &2`]
    MOI_FCL_LEVEL_CLOSED) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
  REWRITE_TAC[GSYM moi_fcl_tc; GSYM moi_fcl_wc] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_fcl_gc] THEN SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `((moi_fcl_wc c h {v} INTER moi_fcl_ldual c {v}) UNION
                 moi_fcl_dual (boundary_complex c) {v:real^N}) INTER
                moi_fcl_tc c h {v}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> s INTER u SUBSET t INTER u`) THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
       [REWRITE_TAC[moi_fcl_gc] THEN SET_TAC[];
        MATCH_MP_TAC CLOSED_UNION THEN
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_INTER]];
      UNDISCH_TAC `moi_fcl_tc c h {v} INTER
                   moi_fcl_dual (boundary_complex c) {v:real^N} = {}` THEN
      UNDISCH_TAC `moi_fcl_tc c h {v} SUBSET moi_fcl_wc c h {v:real^N}` THEN
      SET_TAC[]];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FCL_VERTEX_TET) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `{v:real^N}`; `r:real^N->bool`]
      MOI_FCL_TC_OFF_LINK_GEN) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    SUBGOAL_THEN `(v:real^N) IN moi_fcl_dual (boundary_complex c) {v}` MP_TAC THENL
     [REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `{{v:real^N}}` THEN
      ASM_SIMP_TAC[MOI_FTA_CHAIN_SING; NOT_INSERT_EMPTY; FORALL_IN_INSERT;
                   NOT_IN_EMPTY; IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING;
                   SUBSET_REFL; MOI_FTA_BARY_SING];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_fcl_tc c h {v} INTER
                 moi_fcl_dual (boundary_complex c) {v:real^N} = {}` THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* The second assembly stage (all labels) and the collar of the boundary of  *)
(* a finite combinatorial 3-manifold c at the level 1/2 of the weight: a PL  *)
(* homeomorphism of B PCROSS [0,1] onto W = {weight >= 1/2}, B =             *)
(* complex_boundary c, fixing B PCROSS {0} pointwise (bottom fix).           *)
(* ========================================================================= *)

let MOI_FCL_STAGE2 = prove
 (`!(c:(real^N->bool)->bool) h.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_frn_sig c (boundary_complex c) h
     ==> ?f. pl_map_on (UNIONS {moi_fcl_src (boundary_complex c) p |
                                p | p IN moi_fcl_lab (boundary_complex c)}) f /\
             (!x y. x IN UNIONS {moi_fcl_src (boundary_complex c) p |
                                 p | p IN moi_fcl_lab (boundary_complex c)} /\
                    y IN UNIONS {moi_fcl_src (boundary_complex c) p |
                                 p | p IN moi_fcl_lab (boundary_complex c)} /\
                    f x = f y ==> x = y) /\
             (!p. p IN moi_fcl_lab (boundary_complex c)
                  ==> IMAGE f (moi_fcl_src (boundary_complex c) p) =
                      moi_fcl_tgt c (boundary_complex c) h p)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN boundary_complex c ==> aff_dim s <= &2`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_FCL_BD_AFF_DIM]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FCL_ASM_GEN THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                   `p:(real^N->bool)#num`; `q:(real^N->bool)#num`] MOI_FCL_DIM_FACTS) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[FORALL_PAIR_THM; moi_fcl_lab; IN_ELIM_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `i:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FCL_SRC_CELL THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FCL_BD_DUAL_CELL];
    REWRITE_TAC[FORALL_PAIR_THM; moi_fcl_lab; IN_ELIM_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `i:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_FCL_TGT_CELL THEN
    ASM_SIMP_TAC[MOI_FCL_BD_DUAL_CELL; MOI_FCL_BD_W_CELL] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &2` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `aff_dim(s:real^N->bool) = &0 \/ aff_dim s = &1 \/ aff_dim s = &2` MP_TAC THENL
     [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN
      ASM_SIMP_TAC[] THEN ASM_INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC(ONCE_DEPTH_CONV INT_REDUCE_CONV) THEN
    REWRITE_TAC[NUM_OF_INT_OF_NUM] THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `v:real^N` SUBST_ALL_TAC o
        GEN_REWRITE_RULE I [AFF_DIM_EQ_0]) THEN
      MATCH_MP_TAC MOI_FCL_VERTEX_T_DISK THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FCL_EDGE_T_ARC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^N->real^1`; `s:real^N->bool`]
        MOI_FCL_TRI_CELLS) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]]]);;

(* A complex is the union of the dual cells of its nonempty simplices. *)

let MOI_FCL_UNIONS_DUAL = prove
 (`!l:(real^N->bool)->bool.
     moi_bar_complex l
     ==> UNIONS {moi_fcl_dual l s | s | s IN l /\ ~(s = {})} = UNIONS l`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[moi_fcl_dual; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS g:real^N->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_HULL_SUBSET_MAX THEN
      EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_UNIONS THEN ASM_MESON_TAC[moi_bar_chain]];
    ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV
    [GSYM(MATCH_MP MOI_BAR_UNIONS_SUBDIVISION th)]) THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; MOI_BAR_IN_SUBDIVISION] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(x:real^N) IN m` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
    MOI_FTA_CHAIN_MIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `moi_fcl_dual l (INTERS g:real^N->bool)` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `INTERS g:real^N->bool` THEN
    REWRITE_TAC[] THEN ASM_MESON_TAC[moi_bar_chain; SUBSET];
    REWRITE_TAC[MOI_FCL_IN_DUAL] THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[]]);;

(* The source cells cover B PCROSS [0,1]; the target cells cover W. *)

let MOI_FCL_SRC_UNION = prove
 (`!(c:(real^N->bool)->bool) l.
     lf_simplicial_complex c /\ simplicial_subcomplex l c
     ==> UNIONS {moi_fcl_src l p | p | p IN moi_fcl_lab l} =
         UNIONS l PCROSS interval[vec 0,vec 1]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR; MOI_FTA_BAR_SUB]; ALL_TAC] THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o LAND_CONV)
    [GSYM(MATCH_MP MOI_FCL_UNIONS_DUAL th)]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; FORALL_PAIR_THM; moi_fcl_lab;
                moi_fcl_src; IN_ELIM_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `i:num`] THEN STRIP_TAC THEN
    MATCH_MP_TAC PCROSS_MONO THEN ASM_SIMP_TAC[MOI_FCL_IVAL_CASES] THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIONS;
                IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^1`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `X:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) ASSUME_TAC) THEN
    EXISTS_TAC `moi_fcl_src l ((s:real^N->bool),2)` THEN CONJ_TAC THENL
     [EXISTS_TAC `(s:real^N->bool),2` THEN
      ASM_REWRITE_TAC[moi_fcl_lab; IN_ELIM_THM; FST; SND; LE_REFL];
      ASM_REWRITE_TAC[moi_fcl_src; FST; SND; MOI_FCL_IVAL_CASES;
                      PASTECART_IN_PCROSS] THEN ASM_MESON_TAC[]]]);;

let MOI_FCL_TGT_UNION = prove
 (`!(c:(real^N->bool)->bool) l h.
     lf_simplicial_complex c /\ simplicial_subcomplex l c /\ moi_frn_sig c l h
     ==> UNIONS {moi_fcl_tgt c l h p | p | p IN moi_fcl_lab l} =
         {x | x IN UNIONS c /\ &1 / &2 <= drop(h x)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FTA_LF_BAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `h:real^N->real^1`] MOI_FCL_LV_LEVELS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!j. j <= 2 ==> moi_fcl_lv l (h:real^N->real^1) j SUBSET moi_fcl_lv l h 2`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[ARITH_RULE `j <= 2 <=> j = 0 \/ j = 1 \/ j = 2`] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. moi_fcl_dual c s SUBSET UNIONS c` ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[moi_fcl_dual; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `g:(real^N->bool)->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `UNIONS g:real^N->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_HULL_SUBSET_MAX THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_UNIONS THEN ASM_MESON_TAC[moi_bar_chain]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; FORALL_PAIR_THM; moi_fcl_lab;
                moi_fcl_tgt; IN_ELIM_THM; FST; SND] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `i:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `moi_fcl_lv l (h:real^N->real^1) i SUBSET moi_fcl_lv l h 2`
    MP_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_fcl_dual c (s:real^N->bool) SUBSET UNIONS c` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_fcl_lv; ARITH_EQ] THEN SET_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?u:real^N->bool. u IN c /\ ~(u = {}) /\ x IN moi_fcl_dual c u`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN UNIONS c` THEN
    MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FCL_UNIONS_DUAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->bool) IN l` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `u:real^N->bool`; `x:real^N`]
      MOI_FCL_SIG_ZERO_DUAL) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `moi_fcl_tgt c l (h:real^N->real^1) ((u:real^N->bool),2)` THEN
  CONJ_TAC THENL
   [EXISTS_TAC `(u:real^N->bool),2` THEN
    ASM_REWRITE_TAC[moi_fcl_lab; IN_ELIM_THM; FST; SND; LE_REFL];
    ASM_REWRITE_TAC[moi_fcl_tgt; moi_fcl_lv; FST; SND; ARITH_EQ; IN_INTER;
                    IN_ELIM_THM]]);;

let MOI_FCL_CB_POLY = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> pl_polyhedron (complex_boundary c) /\ compact (complex_boundary c) /\
         locally_polyhedral (complex_boundary c)`,
  GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  SUBGOAL_THEN `FINITE (boundary_complex c:(real^N->bool)->bool) /\
                (!k:real^N->bool. k IN boundary_complex c ==> polytope k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[simplicial_subcomplex];
      ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_POLYTOPE]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (complex_boundary c:real^N->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `boundary_complex c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
    concl th = `UNIONS (boundary_complex c) = complex_boundary (c:(real^N->bool)->bool)`)) THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT]);;

(* The collar at level 1/2 of the weight. *)

let MOI_FCL_COLLAR_RAW = prove
 (`!(c:(real^N->bool)->bool) h.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_frn_sig c (boundary_complex c) h
     ==> ?p q. pl_homeomorphism
                 (complex_boundary c PCROSS interval[vec 0:real^1,vec 1],
                  {x | x IN UNIONS c /\ &1 / &2 <= drop(h x)}) (p,q) /\
               (!x. x IN complex_boundary c ==> p(pastecart x (vec 0)) = x)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FCL_CB_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:real^N->real^1`] MOI_FCL_STAGE2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^(N,1)finite_sum->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `IMAGE (f:real^(N,1)finite_sum->real^N)
      (UNIONS {moi_fcl_src (boundary_complex c) p | p |
               p IN moi_fcl_lab (boundary_complex c)}) =
    UNIONS {moi_fcl_tgt c (boundary_complex c) h p | p |
            p IN moi_fcl_lab (boundary_complex c)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_UNIONS] THEN AP_TERM_TAC THEN
    REWRITE_TAC[SET_RULE
     `!(g:real^(N,1)finite_sum->real^N) (f:(real^N->bool)#num->real^(N,1)finite_sum->bool) P.
        IMAGE (IMAGE g) {f m | m | P m} = {IMAGE g (f m) | m | P m}`] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`]
    MOI_FCL_SRC_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th1 ->
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                   `h:real^N->real^1`] MOI_FCL_TGT_UNION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th2 ->
      RULE_ASSUM_TAC(REWRITE_RULE[th1; th2]))) THEN
  MP_TAC(ISPECL [`complex_boundary (c:(real^N->bool)->bool) PCROSS
                  interval[vec 0:real^1,vec 1]`;
                 `f:real^(N,1)finite_sum->real^N`] MOI_FCL_PLH_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[COMPACT_PCROSS; COMPACT_INTERVAL];
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_TAC `f':real^N->real^(N,1)finite_sum`) THEN
  (* the bottom map g0 *)
  MP_TAC(ISPECL [`complex_boundary (c:(real^N->bool)->bool)`; `vec 0:real^1`]
    MOI_FCL_SLICE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `complex_boundary (c:(real^N->bool)->bool) PCROSS {vec 0:real^1} SUBSET
                complex_boundary (c:(real^N->bool)->bool) PCROSS interval[vec 0,vec 1]`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PCROSS_MONO THEN
    REWRITE_TAC[SUBSET_REFL; SING_SUBSET; ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (f:real^(N,1)finite_sum->real^N)
      (complex_boundary (c:(real^N->bool)->bool) PCROSS {vec 0}) =
    complex_boundary (c:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `boundary_complex c:(real^N->bool)->bool` MOI_FCL_UNIONS_DUAL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `complex_boundary (c:(real^N->bool)->bool) PCROSS {vec 0:real^1} =
      UNIONS {moi_fcl_src (boundary_complex c) ((s:real^N->bool),0) | s |
              s IN boundary_complex c /\ ~(s = {})}`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_fcl_src; FST; SND; MOI_FCL_IVAL_CASES] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        aconv (concl th) `UNIONS {moi_fcl_dual (boundary_complex c) s | s |
                            s IN boundary_complex c /\ ~(s = {})} =
                    complex_boundary (c:(real^N->bool)->bool)`)) THEN
      GEN_REWRITE_TAC I [EXTENSION] THEN
      REWRITE_TAC[FORALL_PASTECART; PASTECART_IN_PCROSS; IN_UNIONS; IN_ELIM_THM;
                  IN_SING] THEN
      MESON_TAC[PASTECART_IN_PCROSS; IN_SING];
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_UNIONS] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM(check (fun th ->
      aconv (concl th) `UNIONS {moi_fcl_dual (boundary_complex c) s | s |
                          s IN boundary_complex c /\ ~(s = {})} =
                  complex_boundary (c:(real^N->bool)->bool)`) th)]) THEN
    AP_TERM_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `Z:real^(N,1)finite_sum->bool` (CONJUNCTS_THEN2
        SUBST1_TAC (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `moi_fcl_src (boundary_complex c) ((s:real^N->bool),0)` THEN
      CONJ_TAC THENL [ALL_TAC; EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]]] THEN
    ASM_SIMP_TAC[moi_fcl_lab; IN_ELIM_THM; FST; SND; LE_0] THEN
    REWRITE_TAC[moi_fcl_tgt; moi_fcl_lv; FST; SND] THEN
    ASM_MESON_TAC[MOI_FCL_DUAL_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?g0'. pl_homeomorphism (complex_boundary (c:(real^N->bool)->bool),
                            complex_boundary c)
                           ((f:real^(N,1)finite_sum->real^N) o
                            (\y:real^N. pastecart y (vec 0:real^1)),g0')`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`complex_boundary (c:(real^N->bool)->bool)`;
                   `(f:real^(N,1)finite_sum->real^N) o
                    (\y:real^N. pastecart y (vec 0:real^1))`] MOI_FCL_PLH_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
        EXISTS_TAC `complex_boundary (c:(real^N->bool)->bool) PCROSS
                    interval[vec 0:real^1,vec 1]` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[o_THM] THEN REPEAT STRIP_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `pastecart (x:real^N) (vec 0:real^1)`)) (concl th))) THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (find_term ((=) `(f:real^(N,1)finite_sum->real^N) x`)) (concl th) &&
          is_forall (concl th))) THEN
        ASM_REWRITE_TAC[PASTECART_IN_PCROSS; ENDS_IN_UNIT_INTERVAL]];
      REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(f:real^(N,1)finite_sum->real^N) o
     (\z. pastecart ((g0':real^N->real^N) (fstcart z)) (sndcart z))`;
    `(\z. pastecart (((f:real^(N,1)finite_sum->real^N) o
                      (\y:real^N. pastecart y (vec 0:real^1))) (fstcart z)) (sndcart z)) o
     (f':real^N->real^(N,1)finite_sum)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `complex_boundary (c:(real^N->bool)->bool) PCROSS
                interval[vec 0:real^1,vec 1]` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FCL_PLH_PCROSS_ID THEN REWRITE_TAC[POLYTOPE_INTERVAL] THEN
      ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[ETA_AX];
      ASM_MESON_TAC[]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[o_THM; FSTCART_PASTECART; SNDCART_PASTECART] THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term ((=) `g0':real^N->real^N`)) (concl th))) THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism; o_THM] THEN
    ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* BOUNDARY_COLLAR (= MOI_FND_COLLAR, Moise 26.2): pass to a fine iterated   *)
(* barycentric subdivision so that the collar at level 1/2 of the weight     *)
(* lies within the distance of the boundary from the complement of the given *)
(* open set v; the boundary lies in the relative interior of the collar      *)
(* since the weight is 1 there.                                              *)
(* ========================================================================= *)

let MOI_FCL_ITER_CMWB = prove
 (`!(c:(real^N->bool)->bool) n.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> FINITE (ITER n barycentric_subdivision c) /\
         combinatorial_manifold_with_boundary 3 (ITER n barycentric_subdivision c) /\
         complex_boundary (ITER n barycentric_subdivision c) = complex_boundary c /\
         UNIONS (ITER n barycentric_subdivision c) = UNIONS c`,
  GEN_TAC THEN INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `d = ITER n barycentric_subdivision (c:(real^N->bool)->bool)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; MOI_BAR_UNIONS_SUBDIVISION] THEN
  MP_TAC(ISPEC `d:(real^N->bool)->bool` COMBINATORIAL_WB_BARYCENTRIC) THEN
  ASM_SIMP_TAC[]);;

(* Points of weight >= 1/2 lie in a simplex meeting the boundary. *)

let MOI_FCL_W_NEAR_B = prove
 (`!(c:(real^N->bool)->bool) h x.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c /\
     moi_frn_sig c (boundary_complex c) h /\
     x IN UNIONS c /\ &1 / &2 <= drop(h x)
     ==> ?m b. m IN c /\ x IN m /\ b IN m /\ b IN complex_boundary c`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FCL_UNIONS_DUAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N` o
    GEN_REWRITE_RULE I [EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `X:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^N) IN moi_fcl_dual c u` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->bool) IN boundary_complex c` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `boundary_complex c:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `u:real^N->bool`; `x:real^N`]
      MOI_FCL_SIG_ZERO_DUAL) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN moi_fcl_dual c u` THEN REWRITE_TAC[MOI_FCL_IN_DUAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?b:real^N. b IN u` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`UNIONS g:real^N->bool`; `b:real^N`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
    ASM SET_TAC[];
    ASM SET_TAC[];
    UNDISCH_TAC `(u:real^N->bool) IN boundary_complex c` THEN
    REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN ASM SET_TAC[]]);;

let BOUNDARY_COLLAR = prove
 (MOI_FND_COLLAR,
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `v:real^N->bool`] THEN
  STRIP_TAC THEN
  (* the boundary is at positive distance from the complement of v *)
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FCL_CB_POLY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
    ASM_REWRITE_TAC[MOI_BAR_SIMPLICIAL_COMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS c:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FCL_UNIONS_CLOSED_FINITE THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`complex_boundary c:real^N->bool`; `UNIONS c DIFF v:real^N->bool`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `open_in (subtopology euclidean (UNIONS c)) (v:real^N->bool)` THEN
      REWRITE_TAC[OPEN_IN_CLOSED_IN_EQ; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      STRIP_TAC THEN MATCH_MP_TAC CLOSED_IN_CLOSED_TRANS THEN
      EXISTS_TAC `UNIONS c:real^N->bool` THEN ASM_REWRITE_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  (* a fine subdivision *)
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real`]
    ITERATED_BARYCENTRIC_SUBDIVISION_FINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `n:num`] MOI_FCL_ITER_CMWB) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `d = ITER n barycentric_subdivision (c:(real^N->bool)->bool)` THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FCL_CMWB_SETUP) THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `boundary_complex d:(real^N->bool)->bool`]
    MOI_FRN_SIG_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `h:real^N->real^1`) THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `h:real^N->real^1`] MOI_FCL_COLLAR_RAW) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^(N,1)finite_sum->real^N`
    (X_CHOOSE_THEN `q:real^N->real^(N,1)finite_sum` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`{x:real^N | x IN UNIONS c /\ &1 / &2 <= drop(h x)}`;
                        `p:real^(N,1)finite_sum->real^N`;
                        `q:real^N->real^(N,1)finite_sum`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [(* the collar lies in v *)
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `h:real^N->real^1`; `x:real^N`]
      MOI_FCL_W_NEAR_B) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:real^N->bool` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `e <= dist(b:real^N,x)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
    REWRITE_TAC[REAL_NOT_LE; dist] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `diameter(m:real^N->bool)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN
      ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; SIMPLEX_IMP_COMPACT];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* the boundary lies in the relative interior of the collar *)
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `{x:real^N | x IN UNIONS c /\ h x IN {y:real^1 | y$1 > &1 / &2}}` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:real^N) IN UNIONS c /\ drop(h x) = &1` MP_TAC THENL
       [CONJ_TAC THENL
         [ASM_MESON_TAC[MOI_FMB_CB_SUBSET; SUBSET];
          MATCH_MP_TAC MOI_FRN_SIG_ONE THEN
          MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`;
                                `boundary_complex d:(real^N->bool)->bool`] THEN
          ASM_REWRITE_TAC[]];
        REWRITE_TAC[drop] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
      MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM; drop] THEN
        MESON_TAC[real_gt; REAL_LT_IMP_LE];
        MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
        REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
        ASM_MESON_TAC[moi_frn_sig]]]]);;

