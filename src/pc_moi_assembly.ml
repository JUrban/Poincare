(* ========================================================================= *)
(* pc_moi_assembly: the implications between the levels of the Moise chain,  *)
(* and sanity theorems for the PL notions.  MOI_MOISE_SMOOTHING_FROM_CHAIN   *)
(* derives the Moise interface from the leaves of the chain, which are its   *)
(* hypotheses.                                                               *)
(* ========================================================================= *)

needs "src/pc_moi_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* Level 1 gives the interface.                                              *)

let MOI_SMOOTHING_FROM_PL = prove
 (`!u:A->bool.
        MOISE_PL_ATLAS_STATEMENT u /\ PL_SMOOTHING_STATEMENT u
        ==> MOISE_SMOOTHING_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[MOISE_PL_ATLAS_STATEMENT; PL_SMOOTHING_STATEMENT;
              MOISE_SMOOTHING_STATEMENT] THEN
  MESON_TAC[]);;


(* Finite complexes are the finite locally finite ones.                      *)

let MOI_SIMPLICIAL_COMPLEX_LF = prove
 (`!c:(real^N->bool)->bool.
        simplicial_complex c <=> FINITE c /\ lf_simplicial_complex c`,
  GEN_TAC THEN REWRITE_TAC[simplicial_complex; lf_simplicial_complex] THEN
  EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN EXISTS_TAC `(:real^N)` THEN
  ASM_SIMP_TAC[OPEN_UNIV; IN_UNIV; FINITE_RESTRICT]);;

(* Transport of a smooth atlas along a homeomorphism.                        *)

let MOI_SMOOTH_ATLAS_IMAGE_IN = prove
 (`!(t:A->B) (s:B->A) (atlas:((A->bool)#(A->real^N))->bool) V psi.
        (V,psi) IN IMAGE (\c. IMAGE t (FST c),SND c o s) atlas <=>
        ?U phi. (U,phi) IN atlas /\ V = IMAGE t U /\ psi = phi o s`,
  REWRITE_TAC[IN_IMAGE; EXISTS_PAIR_THM; PAIR_EQ] THEN MESON_TAC[]);;

let MOI_SMOOTH_ATLAS_TRANSPORT = prove
 (`!(top:A topology) (top':B topology) (t:A->B)
    (atlas:((A->bool)#(A->real^N))->bool).
        homeomorphic_map (top,top') t /\ smooth_manifold_atlas top atlas
        ==> ?atlas':((B->bool)#(B->real^N))->bool.
                smooth_manifold_atlas top' atlas'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `s:B->A`) MP_TAC) THEN
  REWRITE_TAC[smooth_manifold_atlas] THEN STRIP_TAC THEN
  EXISTS_TAC
   `IMAGE (\c:(A->bool)#(A->real^N). IMAGE (t:A->B) (FST c),SND c o (s:B->A))
          atlas` THEN
  REWRITE_TAC[MOI_SMOOTH_ATLAS_IMAGE_IN] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  SUBGOAL_THEN `!U:A->bool. open_in top U ==> IMAGE (s:B->A) (IMAGE (t:A->B) U) = U`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`V:B->bool`; `psi:B->real^N`] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:A->bool` (X_CHOOSE_THEN `phi:A->real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC)))) THEN
    SUBGOAL_THEN
     `open_in top (U:A->bool) /\ open (IMAGE (phi:A->real^N) U) /\
      homeomorphic_map (subtopology top U,subtopology euclidean (IMAGE phi U))
                       phi`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE ((phi:A->real^N) o (s:B->A)) (IMAGE (t:A->B) U) =
                  IMAGE phi U` SUBST1_TAC THENL
     [ASM_SIMP_TAC[IMAGE_o]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:A->B`; `top:A topology`; `top':B topology`;
                     `U:A->bool`] HOMEOMORPHIC_MAP_OPENNESS) THEN
      ASM_SIMP_TAC[OPEN_IN_SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[HOMEOMORPHIC_MAPS_IMP_MAP];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology top (U:A->bool)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN CONJ_TAC THENL
     [ASM_MESON_TAC[HOMEOMORPHIC_MAPS_IMP_MAP; HOMEOMORPHIC_MAPS_SYM];
      ALL_TAC] THEN
    FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    SUBGOAL_THEN `IMAGE (t:A->B) U SUBSET topspace top'` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; IMAGE_SUBSET;
                    SUBSET_TRANS];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SET_RULE `!s t:B->bool. s SUBSET t ==> t INTER s = s`];
    X_GEN_TAC `y:B` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(s:B->A) y IN topspace top` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE; SUBSET; IN_IMAGE];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?(U:A->bool) (phi:A->real^N). (U,phi) IN atlas /\ (s:B->A) y IN U`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (t:A->B) U`; `(phi:A->real^N) o (s:B->A)`] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(s:B->A) y` THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`V1:B->bool`; `psi1:B->real^N`;
                         `V2:B->bool`; `psi2:B->real^N`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `U1:A->bool` (X_CHOOSE_THEN `phi1:A->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))
     (X_CHOOSE_THEN `U2:A->bool` (X_CHOOSE_THEN `phi2:A->real^N`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN SUBST1_TAC))))) THEN
    SUBGOAL_THEN
     `?g:real^N->real^N.
        smooth_map_on (IMAGE (phi1:A->real^N) (U1 INTER U2)) g /\
        !x. x IN U1 INTER U2 ==> g(phi1 x) = (phi2:A->real^N) x`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `g:real^N->real^N` THEN
    SUBGOAL_THEN `(U1:A->bool) SUBSET topspace top /\ U2 SUBSET topspace top`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE ((phi1:A->real^N) o (s:B->A))
            (IMAGE (t:A->B) U1 INTER IMAGE t U2) =
      IMAGE phi1 (U1 INTER U2)`
    SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[o_THM; IN_INTER; IN_IMAGE] THEN
    X_GEN_TAC `y:B` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `a:A`) (X_CHOOSE_TAC `b:A`)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTER] THEN
    ASM SET_TAC[]]);;

(* The smooth half from triangulations: a compact PL 3-manifold has a       *)
(* combinatorial triangulation, and combinatorial 3-manifolds are smoothable.*)

let MOI_PL_SMOOTHING_FROM_TRIANGULATION = prove
 (`!(u:A->bool) (v:N->bool).
        7 <= dimindex(:N) /\
        PL_TRIANGULATION_STATEMENT u v /\ COMBINATORIAL_SMOOTHING_STATEMENT v
        ==> PL_SMOOTHING_STATEMENT u`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[PL_TRIANGULATION_STATEMENT; COMBINATORIAL_SMOOTHING_STATEMENT;
              PL_SMOOTHING_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  MAP_EVERY X_GEN_TAC [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`top:A topology`;
                                `atlas:((A->bool)#(A->real^3))->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool`
   (X_CHOOSE_THEN `t:real^N->A` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:((real^N->bool)#(real^N->real^3))->bool`) THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS c:real^N->bool)`;
                 `top:A topology`; `t:real^N->A`;
                 `a:((real^N->bool)#(real^N->real^3))->bool`]
                MOI_SMOOTH_ATLAS_TRANSPORT) THEN
  ASM_REWRITE_TAC[]);;

(* The whole Moise interface from its three parts (instantiate N := 7).      *)

let MOI_MOISE_SMOOTHING_FROM_PARTS = prove
 (`!(u:A->bool) (v:N->bool).
        7 <= dimindex(:N) /\
        MOISE_PL_ATLAS_STATEMENT u /\ PL_TRIANGULATION_STATEMENT u v /\
        COMBINATORIAL_SMOOTHING_STATEMENT v
        ==> MOISE_SMOOTHING_STATEMENT u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SMOOTHING_FROM_PL THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_PL_SMOOTHING_FROM_TRIANGULATION THEN
  EXISTS_TAC `v:N->bool` THEN ASM_REWRITE_TAC[]);;

(* The triangulation theorem (simplicial form) from the atlas form.          *)

let MOI_MOISE_TRIANGULATION_FROM_PARTS = prove
 (`!(u:A->bool) (v:N->bool).
        MOISE_PL_ATLAS_STATEMENT u /\ PL_TRIANGULATION_STATEMENT u v
        ==> MOISE_TRIANGULATION_STATEMENT u v`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[MOISE_PL_ATLAS_STATEMENT; PL_TRIANGULATION_STATEMENT;
              MOISE_TRIANGULATION_STATEMENT] THEN
  MESON_TAC[]);;

(* The whole chain closes: the Moise interface follows from the two cores    *)
(* (MOISE_352_COMPLEX, COMBINATORIAL_SMOOTHING), the triangulation           *)
(* existence and the four glue implications, with N := 7.                    *)

let MOI_MOISE_SMOOTHING_FROM_CHAIN = prove
 (`!u:A->bool.
     (MOISE_APPROX_STATEMENT u ==> MOISE_PL_ATLAS_STATEMENT u) /\
     (MOISE_352_OPEN_STATEMENT u ==> MOISE_APPROX_STATEMENT u) /\
     (MOISE_352_COMPLEX_STATEMENT (:7) /\ PL_TRIANGULATION_LF_STATEMENT u (:7)
      ==> MOISE_352_OPEN_STATEMENT u) /\
     (PL_TRIANGULATION_LF_STATEMENT u (:7)
      ==> PL_TRIANGULATION_STATEMENT u (:7)) /\
     MOISE_352_COMPLEX_STATEMENT (:7) /\ PL_TRIANGULATION_LF_STATEMENT u (:7) /\
     COMBINATORIAL_SMOOTHING_STATEMENT (:7)
     ==> MOISE_SMOOTHING_STATEMENT u`,
  GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:A->bool`; `(:7)`] MOI_MOISE_SMOOTHING_FROM_PARTS) THEN
  REWRITE_TAC[DIMINDEX_CONV `dimindex(:7)`; LE_REFL] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Sanity theorems for the PL notions (non-vacuity).                         *)
(* ------------------------------------------------------------------------- *)

(* The identity is PL on every open set (one cube around each point).       *)

let MOI_PL_MAP_ON_ID_OPEN = prove
 (`!s:real^N->bool. open s ==> pl_map_on s (\x. x)`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[pl_map_on] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o
    GEN_REWRITE_RULE I [OPEN_CONTAINS_INTERVAL]) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`{interval[a:real^N,b]}`; `interval(a:real^N,b)`] THEN
  ASM_REWRITE_TAC[FINITE_SING; OPEN_INTERVAL; UNIONS_1; IN_SING] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`a:real^N`; `b:real^N`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
    SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_THEN SUBST1_TAC THEN
  ASM_REWRITE_TAC[POLYTOPE_INTERVAL] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^N. x`; `vec 0:real^N`] THEN
  REWRITE_TAC[LINEAR_ID; VECTOR_ADD_RID]);;

(* Euclidean 3-space with the identity chart is a PL 3-manifold.            *)

let MOI_PL_MANIFOLD_ATLAS_EUCLIDEAN = prove
 (`pl_manifold_atlas (euclidean:(real^3)topology) {((:real^3),(\x:real^3. x))}`,
  REWRITE_TAC[pl_manifold_atlas; IN_SING; PAIR_EQ] THEN REPEAT CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[IMAGE_ID; OPEN_IN_EUCLIDEAN; OPEN_UNIV; SUBTOPOLOGY_UNIV;
                    HOMEOMORPHIC_MAP_ID];
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; IN_UNIV] THEN GEN_TAC THEN
    MAP_EVERY EXISTS_TAC [`(:real^3)`; `\x:real^3. x`] THEN
    REWRITE_TAC[IN_UNIV];
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[IMAGE_ID; INTER_UNIV] THEN
    EXISTS_TAC `\x:real^3. x` THEN SIMP_TAC[MOI_PL_MAP_ON_ID_OPEN; OPEN_UNIV]]);;

(* The standard spherical shell, and a sphere separating its two ends.       *)

let MOI_SPHERICAL_SHELL_STANDARD = prove
 (`spherical_shell {y:real^3 | &1 <= norm y /\ norm y <= &2}
                   (sphere(vec 0,&1)) (sphere(vec 0,&2))`,
  REWRITE_TAC[spherical_shell] THEN
  MAP_EVERY EXISTS_TAC [`\y:real^3. y`; `\y:real^3. y`] THEN
  REWRITE_TAC[HOMEOMORPHISM_ID; IMAGE_ID]);;

let MOI_EUCLIDEAN_SEPARATES_SPHERES = prove
 (`euclidean_separates (sphere(vec 0:real^3,&3 / &2))
                       (sphere(vec 0,&1)) (sphere(vec 0,&2))`,
  REWRITE_TAC[euclidean_separates] THEN
  MAP_EVERY EXISTS_TAC
   [`ball(vec 0:real^3,&3 / &2)`; `(:real^3) DIFF cball(vec 0,&3 / &2)`] THEN
  SIMP_TAC[OPEN_BALL; OPEN_DIFF; OPEN_UNIV; CLOSED_CBALL] THEN
  REWRITE_TAC[EXTENSION; SUBSET; DISJOINT; IN_INTER; IN_UNION; IN_DIFF;
              IN_UNIV; IN_BALL_0; IN_CBALL_0; IN_SPHERE_0; NOT_IN_EMPTY] THEN
  REAL_ARITH_TAC);;

