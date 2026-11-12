(* ========================================================================= *)
(* pc_moi_smo_vertex (route M): vertex charts and the top glue of            *)
(* COMBINATORIAL_SMOOTHING_STATEMENT.  Main theorems:                        *)
(*   MOI_SMO_LINK_SMOOTH_FROM_PARTS  C6, C7, D6 ==> C8 (glue);               *)
(*   MOI_SMO_TOP_FROM_PARTS          C5, C8, C9 ==> the smooth core;         *)
(*   MOI_SMO_VERTEX_FROM_EDGE        C4 ==> C9 (cone charts at a vertex).    *)
(* The first part gives the two glue implications.  For the top glue the     *)
(* vertex charts are shrunk to Voronoi cells of the vertex set, so two       *)
(* distinct vertex charts never overlap; vertex charts meet the punctured    *)
(* atlas with smooth transitions by C9.                                      *)
(* ========================================================================= *)

needs "src/pc_moi_smo_link.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* MOI_SMO_LINK_SMOOTH_FROM_PARTS: the link smoothing theorem from its      *)
(* three parts (glue).                                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_SMO_LINK_SMOOTH_FROM_PARTS = prove
 (`!u:N->bool. MOI_SMO_LINK_ATLAS_STATEMENT u /\ MOI_SMO_LINK_PD_STATEMENT u /\
              MOI_SMO_PD2_STATEMENT u
              ==> MOI_SMO_LINK_SMOOTH_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[MOI_SMO_LINK_ATLAS_STATEMENT; MOI_SMO_LINK_PD_STATEMENT;
              MOI_SMO_PD2_STATEMENT; MOI_SMO_LINK_SMOOTH_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "atlas")
    (CONJUNCTS_THEN2 (LABEL_TAC "pd") (LABEL_TAC "pd2"))) THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN STRIP_TAC THEN
  REMOVE_THEN "pd" (MP_TAC o SPECL [`c:(real^N->bool)->bool`; `v:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^N->bool)->bool`
   (X_CHOOSE_THEN `h:real^N->real^3`
     (X_CHOOSE_THEN `h':real^3->real^N` STRIP_ASSUME_TAC))) THEN
  REMOVE_THEN "atlas" (MP_TAC o SPECL [`c:(real^N->bool)->bool`; `v:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "pd2" (MP_TAC o ISPECL
   [`L:(real^N->bool)->bool`; `moi_smo_link_atlas c (v:real^N)`;
    `h:real^N->real^3`; `h':real^3->real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_eq o concl)) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Voronoi cells of a finite set of points.                                  *)
(* ------------------------------------------------------------------------- *)

let moi_svx_cell = new_definition
 `moi_svx_cell (P:real^N->bool) (p:real^N) =
    {x | !q. q IN P /\ ~(q = p) ==> dist(x,p) < dist(x,q)}`;;

let MOI_SVX_DIST_LT_HALFSPACE = prove
 (`!x p q:real^N.
     dist(x,p) < dist(x,q) <=> (&2 % (q - p)) dot x < q dot q - p dot p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[dist; NORM_LT] THEN
  REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_LMUL] THEN
  REWRITE_TAC[DOT_SYM] THEN REAL_ARITH_TAC);;

let MOI_SVX_CELL_OPEN = prove
 (`!P (p:real^N). FINITE P ==> open (moi_svx_cell P p)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_svx_cell P (p:real^N) =
    INTERS (IMAGE (\q. {x:real^N | (&2 % (q - p)) dot x < q dot q - p dot p})
                  (P DELETE p))`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_svx_cell; EXTENSION; IN_INTERS; FORALL_IN_IMAGE;
                IN_ELIM_THM; IN_DELETE; MOI_SVX_DIST_LT_HALFSPACE] THEN
    MESON_TAC[];
    MATCH_MP_TAC OPEN_INTERS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FINITE_DELETE; FORALL_IN_IMAGE] THEN
    REWRITE_TAC[OPEN_HALFSPACE_LT]]);;

let MOI_SVX_CELL_SELF = prove
 (`!P (p:real^N). p IN moi_svx_cell P p`,
  REWRITE_TAC[moi_svx_cell; IN_ELIM_THM; DIST_REFL] THEN
  MESON_TAC[DIST_POS_LT]);;

let MOI_SVX_CELL_DISJOINT = prove
 (`!P (p:real^N) q. p IN P /\ q IN P /\ ~(p = q)
                    ==> moi_svx_cell P p INTER moi_svx_cell P q = {}`,
  REWRITE_TAC[moi_svx_cell; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
  MESON_TAC[REAL_LT_ANTISYM]);;

(* ------------------------------------------------------------------------- *)
(* Generic glue: a smooth atlas on X minus a finite set P, together with    *)
(* one chart around each point of P that is smoothly compatible (both ways) *)
(* with the atlas, gives a smooth atlas on X.                                *)
(* ------------------------------------------------------------------------- *)

let MOI_SVX_OPEN_IN_DIFF_FINITE = prove
 (`!X P:real^N->bool. FINITE P ==> open_in (subtopology euclidean X) (X DIFF P)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `X DIFF P:real^N->bool = X DIFF (X INTER P)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_DIFF THEN CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV];
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_SIMP_TAC[FINITE_IMP_CLOSED]]);;

let MOI_SVX_GLUE = prove
 (`!X P (A0:((real^N->bool)#(real^N->real^3))->bool)
    (U:real^N->real^N->bool) (phi:real^N->real^N->real^3).
     FINITE P /\
     smooth_manifold_atlas (subtopology euclidean (X DIFF P)) A0 /\
     (!p. p IN P
          ==> p IN U p /\ open_in (subtopology euclidean X) (U p) /\
              open (IMAGE (phi p) (U p)) /\
              homeomorphic_map (subtopology euclidean (U p),
                                subtopology euclidean (IMAGE (phi p) (U p)))
                               (phi p) /\
              !V psi. (V,psi) IN A0
                      ==> (?g. smooth_map_on (IMAGE (phi p) (U p INTER V)) g /\
                               !x. x IN U p INTER V ==> g(phi p x) = psi x) /\
                          (?g. smooth_map_on (IMAGE psi (U p INTER V)) g /\
                               !x. x IN U p INTER V ==> g(psi x) = phi p x))
     ==> ?atlas:((real^N->bool)#(real^N->real^3))->bool.
            smooth_manifold_atlas (subtopology euclidean X) atlas`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "pt"))) THEN
  REWRITE_TAC[smooth_manifold_atlas; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ch")
   (CONJUNCTS_THEN2 (LABEL_TAC "cov") (LABEL_TAC "tr"))) THEN
  EXISTS_TAC
   `A0 UNION {(U p INTER moi_svx_cell P p,(phi:real^N->real^N->real^3) p) |
              p | (p:real^N) IN P}` THEN
  SUBGOAL_THEN
   `!V (psi:real^N->real^3).
      (V,psi) IN {(U p INTER moi_svx_cell P p,(phi:real^N->real^N->real^3) p) |
                  p | (p:real^N) IN P} <=>
      ?p. p IN P /\ V = U p INTER moi_svx_cell P p /\ psi = phi p`
  (fun th -> REWRITE_TAC[IN_UNION; th]) THENL
   [REWRITE_TAC[IN_ELIM_THM; PAIR_EQ] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean X) (X DIFF P:real^N->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_SVX_OPEN_IN_DIFF_FINITE]; ALL_TAC] THEN
  (* the restricted vertex charts *)
  SUBGOAL_THEN
   `!p. p IN P
        ==> open_in (subtopology euclidean X) (U p INTER moi_svx_cell P p) /\
            U p INTER moi_svx_cell P p SUBSET X /\
            ?g. homeomorphism (U p INTER moi_svx_cell P p,
                               IMAGE ((phi:real^N->real^N->real^3) p)
                                     (U p INTER moi_svx_cell P p))
                              (phi p,g)`
  (LABEL_TAC "vc") THENL
   [X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
    USE_THEN "pt" (MP_TAC o SPEC `p:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `open_in (subtopology euclidean X)
                    ((U:real^N->real^N->bool) p INTER moi_svx_cell P p)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN ASM_SIMP_TAC[MOI_SVX_CELL_OPEN];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SLK_HMAP) THEN
    DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^N` o CONJUNCT1) THEN
    EXISTS_TAC `g:real^3->real^N` THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC
     [`(U:real^N->real^N->bool) p`;
      `IMAGE ((phi:real^N->real^N->real^3) p) (U p)`] THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* charts *)
    MAP_EVERY X_GEN_TAC [`V:real^N->bool`; `psi:real^N->real^3`] THEN
    STRIP_TAC THENL
     [USE_THEN "ch" (MP_TAC o SPECL [`V:real^N->bool`; `psi:real^N->real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
      SUBGOAL_THEN `V SUBSET X DIFF (P:real^N->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[OPEN_IN_TRANS];
        ASM_REWRITE_TAC[];
        UNDISCH_TAC
         `homeomorphic_map
            (subtopology (subtopology euclidean (X DIFF P)) V,
             subtopology euclidean (IMAGE (psi:real^N->real^3) V)) psi` THEN
        REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
        SUBGOAL_THEN `(X DIFF P) INTER V = V /\ X INTER V = V:real^N->bool`
        (fun th -> REWRITE_TAC[th]) THEN ASM SET_TAC[]];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "vc" (MP_TAC o SPEC `p:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `g:real^3->real^N`))) THEN
      USE_THEN "pt" (MP_TAC o SPEC `p:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN REPEAT CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_SLK_OPEN_IMAGE_SUB THEN
        MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `(U:real^N->real^N->bool) p`] THEN
        ASM_REWRITE_TAC[INTER_SUBSET];
        REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
        SUBGOAL_THEN `X INTER ((U:real^N->real^N->bool) p INTER moi_svx_cell P p) =
                      U p INTER moi_svx_cell P p` SUBST1_TAC THENL
         [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC MOI_SLK_HMAP_OF_HOMEO THEN
        EXISTS_TAC `g:real^3->real^N` THEN ASM_REWRITE_TAC[]]];
    (* covering *)
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(x:real^N) IN P` THENL
     [MAP_EVERY EXISTS_TAC
       [`(U:real^N->real^N->bool) x INTER moi_svx_cell P x`;
        `(phi:real^N->real^N->real^3) x`] THEN
      CONJ_TAC THENL [DISJ2_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INTER; MOI_SVX_CELL_SELF] THEN ASM_MESON_TAC[];
      USE_THEN "cov" (MP_TAC o SPEC `x:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DIFF]; MESON_TAC[]]];
    (* transitions *)
    MAP_EVERY X_GEN_TAC [`V1:real^N->bool`; `psi1:real^N->real^3`;
                         `V2:real^N->bool`; `psi2:real^N->real^3`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "pt" (MP_TAC o SPEC `p:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`V1:real^N->bool`; `psi1:real^N->real^3`] o
                 last o CONJUNCTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC o CONJUNCT2) THEN
      EXISTS_TAC `g:real^3->real^3` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `IMAGE (psi1:real^N->real^3) ((U:real^N->real^N->bool) p INTER V1)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[IN_INTER]];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "pt" (MP_TAC o SPEC `p:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o SPECL [`V2:real^N->bool`; `psi2:real^N->real^3`] o
                 last o CONJUNCTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC o CONJUNCT1) THEN
      EXISTS_TAC `g:real^3->real^3` THEN CONJ_TAC THENL
       [MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
        EXISTS_TAC `IMAGE ((phi:real^N->real^N->real^3) p) ((U:real^N->real^N->bool) p INTER V2)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
        REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[IN_INTER]];
      REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN
      ASM_CASES_TAC `p:real^N = p'` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN EXISTS_TAC `\y:real^3. y` THEN
        REWRITE_TAC[SMOOTH_MAP_ON_ID];
        EXISTS_TAC `\y:real^3. vec 0:real^3` THEN
        REWRITE_TAC[SMOOTH_MAP_ON_CONST] THEN
        MP_TAC(ISPECL [`P:real^N->bool`; `p:real^N`; `p':real^N`]
          MOI_SVX_CELL_DISJOINT) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* MOI_SMO_TOP_FROM_PARTS: the smooth core COMBINATORIAL_SMOOTHING_STATEMENT *)
(* from C5, C8, C9 (glue).                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_SVX_VERTEX_SET_FINITE = prove
 (`!c:(real^N->bool)->bool. FINITE c ==> FINITE {v:real^N | {v} IN c}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\v:real^N. {v}`; `c:(real^N->bool)->bool`] FINITE_IMAGE_INJ) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[]);;

let MOI_SMO_TOP_FROM_PARTS = prove
 (`!u:N->bool. MOI_SMO_PUNCTURED_STATEMENT u /\ MOI_SMO_LINK_SMOOTH_STATEMENT u /\
              MOI_SMO_VERTEX_STATEMENT u
              ==> COMBINATORIAL_SMOOTHING_STATEMENT u`,
  GEN_TAC THEN
  REWRITE_TAC[MOI_SMO_PUNCTURED_STATEMENT; MOI_SMO_LINK_SMOOTH_STATEMENT;
              MOI_SMO_VERTEX_STATEMENT; COMBINATORIAL_SMOOTHING_STATEMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "punc")
    (CONJUNCTS_THEN2 (LABEL_TAC "link") (LABEL_TAC "vert"))) THEN
  X_GEN_TAC `c:(real^N->bool)->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?D:real^N->real^N->real^3.
      !v. {v} IN c
          ==> ?d'. homeomorphism (UNIONS(simplicial_link c v),
                                  sphere(vec 0:real^3,&1)) (D v,d') /\
                   smooth_immersion_into (moi_smo_link_atlas c v) (D v)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `v:real^N` THEN
    ASM_CASES_TAC `{v:real^N} IN c` THEN ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "link" (MP_TAC o SPECL [`c:(real^N->bool)->bool`; `v:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SVX_GLUE THEN
  MAP_EVERY EXISTS_TAC
   [`{v:real^N | {v} IN c}`;
    `moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
     moi_smo_edge_atlas (c:(real^N->bool)->bool)`;
    `moi_smo_vertex_dom (c:(real^N->bool)->bool)`;
    `\v:real^N. moi_smo_vertex_chart c v ((D:real^N->real^N->real^3) v)`] THEN
  ASM_SIMP_TAC[MOI_SVX_VERTEX_SET_FINITE] THEN
  X_GEN_TAC `p:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `p:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d':real^3->real^N` STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "vert" (MP_TAC o SPECL
   [`c:(real^N->bool)->bool`; `p:real^N`;
    `(D:real^N->real^N->real^3) p`; `d':real^3->real^N`]) THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The regular distance to a vertex.  Distances in regular charts depend    *)
(* only on the points (two affine maps that agree on the pairwise distances *)
(* of finitely many points agree on all distances in their convex hull), so *)
(* moi_smo_rho c v x is the regular distance from v in any tetrahedron      *)
(* containing x and v; it is continuous on the open star of v, which makes  *)
(* the vertex domain open in the polyhedron.                                *)
(* ========================================================================= *)

let MOI_SVX_AFFINE_VSUM = prove
 (`!(A:real^N->real^M) (W:real^N->bool) u.
     (?l y. linear l /\ !x. A x = l x + y) /\ FINITE W /\ sum W u = &1
     ==> A(vsum W (\p. u p % p)) = vsum W (\p. u p % A p)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `l:real^N->real^M` (X_CHOOSE_THEN `y:real^M` STRIP_ASSUME_TAC))
   STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LINEAR_VSUM; o_DEF; LINEAR_CMUL; VECTOR_ADD_LDISTRIB; VSUM_ADD;
               VSUM_RMUL; VECTOR_MUL_LID]);;

let MOI_SVX_VSUM_DOT_SELF = prove
 (`!(W:real^N->bool) (c:real^N->real) (a:real^N->real^M).
     FINITE W /\ sum W c = &0
     ==> vsum W (\p. c p % a p) dot vsum W (\p. c p % a p) =
         --(&1 / &2) *
         sum W (\p. sum W (\q. c p * c q * ((a p - a q) dot (a p - a q))))`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `S2 = sum W (\q:real^N. c q * ((a:real^N->real^M) q dot a q))` THEN
  SUBGOAL_THEN
   `!p:real^N. sum W (\q. c p * c q * ((a p - a q) dot (a p - a q))) =
               --(&2) * (c p * sum W (\q. c q * ((a:real^N->real^M) p dot a q))) +
               c p * S2`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN
     `!q:real^N. c p * c q * (((a:real^N->real^M) p - a q) dot (a p - a q)) =
                 (c p * (a p dot a p)) * c q +
                 (--(&2) * c p) * (c q * (a p dot a q)) +
                 c p * (c q * (a q dot a q))`
     (fun th -> REWRITE_TAC[th]) THENL
     [GEN_TAC THEN REWRITE_TAC[DOT_LSUB; DOT_RSUB; DOT_SYM] THEN CONV_TAC REAL_RING;
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; REAL_MUL_RZERO; REAL_ADD_LID] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[SUM_ADD; SUM_LMUL; SUM_RMUL; REAL_MUL_LZERO; REAL_ADD_RID] THEN
  ASM_SIMP_TAC[DOT_LSUM; DOT_RSUM; DOT_LMUL; DOT_RMUL; SUM_LMUL] THEN
  MATCH_MP_TAC(REAL_ARITH `!x y:real. x = y ==> x = --(&1 / &2) * --(&2) * y`) THEN
  REWRITE_TAC[]);;

let MOI_SVX_AFFINE_DIST_HULL = prove
 (`!(A1:real^N->real^M) (A2:real^N->real^M) W x y.
     (?l y. linear l /\ !x. A1 x = l x + y) /\
     (?l y. linear l /\ !x. A2 x = l x + y) /\
     FINITE W /\
     (!p q. p IN W /\ q IN W ==> dist(A1 p,A1 q) = dist(A2 p,A2 q)) /\
     x IN convex hull W /\ y IN convex hull W
     ==> dist(A1 x,A1 y) = dist(A2 x,A2 y)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "a1")
    (CONJUNCTS_THEN2 (LABEL_TAC "a2") STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(x:real^N) IN convex hull W` THEN
  UNDISCH_TAC `(y:real^N) IN convex hull W` THEN
  ASM_SIMP_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!A:real^N->real^M. (?l y. linear l /\ !x. A x = l x + y)
        ==> A x - A y = vsum W (\p. (u p - w p) % A p)`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MAP_EVERY EXPAND_TAC ["x"; "y"] THEN
    ASM_SIMP_TAC[MOI_SVX_AFFINE_VSUM; VECTOR_SUB_RDISTRIB; VSUM_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. p IN W /\ q IN W
          ==> ((A1:real^N->real^M) p - A1 q) dot (A1 p - A1 q) =
              ((A2:real^N->real^M) p - A2 q) dot (A2 p - A2 q)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM NORM_EQ; GSYM dist] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sum W (\p:real^N. u p - w p) = &0` ASSUME_TAC THENL
   [ASM_SIMP_TAC[SUM_SUB; REAL_SUB_REFL]; ALL_TAC] THEN
  REWRITE_TAC[dist; NORM_EQ] THEN ASM_SIMP_TAC[] THEN
  ASM_SIMP_TAC[MOI_SVX_VSUM_DOT_SELF] THEN
  AP_TERM_TAC THEN MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `p:real^N` THEN
  DISCH_TAC THEN BETA_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `q:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
  ASM_SIMP_TAC[]);;

let MOI_SVX_REGMAP_DIST = prove
 (`!c tet1 tet2 (A1:real^N->real^3) A2 x y.
     lf_simplicial_complex c /\ tet1 IN c /\ tet2 IN c /\
     moi_smo_regmap tet1 A1 /\ moi_smo_regmap tet2 A2 /\
     x IN tet1 INTER tet2 /\ y IN tet1 INTER tet2
     ==> dist(A1 x,A1 y) = dist(A2 x,A2 y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(tet1 INTER tet2:real^N->bool) face_of tet1 /\
                (tet1 INTER tet2) face_of tet2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `?V1:real^N->bool. ~affine_dependent V1 /\ tet1 = convex hull V1`
  (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
   [ASM_MESON_TAC[lf_simplicial_complex; simplex]; ALL_TAC] THEN
  SUBGOAL_THEN `?V2:real^N->bool. ~affine_dependent V2 /\ tet2 = convex hull V2`
  (CHOOSE_THEN (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THENL
   [ASM_MESON_TAC[lf_simplicial_complex; simplex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`V1:real^N->bool`;
                 `convex hull V1 INTER convex hull V2:real^N->bool`]
    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V2:real^N->bool`;
                 `convex hull V1 INTER convex hull V2:real^N->bool`]
    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~affine_dependent(C1:real^N->bool) /\ ~affine_dependent(C2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `C1:real^N->bool = C2` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `p:real^N` THEN
    MP_TAC(ISPECL [`C1:real^N->bool`; `p:real^N`]
      EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    MP_TAC(ISPECL [`C2:real^N->bool`; `p:real^N`]
      EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `convex hull C1:real^N->bool = convex hull C2`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SVX_AFFINE_DIST_HULL THEN
  EXISTS_TAC `C1:real^N->bool` THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[moi_smo_regmap];
    ASM_MESON_TAC[moi_smo_regmap];
    ASM_MESON_TAC[FINITE_SUBSET; AFFINE_INDEPENDENT_IMP_FINITE];
    MAP_EVERY X_GEN_TAC [`p:real^N`; `q:real^N`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `p:real^N = q` THEN ASM_REWRITE_TAC[DIST_REFL] THEN
    SUBGOAL_THEN
     `p extreme_point_of convex hull V1 /\ q extreme_point_of convex hull V1 /\
      p extreme_point_of convex hull V2 /\
      (q:real^N) extreme_point_of convex hull V2`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[moi_smo_regmap];
    ASM_MESON_TAC[IN_INTER];
    ASM_MESON_TAC[IN_INTER]]);;

(* ------------------------------------------------------------------------- *)
(* The regular distance in a tetrahedron, regular charts sending v to 0.     *)
(* ------------------------------------------------------------------------- *)

let MOI_SVX_RHO_EQ = prove
 (`!c (v:real^N) x tet (A:real^N->real^3).
     lf_simplicial_complex c /\ tet IN c /\ aff_dim tet = &3 /\ v IN tet /\
     x IN tet /\ moi_smo_regmap tet A
     ==> moi_smo_rho c v x = dist(A x,A v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_smo_rho] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `r:real` THEN BETA_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `tet':real^N->bool`
      (X_CHOOSE_THEN `A':real^N->real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SVX_REGMAP_DIST THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tet':real^N->bool`;
                          `tet:real^N->bool`] THEN
    ASM_REWRITE_TAC[IN_INTER];
    DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC [`tet:real^N->bool`; `A:real^N->real^3`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SVX_TET_REGMAP0 = prove
 (`!c tet (v:real^N).
     lf_simplicial_complex c /\ tet IN c /\ aff_dim tet = &3 /\
     v extreme_point_of tet
     ==> ?A:real^N->real^3. moi_smo_regmap tet A /\ A v = vec 0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`]
    MOI_SBA_LF_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tet:real^N->bool`; `v:real^N`] MOI_SBA_TET_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
    (X_CHOOSE_THEN `q4:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC MOI_SBA_REGMAP_EXISTS THEN ASM_REWRITE_TAC[]);;

let MOI_SVX_REGMAP_INJ_TET = prove
 (`!c tet (A:real^N->real^3) x y.
     lf_simplicial_complex c /\ tet IN c /\ aff_dim tet = &3 /\
     moi_smo_regmap tet A /\ x IN tet /\ y IN tet /\ A x = A y
     ==> x = y`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(tet:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`]
    MOI_SBA_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`]
    MOI_SBA_LF_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tet:real^N->bool`; `w:real^N`] MOI_SBA_TET_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q2:real^N` (X_CHOOSE_THEN `q3:real^N`
    (X_CHOOSE_THEN `q4:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MATCH_MP_TAC MOI_SBA_REGMAP_INJ THEN
  MAP_EVERY EXISTS_TAC [`w:real^N`; `q2:real^N`; `q3:real^N`; `q4:real^N`;
                        `A:real^N->real^3`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_SVX_OPEN_STAR_CARRIER = prove
 (`!c s (x:real^N).
     x IN moi_smo_open_star c s
     ==> ?t. t IN c /\ s face_of t /\ x IN relative_interior t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_smo_open_star; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let MOI_SVX_STAR_CARRIER = prove
 (`!c (v:real^N) x.
     x IN moi_smo_open_star c {v}
     ==> ?s0. s0 IN c /\ v IN s0 /\ x IN relative_interior s0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_SVX_OPEN_STAR_CARRIER) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s0:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN SET_TAC[]);;

let MOI_SVX_STAR_TET = prove
 (`!c (v:real^N) s0.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\ s0 IN c /\ v IN s0
     ==> ?tet A:real^N->real^3.
            tet IN c /\ aff_dim tet = &3 /\ s0 SUBSET tet /\
            moi_smo_regmap tet A /\ A v = vec 0 /\
            !y. y IN tet ==> moi_smo_rho c v y = norm(A y)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool) /\
                simplicial_complex c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_SCF_LF_SC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s0:real^N->bool`] MOI_SCF_CF_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tet:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N) extreme_point_of tet` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_VERTEX_EXTREME THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `tet:real^N->bool`; `v:real^N`]
    MOI_SVX_TET_REGMAP0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`tet:real^N->bool`; `A:real^N->real^3`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`;
                 `tet:real^N->bool`; `A:real^N->real^3`] MOI_SVX_RHO_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[DIST_0]);;

let MOI_SVX_RHO_STAR = prove
 (`!c (v:real^N) x.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     x IN moi_smo_open_star c {v}
     ==> ?tet A:real^N->real^3.
            tet IN c /\ aff_dim tet = &3 /\ v IN tet /\ x IN tet /\
            moi_smo_regmap tet A /\ A v = vec 0 /\
            !y. y IN tet ==> moi_smo_rho c v y = norm(A y)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_SVX_STAR_CARRIER) THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s0:real^N->bool`]
    MOI_SVX_STAR_TET) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `tet:real^N->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `A:real^N->real^3` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `s0:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[]);;

let MOI_SVX_V_IN_STAR = prove
 (`!c (v:real^N). {v} IN c ==> v IN moi_smo_open_star c {v}`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[moi_smo_open_star; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `relative_interior {v:real^N}` THEN CONJ_TAC THENL
   [EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FACE_OF_REFL THEN REWRITE_TAC[CONVEX_SING];
    REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING]]);;

let MOI_SVX_RHO_V = prove
 (`!c (v:real^N).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c
     ==> moi_smo_rho c v v = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `v:real^N`]
    MOI_SVX_RHO_STAR) THEN
  ASM_SIMP_TAC[MOI_SVX_V_IN_STAR] THEN
  STRIP_TAC THEN ASM_SIMP_TAC[NORM_0]);;

let MOI_SVX_RHO_POS = prove
 (`!c (v:real^N) x.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     x IN moi_smo_open_star c {v}
     ==> &0 <= moi_smo_rho c v x /\
         (~(x = v) ==> &0 < moi_smo_rho c v x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SVX_RHO_STAR) THEN
  DISCH_THEN(X_CHOOSE_THEN `tet:real^N->bool`
    (X_CHOOSE_THEN `A:real^N->real^3` STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[NORM_POS_LE; NORM_POS_LT] THEN DISCH_TAC THEN
  DISCH_TAC THEN UNDISCH_TAC `~(x:real^N = v)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_SVX_REGMAP_INJ_TET THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tet:real^N->bool`;
                        `A:real^N->real^3`] THEN
  ASM_MESON_TAC[combinatorial_manifold]);;

(* ------------------------------------------------------------------------- *)
(* Continuity of the regular distance on the open star; openness of the     *)
(* vertex domain.                                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_SVX_RHO_CONT = prove
 (`!c (v:real^N).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c
     ==> (\x. lift(moi_smo_rho c v x)) continuous_on moi_smo_open_star c {v}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
  EXISTS_TAC `UNIONS {tet | tet IN c /\ aff_dim tet = &3 /\ (v:real^N) IN tet}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PLM_CONTINUOUS_ON_UNIONS_CLOSED THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `tet:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SBA_LF_CONVEX; combinatorial_manifold]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `tet:real^N->bool`]
      MOI_SVX_STAR_TET) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `tet':real^N->bool`
      (X_CHOOSE_THEN `A:real^N->real^3` STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `\y:real^N. lift(norm((A:real^N->real^3) y))` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
      AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM SET_TAC[];
      MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      MATCH_MP_TAC MOI_SBA_AFFINE_CONTINUOUS_ON THEN
      ASM_MESON_TAC[moi_smo_regmap]];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `x:real^N`]
      MOI_SVX_RHO_STAR) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let MOI_SVX_DOM_OPEN = prove
 (`!c (v:real^N).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c
     ==> open_in (subtopology euclidean (UNIONS c)) (moi_smo_vertex_dom c v)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS THEN
  EXISTS_TAC `moi_smo_open_star c {v:real^N}` THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `moi_smo_vertex_dom c (v:real^N) =
      {x | x IN moi_smo_open_star c {v} /\
           (\x. lift(moi_smo_rho c v x)) x IN {y:real^1 | y$1 < inv(&2)}}`
    SUBST1_TAC THENL
     [REWRITE_TAC[moi_smo_vertex_dom; EXTENSION; IN_ELIM_THM; LIFT_COMPONENT];
      MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
      ASM_SIMP_TAC[MOI_SVX_RHO_CONT; OPEN_HALFSPACE_COMPONENT_LT]];
    MATCH_MP_TAC MOI_SBA_OPEN_STAR_OPEN THEN
    ASM_MESON_TAC[combinatorial_manifold]]);;

let MOI_SVX_V_IN_DOM = prove
 (`!c (v:real^N).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c
     ==> v IN moi_smo_vertex_dom c v`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[moi_smo_vertex_dom; IN_ELIM_THM; MOI_SVX_V_IN_STAR; MOI_SVX_RHO_V] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV);;

(* ========================================================================= *)
(* The ray from v.  For x in the relative interior of a simplex s0 at v,    *)
(* the ray from v through x meets the link in moi_smo_ray c v x, x lies     *)
(* strictly between v and that point, and the open segment from v to it     *)
(* stays in the relative interior of s0.  The regular distance is           *)
(* homogeneous along rays.                                                  *)
(* ========================================================================= *)

let MOI_SVX_RAY_UNIQUE = prove
 (`!c (v:real^N) l s.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     l IN UNIONS(simplicial_link c v) /\ &0 < s /\ s <= &1
     ==> moi_smo_ray c v (v + s % (l - v)) = l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SLK_LINK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_smo_ray] THEN MATCH_MP_TAC SELECT_UNIQUE THEN
  X_GEN_TAC `l':real^N` THEN BETA_TAC THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `s':real` STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`s':real`; `s:real`] THEN ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[]]);;

let MOI_SVX_RAY_PROPS = prove
 (`!c (v:real^N) s0 x.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\ s0 IN c /\
     v IN s0 /\ x IN relative_interior s0 /\ ~(x = v)
     ==> moi_smo_ray c v x IN UNIONS(simplicial_link c v) /\
         moi_smo_ray c v x IN s0 /\
         (?s. &0 < s /\ s < &1 /\ x = v + s % (moi_smo_ray c v x - v)) /\
         (!r. &0 < r /\ r < &1
              ==> v + r % (moi_smo_ray c v x - v) IN relative_interior s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_SCF_LF_SC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s0:real^N->bool`]
    MOI_SCF_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `sg:real^N->bool`]
    MOI_SCF_LINK_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
     is_var(lhs(concl th)) && fst(dest_var(lhs(concl th))) = "sg")) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOI_SCF_HULL_INSERT_HULL]) THEN
  REWRITE_TAC[MOI_SCF_HULL_INSERT_HULL] THEN
  SUBGOAL_THEN `FINITE (C:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE; FINITE_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?u. &0 < u v /\ (!p:real^N. p IN C ==> &0 < u p) /\
        u v + sum C u = &1 /\ u v % v + vsum C (\p. u p % p) = x`
  (X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THENL
   [UNDISCH_TAC `(x:real^N) IN relative_interior(convex hull (v INSERT C))` THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FORALL_IN_INSERT] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(C:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[SUM_CLAUSES; VSUM_CLAUSES; REAL_ADD_RID;
                                VECTOR_ADD_RID]) THEN
    UNDISCH_TAC `~(x:real^N = v)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < sum C (u:real^N->real) /\ sum C u < &1` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    MATCH_MP_TAC SUM_POS_LT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t = sum C (u:real^N->real)` THEN
  ABBREV_TAC `l = inv t % vsum C (\p:real^N. u p % p)` THEN
  SUBGOAL_THEN `t % (l:real^N) = vsum C (\p. u p % p)` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^N) IN convex hull C` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
    EXISTS_TAC `\p:real^N. inv t * u p` THEN BETA_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[REAL_LE_MUL; REAL_LE_INV_EQ; REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[SUM_LMUL] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
      EXPAND_TAC "l" THEN REWRITE_TAC[GSYM VECTOR_MUL_ASSOC; VSUM_LMUL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `x:real^N = v + t % (l - v)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(u:real^N->real) v = &1 - t` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `(u:real^N->real) v % v + vsum C (\p. u p % p) = x` THEN
    REWRITE_TAC[ASSUME `(u:real^N->real) v = &1 - t`;
                GSYM(ASSUME `t % (l:real^N) = vsum C (\p. u p % p)`)] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_smo_ray c v (x:real^N) = l` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SVX_RAY_UNIQUE THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `convex hull C:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `convex hull C:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(l:real^N) IN convex hull C` THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^N). s SUBSET t ==> x IN s ==> x IN t`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
    EXISTS_TAC `\p:real^N. if p = v then &1 - r else r * inv t * u p` THEN
    ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FORALL_IN_INSERT] THEN
    SUBGOAL_THEN `!p:real^N. p IN C ==> ~(p = v)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_INV];
      SUBGOAL_THEN
       `sum C (\p:real^N. if p = v then &1 - r else r * inv t * u p) =
        sum C (\p. (r * inv t) * u p)`
      SUBST1_TAC THENL
       [MATCH_MP_TAC SUM_EQ THEN ASM_SIMP_TAC[REAL_MUL_ASSOC]; ALL_TAC] THEN
      ASM_REWRITE_TAC[SUM_LMUL] THEN
      ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN
       `vsum C (\p:real^N. (if p = v then &1 - r else r * inv t * u p) % p) =
        vsum C (\p. (r * inv t) % (u p % p))`
      SUBST1_TAC THENL
       [MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_ASSOC];
        ALL_TAC] THEN
      REWRITE_TAC[VSUM_LMUL;
                  GSYM(ASSUME `t % (l:real^N) = vsum C (\p. u p % p)`);
                  VECTOR_MUL_ASSOC] THEN
      SUBGOAL_THEN `(r * inv t) * t = r` SUBST1_TAC THENL
       [ASM_SIMP_TAC[GSYM REAL_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                     REAL_MUL_RID];
        VECTOR_ARITH_TAC]]]);;

let MOI_SVX_RHO_RAY = prove
 (`!c (v:real^N) s0 x.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\ s0 IN c /\
     v IN s0 /\ x IN relative_interior s0 /\ ~(x = v)
     ==> ?s. &0 < s /\ s < &1 /\ x = v + s % (moi_smo_ray c v x - v) /\
             moi_smo_rho c v x = s * moi_smo_rho c v (moi_smo_ray c v x) /\
             &0 < moi_smo_rho c v (moi_smo_ray c v x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s0:real^N->bool`;
                 `x:real^N`] MOI_SVX_RAY_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `l = moi_smo_ray c v (x:real^N)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real`
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
         (ASSUME_TAC o SYM)))) ASSUME_TAC))) THEN
  EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s0:real^N->bool`]
    MOI_SVX_STAR_TET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tet:real^N->bool`
    (X_CHOOSE_THEN `A:real^N->real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^N) IN tet /\ (l:real^N) IN tet /\ (v:real^N) IN tet`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `s0:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^N->real^3) x = s % A l` ASSUME_TAC THENL
   [UNDISCH_TAC `v + s % (l - v):real^N = x` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_SBA_AFFINE_HOMOG THEN ASM_MESON_TAC[moi_smo_regmap];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_smo_rho c v (x:real^N) = norm((A:real^N->real^3) x) /\
                moi_smo_rho c v (l:real^N) = norm(A l)`
  (CONJUNCTS_THEN SUBST1_TAC) THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < s ==> abs s = s`] THEN
  REWRITE_TAC[NORM_POS_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SLK_LINK_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `l:real^N = v` (fun th -> ASM_MESON_TAC[th]) THEN
  MATCH_MP_TAC MOI_SVX_REGMAP_INJ_TET THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `tet:real^N->bool`;
                        `A:real^N->real^3`] THEN
  ASM_MESON_TAC[combinatorial_manifold]);;

(* ========================================================================= *)
(* Edge charts at v.  Every point of the punctured open star of v lies in   *)
(* the open star of an edge at v; there C4 gives an edge chart that is a    *)
(* star chart at v, its norm is the regular distance to v (the labelling    *)
(* with v sent to the third basis vector is not homogeneous), and the       *)
(* midpoint of the ray segment stays in its domain.                         *)
(* ========================================================================= *)

let MOI_SVX_EDGE_AT = prove
 (`!c (v:real^N) x.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     x IN moi_smo_open_star c {v} /\ ~(x = v)
     ==> ?e. e IN c /\ aff_dim e = &1 /\ v extreme_point_of e /\
             x IN moi_smo_open_star c e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool) /\
                simplicial_complex c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_SCF_LF_SC]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SVX_STAR_CARRIER) THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s0:real^N->bool`]
    MOI_SCF_SC_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N) IN V` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> REWRITE_TAC[GSYM th]) THEN
    MATCH_MP_TAC MOI_SCF_VERTEX_EXTREME THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?w:real^N. w IN V /\ ~(w = v)` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC);
    SUBGOAL_THEN `V = {v:real^N}` SUBST_ALL_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior s0` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_SING; RELATIVE_INTERIOR_SING; IN_SING]] THEN
  SUBGOAL_THEN `segment[v:real^N,w] face_of s0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{v:real^N,w}` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `segment[v:real^N,w]` THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex];
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
    REWRITE_TAC[EXTREME_POINT_OF_SEGMENT];
    REWRITE_TAC[moi_smo_open_star; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `relative_interior s0:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_SVX_OPEN_STAR_SUB = prove
 (`!c e1 e2:real^N->bool.
     lf_simplicial_complex c /\ e1 IN c /\ ~(e1 = {}) /\
     moi_smo_open_star c e1 SUBSET moi_smo_open_star c e2
     ==> e2 SUBSET e1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(relative_interior e1:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MOI_SBA_LF_CONVEX]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  SUBGOAL_THEN `(x:real^N) IN moi_smo_open_star c e2` MP_TAC THENL
   [ASM_MESON_TAC[MOI_SBA_RELINT_IN_STAR; SUBSET]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_SVX_OPEN_STAR_CARRIER) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `e1:real^N->bool = t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOI_SBA_RELINT_EQ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM SET_TAC[];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]);;

let MOI_SVX_OPEN_STAR_EQ = prove
 (`!c e1 e2:real^N->bool.
     lf_simplicial_complex c /\ e1 IN c /\ e2 IN c /\ ~(e1 = {}) /\
     ~(e2 = {}) /\ moi_smo_open_star c e1 = moi_smo_open_star c e2
     ==> e1 = e2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_SVX_OPEN_STAR_SUB THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL]);;

let MOI_SVX_V_NOT_IN_STAR = prove
 (`!c (v:real^N) s.
     lf_simplicial_complex c /\ {v} IN c /\ v IN moi_smo_open_star c s
     ==> s SUBSET {v}`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_SVX_OPEN_STAR_CARRIER) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{v:real^N} = t` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOI_SBA_RELINT_EQ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SING] THEN ASM SET_TAC[];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]);;

let MOI_SVX_TWO_SCALES = prove
 (`!z:real^3. norm(basis 3 + inv(&2) % (z - basis 3)) = inv(&2) * norm z /\
              norm(basis 3 + inv(&4) % (z - basis 3)) = inv(&4) * norm z
              ==> F`,
  GEN_TAC THEN
  SUBGOAL_THEN
   `!t. &0 <= t
        ==> (norm(basis 3 + t % (z - basis 3)) = t * norm(z:real^3) <=>
             (&1 - t) pow 2 + &2 * t * (&1 - t) * z$3 = &0)`
  (fun th -> SIMP_TAC[th; REAL_LE_INV_EQ; REAL_POS]) THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `t * norm(z:real^3) = norm(t % z)` SUBST1_TAC THENL
     [ASM_SIMP_TAC[NORM_MUL; REAL_ARITH `&0 <= t ==> abs t = t`]; ALL_TAC] THEN
    REWRITE_TAC[NORM_EQ] THEN
    REWRITE_TAC[DOT_LADD; DOT_RADD; DOT_LMUL; DOT_RMUL; DOT_LSUB; DOT_RSUB] THEN
    SIMP_TAC[DOT_BASIS; DOT_BASIS_BASIS; DIMINDEX_3; ARITH] THEN
    MATCH_MP_TAC(REAL_ARITH `!a b c:real. a - b = c ==> (a = b <=> c = &0)`) THEN
    CONV_TAC REAL_RING;
    CONV_TAC REAL_RAT_REDUCE_CONV THEN REAL_ARITH_TAC]);;

let MOI_SVX_AFFINE_SEG = prove
 (`!(A:real^N->real^M) b x t.
     (?l y. linear l /\ !x. A x = l x + y)
     ==> A(b + t % (x - b)) = A b + t % (A x - A b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; LINEAR_SUB] THEN VECTOR_ARITH_TAC);;

let MOI_SVX_EDGE_NORM = prove
 (`!c (v:real^N) e (kappa:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     e IN c /\ aff_dim e = &1 /\ v extreme_point_of e /\
     (moi_smo_open_star c e,kappa) IN moi_smo_edge_atlas c /\
     (moi_smo_open_star c e,kappa) IN moi_smo_star_atlas c v
     ==> !x. x IN moi_smo_open_star c e ==> norm(kappa x) = moi_smo_rho c v x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x t. x IN moi_smo_open_star c e /\ &0 < t /\ t <= &1
          ==> v + t % (x - v) IN moi_smo_open_star c e /\
              (kappa:real^N->real^3)(v + t % (x - v)) = t % kappa x`
  (LABEL_TAC "hom") THENL
   [UNDISCH_TAC `(moi_smo_open_star c e,kappa) IN
                 moi_smo_star_atlas c (v:real^N)` THEN
    REWRITE_TAC[MOI_SBA_STAR_ATLAS_IN] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(moi_smo_open_star c e,kappa) IN
               moi_smo_edge_atlas (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_smo_edge_atlas; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` (X_CHOOSE_THEN `kappa':real^N->real^3`
    (CONJUNCTS_THEN2 MP_TAC MP_TAC))) THEN
  REWRITE_TAC[PAIR_EQ] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (SUBST_ALL_TAC o SYM)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (X_CHOOSE_THEN `a:real^N`
      (X_CHOOSE_THEN `b:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 (LABEL_TAC "eqe") ASSUME_TAC))))))) THEN
  REMOVE_THEN "eqe" SUBST_ALL_TAC THEN
  SUBGOAL_THEN `e:real^N->bool = segment[a,b]` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOI_SVX_OPEN_STAR_EQ THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN MESON_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SVX_OPEN_STAR_CARRIER) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_SCF_CF_PURE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tet:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `segment[a:real^N,b] SUBSET tet /\ (x:real^N) IN tet`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `tet:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` (X_CHOOSE_THEN `th:real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!y. y IN tet INTER moi_smo_open_star c (segment[a,b])
        ==> norm((kappa:real^N->real^3) y) = norm((A:real^N->real^3) y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_SMO_TWIST_NORM]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN tet /\ (b:real^N) IN tet` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `v:real^N = a \/ v = b` MP_TAC THENL
   [ASM_MESON_TAC[EXTREME_POINT_OF_SEGMENT]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `x:real^N`;
                   `tet:real^N->bool`; `A:real^N->real^3`] MOI_SVX_RHO_EQ) THEN
    ASM_REWRITE_TAC[DIST_0] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t0. &0 < t0 /\ t0 <= &1
         ==> norm(basis 3 + t0 % ((A:real^N->real^3) x - basis 3)) =
             t0 * norm(A x)`
  ASSUME_TAC THENL
   [X_GEN_TAC `t0:real` THEN STRIP_TAC THEN
    USE_THEN "hom" (MP_TAC o SPECL [`x:real^N`; `t0:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `b + t0 % (x - b):real^N IN tet` ASSUME_TAC THENL
     [SUBGOAL_THEN `b + t0 % (x - b):real^N = (&1 - t0) % b + t0 % x`
      SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
      MATCH_MP_TAC IN_CONVEX_SET THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_SBA_LF_CONVEX]; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`A:real^N->real^3`; `b:real^N`; `x:real^N`; `t0:real`]
      MOI_SVX_AFFINE_SEG) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[moi_smo_regmap]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN
     `norm((A:real^N->real^3) (b + t0 % (x - b))) =
      norm((kappa:real^N->real^3) (b + t0 % (x - b)))`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
    AP_TERM_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MATCH_MP_TAC MOI_SVX_TWO_SCALES THEN
  EXISTS_TAC `(A:real^N->real^3) x` THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOI_SVX_EDGE_MID = prove
 (`!c (v:real^N) e x.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\ e IN c /\ v IN e /\
     x IN moi_smo_open_star c e /\ ~(x = v)
     ==> v + inv(&2) % (moi_smo_ray c v x - v) IN moi_smo_open_star c e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SVX_OPEN_STAR_CARRIER) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                 `x:real^N`] MOI_SVX_RAY_PROPS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `inv(&2)` o last o CONJUNCTS) THEN
  ANTS_TAC THENL [CONV_TAC REAL_RAT_REDUCE_CONV; DISCH_TAC] THEN
  REWRITE_TAC[moi_smo_open_star; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `relative_interior t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_SVX_EDGE_CHART = prove
 (`!u c (v:real^N) x.
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\ {v} IN c /\
     x IN moi_smo_open_star c {v} /\ ~(x = v)
     ==> ?K kappa:real^N->real^3.
            (K,kappa) IN moi_smo_star_atlas c v /\
            (K,kappa) IN moi_smo_edge_atlas c /\ x IN K /\
            K SUBSET moi_smo_open_star c {v} /\ ~(v IN K) /\
            (!y. y IN K ==> norm(kappa y) = moi_smo_rho c v y) /\
            (!y. y IN K ==> v + inv(&2) % (moi_smo_ray c v y - v) IN K)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `x:real^N`]
    MOI_SVX_EDGE_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N) IN e` ASSUME_TAC THENL
   [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
  UNDISCH_TAC `MOI_SMO_EDGE_STATEMENT (u:N->bool)` THEN
  REWRITE_TAC[MOI_SMO_EDGE_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `c:(real^N->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`e:real^N->bool`; `v:real^N`] o CONJUNCT1) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `kappa:real^N->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((v:real^N) IN moi_smo_open_star c e)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
      MOI_SVX_V_NOT_IN_STAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`moi_smo_open_star c (e:real^N->bool)`;
                        `kappa:real^N->real^3`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SBA_OPEN_STAR_MONO THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    MATCH_MP_TAC MOI_SVX_EDGE_NORM THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_SVX_EDGE_MID THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Calculus of the cone map y |-> |y| G(gnom(R y)), where G is a smooth     *)
(* immersion of an open set of the plane into the unit sphere and R is      *)
(* orthogonal.  It is smooth where (R y)$3 > 0, and its derivative is       *)
(* invertible there: the radial part is detected by |F y| = |y| (derivative *)
(* of the squared norm), the transverse part by the injective derivative of *)
(* G, which is tangent to the sphere, and the kernel of the derivative of   *)
(* the gnomonic projection, which is the radial line.                       *)
(* ========================================================================= *)

let MOI_SVX_DERIV_UNIQUE_OPEN = prove
 (`!(f:real^M->real^N) g f' g' N x.
     open N /\ x IN N /\ (!y. y IN N ==> f y = g y) /\
     (f has_derivative f') (at x) /\ (g has_derivative g') (at x)
     ==> f' = g'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?d. &0 < d /\ ball(x:real^M,d) SUBSET N` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  MATCH_MP_TAC FRECHET_DERIVATIVE_UNIQUE_AT THEN
  MAP_EVERY EXISTS_TAC [`g:real^M->real^N`; `x:real^M`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HAS_DERIVATIVE_TRANSFORM_AT THEN
  MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `d:real`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
  ASM_REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM]);;

let MOI_SVX_SQNORM_DERIV = prove
 (`!(f:real^M->real^N) (g:real^M->real^P) f' g' N y0.
     open N /\ y0 IN N /\ (!y. y IN N ==> norm(f y) = norm(g y)) /\
     (f has_derivative f') (at y0) /\ (g has_derivative g') (at y0)
     ==> !h. f y0 dot f' h = g y0 dot g' h`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `((\y. lift(norm((f:real^M->real^N) y) pow 2)) has_derivative
     (\h:real^M. &2 % lift(f y0 dot (f':real^M->real^N) h))) (at y0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `\x:real^N. lift(norm x pow 2)`;
                   `f':real^M->real^N`;
                   `\x:real^N. &2 % lift((f:real^M->real^N) y0 dot x)`; `y0:real^M`]
      DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT; o_DEF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y. lift(norm((g:real^M->real^P) y) pow 2)) has_derivative
     (\h:real^M. &2 % lift(g y0 dot (g':real^M->real^P) h))) (at y0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`g:real^M->real^P`; `\x:real^P. lift(norm x pow 2)`;
                   `g':real^M->real^P`;
                   `\x:real^P. &2 % lift((g:real^M->real^P) y0 dot x)`; `y0:real^M`]
      DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_SQNORM_AT; o_DEF];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\y. lift(norm((f:real^M->real^N) y) pow 2)`;
    `\y. lift(norm((g:real^M->real^P) y) pow 2)`;
    `\h:real^M. &2 % lift((f:real^M->real^N) y0 dot (f':real^M->real^N) h)`;
    `\h:real^M. &2 % lift((g:real^M->real^P) y0 dot (g':real^M->real^P) h)`;
    `N:real^M->bool`; `y0:real^M`] MOI_SVX_DERIV_UNIQUE_OPEN) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(fun th -> X_GEN_TAC `h:real^M` THEN MP_TAC(AP_THM th `h:real^M`)) THEN
  REWRITE_TAC[GSYM LIFT_CMUL; LIFT_EQ] THEN REAL_ARITH_TAC);;

let MOI_SVX_GNOM_KERNEL = prove
 (`!z w:real^3. &0 < z$3 /\ frechet_derivative moi_smo_gnom (at z) w = vec 0
                ==> w = (w$3 / z$3) % z`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `Dg = frechet_derivative moi_smo_gnom (at (z:real^3))` THEN
  ABBREV_TAC `E = \p:real^2. vector[p$1; p$2; &0]:real^3` THEN
  SUBGOAL_THEN `linear (E:real^2->real^3)` ASSUME_TAC THENL
   [EXPAND_TAC "E" THEN REWRITE_TAC[linear] THEN BETA_TAC THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. &0 < y$3 ==> y = y$3 % E(moi_smo_gnom y) + y$3 % basis 3`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "E" THEN BETA_TAC THEN
    FIRST_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [MATCH_MP MOI_SLK_GNOM_LIFT th]) THEN
    SIMP_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VECTOR_ADD_COMPONENT;
             VECTOR_MUL_COMPONENT; BASIS_COMPONENT; ARITH] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `open {y:real^3 | y$3 > &0}` ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT]; ALL_TAC] THEN
  SUBGOAL_THEN `(moi_smo_gnom has_derivative Dg) (at (z:real^3))` ASSUME_TAC THENL
   [EXPAND_TAC "Dg" THEN
    MP_TAC(ISPECL [`{y:real^3 | y$3 > &0}`; `moi_smo_gnom`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_SLK_GNOM_SMOOTH THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; real_gt] THEN REAL_ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; real_gt]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y:real^3. y$3 % (E:real^2->real^3)(moi_smo_gnom y) + y$3 % basis 3) has_derivative
     (\w:real^3. (z$3 % E((Dg:real^3->real^2) w) + w$3 % E(moi_smo_gnom z)) +
                 w$3 % basis 3)) (at z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HAS_DERIVATIVE_ADD THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`\y:real^3. y$3`; `\y:real^3. y$3`;
                     `(E:real^2->real^3) o moi_smo_gnom`;
                     `(E:real^2->real^3) o (Dg:real^3->real^2)`; `z:real^3`]
        HAS_DERIVATIVE_MUL_AT) THEN
      REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
        REWRITE_TAC[LINEAR_LIFT_COMPONENT];
        MP_TAC(ISPECL [`moi_smo_gnom`; `E:real^2->real^3`; `Dg:real^3->real^2`;
                       `E:real^2->real^3`; `z:real^3`] DIFF_CHAIN_AT) THEN
        ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR; o_DEF]];
      MATCH_MP_TAC HAS_DERIVATIVE_LINEAR THEN
      REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`\y:real^3. y`;
    `\y:real^3. y$3 % (E:real^2->real^3)(moi_smo_gnom y) + y$3 % basis 3`;
    `\w:real^3. w`;
    `\w:real^3. (z$3 % (E:real^2->real^3)((Dg:real^3->real^2) w) +
                 w$3 % E(moi_smo_gnom z)) + w$3 % basis 3`;
    `{y:real^3 | y$3 > &0}`; `z:real^3`] MOI_SVX_DERIV_UNIQUE_OPEN) THEN
  ASM_REWRITE_TAC[HAS_DERIVATIVE_ID; IN_ELIM_THM; real_gt] THEN
  TRY(ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
  DISCH_THEN(MP_TAC o C AP_THM `w:real^3`) THEN BETA_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MATCH_MP LINEAR_0 (ASSUME `linear(E:real^2->real^3)`);
              VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
  FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV)
   [MATCH_MP th (ASSUME `&0 < (z:real^3)$3`)]) THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
  ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]);;

let MOI_SVX_UNIT_DERIV = prove
 (`!(G:real^2->real^3) P p.
     open P /\ p IN P /\ smooth_map_on P G /\ (!q. q IN P ==> norm(G q) = &1)
     ==> !k. G p dot frechet_derivative G (at p) k = &0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((G:real^2->real^3) has_derivative frechet_derivative G (at p))
                (at p)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SMOOTH_MAP_ON_HAS_DERIVATIVE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`G:real^2->real^3`; `\q:real^2. (G:real^2->real^3) p`;
                 `frechet_derivative (G:real^2->real^3) (at p)`;
                 `\h:real^2. vec 0:real^3`; `P:real^2->bool`; `p:real^2`]
    MOI_SVX_SQNORM_DERIV) THEN
  ASM_SIMP_TAC[HAS_DERIVATIVE_CONST] THEN
  REWRITE_TAC[DOT_RZERO] THEN DISCH_THEN MATCH_ACCEPT_TAC);;

let MOI_SVX_CONE_PARTS = prove
 (`!(R:real^3->real^3) (G:real^2->real^3) P S.
     linear R /\ open P /\ smooth_map_on P G /\ open S /\
     (!y. y IN S ==> &0 < (R y)$3 /\ moi_smo_gnom(R y) IN P)
     ==> (!y. y IN S ==> ~(y = vec 0)) /\
         smooth_map_on S (\y. lift(norm y)) /\
         smooth_map_on S (\y. G(moi_smo_gnom(R y))) /\
         smooth_map_on S (\y. norm y % G(moi_smo_gnom(R y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. y IN S ==> ~(y = vec 0)` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^3`) THEN
    ASM_REWRITE_TAC[MATCH_MP LINEAR_0 (ASSUME `linear(R:real^3->real^3)`);
                    VEC_COMPONENT; REAL_LT_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (\y:real^3. lift(norm y))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `\y:real^3. y`] SMOOTH_MAP_ON_LIFT_NORM) THEN
    ASM_SIMP_TAC[SMOOTH_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (\y:real^3. moi_smo_gnom(R y))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `{z:real^3 | z$3 > &0}`;
                   `R:real^3->real^3`; `moi_smo_gnom`]
      SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; real_gt] THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC MOI_SBA_AFFINE_SMOOTH THEN
      MAP_EVERY EXISTS_TAC [`R:real^3->real^3`; `vec 0:real^3`] THEN
      ASM_REWRITE_TAC[VECTOR_ADD_RID];
      MATCH_MP_TAC MOI_SLK_GNOM_SMOOTH THEN
      REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; IN_ELIM_THM; real_gt] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `smooth_map_on S (\y:real^3. (G:real^2->real^3)(moi_smo_gnom(R y)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`S:real^3->bool`; `P:real^2->bool`;
                   `\y:real^3. moi_smo_gnom(R y)`; `G:real^2->real^3`]
      SMOOTH_MAP_ON_COMPOSE_OPEN) THEN
    REWRITE_TAC[o_DEF] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `\a:real^1 x:real^3. drop a % x`;
                 `\y:real^3. lift(norm y)`;
                 `\y:real^3. (G:real^2->real^3)(moi_smo_gnom(R y))`]
    SMOOTH_MAP_ON_BILINEAR_OPEN) THEN
  ASM_REWRITE_TAC[BILINEAR_DROP_MUL; LIFT_DROP]);;

let MOI_SVX_CONE_DET = prove
 (`!(R:real^3->real^3) (G:real^2->real^3) P y0.
     orthogonal_transformation R /\ open P /\ smooth_map_on P G /\
     (!p. p IN P ==> norm(G p) = &1) /\
     (!p h. p IN P /\ frechet_derivative G (at p) h = vec 0 ==> h = vec 0) /\
     &0 < (R y0)$3 /\ moi_smo_gnom(R y0) IN P
     ==> ~(det(matrix(frechet_derivative
                       (\y. norm y % G(moi_smo_gnom(R y))) (at y0))) = &0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `linear (R:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  ABBREV_TAC `S0 = {y:real^3 | &0 < (R y)$3 /\ moi_smo_gnom(R y) IN P}` THEN
  SUBGOAL_THEN `open (S0:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S0" THEN
    SUBGOAL_THEN
     `{y:real^3 | &0 < (R y)$3 /\ moi_smo_gnom(R y) IN P} =
      {y | y IN {y | (R:real^3->real^3) y IN {z:real^3 | z$3 > &0}} /\
           (moi_smo_gnom o R) y IN P}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; o_THM; real_gt]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN ASM_REWRITE_TAC[ETA_AX] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
        MATCH_MP_TAC MOI_SLK_GNOM_CONTINUOUS THEN
        REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM; real_gt] THEN MESON_TAC[]];
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
      ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; OPEN_HALFSPACE_COMPONENT_GT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN S0 ==> &0 < ((R:real^3->real^3) y)$3 /\ moi_smo_gnom(R y) IN P`
  ASSUME_TAC THENL [EXPAND_TAC "S0" THEN SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN `(y0:real^3) IN S0` ASSUME_TAC THENL
   [EXPAND_TAC "S0" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real^3->real^3`; `G:real^2->real^3`; `P:real^2->bool`;
                 `S0:real^3->bool`] MOI_SVX_CONE_PARTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `p0 = moi_smo_gnom((R:real^3->real^3) y0)` THEN
  ABBREV_TAC `Nn = frechet_derivative (\y:real^3. lift(norm y)) (at y0)` THEN
  ABBREV_TAC `Dg = frechet_derivative moi_smo_gnom (at ((R:real^3->real^3) y0))` THEN
  ABBREV_TAC `DG = frechet_derivative (G:real^2->real^3) (at p0)` THEN
  SUBGOAL_THEN `((\y:real^3. lift(norm y)) has_derivative Nn) (at y0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "Nn" THEN ASM_MESON_TAC[SMOOTH_MAP_ON_HAS_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN `(moi_smo_gnom has_derivative Dg) (at ((R:real^3->real^3) y0))`
  ASSUME_TAC THENL
   [EXPAND_TAC "Dg" THEN
    MP_TAC(ISPECL [`{z:real^3 | z$3 > &0}`; `moi_smo_gnom`]
      SMOOTH_MAP_ON_HAS_DERIVATIVE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
      MATCH_MP_TAC MOI_SLK_GNOM_SMOOTH THEN
      REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT; IN_ELIM_THM; real_gt] THEN
      REAL_ARITH_TAC;
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM; real_gt]];
    ALL_TAC] THEN
  SUBGOAL_THEN `((G:real^2->real^3) has_derivative DG) (at p0)` ASSUME_TAC THENL
   [EXPAND_TAC "DG" THEN ASM_MESON_TAC[SMOOTH_MAP_ON_HAS_DERIVATIVE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((\y:real^3. (G:real^2->real^3)(moi_smo_gnom(R y))) has_derivative
     (\h. (DG:real^2->real^3)((Dg:real^3->real^2)(R h)))) (at y0)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`R:real^3->real^3`; `moi_smo_gnom`; `R:real^3->real^3`;
                   `Dg:real^3->real^2`; `y0:real^3`] DIFF_CHAIN_AT) THEN
    ASM_SIMP_TAC[HAS_DERIVATIVE_LINEAR] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`moi_smo_gnom o (R:real^3->real^3)`; `G:real^2->real^3`;
                   `(Dg:real^3->real^2) o (R:real^3->real^3)`;
                   `DG:real^2->real^3`; `y0:real^3`] DIFF_CHAIN_AT) THEN
    ASM_REWRITE_TAC[o_THM] THEN REWRITE_TAC[o_DEF];
    ALL_TAC] THEN
  ABBREV_TAC
   `L = \h:real^3. norm(y0:real^3) % (DG:real^2->real^3)((Dg:real^3->real^2)(R h)) +
                  drop((Nn:real^3->real^1) h) % (G:real^2->real^3) p0` THEN
  SUBGOAL_THEN
   `((\y:real^3. norm y % (G:real^2->real^3)(moi_smo_gnom(R y))) has_derivative L)
    (at y0)`
  ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN
    MP_TAC(ISPECL [`\y:real^3. norm y`; `\h:real^3. drop((Nn:real^3->real^1) h)`;
                   `\y:real^3. (G:real^2->real^3)(moi_smo_gnom(R y))`;
                   `\h:real^3. (DG:real^2->real^3)((Dg:real^3->real^2)
                                     ((R:real^3->real^3) h))`; `y0:real^3`]
      HAS_DERIVATIVE_MUL_AT) THEN
    ASM_REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX];
    ALL_TAC] THEN
  SUBGOAL_THEN `linear (L:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[has_derivative]; ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP FRECHET_DERIVATIVE_AT) THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  ASM_SIMP_TAC[MATRIX_WORKS] THEN
  REWRITE_TAC[NOT_EXISTS_THM; TAUT `~(~a /\ b) <=> b ==> a`] THEN
  X_GEN_TAC `h:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y0:real^3) dot h = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\y:real^3. norm y % (G:real^2->real^3)(moi_smo_gnom(R y))`;
                   `\y:real^3. y`; `L:real^3->real^3`; `\h:real^3. h`;
                   `S0:real^3->bool`; `y0:real^3`] MOI_SVX_SQNORM_DERIV) THEN
    ASM_REWRITE_TAC[HAS_DERIVATIVE_ID] THEN ANTS_TAC THENL
     [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      ASM_SIMP_TAC[NORM_MUL; REAL_ABS_NORM; REAL_MUL_RID];
      DISCH_THEN(MP_TAC o SPEC `h:real^3`) THEN ASM_REWRITE_TAC[DOT_RZERO] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `drop((Nn:real^3->real^1) h) = &0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`G:real^2->real^3`; `P:real^2->bool`; `p0:real^2`]
      MOI_SVX_UNIT_DERIV) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o SPEC `(Dg:real^3->real^2)((R:real^3->real^3) h)`) THEN
    UNDISCH_TAC `(L:real^3->real^3) h = vec 0` THEN EXPAND_TAC "L" THEN
    DISCH_THEN(MP_TAC o AP_TERM `\z:real^3. (G:real^2->real^3) p0 dot z`) THEN
    ASM_REWRITE_TAC[DOT_RADD; DOT_RMUL; DOT_RZERO; REAL_MUL_RZERO;
                    REAL_ADD_LID] THEN
    SUBGOAL_THEN `(G:real^2->real^3) p0 dot G p0 = &1` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM NORM_POW_2] THEN ASM_SIMP_TAC[] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(DG:real^2->real^3)((Dg:real^3->real^2)((R:real^3->real^3) h)) = vec 0`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(L:real^3->real^3) h = vec 0` THEN EXPAND_TAC "L" THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; VECTOR_MUL_EQ_0] THEN
    REWRITE_TAC[NORM_EQ_0] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Dg:real^3->real^2)((R:real^3->real^3) h) = vec 0` ASSUME_TAC THENL
   [UNDISCH_TAC `(DG:real^2->real^3)((Dg:real^3->real^2)
                                     ((R:real^3->real^3) h)) = vec 0` THEN
    EXPAND_TAC "DG" THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(R:real^3->real^3) y0`; `(R:real^3->real^3) h`]
    MOI_SVX_GNOM_KERNEL) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `cc = ((R:real^3->real^3) h)$3 / (R y0)$3` THEN
  ASM_SIMP_TAC[GSYM LINEAR_CMUL] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MATCH_MP ORTHOGONAL_TRANSFORMATION_INJECTIVE
    (ASSUME `orthogonal_transformation (R:real^3->real^3)`))) THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `(y0:real^3) dot (cc % y0) = &0` THEN
  REWRITE_TAC[DOT_RMUL; REAL_ENTIRE] THEN
  ASM_SIMP_TAC[DOT_EQ_0; VECTOR_MUL_LZERO] THEN
  ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* The vertex chart in a star chart at v.  Near each point of the domain of  *)
(* a star chart (K,kappa) with |kappa| = rho, the vertex chart is            *)
(* y |-> |y| G(gnom(R y)) in the coordinates y = kappa x, G the              *)
(* immersion given by d in the link chart of (K,kappa,R).  Consequences:     *)
(* smoothness of chart o kappa^-1, continuity and injectivity of the         *)
(* vertex chart, its homeomorphism onto an open set (invariance of domain),  *)
(* and smoothness of kappa o chart^-1 (inverse function theorem).            *)
(* ========================================================================= *)

let MOI_SVX_HOMOG_SCALE = prove
 (`!K (kappa:real^N->real^3) v x m r.
     (!x t. x IN K /\ &0 < t /\ t <= &1
            ==> v + t % (x - v) IN K /\ kappa(v + t % (x - v)) = t % kappa x) /\
     x IN K /\ m IN K /\ &0 < r /\ x - v = r % (m - v)
     ==> kappa x = r % kappa m`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "hom") STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `r <= &1` THENL
   [SUBGOAL_THEN `x:real^N = v + r % (m - v)` SUBST1_TAC THENL
     [UNDISCH_TAC `x - v:real^N = r % (m - v)` THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "hom" (MP_TAC o SPECL [`m:real^N`; `r:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `m:real^N = v + inv r % (x - v)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(kappa:real^N->real^3) m = inv r % kappa x` SUBST1_TAC THENL
   [USE_THEN "hom" (MP_TAC o SPECL [`x:real^N`; `inv r`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_INV_EQ] THEN MATCH_MP_TAC REAL_INV_LE_1 THEN
      ASM_REAL_ARITH_TAC;
      ASM_MESON_TAC[]];
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

let MOI_SVX_LOCAL = prove
 (`!u c (v:real^N) (d:real^N->real^3) d' K (kappa:real^N->real^3) x0.
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\ {v} IN c /\
     homeomorphism (UNIONS(simplicial_link c v),sphere(vec 0:real^3,&1)) (d,d') /\
     smooth_immersion_into (moi_smo_link_atlas c v) d /\
     (K,kappa) IN moi_smo_star_atlas c v /\ K SUBSET moi_smo_open_star c {v} /\
     ~(v IN K) /\
     (!y. y IN K ==> norm(kappa y) = moi_smo_rho c v y) /\
     (!y. y IN K ==> v + inv(&2) % (moi_smo_ray c v y - v) IN K) /\
     x0 IN K
     ==> ?(R:real^3->real^3) (G:real^2->real^3) (P:real^2->bool).
            orthogonal_transformation R /\ open P /\ smooth_map_on P G /\
            (!p. p IN P ==> norm(G p) = &1) /\
            (!p h. p IN P /\ frechet_derivative G (at p) h = vec 0 ==> h = vec 0) /\
            &0 < (R(kappa x0))$3 /\
            (!x. x IN K /\ &0 < (R(kappa x))$3
                 ==> moi_smo_gnom(R(kappa x)) IN P /\
                     moi_smo_vertex_chart c v d x =
                     norm(kappa x) % G(moi_smo_gnom(R(kappa x))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x t. x IN K /\ &0 < t /\ t <= &1
          ==> v + t % (x - v) IN K /\
              (kappa:real^N->real^3)(v + t % (x - v)) = t % kappa x`
  (LABEL_TAC "hom") THENL
   [UNDISCH_TAC `((K:real^N->bool),(kappa:real^N->real^3)) IN
                 moi_smo_star_atlas c v` THEN
    REWRITE_TAC[MOI_SBA_STAR_ATLAS_IN] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `K:real^N->bool`; `kappa:real^N->real^3`] MOI_SLK_STAR_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SLK_HMAP) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `kinv:real^3->real^N`)
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj"))) THEN
  SUBGOAL_THEN `~((kappa:real^N->real^3) x0 = vec 0)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SLK_NONZERO THEN
    MAP_EVERY EXISTS_TAC [`K:real^N->bool`; `v:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(kappa:real^N->real^3) x0`;
                 `norm((kappa:real^N->real^3) x0) % basis 3:real^3`]
    ORTHOGONAL_TRANSFORMATION_EXISTS) THEN
  ANTS_TAC THENL
   [SIMP_TAC[NORM_MUL; REAL_ABS_NORM; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `linear (R:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!l. l IN UNIONS(simplicial_link c v) ==> norm((d:real^N->real^3) l) = &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `l:real^N` THEN DISCH_TAC THEN REWRITE_TAC[GSYM IN_SPHERE_0] THEN
    UNDISCH_TAC `homeomorphism (UNIONS(simplicial_link c (v:real^N)),
                                sphere(vec 0:real^3,&1))
                               ((d:real^N->real^3),(d':real^3->real^N))` THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `W = {l | l IN UNIONS(simplicial_link c v) /\ v + inv(&2) % (l - v) IN K /\
             &0 < ((R:real^3->real^3)
                    ((kappa:real^N->real^3)(v + inv(&2) % (l - v))))$3}` THEN
  ABBREV_TAC
   `psi = \l:real^N. moi_smo_gnom((R:real^3->real^3)
                       ((kappa:real^N->real^3)(v + inv(&2) % (l - v))))` THEN
  SUBGOAL_THEN `((W:real^N->bool),(psi:real^N->real^2)) IN moi_smo_link_atlas c v`
  ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["W"; "psi"] THEN
    REWRITE_TAC[moi_smo_link_atlas; IN_ELIM_THM; PAIR_EQ] THEN
    MAP_EVERY EXISTS_TAC [`K:real^N->bool`; `kappa:real^N->real^3`;
                          `R:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `smooth_immersion_into (moi_smo_link_atlas c v) (d:real^N->real^3)` THEN
  REWRITE_TAC[smooth_immersion_into] THEN
  DISCH_THEN(MP_TAC o SPECL [`W:real^N->bool`; `psi:real^N->real^2`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^2->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `open (IMAGE (psi:real^N->real^2) W)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `u:N->bool` MOI_SMO_LINK_ATLAS_FROM_EDGE) THEN
    ASM_REWRITE_TAC[MOI_SMO_LINK_ATLAS_STATEMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`c:(real^N->bool)->bool`; `v:real^N`]) THEN
    ASM_REWRITE_TAC[smooth_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPECL [`W:real^N->bool`; `psi:real^N->real^2`] o
               CONJUNCT1) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`R:real^3->real^3`; `G:real^2->real^3`;
                        `IMAGE (psi:real^N->real^2) W`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `l:real^N` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(l:real^N) IN W` THEN EXPAND_TAC "W" THEN SIMP_TAC[IN_ELIM_THM];
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH;
             REAL_MUL_RID; NORM_POS_LT;
             ASSUME `(R:real^3->real^3)((kappa:real^N->real^3) x0) =
                     norm(kappa x0) % basis 3`;
             ASSUME `~((kappa:real^N->real^3) x0 = vec 0)`];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN moi_smo_open_star c {v} /\ ~(x = v)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SVX_STAR_CARRIER) THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s0:real^N->bool`;
                 `x:real^N`] MOI_SVX_RAY_PROPS) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `l = moi_smo_ray c v (x:real^N)` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  SUBGOAL_THEN `v + inv(&2) % (l - v):real^N IN K` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_smo_ray c v (x:real^N) = l` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(kappa:real^N->real^3) x = (&2 * s) % kappa(v + inv(&2) % (l - v))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SVX_HOMOG_SCALE THEN
    MAP_EVERY EXISTS_TAC [`K:real^N->bool`; `v:real^N`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `x:real^N = v + s % (l - v)` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[VECTOR_ARITH `(v + s % (l - v)) - v:real^N = s % (l - v)`;
                VECTOR_ARITH `(v + inv(&2) % (l - v)) - v:real^N = inv(&2) % (l - v)`;
                VECTOR_MUL_ASSOC] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&0 < ((R:real^3->real^3)((kappa:real^N->real^3)(v + inv(&2) % (l - v))))$3`
  ASSUME_TAC THENL
   [UNDISCH_TAC `&0 < ((R:real^3->real^3)((kappa:real^N->real^3) x))$3` THEN
    ASM_SIMP_TAC[LINEAR_CMUL; VECTOR_MUL_COMPONENT] THEN
    REWRITE_TAC[REAL_ARITH `&0 < (&2 * s) * y <=> &0 < s * y`] THEN
    ASM_SIMP_TAC[REAL_LT_MUL_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^N) IN W` ASSUME_TAC THENL
   [EXPAND_TAC "W" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_smo_gnom((R:real^3->real^3)((kappa:real^N->real^3) x)) =
    (psi:real^N->real^2) l`
  ASSUME_TAC THENL
   [EXPAND_TAC "psi" THEN ASM_SIMP_TAC[LINEAR_CMUL] THEN
    MATCH_MP_TAC MOI_SLK_GNOM_CMUL THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[ASSUME `moi_smo_gnom((R:real^3->real^3)((kappa:real^N->real^3) x)) =
                      (psi:real^N->real^2) l`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_smo_vertex_chart; ASSUME `moi_smo_ray c v (x:real^N) = l`] THEN
  SUBGOAL_THEN `(G:real^2->real^3)((psi:real^N->real^2) l) = (d:real^N->real^3) l`
  SUBST1_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN CONV_TAC SYM_CONV THEN ASM_SIMP_TAC[]);;

let MOI_SVX_OPEN_RHALF = prove
 (`!R:real^3->real^3. linear R ==> open {y | &0 < (R y)$3}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{y | &0 < ((R:real^3->real^3) y)$3} =
                {y | R y IN {z:real^3 | z$3 > &0}}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; real_gt]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
  ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT; OPEN_HALFSPACE_COMPONENT_GT]);;

let MOI_SVX_G0 = prove
 (`!u c (v:real^N) (d:real^N->real^3) d' K (kappa:real^N->real^3).
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\ {v} IN c /\
     homeomorphism (UNIONS(simplicial_link c v),sphere(vec 0:real^3,&1)) (d,d') /\
     smooth_immersion_into (moi_smo_link_atlas c v) d /\
     (K,kappa) IN moi_smo_star_atlas c v /\ K SUBSET moi_smo_open_star c {v} /\
     ~(v IN K) /\
     (!y. y IN K ==> norm(kappa y) = moi_smo_rho c v y) /\
     (!y. y IN K ==> v + inv(&2) % (moi_smo_ray c v y - v) IN K)
     ==> open_in (subtopology euclidean (UNIONS c)) (moi_smo_vertex_dom c v INTER K) /\
         open (IMAGE kappa (moi_smo_vertex_dom c v INTER K)) /\
         ?G0. smooth_map_on (IMAGE kappa (moi_smo_vertex_dom c v INTER K)) G0 /\
              !x. x IN moi_smo_vertex_dom c v INTER K
                  ==> G0(kappa x) = moi_smo_vertex_chart c v d x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `K:real^N->bool`; `kappa:real^N->real^3`] MOI_SLK_STAR_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SLK_HMAP) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `kinv:real^3->real^N`)
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c))
                  (moi_smo_vertex_dom c (v:real^N) INTER K)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_INTER THEN ASM_SIMP_TAC[MOI_SVX_DOM_OPEN]; ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (kappa:real^N->real^3)
                       (moi_smo_vertex_dom c v INTER K))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SLK_OPEN_IMAGE_SUB THEN
    MAP_EVERY EXISTS_TAC [`UNIONS c:real^N->bool`; `K:real^N->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `\y. moi_smo_vertex_chart c v (d:real^N->real^3)
                    ((kinv:real^3->real^N) y)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    BETA_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `homeomorphism (K,IMAGE (kappa:real^N->real^3) K) (kappa,kinv)` THEN
    REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC MOI_SLK_SMOOTH_LOCAL THEN ASM_REWRITE_TAC[FORALL_IN_IMAGE] THEN
  X_GEN_TAC `x0:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `d:real^N->real^3`; `d':real^3->real^N`; `K:real^N->bool`;
                 `kappa:real^N->real^3`; `x0:real^N`] MOI_SVX_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3` (X_CHOOSE_THEN `G:real^2->real^3`
    (X_CHOOSE_THEN `P:real^2->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `linear (R:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  ABBREV_TAC `t = IMAGE (kappa:real^N->real^3) (moi_smo_vertex_dom c v INTER K) INTER
                  {y | &0 < ((R:real^3->real^3) y)$3}` THEN
  SUBGOAL_THEN `open (t:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN MATCH_MP_TAC OPEN_INTER THEN
    ASM_SIMP_TAC[MOI_SVX_OPEN_RHALF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN t
        ==> ?x. x IN moi_smo_vertex_dom c v INTER K /\ y = (kappa:real^N->real^3) x /\
                &0 < ((R:real^3->real^3) y)$3`
  ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[IN_INTER; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `\y:real^3. norm y % (G:real^2->real^3)(moi_smo_gnom(R y))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(kinv:real^3->real^N)((kappa:real^N->real^3) x) = x` SUBST1_TAC THENL
     [UNDISCH_TAC `homeomorphism (K,IMAGE (kappa:real^N->real^3) K) (kappa,kinv)` THEN
      REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real^3->real^3`; `G:real^2->real^3`; `P:real^2->bool`;
                 `t:real^3->bool`] MOI_SVX_CONE_PARTS) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);;

let MOI_SVX_CONT_COMPARE = prove
 (`!(f:real^N->real^M) g s a.
     (\x. lift(g x)) continuous (at a within s) /\ g a = &0 /\
     (!x. x IN s ==> norm(f x - f a) <= g x)
     ==> f continuous (at a within s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONTINUOUS_WITHIN] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[LIM_NULL] THEN MATCH_MP_TAC LIM_NULL_COMPARISON THEN
  EXISTS_TAC `g:real^N->real` THEN CONJ_TAC THENL
   [REWRITE_TAC[EVENTUALLY_WITHIN] THEN EXISTS_TAC `&1` THEN
    ASM_SIMP_TAC[REAL_LT_01];
    UNDISCH_TAC `((\x. lift((g:real^N->real) x)) --> lift(g a))
                 (at a within s)` THEN
    ASM_REWRITE_TAC[LIFT_NUM]]);;

let MOI_SVX_CHART_NORM = prove
 (`!c (v:real^N) (d:real^N->real^3) d' x.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     homeomorphism (UNIONS(simplicial_link c v),sphere(vec 0:real^3,&1)) (d,d') /\
     x IN moi_smo_open_star c {v}
     ==> norm(moi_smo_vertex_chart c v d x) = moi_smo_rho c v x /\
         (x = v ==> moi_smo_vertex_chart c v d x = vec 0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `x:real^N = v` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    ASM_SIMP_TAC[moi_smo_vertex_chart; MOI_SVX_RHO_V; VECTOR_MUL_LZERO; NORM_0];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_smo_vertex_chart] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SVX_STAR_CARRIER) THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s0:real^N->bool`;
                 `x:real^N`] MOI_SVX_RAY_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `norm((d:real^N->real^3)(moi_smo_ray c v x)) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_SPHERE_0] THEN
    UNDISCH_TAC `homeomorphism (UNIONS(simplicial_link c (v:real^N)),
                                sphere(vec 0:real^3,&1))
                               ((d:real^N->real^3),(d':real^3->real^N))` THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID; REAL_ABS_REFL] THEN
  ASM_MESON_TAC[MOI_SVX_RHO_POS]);;

let MOI_SVX_CHART_CONT = prove
 (`!u c (v:real^N) (d:real^N->real^3) d'.
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\ {v} IN c /\
     homeomorphism (UNIONS(simplicial_link c v),sphere(vec 0:real^3,&1)) (d,d') /\
     smooth_immersion_into (moi_smo_link_atlas c v) d
     ==> (moi_smo_vertex_chart c v d) continuous_on (moi_smo_vertex_dom c v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_smo_vertex_dom c (v:real^N) SUBSET moi_smo_open_star c {v}`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_smo_vertex_dom; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `x:real^N = v` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC MOI_SVX_CONT_COMPARE THEN
    EXISTS_TAC `moi_smo_rho c (v:real^N)` THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SVX_RHO_CONT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `moi_smo_vertex_dom c (v:real^N)` o
                 MATCH_MP (REWRITE_RULE[IMP_CONJ] CONTINUOUS_ON_SUBSET)) THEN
      ASM_REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MOI_SVX_RHO_V];
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `d:real^N->real^3`;
                     `d':real^3->real^N`; `v:real^N`] MOI_SVX_CHART_NORM) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `d:real^N->real^3`;
                     `d':real^3->real^N`; `y:real^N`] MOI_SVX_CHART_NORM) THEN
      ASM_SIMP_TAC[MOI_SVX_V_IN_STAR] THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SIMP_TAC[VECTOR_SUB_RZERO; REAL_LE_REFL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`; `x:real^N`]
    MOI_SVX_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real^N->bool` (X_CHOOSE_THEN `kappa:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `d:real^N->real^3`; `d':real^3->real^N`; `K:real^N->bool`;
                 `kappa:real^N->real^3`] MOI_SVX_G0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `G0:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `K:real^N->bool`; `kappa:real^N->real^3`] MOI_SLK_STAR_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SLK_HMAP) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(moi_smo_vertex_chart c v (d:real^N->real^3)) continuous_on
    (moi_smo_vertex_dom c v INTER K)`
  MP_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_EQ THEN
    EXISTS_TAC `(G0:real^3->real^3) o (kappa:real^N->real^3)` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET];
      ASM_MESON_TAC[SMOOTH_MAP_ON_CONTINUOUS_ON]];
    ALL_TAC] THEN
  REWRITE_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_WITHIN] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[IN_INTER] THEN
  MATCH_MP_TAC EQ_IMP THEN MATCH_MP_TAC CONTINUOUS_WITHIN_OPEN_IN THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
  EXISTS_TAC `UNIONS c:real^N->bool` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `UNIONS c INTER K:real^N->bool = K` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS c:real^N->bool)`; `K:real^N->bool`]
      OPEN_IN_SUBSET) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN SET_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SVX_DOM_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]]);;

let MOI_SVX_CHART_INJ = prove
 (`!c (v:real^N) (d:real^N->real^3) d'.
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     homeomorphism (UNIONS(simplicial_link c v),sphere(vec 0:real^3,&1)) (d,d')
     ==> !x y. x IN moi_smo_vertex_dom c v /\ y IN moi_smo_vertex_dom c v /\
               moi_smo_vertex_chart c v d x = moi_smo_vertex_chart c v d y
               ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN moi_smo_open_star c {v} /\ y IN moi_smo_open_star c {v}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN moi_smo_vertex_dom c v` THEN
    UNDISCH_TAC `(y:real^N) IN moi_smo_vertex_dom c v` THEN
    SIMP_TAC[moi_smo_vertex_dom; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_smo_rho c v (x:real^N) = moi_smo_rho c v y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `d:real^N->real^3`;
                   `d':real^3->real^N`; `x:real^N`] MOI_SVX_CHART_NORM) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `d:real^N->real^3`;
                   `d':real^3->real^N`; `y:real^N`] MOI_SVX_CHART_NORM) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SVX_RHO_V) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`]
    MOI_SVX_RHO_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `x:real^N`]
    MOI_SVX_RHO_POS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_CASES_TAC `x:real^N = v` THENL
   [UNDISCH_TAC `moi_smo_rho c v (x:real^N) = moi_smo_rho c v y` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    ASM_CASES_TAC `y:real^N = v` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(y:real^N = v) ==> &0 < moi_smo_rho c v y` THEN
    ASM_REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  ASM_CASES_TAC `y:real^N = v` THENL
   [UNDISCH_TAC `moi_smo_rho c v (x:real^N) = moi_smo_rho c v y` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(x:real^N = v) ==> &0 < moi_smo_rho c v x` THEN
    ASM_REWRITE_TAC[REAL_LT_REFL];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SVX_STAR_CARRIER o
    check (fun th -> concl th = `(x:real^N) IN moi_smo_open_star c {v}`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SVX_STAR_CARRIER o
    check (fun th -> concl th = `(y:real^N) IN moi_smo_open_star c {v}`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s1:real^N->bool`;
                 `x:real^N`] MOI_SVX_RAY_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s2:real^N->bool`;
                 `y:real^N`] MOI_SVX_RAY_PROPS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s1:real^N->bool`;
                 `x:real^N`] MOI_SVX_RHO_RAY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s2:real^N->bool`;
                 `y:real^N`] MOI_SVX_RHO_RAY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_smo_ray c v (x:real^N) = moi_smo_ray c v y` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(d:real^N->real^3)(moi_smo_ray c v x) = d(moi_smo_ray c v y)`
    MP_TAC THENL
     [UNDISCH_TAC `moi_smo_vertex_chart c v (d:real^N->real^3) x =
                   moi_smo_vertex_chart c v d y` THEN
      REWRITE_TAC[moi_smo_vertex_chart;
                  ASSUME `moi_smo_rho c v (x:real^N) = moi_smo_rho c v y`;
                  VECTOR_MUL_LCANCEL] THEN
      SUBGOAL_THEN `~(moi_smo_rho c v (y:real^N) = &0)`
        (fun th -> REWRITE_TAC[th]) THEN
      ASM_MESON_TAC[REAL_LT_IMP_NZ];
      UNDISCH_TAC `homeomorphism (UNIONS(simplicial_link c (v:real^N)),
                                  sphere(vec 0:real^3,&1))
                                 ((d:real^N->real^3),(d':real^3->real^N))` THEN
      REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
      DISCH_THEN(MP_TAC o AP_TERM `d':real^3->real^N`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s:real = s'` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_smo_rho c v (x:real^N) = moi_smo_rho c v y` THEN
    ASM_REWRITE_TAC[REAL_EQ_MUL_RCANCEL] THEN
    ASM_MESON_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_SVX_CHART_HOMEO = prove
 (`!u c (v:real^N) (d:real^N->real^3) d'.
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\ {v} IN c /\
     homeomorphism (UNIONS(simplicial_link c v),sphere(vec 0:real^3,&1)) (d,d') /\
     smooth_immersion_into (moi_smo_link_atlas c v) d
     ==> open (IMAGE (moi_smo_vertex_chart c v d) (moi_smo_vertex_dom c v)) /\
         ?cinv. homeomorphism (moi_smo_vertex_dom c v,
                               IMAGE (moi_smo_vertex_chart c v d)
                                     (moi_smo_vertex_dom c v))
                              (moi_smo_vertex_chart c v d,cinv)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_SBA_IOD_FWD THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN
  ASM_SIMP_TAC[MOI_SVX_DOM_OPEN] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_smo_vertex_dom; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC MOI_SVX_CHART_CONT THEN
    MAP_EVERY EXISTS_TAC [`u:N->bool`; `d':real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SVX_CHART_INJ THEN EXISTS_TAC `d':real^3->real^N` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_SVX_H = prove
 (`!u c (v:real^N) (d:real^N->real^3) d' K (kappa:real^N->real^3).
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\ {v} IN c /\
     homeomorphism (UNIONS(simplicial_link c v),sphere(vec 0:real^3,&1)) (d,d') /\
     smooth_immersion_into (moi_smo_link_atlas c v) d /\
     (K,kappa) IN moi_smo_star_atlas c v /\ K SUBSET moi_smo_open_star c {v} /\
     ~(v IN K) /\
     (!y. y IN K ==> norm(kappa y) = moi_smo_rho c v y) /\
     (!y. y IN K ==> v + inv(&2) % (moi_smo_ray c v y - v) IN K)
     ==> ?H. smooth_map_on (IMAGE (moi_smo_vertex_chart c v d)
                                  (moi_smo_vertex_dom c v INTER K)) H /\
             !x. x IN moi_smo_vertex_dom c v INTER K
                 ==> H(moi_smo_vertex_chart c v d x) = kappa x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `d:real^N->real^3`; `d':real^3->real^N`] MOI_SVX_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `cinv:real^3->real^N`)) THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `d:real^N->real^3`; `d':real^3->real^N`; `K:real^N->bool`;
                 `kappa:real^N->real^3`] MOI_SVX_G0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `K:real^N->bool`; `kappa:real^N->real^3`] MOI_SLK_STAR_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SLK_HMAP) THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_smo_vertex_dom c (v:real^N) SUBSET UNIONS c` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SVX_DOM_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!Z. open_in (subtopology euclidean (moi_smo_vertex_dom c v)) Z
        ==> open (IMAGE (moi_smo_vertex_chart c v (d:real^N->real^3)) Z)`
  (LABEL_TAC "openimg") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (moi_smo_vertex_chart c v (d:real^N->real^3))
                      (moi_smo_vertex_dom c v)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`cinv:real^3->real^N`; `moi_smo_vertex_dom c (v:real^N)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (moi_smo_vertex_dom c v))
            (moi_smo_vertex_dom c (v:real^N) INTER K)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  EXISTS_TAC `\z:real^3. (kappa:real^N->real^3)((cinv:real^3->real^N) z)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    BETA_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `homeomorphism (moi_smo_vertex_dom c v,
                                IMAGE (moi_smo_vertex_chart c v (d:real^N->real^3))
                                      (moi_smo_vertex_dom c v))
                               (moi_smo_vertex_chart c v d,cinv)` THEN
    REWRITE_TAC[homeomorphism] THEN ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC MOI_SLK_SMOOTH_LOCAL THEN CONJ_TAC THENL
   [USE_THEN "openimg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x0:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `d:real^N->real^3`; `d':real^3->real^N`; `K:real^N->bool`;
                 `kappa:real^N->real^3`; `x0:real^N`] MOI_SVX_LOCAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->real^3` (X_CHOOSE_THEN `G:real^2->real^3`
    (X_CHOOSE_THEN `P:real^2->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `linear (R:real^3->real^3)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ORTHOGONAL_TRANSFORMATION]; ALL_TAC] THEN
  ABBREV_TAC `S = IMAGE (kappa:real^N->real^3) (moi_smo_vertex_dom c v INTER K) INTER
                  {y | &0 < ((R:real^3->real^3) y)$3}` THEN
  SUBGOAL_THEN `open (S:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC OPEN_INTER THEN
    ASM_SIMP_TAC[MOI_SVX_OPEN_RHALF];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN S
        ==> ?x. x IN moi_smo_vertex_dom c v INTER K /\ y = (kappa:real^N->real^3) x /\
                &0 < ((R:real^3->real^3) y)$3`
  ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_INTER; IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN S ==> &0 < ((R:real^3->real^3) y)$3 /\ moi_smo_gnom(R y) IN P`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(kappa:real^N->real^3) x0 IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE; IN_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`R:real^3->real^3`; `G:real^2->real^3`; `P:real^2->bool`;
                 `S:real^3->bool`] MOI_SVX_CONE_PARTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`R:real^3->real^3`; `G:real^2->real^3`; `P:real^2->bool`;
                 `(kappa:real^N->real^3) x0`] MOI_SVX_CONE_DET) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`\y:real^3. norm y % (G:real^2->real^3)(moi_smo_gnom(R y))`;
                 `S:real^3->bool`; `(kappa:real^N->real^3) x0`]
    SMOOTH_INVERSE_FUNCTION_THEOREM) THEN
  ASM_REWRITE_TAC[diffeomorphism_on] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (X_CHOOSE_THEN `w:real^3->bool`
    (X_CHOOSE_THEN `Finv:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `IMAGE (moi_smo_vertex_chart c v (d:real^N->real^3))
                    {x | x IN moi_smo_vertex_dom c v INTER K /\
                         (kappa:real^N->real^3) x IN t}` THEN
  SUBGOAL_THEN
   `!x. x IN moi_smo_vertex_dom c v INTER K /\ (kappa:real^N->real^3) x IN t
        ==> moi_smo_vertex_chart c v (d:real^N->real^3) x =
            norm(kappa x) % (G:real^2->real^3)(moi_smo_gnom((R:real^3->real^3)(kappa x)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o
      check (fun th -> can (term_match [] `!x:real^N. x IN K /\ P x ==> Q x`)
                           (concl th))) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(kappa:real^N->real^3) x IN S` MP_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "openimg" MATCH_MP_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS THEN
    EXISTS_TAC `moi_smo_vertex_dom c (v:real^N) INTER K` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN EXISTS_TAC `Finv:real^3->real^3` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "openimg" MATCH_MP_TAC THEN MATCH_MP_TAC OPEN_IN_TRANS THEN
    EXISTS_TAC `moi_smo_vertex_dom c (v:real^N) INTER K` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; INTER_SUBSET];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(cinv:real^3->real^N)(moi_smo_vertex_chart c v d x) = x`
    SUBST1_TAC THENL
     [UNDISCH_TAC `homeomorphism (moi_smo_vertex_dom c v,
                                  IMAGE (moi_smo_vertex_chart c v (d:real^N->real^3))
                                        (moi_smo_vertex_dom c v))
                                 (moi_smo_vertex_chart c v d,cinv)` THEN
      REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN EXISTS_TAC `w:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `IMAGE (\y:real^3. norm y % (G:real^2->real^3)
                                      (moi_smo_gnom((R:real^3->real^3) y))) t = w` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(kappa:real^N->real^3) x` THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Smooth compatibility of the vertex chart with every chart of the three    *)
(* families (tetrahedra, unfoldings, edges), routed through the edge star    *)
(* charts at v given by C4, and the theorem C4 ==> C9.                       *)
(* ========================================================================= *)

let MOI_SVX_DOM_SUBSET = prove
 (`!c (v:real^N).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c
     ==> moi_smo_vertex_dom c v SUBSET moi_smo_open_star c {v} /\
         moi_smo_vertex_dom c v SUBSET UNIONS c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_smo_vertex_dom; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SVX_DOM_OPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY]]);;

let MOI_SVX_OPENIMG = prove
 (`!u c (v:real^N) (d:real^N->real^3) d'.
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\ {v} IN c /\
     homeomorphism (UNIONS(simplicial_link c v),sphere(vec 0:real^3,&1)) (d,d') /\
     smooth_immersion_into (moi_smo_link_atlas c v) d
     ==> !Z. open_in (subtopology euclidean (UNIONS c)) Z /\
             Z SUBSET moi_smo_vertex_dom c v
             ==> open (IMAGE (moi_smo_vertex_chart c v d) Z)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `Z:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `d:real^N->real^3`; `d':real^3->real^N`] MOI_SVX_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `cinv:real^3->real^N`)) THEN
  MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
  EXISTS_TAC `IMAGE (moi_smo_vertex_chart c v (d:real^N->real^3))
                    (moi_smo_vertex_dom c v)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
  MAP_EVERY EXISTS_TAC [`cinv:real^3->real^N`; `moi_smo_vertex_dom c (v:real^N)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
  EXISTS_TAC `UNIONS c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MOI_SVX_DOM_SUBSET]);;

let MOI_SVX_FAM_CHART_OK = prove
 (`!u c (U:real^N->bool) (phi:real^N->real^3).
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas c
     ==> open_in (subtopology euclidean (UNIONS c)) U /\ open (IMAGE phi U) /\
         homeomorphic_map (subtopology euclidean U,
                           subtopology euclidean (IMAGE phi U)) phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((U:real^N->bool),(phi:real^N->real^3)) IN
      moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c \/
    (U,phi) IN moi_smo_edge_atlas c`
  MP_TAC THENL
   [UNDISCH_TAC `((U:real^N->bool),(phi:real^N->real^3)) IN
                 moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                 moi_smo_edge_atlas c` THEN
    REWRITE_TAC[IN_UNION] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_SBA_ATLAS) THEN
    ASM_REWRITE_TAC[smooth_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `phi:real^N->real^3`] o
               CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `(U:real^N->bool) SUBSET
      UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}`
    ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS THEN
      EXISTS_TAC `UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}:real^N->bool` THEN
      ASM_SIMP_TAC[MOI_SLK_X1_OPEN];
      FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC
       `homeomorphic_map
         (subtopology (subtopology euclidean
            (UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1})) U,
          subtopology euclidean (IMAGE (phi:real^N->real^3) U)) phi` THEN
      REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
      SUBGOAL_THEN
       `(UNIONS c DIFF UNIONS {e | e IN c /\ aff_dim e <= &1}) INTER U =
        (U:real^N->bool)`
      SUBST1_TAC THENL [ASM SET_TAC[]; REWRITE_TAC[]]];
    FIRST_X_ASSUM(MP_TAC o SPEC `c:(real^N->bool)->bool` o
                  GEN_REWRITE_RULE I [MOI_SMO_EDGE_STATEMENT]) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]);;

let MOI_SVX_V_NOT_IN_FAM = prove
 (`!c (v:real^N) U (phi:real^N->real^3).
     FINITE c /\ combinatorial_manifold 3 c /\ {v} IN c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas c
     ==> ~(v IN U)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN
   `((U:real^N->bool),(phi:real^N->real^3)) IN
      moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c \/
    (U,phi) IN moi_smo_edge_atlas c`
  MP_TAC THENL
   [UNDISCH_TAC `((U:real^N->bool),(phi:real^N->real^3)) IN
                 moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                 moi_smo_edge_atlas c` THEN
    REWRITE_TAC[IN_UNION] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_SBA_ATLAS) THEN
    ASM_REWRITE_TAC[smooth_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPECL [`U:real^N->bool`; `phi:real^N->real^3`] o
               CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET o
                                      CONJUNCT1) THEN
    MATCH_MP_TAC(SET_RULE `(v:real^N) IN B ==> U SUBSET A DIFF B ==> ~(v IN U)`) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `{v:real^N}` THEN
    ASM_REWRITE_TAC[AFF_DIM_SING; IN_SING] THEN INT_ARITH_TAC;
    UNDISCH_TAC `((U:real^N->bool),(phi:real^N->real^3)) IN moi_smo_edge_atlas c` THEN
    REWRITE_TAC[moi_smo_edge_atlas; IN_ELIM_THM; PAIR_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (X_CHOOSE_THEN `k:real^N->real^3`
      (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))
        (CONJUNCTS_THEN2 SUBST1_TAC (K ALL_TAC))))) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
      MOI_SVX_V_NOT_IN_STAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC]);;

let MOI_SVX_C4_TRANS = prove
 (`!u c (K:real^N->bool) (kappa:real^N->real^3) U (phi:real^N->real^3).
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\
     (K,kappa) IN moi_smo_edge_atlas c /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas c
     ==> (?g. smooth_map_on (IMAGE kappa (K INTER U)) g /\
              !x. x IN K INTER U ==> g(kappa x) = phi x) /\
         (?g. smooth_map_on (IMAGE phi (K INTER U)) g /\
              !x. x IN K INTER U ==> g(phi x) = kappa x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `c:(real^N->bool)->bool` o
                GEN_REWRITE_RULE I [MOI_SMO_EDGE_STATEMENT]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_SVX_TRANS_A = prove
 (`!u c (v:real^N) (d:real^N->real^3) d' U (phi:real^N->real^3).
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\ {v} IN c /\
     homeomorphism (UNIONS(simplicial_link c v),sphere(vec 0:real^3,&1)) (d,d') /\
     smooth_immersion_into (moi_smo_link_atlas c v) d /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas c
     ==> ?g. smooth_map_on (IMAGE (moi_smo_vertex_chart c v d)
                                  (moi_smo_vertex_dom c v INTER U)) g /\
             !x. x IN moi_smo_vertex_dom c v INTER U
                 ==> g(moi_smo_vertex_chart c v d x) = phi x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `d:real^N->real^3`; `d':real^3->real^N`] MOI_SVX_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `cinv:real^3->real^N`)) THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `d:real^N->real^3`; `d':real^3->real^N`] MOI_SVX_OPENIMG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "openimg") THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `U:real^N->bool`;
                 `phi:real^N->real^3`] MOI_SVX_FAM_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SVX_DOM_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SVX_DOM_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!x. x IN moi_smo_vertex_dom c v
        ==> (cinv:real^3->real^N)(moi_smo_vertex_chart c v (d:real^N->real^3) x) = x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (moi_smo_vertex_dom c v,
                                IMAGE (moi_smo_vertex_chart c v (d:real^N->real^3))
                                      (moi_smo_vertex_dom c v))
                               (moi_smo_vertex_chart c v d,cinv)` THEN
    SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  EXISTS_TAC `\z:real^3. (phi:real^N->real^3)((cinv:real^3->real^N) z)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC MOI_SLK_SMOOTH_LOCAL THEN CONJ_TAC THENL
   [USE_THEN "openimg" MATCH_MP_TAC THEN REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x0:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x0:real^N = v)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `U:real^N->bool`;
                   `phi:real^N->real^3`] MOI_SVX_V_NOT_IN_FAM) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`; `x0:real^N`]
    MOI_SVX_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real^N->bool` (X_CHOOSE_THEN `kappa:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `d:real^N->real^3`; `d':real^3->real^N`; `K:real^N->bool`;
                 `kappa:real^N->real^3`] MOI_SVX_H) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^3->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `K:real^N->bool`;
                 `kappa:real^N->real^3`; `U:real^N->bool`; `phi:real^N->real^3`]
    MOI_SVX_C4_TRANS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g2:real^3->real^3` STRIP_ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `K:real^N->bool`; `kappa:real^N->real^3`] MOI_SLK_STAR_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (UNIONS c))
            (moi_smo_vertex_dom c v INTER U INTER K:real^N->bool)`
  ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (moi_smo_vertex_chart c v (d:real^N->real^3))
                    (moi_smo_vertex_dom c v INTER U INTER K)` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "openimg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `(g2:real^3->real^3) o (H:real^3->real^3)` THEN REPEAT CONJ_TAC THENL
   [USE_THEN "openimg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN BETA_TAC THEN
    SUBGOAL_THEN `(H:real^3->real^3)(moi_smo_vertex_chart c v d x) =
                  (kappa:real^N->real^3) x` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x:real^N. x IN A INTER B ==> (H:real^3->real^3) (f x) = k x`)
            (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    ASM_SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (kappa:real^N->real^3) (K INTER U)` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "openimg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC MOI_SLK_OPEN_IMAGE_SUB THEN
    MAP_EVERY EXISTS_TAC [`UNIONS c:real^N->bool`; `K:real^N->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC OPEN_IN_INTER THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(H:real^3->real^3)(moi_smo_vertex_chart c v d x) =
                  (kappa:real^N->real^3) x` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (term_match [] `!x:real^N. x IN A INTER B ==> (H:real^3->real^3) (f x) = k x`)
            (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER];
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (moi_smo_vertex_chart c v (d:real^N->real^3))
                      (moi_smo_vertex_dom c v INTER K)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ASM_REWRITE_TAC[]]);;

let MOI_SVX_TRANS_B = prove
 (`!u c (v:real^N) (d:real^N->real^3) d' U (phi:real^N->real^3).
     MOI_SMO_EDGE_STATEMENT (u:N->bool) /\ FINITE c /\
     combinatorial_manifold 3 c /\ {v} IN c /\
     homeomorphism (UNIONS(simplicial_link c v),sphere(vec 0:real^3,&1)) (d,d') /\
     smooth_immersion_into (moi_smo_link_atlas c v) d /\
     (U,phi) IN moi_smo_tet_atlas c UNION moi_smo_unfold_atlas c UNION
                moi_smo_edge_atlas c
     ==> ?g. smooth_map_on (IMAGE phi (moi_smo_vertex_dom c v INTER U)) g /\
             !x. x IN moi_smo_vertex_dom c v INTER U
                 ==> g(phi x) = moi_smo_vertex_chart c v d x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `U:real^N->bool`;
                 `phi:real^N->real^3`] MOI_SVX_FAM_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SLK_HMAP) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `pinv:real^3->real^N`)
    (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `!x. x IN U ==> (pinv:real^3->real^N)((phi:real^N->real^3) x) = x`
  ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (U,IMAGE (phi:real^N->real^3) U) (phi,pinv)` THEN
    SIMP_TAC[homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SVX_DOM_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_SVX_DOM_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!Z. open_in (subtopology euclidean (UNIONS c)) Z /\ Z SUBSET U
        ==> open (IMAGE (phi:real^N->real^3) Z)`
  (LABEL_TAC "openimg") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_SLK_OPEN_IMAGE_SUB THEN
    MAP_EVERY EXISTS_TAC [`UNIONS c:real^N->bool`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\y:real^3. moi_smo_vertex_chart c v (d:real^N->real^3)
                           ((pinv:real^3->real^N) y)` THEN
  CONJ_TAC THENL
   [ALL_TAC;
    X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[]] THEN
  MATCH_MP_TAC MOI_SLK_SMOOTH_LOCAL THEN CONJ_TAC THENL
   [USE_THEN "openimg" MATCH_MP_TAC THEN REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC OPEN_IN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `x0:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x0:real^N = v)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `U:real^N->bool`;
                   `phi:real^N->real^3`] MOI_SVX_V_NOT_IN_FAM) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`; `x0:real^N`]
    MOI_SVX_EDGE_CHART) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:real^N->bool` (X_CHOOSE_THEN `kappa:real^N->real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `d:real^N->real^3`; `d':real^3->real^N`; `K:real^N->bool`;
                 `kappa:real^N->real^3`] MOI_SVX_G0) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `G0:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `K:real^N->bool`;
                 `kappa:real^N->real^3`; `U:real^N->bool`; `phi:real^N->real^3`]
    MOI_SVX_C4_TRANS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g3:real^3->real^3` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `K:real^N->bool`; `kappa:real^N->real^3`] MOI_SLK_STAR_CHART_OK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (UNIONS c))
            (moi_smo_vertex_dom c v INTER U INTER K:real^N->bool)`
  ASSUME_TAC THENL
   [REPEAT(MATCH_MP_TAC OPEN_IN_INTER THEN CONJ_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (phi:real^N->real^3) (moi_smo_vertex_dom c v INTER U INTER K)` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "openimg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_EQ_OPEN THEN
  EXISTS_TAC `(G0:real^3->real^3) o (g3:real^3->real^3)` THEN REPEAT CONJ_TAC THENL
   [USE_THEN "openimg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE; IN_INTER; o_THM] THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN BETA_TAC THEN ASM_SIMP_TAC[IN_INTER];
    ALL_TAC] THEN
  MATCH_MP_TAC SMOOTH_MAP_ON_COMPOSE_OPEN THEN
  EXISTS_TAC `IMAGE (kappa:real^N->real^3) (moi_smo_vertex_dom c v INTER K)` THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "openimg" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
    STRIP_TAC THEN ASM_SIMP_TAC[IN_INTER] THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER];
    MATCH_MP_TAC SMOOTH_MAP_ON_SUBSET THEN
    EXISTS_TAC `IMAGE (phi:real^N->real^3) (K INTER U)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* MOI_SMO_VERTEX_FROM_EDGE: C4 ==> C9.                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_SMO_VERTEX_FROM_EDGE = prove
 (`!u:N->bool. MOI_SMO_EDGE_STATEMENT u ==> MOI_SMO_VERTEX_STATEMENT u`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[MOI_SMO_VERTEX_STATEMENT] THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `v:real^N`;
                       `d:real^N->real^3`; `d':real^3->real^N`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`u:N->bool`; `c:(real^N->bool)->bool`; `v:real^N`;
                 `d:real^N->real^3`; `d':real^3->real^N`] MOI_SVX_CHART_HOMEO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `cinv:real^3->real^N`)) THEN
  ASM_SIMP_TAC[MOI_SVX_V_IN_DOM; MOI_SVX_DOM_OPEN] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SLK_HMAP_OF_HOMEO THEN EXISTS_TAC `cinv:real^3->real^N` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `phi:real^N->real^3`] THEN DISCH_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_SVX_TRANS_A THEN
    MAP_EVERY EXISTS_TAC [`u:N->bool`; `d':real^3->real^N`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_SVX_TRANS_B THEN
    MAP_EVERY EXISTS_TAC [`u:N->bool`; `d':real^3->real^N`] THEN
    ASM_REWRITE_TAC[]]);;

