(* ========================================================================= *)
(* pc_moi_fnd_splitann: the splitting operation at an annulus in real^3     *)
(* (Moise, Geometric Topology in Dimensions 2 and 3, GTM 47, 33.1 Lemma 4,  *)
(* p.232).  Main theorem:                                                    *)
(*   SPLIT_ANNULUS_R3_COND :                                                 *)
(*     |- MOI_FSN_ANNULUS_NBHD ==> MOI_FND_SPLIT_ANNULUS_R3                  *)
(* MOI_FSN_ANNULUS_NBHD (the structure of the second-derived neighbourhood  *)
(* of an annulus whose rims lie on a closed surface: the trace annuli and   *)
(* the four frontier annuli) is proved in pc_moi_fnd_annnbhd               *)
(* (ANNULUS_NBHD).  Route as in pc_moi_fnd_split: a triangulated box with  *)
(* the annulus and M as subcomplexes, N its derived neighbourhood, the new  *)
(* surface m' glued from closure(M - a1 - a2) and the parallel annuli b1,  *)
(* b2, and the x-clause by closure(|x| - N) or |x| UNION N.                 *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_split.ml";;
needs "src/pc_moi_fnd_splitannstmt.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* A triangulated box around a compact polyhedron d and M, as               *)
(* MOI_FSP_SETUP of pc_moi_fnd_split (which uses the disk hypothesis only   *)
(* to get a nonempty compact polyhedron), and its instance for an annulus.  *)
(* ========================================================================= *)

let MOI_FSN_SETUP = prove
 (`!(m:(real^3->bool)->bool) d v.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_polyhedron d /\ compact d /\ ~(d = {}) /\ open v /\ d SUBSET v
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

let MOI_FSN_SETUP_BOX = prove
 (`!(m:(real^3->bool)->bool) d v.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_polyhedron d /\ compact d /\ ~(d = {}) /\ open v /\ d SUBSET v
     ==> ?a b t ld lm. moi_fsp_box m d v a b t ld lm`,
  REWRITE_TAC[moi_fsp_box] THEN MATCH_ACCEPT_TAC MOI_FSN_SETUP);;

(* The box for an annulus. *)

let MOI_FSN_ANN_BOX = prove
 (`!(m:(real^3->bool)->bool) a j1 j2 v.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ open v /\ a SUBSET v
     ==> ?p q t la lm. moi_fsp_box m a v p q t la lm`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSN_SETUP_BOX THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_S5C_ANN_POLYHEDRON];
    ASM_MESON_TAC[MOI_S5C_ANN_COMPACT];
    MP_TAC(ISPECL [`a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`] MOI_S5C_ANN_PARTS) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Facts on N = derived_nbhd t la in the box (as MOI_FSP_N_FACTS,           *)
(* without the 3-cell part), the ends predicate (the conclusion of the      *)
(* antecedent MOI_FSN_ANNULUS_NBHD in the box), and its existence.          *)
(* ========================================================================= *)

let MOI_FSN_N_FACTS = prove
 (`!(m:(real^3->bool)->bool) a v p q t la lm.
     moi_fsp_box m a v p q t la lm
     ==> FINITE la /\ FINITE (derived_nbhd_complex t la) /\
         lf_simplicial_complex (derived_nbhd_complex t la) /\
         simplicial_subcomplex (derived_nbhd_complex t la)
           (barycentric_subdivision (barycentric_subdivision t)) /\
         UNIONS (derived_nbhd_complex t la) = derived_nbhd t la /\
         combinatorial_manifold_with_boundary 3 (derived_nbhd_complex t la) /\
         complex_boundary (derived_nbhd_complex t la) = derived_frontier t la /\
         compact (derived_nbhd t la) /\
         derived_frontier t la SUBSET derived_nbhd t la /\
         a INTER derived_frontier t la = {} /\
         a SUBSET derived_nbhd t la /\
         derived_nbhd t la SUBSET v INTER interval(p,q) /\
         DISJOINT (derived_nbhd t la) (complex_boundary t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsp_box] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (la:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`]
    DERIVED_NBHD_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DISJOINT (derived_nbhd t la) (complex_boundary (t:(real^3->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `derived_nbhd t la SUBSET v INTER interval(p:real^3,q)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `derived_nbhd t la INTER complex_boundary t = {}:real^3->bool` SUBST1_TAC THENL
   [UNDISCH_TAC `DISJOINT (derived_nbhd t la) (complex_boundary (t:(real^3->bool)->bool))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNION_EMPTY] THEN
  SUBGOAL_THEN `derived_frontier t la SUBSET derived_nbhd t (la:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[derived_frontier] THEN MATCH_MP_TAC FRONTIER_OF_SUBSET_CLOSED_IN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a SUBSET derived_nbhd t (la:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(subtopology euclidean (interval[p:real^3,q])) interior_of
                (derived_nbhd t (la:(real^3->bool)->bool))` THEN
    ASM_REWRITE_TAC[INTERIOR_OF_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `derived_nbhd t la SUBSET v INTER interval(p:real^3,q)` THEN SET_TAC[];
    UNDISCH_TAC `a SUBSET (subtopology euclidean (interval[p:real^3,q])) interior_of
                   (derived_nbhd t (la:(real^3->bool)->bool))` THEN
    REWRITE_TAC[derived_frontier; frontier_of] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    UNDISCH_TAC `derived_nbhd t la SUBSET v INTER interval(p:real^3,q)` THEN SET_TAC[]]);;

(* The ends predicate: the trace annuli a1, a2 of N on M around the rims    *)
(* j1, j2, their ends k11 k12 and k21 k22 (the circles of F INTER M), the   *)
(* parallel annuli b1, b2 and the rim annuli c1, c2 of F.                   *)

let moi_fsn_ends = new_definition
 `moi_fsn_ends (m:(real^3->bool)->bool) (t:(real^3->bool)->bool)
               (la:(real^3->bool)->bool) (j1:real^3->bool) j2 a1 a2 b1 b2 c1 c2
               k11 k12 k21 k22 <=>
    derived_nbhd t la INTER UNIONS m = a1 UNION a2 /\ DISJOINT a1 a2 /\
    pl_annulus_with_ends a1 k11 k12 /\ pl_annulus_with_ends a2 k21 k22 /\
    j1 SUBSET a1 DIFF (k11 UNION k12) /\ j2 SUBSET a2 DIFF (k21 UNION k22) /\
    derived_frontier t la INTER UNIONS m = k11 UNION k12 UNION k21 UNION k22 /\
    derived_frontier t la = b1 UNION b2 UNION c1 UNION c2 /\
    pl_annulus_with_ends b1 k11 k21 /\ pl_annulus_with_ends b2 k12 k22 /\
    pl_annulus_with_ends c1 k11 k12 /\ pl_annulus_with_ends c2 k21 k22 /\
    DISJOINT b1 b2 /\ DISJOINT c1 c2 /\
    b1 INTER c1 = k11 /\ b1 INTER c2 = k21 /\
    b2 INTER c1 = k12 /\ b2 INTER c2 = k22`;;

let MOI_FSN_ENDS_EXIST = prove
 (mk_imp(MOI_FSN_ANNULUS_NBHD,
  `!(m:(real^3->bool)->bool) a j1 j2 v p q t la lm.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     moi_fsp_box m a v p q t la lm
     ==> ?a1 a2 b1 b2 c1 c2 k11 k12 k21 k22.
           moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22`),
  DISCH_THEN(LABEL_TAC "NB") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `v:real^3->bool`;
                 `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSN_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m a v p q t la (lm:(real^3->bool)->bool)`) (concl th))) THEN
  USE_THEN "NB" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                                 `lm:(real^3->bool)->bool`; `j1:real^3->bool`;
                                 `j2:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_fsn_ends] THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The two rims as subcomplexes of lm, and the trace annuli as              *)
(* their two-dimensional derived neighbourhoods in lm (POLYGON_2 for each  *)
(* rim): complexes, ends, and the complements in M.                         *)
(* ========================================================================= *)

(* The frontier of a union of two disjoint closed sets. *)

let MOI_FSN_FRONTIER_OF_UNION_SEP = prove
 (`!top (s:A->bool) t.
     closed_in top s /\ closed_in top t /\ DISJOINT s t
     ==> top frontier_of (s UNION t) = top frontier_of s UNION top frontier_of t`,
  SUBGOAL_THEN
   `!top (u:A->bool) v.
      closed_in top u /\ closed_in top v /\ DISJOINT u v
      ==> top frontier_of u SUBSET top frontier_of (u UNION v)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[frontier_of; SUBSET; IN_DIFF] THEN
    X_GEN_TAC `x:A` THEN STRIP_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN `top closure_of u SUBSET top closure_of (u UNION v:A->bool)` MP_TAC THENL
       [MATCH_MP_TAC CLOSURE_OF_MONO THEN SET_TAC[];
        UNDISCH_TAC `(x:A) IN top closure_of u` THEN SET_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN UNDISCH_TAC `~((x:A) IN top interior_of u)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:A) IN u /\ x IN topspace top` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(x:A) IN top closure_of u` THEN ASM_SIMP_TAC[CLOSURE_OF_CLOSED_IN];
        MP_TAC(ISPECL [`top:A topology`; `u:A->bool`] CLOSURE_OF_SUBSET_TOPSPACE) THEN
        UNDISCH_TAC `(x:A) IN top closure_of u` THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `top interior_of (u UNION v) INTER (topspace top DIFF v) SUBSET
                  top interior_of (u:A->bool)` MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`top:A topology`; `u UNION v:A->bool`] INTERIOR_OF_SUBSET) THEN
        SET_TAC[];
        MATCH_MP_TAC OPEN_IN_INTER THEN REWRITE_TAC[OPEN_IN_INTERIOR_OF] THEN
        MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[OPEN_IN_TOPSPACE]];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (u:A->bool) v` THEN UNDISCH_TAC `(x:A) IN u` THEN
    UNDISCH_TAC `(x:A) IN topspace top` THEN
    UNDISCH_TAC `(x:A) IN top interior_of (u UNION v)` THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[FRONTIER_OF_UNION_SUBSET; UNION_SUBSET] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[UNION_COMM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (s:A->bool) t` THEN SET_TAC[]]);;

(* The two rims as subcomplexes of lm. *)

let MOI_FSN_RIM_SPLIT = prove
 (`!(t:(real^N->bool)->bool) la lm (j1:real^N->bool) j2.
     lf_simplicial_complex t /\ simplicial_subcomplex la t /\ simplicial_subcomplex lm t /\
     UNIONS la INTER UNIONS lm = j1 UNION j2 /\ closed j1 /\ closed j2 /\ DISJOINT j1 j2
     ==> simplicial_subcomplex {s | s IN la INTER lm /\ s SUBSET j1} lm /\
         simplicial_subcomplex {s | s IN la INTER lm /\ s SUBSET j2} lm /\
         UNIONS {s | s IN la INTER lm /\ s SUBSET j1} = j1 /\
         UNIONS {s | s IN la INTER lm /\ s SUBSET j2} = j2 /\
         derived_nbhd lm (la INTER lm) =
         derived_nbhd lm {s | s IN la INTER lm /\ s SUBSET j1} UNION
         derived_nbhd lm {s | s IN la INTER lm /\ s SUBSET j2}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `la:(real^N->bool)->bool`;
                 `lm:(real^N->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN la INTER lm ==> s SUBSET j1 \/ s SUBSET j2`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `connected (s:real^N->bool) /\ s SUBSET j1 UNION j2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
         [UNDISCH_TAC `(s:real^N->bool) IN la INTER lm` THEN REWRITE_TAC[IN_INTER] THEN
          STRIP_TAC THEN
          UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
          REWRITE_TAC[lf_simplicial_complex] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
          ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
          ALL_TAC] THEN
        MATCH_MP_TAC CONVEX_CONNECTED THEN
        UNDISCH_TAC `n simplex (s:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
        MESON_TAC[CONVEX_CONVEX_HULL];
        UNDISCH_TAC `UNIONS (la INTER lm:(real^N->bool)->bool) = j1 UNION j2` THEN
        UNDISCH_TAC `(s:real^N->bool) IN la INTER lm` THEN SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `connected (s:real^N->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED] THEN
    REWRITE_TAC[NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`j1:real^N->bool`; `j2:real^N->bool`]) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (j1:real^N->bool) j2` THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET j1 UNION j2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (la INTER lm:(real^N->bool)->bool) = j1 UNION j2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS {s | s IN la INTER lm /\ s SUBSET j1} = (j1:real^N->bool) /\
                UNIONS {s | s IN la INTER lm /\ s SUBSET j2} = (j2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
    (CONJ_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    UNDISCH_TAC `UNIONS (la INTER lm:(real^N->bool)->bool) = j1 UNION j2` THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNION] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `j2:real^N->bool`)) (concl th) &&
      can (find_term ((=) `la INTER lm:(real^N->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex la (t:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `simplicial_subcomplex lm (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]]];
    UNDISCH_TAC `simplicial_subcomplex la (t:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `simplicial_subcomplex lm (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM; IN_INTER] THEN REPEAT STRIP_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]; ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]]];
    REWRITE_TAC[derived_nbhd] THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* In the box with the ends: the trace annuli are the derived neighbourhoods *)
(* in lm of the two rims, and their ends are the derived frontiers.          *)

let MOI_FSN_TRACES = prove
 (`!(m:(real^3->bool)->bool) a j1 j2 v p q t la lm a1 a2 b1 b2 c1 c2 k11 k12 k21 k22.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     moi_fsp_box m a v p q t la lm /\
     moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22
     ==> simplicial_subcomplex {s | s IN la INTER lm /\ s SUBSET j1} lm /\
         simplicial_subcomplex {s | s IN la INTER lm /\ s SUBSET j2} lm /\
         UNIONS {s | s IN la INTER lm /\ s SUBSET j1} = j1 /\
         UNIONS {s | s IN la INTER lm /\ s SUBSET j2} = j2 /\
         pl_sphere 1 j1 /\ pl_sphere 1 j2 /\
         derived_nbhd lm {s | s IN la INTER lm /\ s SUBSET j1} = a1 /\
         derived_nbhd lm {s | s IN la INTER lm /\ s SUBSET j2} = a2 /\
         derived_frontier lm {s | s IN la INTER lm /\ s SUBSET j1} = k11 UNION k12 /\
         derived_frontier lm {s | s IN la INTER lm /\ s SUBSET j2} = k21 UNION k22`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m a v p q t la (lm:(real^3->bool)->bool)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsn_ends] o check (fun th ->
    can (term_match []
      `moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 (k22:real^3->bool)`)
      (concl th))) THEN
  ABBREV_TAC `l1 = {s | s IN la INTER lm /\ s SUBSET (j1:real^3->bool)}` THEN
  ABBREV_TAC `l2 = {s | s IN la INTER lm /\ s SUBSET (j2:real^3->bool)}` THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`] MOI_S5C_ANN_PARTS) THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`] MOI_S5C_ANN_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 1 (j1:real^3->bool) /\ pl_sphere 1 (j2:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5C_ANN_END_SPHERES THEN EXISTS_TAC `a:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `convex hull {vec 0:real^3, basis 1, basis 2}` THEN
    REWRITE_TAC[MOI_S5C_SIMPLEX2_R3];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`] MOI_FSN_RIM_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM_REWRITE_TAC[DISJOINT];
    ASM_REWRITE_TAC[] THEN STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`]
    MOI_FN2_DERIVED_TRACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l1:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l2:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l1:(real^3->bool)->bool`] DERIVED_NBHD_POLYGON_2) THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l2:(real^3->bool)->bool`] DERIVED_NBHD_POLYGON_2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `~(j1:real^3->bool = {}) /\ ~(j2:real^3->bool = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSP_SPHERE1_NONEMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a1:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`] MOI_S5C_ANN_COMPACT) THEN
  MP_TAC(ISPECL [`a2:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`] MOI_S5C_ANN_COMPACT) THEN
  MP_TAC(ISPECL [`a1:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`] MOI_S5C_ANN_ENDS_SUBSET) THEN
  MP_TAC(ISPECL [`a2:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`] MOI_S5C_ANN_ENDS_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `derived_nbhd lm l1 SUBSET (a1:real^3->bool) /\
                derived_nbhd lm l2 SUBSET (a2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `connected (derived_nbhd lm (l1:(real^3->bool)->bool))`;
      UNDISCH_TAC `connected (derived_nbhd lm (l2:(real^3->bool)->bool))`] THEN
    REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`a1:real^3->bool`; `a2:real^3->bool`]) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    MAP_EVERY UNDISCH_TAC
     [`a1 UNION a2 = derived_nbhd lm l1 UNION derived_nbhd lm (l2:(real^3->bool)->bool)`;
      `DISJOINT (a1:real^3->bool) a2`; `(j1:real^3->bool) SUBSET a1 DIFF (k11 UNION k12)`;
      `(j2:real^3->bool) SUBSET a2 DIFF (k21 UNION k22)`;
      `~(j1:real^3->bool = {})`; `~(j2:real^3->bool = {})`;
      `(j1:real^3->bool) SUBSET (subtopology euclidean (UNIONS m)) interior_of
         derived_nbhd lm (l1:(real^3->bool)->bool)`;
      `(j2:real^3->bool) SUBSET (subtopology euclidean (UNIONS m)) interior_of
         derived_nbhd lm (l2:(real^3->bool)->bool)`] THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS m:real^3->bool)`;
                   `derived_nbhd lm (l1:(real^3->bool)->bool)`] INTERIOR_OF_SUBSET) THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS m:real^3->bool)`;
                   `derived_nbhd lm (l2:(real^3->bool)->bool)`] INTERIOR_OF_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `derived_nbhd lm l1 = (a1:real^3->bool) /\
                derived_nbhd lm l2 = (a2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`a1 UNION a2 = derived_nbhd lm l1 UNION derived_nbhd lm (l2:(real^3->bool)->bool)`;
      `DISJOINT (a1:real^3->bool) a2`;
      `derived_nbhd lm l1 SUBSET (a1:real^3->bool)`;
      `derived_nbhd lm l2 SUBSET (a2:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th =
    `a1 UNION a2 = derived_nbhd lm l1 UNION derived_nbhd lm (l2:(real^3->bool)->bool)`)) THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean (UNIONS m)) (a1:real^3->bool) /\
                closed_in (subtopology euclidean (UNIONS m)) (a2:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> SUBST1_TAC(SYM(ASSUME t)))
      [`derived_nbhd lm l1 = (a1:real^3->bool)`; `derived_nbhd lm l2 = (a2:real^3->bool)`] THEN
    CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `derived_frontier lm (la INTER lm) =
                derived_frontier lm l1 UNION derived_frontier lm (l2:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[derived_frontier] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FSN_FRONTIER_OF_UNION_SEP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `derived_frontier lm l1 SUBSET (a1:real^3->bool) /\
                derived_frontier lm l2 SUBSET (a2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[derived_frontier] THEN CONJ_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `derived_nbhd lm l1 = (a1:real^3->bool)`));
      SUBST1_TAC(SYM(ASSUME `derived_nbhd lm l2 = (a2:real^3->bool)`))] THEN
    MATCH_MP_TAC FRONTIER_OF_SUBSET_CLOSED_IN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `k11 UNION k12 UNION k21 UNION k22 =
                derived_frontier lm (la INTER lm:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(b1 UNION b2 UNION c1 UNION c2) INTER UNIONS m =
       derived_frontier lm (la INTER lm:(real^3->bool)->bool)`;
      `derived_frontier t la INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
      `derived_frontier t la = b1 UNION b2 UNION c1 UNION (c2:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`derived_frontier lm (la INTER lm) =
     derived_frontier lm l1 UNION derived_frontier lm (l2:(real^3->bool)->bool)`;
    `k11 UNION k12 UNION k21 UNION k22 = derived_frontier lm (la INTER lm:(real^3->bool)->bool)`;
    `derived_frontier lm l1 SUBSET (a1:real^3->bool)`;
    `derived_frontier lm l2 SUBSET (a2:real^3->bool)`;
    `DISJOINT (a1:real^3->bool) a2`;
    `(k11:real^3->bool) SUBSET a1`; `(k12:real^3->bool) SUBSET a1`;
    `(k21:real^3->bool) SUBSET a2`; `(k22:real^3->bool) SUBSET a2`] THEN
  SET_TAC[]);;

(* ========================================================================= *)
(* Surface complexes for the new surface m'.  The complement in M           *)
(* of the two trace annuli is a surface with boundary the four ends (the    *)
(* charts of pc_moi_s28_trib/s28_cut, locally as the complement of one      *)
(* trace, which POLYGON_2 handles); annulus complexes from a reference one; *)
(* disjoint unions of surfaces.                                             *)
(* ========================================================================= *)

(* The complement of two disjoint closed sets a1, a2 in a closed surface K, *)
(* given that the complement of each one is a surface with boundary e_i     *)
(* inside a_i.                                                               *)

let MOI_FSN_COMPL2 = prove
 (`!(K:(real^N->bool)->bool) A (a1:real^N->bool) a2 e1 e2.
     FINITE K /\ combinatorial_manifold 2 K /\
     simplicial_subcomplex A K /\ UNIONS A = a1 UNION a2 /\
     closed a1 /\ closed a2 /\ DISJOINT a1 a2 /\
     combinatorial_manifold_with_boundary 2 {s | s IN K /\ s SUBSET closure (UNIONS K DIFF a1)} /\
     UNIONS {s | s IN K /\ s SUBSET closure (UNIONS K DIFF a1)} = closure (UNIONS K DIFF a1) /\
     surface_boundary {s | s IN K /\ s SUBSET closure (UNIONS K DIFF a1)} = e1 /\
     combinatorial_manifold_with_boundary 2 {s | s IN K /\ s SUBSET closure (UNIONS K DIFF a2)} /\
     UNIONS {s | s IN K /\ s SUBSET closure (UNIONS K DIFF a2)} = closure (UNIONS K DIFF a2) /\
     surface_boundary {s | s IN K /\ s SUBSET closure (UNIONS K DIFF a2)} = e2 /\
     e1 SUBSET a1 /\ e2 SUBSET a2
     ==> FINITE {s | s IN K /\ s SUBSET closure (UNIONS K DIFF (a1 UNION a2))} /\
         combinatorial_manifold_with_boundary 2
           {s | s IN K /\ s SUBSET closure (UNIONS K DIFF (a1 UNION a2))} /\
         UNIONS {s | s IN K /\ s SUBSET closure (UNIONS K DIFF (a1 UNION a2))} =
         closure (UNIONS K DIFF (a1 UNION a2)) /\
         surface_boundary {s | s IN K /\ s SUBSET closure (UNIONS K DIFF (a1 UNION a2))} =
         e1 UNION e2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `A:(real^N->bool)->bool`] MOI_FSP_COMP_UNIONS2) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `A:(real^N->bool)->bool`] MOI_FSP_COMP_SUBCX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `X = UNIONS (K:(real^N->bool)->bool)` THEN
  ABBREV_TAC `C = {s | s IN K /\ s SUBSET closure (X DIFF (a1 UNION a2:real^N->bool))}` THEN
  ABBREV_TAC `C1 = {s | s IN K /\ s SUBSET closure (X DIFF (a1:real^N->bool))}` THEN
  ABBREV_TAC `C2 = {s | s IN K /\ s SUBSET closure (X DIFF (a2:real^N->bool))}` THEN
  SUBGOAL_THEN `closed (X:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (C:(real^N->bool)->bool) /\ FINITE (C1:(real^N->bool)->bool) /\
                FINITE (C2:(real^N->bool)->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["C"; "C1"; "C2"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (C:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* point-set facts *)
  SUBGOAL_THEN
   `closure (X DIFF (a1 UNION a2)) SUBSET closure (X DIFF a1:real^N->bool) /\
    closure (X DIFF (a1 UNION a2)) SUBSET closure (X DIFF a2:real^N->bool) /\
    closure (X DIFF (a1 UNION a2)) SUBSET (X:real^N->bool) /\
    closure (X DIFF a1) DIFF a2 SUBSET closure (X DIFF (a1 UNION a2:real^N->bool)) /\
    closure (X DIFF a2) DIFF a1 SUBSET closure (X DIFF (a1 UNION a2:real^N->bool)) /\
    X DIFF (a1 UNION a2) SUBSET closure (X DIFF (a1 UNION a2:real^N->bool))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[];
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `((:real^N) DIFF a2) INTER (X DIFF a1) = X DIFF (a1 UNION a2:real^N->bool)`
      (SUBST1_TAC o SYM) THENL [SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`(:real^N) DIFF a2`; `X DIFF (a1:real^N->bool)`]
        OPEN_INTER_CLOSURE_SUBSET) THEN
      REWRITE_TAC[GSYM closed] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `((:real^N) DIFF a1) INTER (X DIFF a2) = X DIFF (a1 UNION a2:real^N->bool)`
      (SUBST1_TAC o SYM) THENL [SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`(:real^N) DIFF a1`; `X DIFF (a2:real^N->bool)`]
        OPEN_INTER_CLOSURE_SUBSET) THEN
      REWRITE_TAC[GSYM closed] THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[CLOSURE_SUBSET]];
    ALL_TAC] THEN
  (* the charts of K, C1, C2 *)
  MP_TAC(ISPEC `K:(real^N->bool)->bool` SURF_CHARTS) THEN
  ASM_SIMP_TAC[MOI_S8TA_CM_CMB] THEN
  DISCH_THEN(fun th -> ASSUME_TAC(CONJUNCT1 th) THEN ASSUME_TAC(CONJUNCT2(CONJUNCT2 th))) THEN
  SUBGOAL_THEN `!y:real^N. y IN X ==> moi_s28_locally_r2 X y` (LABEL_TAC "RK") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `moi_s28_locally_r2:(real^N->bool)->real^N->bool`)) (concl th) &&
      can (find_term ((=) `surface_boundary (K:(real^N->bool)->bool)`)) (concl th))) THEN
    ASM_REWRITE_TAC[DIFF_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPEC `C1:(real^N->bool)->bool` SURF_CHARTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "R1") (CONJUNCTS_THEN2 (LABEL_TAC "H1") (K ALL_TAC))) THEN
  MP_TAC(ISPEC `C2:(real^N->bool)->bool` SURF_CHARTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "R2") (CONJUNCTS_THEN2 (LABEL_TAC "H2") (K ALL_TAC))) THEN
  (* local identity of C with C1 near a1 and with C2 near a2 *)
  SUBGOAL_THEN
   `open_in (subtopology euclidean (closure (X DIFF a1)))
            (closure (X DIFF a1) DIFF (a2:real^N->bool)) /\
    open_in (subtopology euclidean (closure (X DIFF a2)))
            (closure (X DIFF a2) DIFF (a1:real^N->bool)) /\
    open_in (subtopology euclidean (closure (X DIFF (a1 UNION a2))))
            (closure (X DIFF (a1 UNION a2)) DIFF (a2:real^N->bool)) /\
    open_in (subtopology euclidean (closure (X DIFF (a1 UNION a2))))
            (closure (X DIFF (a1 UNION a2)) DIFF (a1:real^N->bool)) /\
    open_in (subtopology euclidean X) (X DIFF (a1 UNION a2:real^N->bool))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_DIFF_CLOSED THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN; SUBSET_UNIV; GSYM CLOSED_IN] THEN
    ASM_SIMP_TAC[CLOSED_UNION];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closure (X DIFF a1) DIFF a2 = closure (X DIFF (a1 UNION a2)) DIFF (a2:real^N->bool) /\
    closure (X DIFF a2) DIFF a1 = closure (X DIFF (a1 UNION a2)) DIFF (a1:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM SET_TAC[]; ALL_TAC] THEN
  (* each point of C is locally a plane or a half-plane *)
  SUBGOAL_THEN
   `!y:real^N. y IN closure (X DIFF (a1 UNION a2))
               ==> (moi_s28_locally_r2 (closure (X DIFF (a1 UNION a2))) y <=>
                    (if y IN a1 then moi_s28_locally_r2 (closure (X DIFF a1)) y
                     else if y IN a2 then moi_s28_locally_r2 (closure (X DIFF a2)) y
                     else T)) /\
                   (y IN a1 /\ moi_s28_locally_half (closure (X DIFF a1)) y
                    ==> moi_s28_locally_half (closure (X DIFF (a1 UNION a2))) y) /\
                   (y IN a2 /\ moi_s28_locally_half (closure (X DIFF a2)) y
                    ==> moi_s28_locally_half (closure (X DIFF (a1 UNION a2))) y)`
  (LABEL_TAC "LOC") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ALL_TAC;
      STRIP_TAC THEN MATCH_MP_TAC MOI_S8CU_HALF_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`closure (X DIFF (a1:real^N->bool))`;
                            `closure (X DIFF a1) DIFF (a2:real^N->bool)`] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (a1:real^N->bool) a2` THEN
      UNDISCH_TAC `(y:real^N) IN closure (X DIFF (a1 UNION a2))` THEN
      UNDISCH_TAC `(y:real^N) IN a1` THEN ASM SET_TAC[];
      STRIP_TAC THEN MATCH_MP_TAC MOI_S8CU_HALF_RESTRICT THEN
      MAP_EVERY EXISTS_TAC [`closure (X DIFF (a2:real^N->bool))`;
                            `closure (X DIFF a2) DIFF (a1:real^N->bool)`] THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (a1:real^N->bool) a2` THEN
      UNDISCH_TAC `(y:real^N) IN closure (X DIFF (a1 UNION a2))` THEN
      UNDISCH_TAC `(y:real^N) IN a2` THEN ASM SET_TAC[]] THEN
    COND_CASES_TAC THENL
     [EQ_TAC THEN DISCH_TAC THENL
       [MATCH_MP_TAC MOI_S8CU_R2_SUPER THEN
        EXISTS_TAC `closure (X DIFF (a1 UNION a2)) DIFF (a2:real^N->bool)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
          MAP_EVERY EXISTS_TAC [`closure (X DIFF (a1 UNION a2:real^N->bool))`;
                                `closure (X DIFF (a1 UNION a2)) DIFF (a2:real^N->bool)`] THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (a1:real^N->bool) a2` THEN
          UNDISCH_TAC `(y:real^N) IN closure (X DIFF (a1 UNION a2))` THEN
          UNDISCH_TAC `(y:real^N) IN a1` THEN SET_TAC[];
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
            lhs(concl th) = `closure (X DIFF a1) DIFF (a2:real^N->bool)`)) THEN
          ASM_REWRITE_TAC[]];
        MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
        MAP_EVERY EXISTS_TAC [`closure (X DIFF (a1:real^N->bool))`;
                              `closure (X DIFF a1) DIFF (a2:real^N->bool)`] THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (a1:real^N->bool) a2` THEN
        UNDISCH_TAC `(y:real^N) IN closure (X DIFF (a1 UNION a2))` THEN
        UNDISCH_TAC `(y:real^N) IN a1` THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    COND_CASES_TAC THENL
     [EQ_TAC THEN DISCH_TAC THENL
       [MATCH_MP_TAC MOI_S8CU_R2_SUPER THEN
        EXISTS_TAC `closure (X DIFF (a1 UNION a2)) DIFF (a1:real^N->bool)` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
          MAP_EVERY EXISTS_TAC [`closure (X DIFF (a1 UNION a2:real^N->bool))`;
                                `closure (X DIFF (a1 UNION a2)) DIFF (a1:real^N->bool)`] THEN
          ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (a1:real^N->bool) a2` THEN
          UNDISCH_TAC `(y:real^N) IN closure (X DIFF (a1 UNION a2))` THEN
          UNDISCH_TAC `(y:real^N) IN a2` THEN SET_TAC[];
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
            lhs(concl th) = `closure (X DIFF a2) DIFF (a1:real^N->bool)`)) THEN
          ASM_REWRITE_TAC[]];
        MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
        MAP_EVERY EXISTS_TAC [`closure (X DIFF (a2:real^N->bool))`;
                              `closure (X DIFF a2) DIFF (a1:real^N->bool)`] THEN
        ASM_REWRITE_TAC[] THEN UNDISCH_TAC `DISJOINT (a1:real^N->bool) a2` THEN
        UNDISCH_TAC `(y:real^N) IN closure (X DIFF (a1 UNION a2))` THEN
        UNDISCH_TAC `(y:real^N) IN a2` THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8CU_R2_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `X DIFF (a1 UNION a2:real^N->bool)`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(USE_THEN "RK" MATCH_MP_TAC) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  (* SURF_LOCAL *)
  MP_TAC(ISPEC `C:(real^N->bool)->bool` SURF_LOCAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "LOC" (MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^N) IN a1` THEN ASM_REWRITE_TAC[] THENL
     [ASM_CASES_TAC `(y:real^N) IN e1` THENL
       [USE_THEN "H1" (MP_TAC o C MP (ASSUME `(y:real^N) IN e1`) o SPEC `y:real^N`) THEN
        MESON_TAC[];
        USE_THEN "R1" (MP_TAC o SPEC `y:real^N`) THEN
        ANTS_TAC THENL
         [REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(y:real^N) IN closure (X DIFF (a1 UNION a2))` THEN
          UNDISCH_TAC `closure (X DIFF (a1 UNION a2)) SUBSET closure (X DIFF a1:real^N->bool)` THEN
          SET_TAC[];
          MESON_TAC[]]];
      ASM_CASES_TAC `(y:real^N) IN a2` THEN ASM_REWRITE_TAC[] THENL
       [ASM_CASES_TAC `(y:real^N) IN e2` THENL
         [USE_THEN "H2" (MP_TAC o C MP (ASSUME `(y:real^N) IN e2`) o SPEC `y:real^N`) THEN
          MESON_TAC[];
          USE_THEN "R2" (MP_TAC o SPEC `y:real^N`) THEN
          ANTS_TAC THENL
           [REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
            UNDISCH_TAC `(y:real^N) IN closure (X DIFF (a1 UNION a2))` THEN
            UNDISCH_TAC `closure (X DIFF (a1 UNION a2)) SUBSET closure (X DIFF a2:real^N->bool)` THEN
            SET_TAC[];
            MESON_TAC[]]];
        MESON_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN X_GEN_TAC `y:real^N` THEN
  ASM_CASES_TAC `(y:real^N) IN closure (X DIFF (a1 UNION a2))` THEN ASM_REWRITE_TAC[] THENL
   [USE_THEN "LOC" (MP_TAC o CONJUNCT1 o C MP
      (ASSUME `(y:real^N) IN closure (X DIFF (a1 UNION a2))`) o SPEC `y:real^N`) THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN a1` THEN ASM_REWRITE_TAC[] THENL
     [SUBGOAL_THEN `~((y:real^N) IN e2)` ASSUME_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(y:real^N) IN a1`; `(e2:real^N->bool) SUBSET a2`;
                               `DISJOINT (a1:real^N->bool) a2`] THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EQ_TAC THENL
       [DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        UNDISCH_TAC `~moi_s28_locally_r2 (closure (X DIFF (a1:real^N->bool))) y` THEN
        REWRITE_TAC[] THEN USE_THEN "R1" MATCH_MP_TAC THEN
        REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`(y:real^N) IN closure (X DIFF (a1 UNION a2))`;
          `closure (X DIFF (a1 UNION a2)) SUBSET closure (X DIFF a1:real^N->bool)`] THEN
        SET_TAC[];
        DISCH_TAC THEN
        USE_THEN "H1" (MP_TAC o C MP (ASSUME `(y:real^N) IN e1`) o SPEC `y:real^N`) THEN
        SIMP_TAC[]];
      ASM_CASES_TAC `(y:real^N) IN a2` THEN ASM_REWRITE_TAC[] THENL
       [SUBGOAL_THEN `~((y:real^N) IN e1)` ASSUME_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`(y:real^N) IN a2`; `(e1:real^N->bool) SUBSET a1`;
                                 `DISJOINT (a1:real^N->bool) a2`] THEN SET_TAC[];
          ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN EQ_TAC THENL
         [DISCH_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
          UNDISCH_TAC `~moi_s28_locally_r2 (closure (X DIFF (a2:real^N->bool))) y` THEN
          REWRITE_TAC[] THEN USE_THEN "R2" MATCH_MP_TAC THEN
          REWRITE_TAC[IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
          MAP_EVERY UNDISCH_TAC
           [`(y:real^N) IN closure (X DIFF (a1 UNION a2))`;
            `closure (X DIFF (a1 UNION a2)) SUBSET closure (X DIFF a2:real^N->bool)`] THEN
          SET_TAC[];
          DISCH_TAC THEN
          USE_THEN "H2" (MP_TAC o C MP (ASSUME `(y:real^N) IN e2`) o SPEC `y:real^N`) THEN
          SIMP_TAC[]];
        MAP_EVERY UNDISCH_TAC [`~((y:real^N) IN a1)`; `~((y:real^N) IN a2)`;
                               `(e1:real^N->bool) SUBSET a1`; `(e2:real^N->bool) SUBSET a2`] THEN
        SET_TAC[]]];
    SUBGOAL_THEN `~((y:real^N) IN e1) /\ ~((y:real^N) IN e2)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `~((y:real^N) IN closure (X DIFF (a1 UNION a2)))` THEN REWRITE_TAC[] THENL
       [USE_THEN "H1" (MP_TAC o C MP (ASSUME `(y:real^N) IN e1`) o SPEC `y:real^N`);
        USE_THEN "H2" (MP_TAC o C MP (ASSUME `(y:real^N) IN e2`) o SPEC `y:real^N`)] THEN
      REWRITE_TAC[moi_s28_locally_half] THEN
      DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (K ALL_TAC)) THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^2`
        (X_CHOOSE_THEN `k:real^2->real^N` STRIP_ASSUME_TAC))) THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET o check (fun th ->
        can (term_match [] `open_in (subtopology euclidean x) (u:real^N->bool)`) (concl th) &&
        rand(concl th) = `u:real^N->bool`)) THEN
      FIRST_ASSUM(MP_TAC o check (fun th -> concl th = `(y:real^N) IN e1` ||
                                            concl th = `(y:real^N) IN e2`)) THEN
      MAP_EVERY UNDISCH_TAC
       [`(y:real^N) IN u`; `(e1:real^N->bool) SUBSET a1`; `(e2:real^N->bool) SUBSET a2`;
        `DISJOINT (a1:real^N->bool) a2`;
        `closure (X DIFF a1) DIFF a2 SUBSET closure (X DIFF (a1 UNION a2:real^N->bool))`;
        `closure (X DIFF a2) DIFF a1 SUBSET closure (X DIFF (a1 UNION a2:real^N->bool))`] THEN
      SET_TAC[];
      ASM_REWRITE_TAC[]]]);;

(* Triangulations of an annulus are surfaces with the ends as boundary and  *)
(* Euler characteristic 0, given one reference triangulation of an annulus *)
(* (surface invariance under the homeomorphism of the charts).              *)

let MOI_FSN_ANN_COMPLEX_REF = prove
 (`!(A:(real^N->bool)->bool) p0 p1 (D:(real^N->bool)->bool) e0 e1.
     FINITE A /\ combinatorial_manifold_with_boundary 2 A /\
     pl_annulus_with_ends (UNIONS A) p0 p1 /\ surface_boundary A = p0 UNION p1 /\
     FINITE D /\ simplicial_complex D /\ pl_annulus_with_ends (UNIONS D) e0 e1
     ==> combinatorial_manifold_with_boundary 2 D /\ surface_boundary D = e0 UNION e1 /\
         complex_euler D = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1]) /\
    relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]) SUBSET
    interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&1;&1],vector[&1;&1])`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_S5C_IN_SQANN] THEN
    SIMP_TAC[MOI_S5C_SQ_RF; REAL_ARITH `&0 < &1`; REAL_ARITH `&0 < &2`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_annulus (UNIONS (D:(real^N->bool)->bool))` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_annulus_with_ends (UNIONS (D:(real^N->bool)->bool)) e0 e1` THEN
    REWRITE_TAC[pl_annulus_with_ends; pl_annulus] THEN MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_annulus_with_ends (UNIONS (A:(real^N->bool)->bool)) p0 p1` THEN
  UNDISCH_TAC `pl_annulus_with_ends (UNIONS (D:(real^N->bool)->bool)) e0 e1` THEN
  REWRITE_TAC[pl_annulus_with_ends; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^2->real^N` (X_CHOOSE_THEN `g2:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^2->real^N` (X_CHOOSE_THEN `g1:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`A:(real^N->bool)->bool`; `D:(real^N->bool)->bool`;
                 `(f2:real^2->real^N) o (g1:real^N->real^2)`;
                 `(f1:real^2->real^N) o (g2:real^N->real^2)`] MOI_FRB_SURF_INVARIANT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                interval(--vector[&1;&1],vector[&1;&1])` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `surface_boundary (D:(real^N->bool)->bool)`)) THEN
    ASM_REWRITE_TAC[IMAGE_UNION; IMAGE_o] THEN
    FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[homeomorphism] o check (fun th ->
      can (term_match [] `homeomorphism (s,UNIONS (A:(real^N->bool)->bool))
                                        (f:real^2->real^N,g)`) (concl th))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `IMAGE (g1:real^N->real^2)
        (IMAGE f1 (relative_frontier (interval[--vector[&1;&1],vector[&1;&1]]))) =
      relative_frontier (interval[--vector[&1;&1],vector[&1;&1]]) /\
      IMAGE (g1:real^N->real^2)
        (IMAGE f1 (relative_frontier (interval[--vector[&2;&2],vector[&2;&2]]))) =
      relative_frontier (interval[--vector[&2;&2],vector[&2;&2]])`
    (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM IMAGE_o] THEN CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `(!x:real^2. x IN s ==> f x = x) ==> IMAGE f s = s`) THEN
    REWRITE_TAC[o_THM] THEN ASM SET_TAC[];
    MP_TAC(ISPEC `D:(real^N->bool)->bool` COMPLEX_EULER_VALUES) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_FSB_DIM]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o el 4 o CONJUNCTS) THEN ASM_REWRITE_TAC[]]);;

(* The union of two surfaces with disjoint polyhedra. *)

let MOI_FSN_DISJ_UNION_CMWB2 = prove
 (`!(c:(real^N->bool)->bool) d.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\
     FINITE d /\ combinatorial_manifold_with_boundary 2 d /\
     DISJOINT (UNIONS c) (UNIONS d)
     ==> FINITE (c UNION d) /\ simplicial_complex (c UNION d) /\
         combinatorial_manifold_with_boundary 2 (c UNION d) /\
         UNIONS (c UNION d) = UNIONS c UNION UNIONS d /\
         surface_boundary (c UNION d) = surface_boundary c UNION surface_boundary d /\
         complex_euler (c UNION d) = complex_euler c + complex_euler d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_S8TA_CMB_FACTS) THEN
  MP_TAC(ISPEC `d:(real^N->bool)->bool` MOI_S8TA_CMB_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s t:real^N->bool. s IN c /\ t IN d ==> s INTER t = {}` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (UNIONS c) (UNIONS (d:(real^N->bool)->bool))` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (c UNION d:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `lf_simplicial_complex (d:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex; IN_UNION] THEN
    STRIP_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THENL
       [ASM_MESON_TAC[];
        SUBGOAL_THEN `(s:real^N->bool) INTER s' = {}` SUBST1_TAC THENL
         [ASM_MESON_TAC[]; REWRITE_TAC[EMPTY_FACE_OF]];
        SUBGOAL_THEN `(s:real^N->bool) INTER s' = {}` SUBST1_TAC THENL
         [ASM_MESON_TAC[INTER_COMM]; REWRITE_TAC[EMPTY_FACE_OF]];
        ASM_MESON_TAC[]];
      REPEAT STRIP_TAC THEN EXISTS_TAC `(:real^N)` THEN
      REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c UNION d:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[FINITE_UNION] THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[FINITE_UNION; UNIONS_UNION] THEN
  SUBGOAL_THEN `simplicial_complex (c UNION d:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF; FINITE_UNION]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!v:real^N. {v} IN c ==> simplicial_link (c UNION d) v = simplicial_link c v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_link; EXTENSION; IN_ELIM_THM; IN_UNION] THEN
    X_GEN_TAC `s:real^N->bool` THEN
    SUBGOAL_THEN `!t:real^N->bool. t IN d ==> ~(v IN t)` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`{v:real^N}`; `t:real^N->bool`]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    ASM_MESON_TAC[lf_simplicial_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. {v} IN d ==> simplicial_link (c UNION d) v = simplicial_link d v`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_link; EXTENSION; IN_ELIM_THM; IN_UNION] THEN
    X_GEN_TAC `s:real^N->bool` THEN
    SUBGOAL_THEN `!t:real^N->bool. t IN c ==> ~(v IN t)` ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`t:real^N->bool`; `{v:real^N}`]) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    TRY(EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    ASM_MESON_TAC[lf_simplicial_complex];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN ASM_SIMP_TAC[];
    REWRITE_TAC[surface_boundary] THEN
    SUBGOAL_THEN
     `!e:real^N->bool. e IN c /\ aff_dim e = &1
        ==> {r | r IN c UNION d /\ aff_dim r = &2 /\ e SUBSET r} =
            {r | r IN c /\ aff_dim r = &2 /\ e SUBSET r}`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `r:real^N->bool` THEN
      SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `aff_dim (e:real^N->bool) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `(r:real^N->bool) IN d` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`e:real^N->bool`; `r:real^N->bool`] o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `d:(real^N->bool)->bool`)) (concl th) &&
        can (find_term ((=) `c:(real^N->bool)->bool`)) (concl th) &&
        not (can (find_term ((=) `simplicial_link:((real^N->bool)->bool)->real^N->(real^N->bool)->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e:real^N->bool = {})` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!e:real^N->bool. e IN d /\ aff_dim e = &1
        ==> {r | r IN c UNION d /\ aff_dim r = &2 /\ e SUBSET r} =
            {r | r IN d /\ aff_dim r = &2 /\ e SUBSET r}`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN
      X_GEN_TAC `r:real^N->bool` THEN
      SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `aff_dim (e:real^N->bool) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      ASM_CASES_TAC `(r:real^N->bool) IN c` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`r:real^N->bool`; `e:real^N->bool`] o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `d:(real^N->bool)->bool`)) (concl th) &&
        can (find_term ((=) `c:(real^N->bool)->bool`)) (concl th) &&
        not (can (find_term ((=) `simplicial_link:((real^N->bool)->bool)->real^N->(real^N->bool)->bool`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(e:real^N->bool = {})` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_UNION] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THEN STRIP_TAC THENL
     [DISJ1_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        is_comb(lhs(concl th)) && is_const(rator(lhs(concl th))) &&
        fst(dest_const(rator(lhs(concl th)))) = "CARD")) THEN
      REWRITE_TAC[GSYM IN_UNION] THEN ASM_SIMP_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        is_comb(lhs(concl th)) && is_const(rator(lhs(concl th))) &&
        fst(dest_const(rator(lhs(concl th)))) = "CARD")) THEN
      REWRITE_TAC[GSYM IN_UNION] THEN ASM_SIMP_TAC[];
      EXISTS_TAC `t:real^N->bool` THEN REWRITE_TAC[GSYM IN_UNION] THEN
      ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[IN_UNION];
      EXISTS_TAC `t:real^N->bool` THEN REWRITE_TAC[GSYM IN_UNION] THEN
      ASM_SIMP_TAC[] THEN ASM_REWRITE_TAC[IN_UNION]];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `d:(real^N->bool)->bool`] COMPLEX_EULER_UNION) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `z = &0 ==> x + y - z = x + y`) THEN
    REWRITE_TAC[complex_euler] THEN MATCH_MP_TAC SUM_EQ_0 THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `{s | s IN c INTER d /\ aff_dim (s:real^N->bool) = &k} = {}`
      (fun th -> REWRITE_TAC[th; CARD_CLAUSES; REAL_MUL_RZERO]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s:real^N->bool`; `s:real^N->bool`] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `d:(real^N->bool)->bool`)) (concl th) &&
      can (find_term ((=) `c:(real^N->bool)->bool`)) (concl th) &&
      not (can (find_term ((=) `simplicial_link:((real^N->bool)->bool)->real^N->(real^N->bool)->bool`)) (concl th)) &&
      not (can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th)))) THEN
    ASM_REWRITE_TAC[INTER_IDEMPOT] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim ({}:real^N->bool) = &k` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
    INT_ARITH_TAC]);;

(* The gluing of surfaces along common boundary components (s26_surf). *)

let MOI_FSN_GLUE = prove
 (MOI_S26_SURF_GLUE_BODY,
  ACCEPT_TAC(MP SURF_GLUE MOI_FRB_SURF_INVARIANT));;

(* In the box with the ends: the complement in M of the two trace annuli is *)
(* a surface C with the four ends as boundary and chi C = chi m (glue C and *)
(* the traces back to M); the first trace is a reference annulus complex.   *)

let MOI_FSN_M_COMPL = prove
 (`!(m:(real^3->bool)->bool) a j1 j2 v p q t la lm a1 a2 b1 b2 c1 c2 k11 k12 k21 k22.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     moi_fsp_box m a v p q t la lm /\
     moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22
     ==> ?C A1 A12:(real^3->bool)->bool.
           FINITE C /\ combinatorial_manifold_with_boundary 2 C /\
           UNIONS C = closure (UNIONS m DIFF (a1 UNION a2)) /\
           surface_boundary C = k11 UNION k12 UNION k21 UNION k22 /\
           complex_euler C = complex_euler m /\
           closure (UNIONS m DIFF (a1 UNION a2)) INTER (a1 UNION a2) =
           k11 UNION k12 UNION k21 UNION k22 /\ closed (UNIONS m) /\
           FINITE A1 /\ combinatorial_manifold_with_boundary 2 A1 /\
           UNIONS A1 = a1 /\ surface_boundary A1 = k11 UNION k12 /\
           FINITE A12 /\ combinatorial_manifold_with_boundary 2 A12 /\
           UNIONS A12 = a1 UNION a2 /\
           surface_boundary A12 = k11 UNION k12 UNION k21 UNION k22`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_FSN_TRACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m a v p q t la (lm:(real^3->bool)->bool)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsn_ends] o check (fun th ->
    can (term_match []
      `moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 (k22:real^3->bool)`)
      (concl th))) THEN
  ABBREV_TAC `l1 = {s | s IN la INTER lm /\ s SUBSET (j1:real^3->bool)}` THEN
  ABBREV_TAC `l2 = {s | s IN la INTER lm /\ s SUBSET (j2:real^3->bool)}` THEN
  SUBGOAL_THEN `lf_simplicial_complex (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l1:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l2:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l1:(real^3->bool)->bool`] DERIVED_NBHD_POLYGON_2) THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l2:(real^3->bool)->bool`] DERIVED_NBHD_POLYGON_2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  MP_TAC(ISPECL [`a1:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`] MOI_S5C_ANN_COMPACT) THEN
  MP_TAC(ISPECL [`a2:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`] MOI_S5C_ANN_COMPACT) THEN
  MP_TAC(ISPECL [`a1:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`] MOI_S5C_ANN_ENDS_SUBSET) THEN
  MP_TAC(ISPECL [`a2:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`] MOI_S5C_ANN_ENDS_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  (* the second derived of lm *)
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `lmT = barycentric_subdivision (barycentric_subdivision (lm:(real^3->bool)->bool))` THEN
  SUBGOAL_THEN `FINITE (lmT:(real^3->bool)->bool) /\ lf_simplicial_complex lmT`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "lmT" THEN ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE] THEN
    MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
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
  SUBGOAL_THEN `closed (UNIONS (m:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN EXISTS_TAC `m:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[combinatorial_manifold];
    ALL_TAC] THEN
  (* the two traces as one surface *)
  MP_TAC(ISPECL [`derived_nbhd_complex lm (l1:(real^3->bool)->bool)`;
                 `derived_nbhd_complex lm (l2:(real^3->bool)->bool)`] MOI_FSN_DISJ_UNION_CMWB2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `A12 = derived_nbhd_complex lm l1 UNION
                    derived_nbhd_complex lm (l2:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `simplicial_subcomplex (A12:(real^3->bool)->bool) lmT` ASSUME_TAC THENL
   [EXPAND_TAC "A12" THEN
    UNDISCH_TAC `simplicial_subcomplex (derived_nbhd_complex lm (l1:(real^3->bool)->bool)) lmT` THEN
    UNDISCH_TAC `simplicial_subcomplex (derived_nbhd_complex lm (l2:(real^3->bool)->bool)) lmT` THEN
    REWRITE_TAC[simplicial_subcomplex; IN_UNION] THEN SET_TAC[];
    ALL_TAC] THEN
  (* the complement *)
  MP_TAC(ISPECL [`lmT:(real^3->bool)->bool`; `A12:(real^3->bool)->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`;
                 `k11 UNION k12:real^3->bool`; `k21 UNION k22:real^3->bool`] MOI_FSN_COMPL2) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; UNION_SUBSET] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `C = {s | s IN lmT /\ s SUBSET closure (UNIONS m DIFF (a1 UNION a2:real^3->bool))}` THEN
  (* chi C by gluing C and the traces back to M *)
  SUBGOAL_THEN `closure (UNIONS m DIFF (a1 UNION a2)) INTER (a1 UNION a2) =
                k11 UNION k12 UNION k21 UNION (k22:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a1 UNION a2:real^3->bool`; `UNIONS m:real^3->bool`] MOI_FSP_SUBTOP_FRONTIER) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CLOSED_UNION; COMPACT_IMP_CLOSED] THEN
       (MAP_EVERY UNDISCH_TAC
         [`derived_nbhd t la INTER UNIONS m = a1 UNION (a2:real^3->bool)`;
          `a1 UNION a2 = derived_nbhd lm (la INTER lm:(real^3->bool)->bool)`] THEN
        SET_TAC[]);
      ALL_TAC] THEN
    SUBGOAL_THEN `(subtopology euclidean (UNIONS m)) frontier_of (a1 UNION a2) =
                  k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`
    (fun th -> REWRITE_TAC[th]) THENL
     [SUBGOAL_THEN `derived_frontier lm (la INTER lm) =
                    (subtopology euclidean (UNIONS m)) frontier_of (a1 UNION a2:real^3->bool)`
      (SUBST1_TAC o SYM) THENL
       [REWRITE_TAC[derived_frontier] THEN ASM_REWRITE_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`(b1 UNION b2 UNION c1 UNION c2) INTER UNIONS m =
           derived_frontier lm (la INTER lm:(real^3->bool)->bool)`;
          `derived_frontier t la = b1 UNION b2 UNION c1 UNION (c2:real^3->bool)`;
          `derived_frontier t la INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`] THEN
        SET_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`C:(real^3->bool)->bool`; `A12:(real^3->bool)->bool`;
                 `k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`]
    (INST_TYPE [`:3`,`:N`] MOI_FSN_GLUE)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNION_ASSOC] THEN REPEAT CONJ_TAC THEN
    TRY(MESON_TAC[IN_COMPONENTS_SUBSET] THEN NO_TAC) THEN
    TRY(SET_TAC[] THEN NO_TAC) THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNION_ASSOC] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `complex_euler (e0:(real^3->bool)->bool) = complex_euler (m:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FEU_COMPLEX_EULER_SAME_POLYHEDRON THEN
    REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[combinatorial_manifold_with_boundary];
      ASM_MESON_TAC[combinatorial_manifold];
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
         [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
          UNDISCH_TAC `derived_nbhd t la INTER UNIONS m = a1 UNION (a2:real^3->bool)` THEN
          SET_TAC[]];
        MP_TAC(ISPEC `UNIONS m DIFF (a1 UNION a2:real^3->bool)` CLOSURE_SUBSET) THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`C:(real^3->bool)->bool`;
                        `derived_nbhd_complex lm (l1:(real^3->bool)->bool)`;
                        `A12:(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `complex_euler (e0:(real^3->bool)->bool) = complex_euler (m:(real^3->bool)->bool)` THEN
  REWRITE_TAC[UNION_ASSOC] THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The new surface m': the complement C of the traces glued to the parallel *)
(* annuli b1, b2 along the four ends; chi unchanged.                        *)

let MOI_FSN_MPRIME = prove
 (`!(m:(real^3->bool)->bool) a j1 j2 v p q t la lm a1 a2 b1 b2 c1 c2 k11 k12 k21 k22.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     moi_fsp_box m a v p q t la lm /\
     moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22
     ==> ?m':(real^3->bool)->bool.
           FINITE m' /\ combinatorial_manifold 2 m' /\
           UNIONS m' = (UNIONS m DIFF (a1 UNION a2)) UNION b1 UNION b2 /\
           complex_euler m' = complex_euler m`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_FSN_M_COMPL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(real^3->bool)->bool` (X_CHOOSE_THEN `A1:(real^3->bool)->bool`
    (X_CHOOSE_THEN `A12:(real^3->bool)->bool` STRIP_ASSUME_TAC))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsn_ends] o check (fun th ->
    can (term_match []
      `moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 (k22:real^3->bool)`)
      (concl th))) THEN
  SUBGOAL_THEN
   `!b (e0:real^3->bool) e1.
      pl_annulus_with_ends b e0 e1
      ==> ?B:(real^3->bool)->bool.
            FINITE B /\ combinatorial_manifold_with_boundary 2 B /\ UNIONS B = b /\
            surface_boundary B = e0 UNION e1 /\ complex_euler B = &0`
  (LABEL_TAC "BC") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`b:real^3->bool`; `b:real^3->bool`; `b:real^3->bool`] MOI_FSP_TRIANGULATE3) THEN
    ANTS_TAC THENL [REWRITE_TAC[SUBSET_REFL] THEN ASM_MESON_TAC[MOI_S5C_ANN_POLYHEDRON]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `B:(real^3->bool)->bool` (X_CHOOSE_THEN `lx:(real^3->bool)->bool`
      (X_CHOOSE_THEN `ly:(real^3->bool)->bool` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `B:(real^3->bool)->bool` THEN
    SUBGOAL_THEN `FINITE (B:(real^3->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FSN_ANN_COMPLEX_REF THEN
    MAP_EVERY EXISTS_TAC [`A1:(real^3->bool)->bool`; `k11:real^3->bool`; `k12:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "BC" (MP_TAC o C MATCH_MP (ASSUME `pl_annulus_with_ends b2 k12 (k22:real^3->bool)`)) THEN
  USE_THEN "BC" (MP_TAC o C MATCH_MP (ASSUME `pl_annulus_with_ends b1 k11 (k21:real^3->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `B1:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `B2:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`B1:(real^3->bool)->bool`; `B2:(real^3->bool)->bool`] MOI_FSN_DISJ_UNION_CMWB2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the ends and the pieces *)
  MP_TAC(ISPECL [`b1:real^3->bool`; `k11:real^3->bool`; `k21:real^3->bool`] MOI_S5C_ANN_ENDS_SUBSET) THEN
  MP_TAC(ISPECL [`b2:real^3->bool`; `k12:real^3->bool`; `k22:real^3->bool`] MOI_S5C_ANN_ENDS_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(b1 UNION b2) INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`derived_frontier t la INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
      `derived_frontier t la = b1 UNION b2 UNION c1 UNION (c2:real^3->bool)`;
      `(k11:real^3->bool) SUBSET b1`; `(k21:real^3->bool) SUBSET b1`;
      `(k12:real^3->bool) SUBSET b2`; `(k22:real^3->bool) SUBSET b2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `surface_boundary (C:(real^3->bool)->bool) SUBSET UNIONS C` ASSUME_TAC THENL
   [REWRITE_TAC[surface_boundary] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closure (UNIONS m DIFF (a1 UNION a2)) SUBSET UNIONS (m:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`C:(real^3->bool)->bool`; `B1 UNION B2:(real^3->bool)->bool`;
                 `k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`]
    (INST_TYPE [`:3`,`:N`] MOI_FSN_GLUE)) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      SET_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN SET_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(b1 UNION b2) INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
        `closure (UNIONS m DIFF (a1 UNION a2)) SUBSET UNIONS (m:(real^3->bool)->bool)`;
        `surface_boundary (C:(real^3->bool)->bool) SUBSET UNIONS C`;
        `UNIONS C = closure (UNIONS m DIFF (a1 UNION a2:real^3->bool))`;
        `surface_boundary C = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
        `(k11:real^3->bool) SUBSET b1`; `(k21:real^3->bool) SUBSET b1`;
        `(k12:real^3->bool) SUBSET b2`; `(k22:real^3->bool) SUBSET b2`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`closure (UNIONS m DIFF (a1 UNION a2)) INTER (a1 UNION a2) =
       k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
      `closure (UNIONS m DIFF (a1 UNION a2)) SUBSET UNIONS (m:(real^3->bool)->bool)`;
      `(k11:real^3->bool) SUBSET b1`; `(k21:real^3->bool) SUBSET b1`;
      `(k12:real^3->bool) SUBSET b2`; `(k22:real^3->bool) SUBSET b2`] THEN
    MP_TAC(ISPEC `UNIONS m DIFF (a1 UNION a2:real^3->bool)` CLOSURE_SUBSET) THEN
    SET_TAC[];
    REAL_ARITH_TAC]);;

(* ========================================================================= *)
(* The cut context and the corners (as MOI_FSP_CUT_CTX and                   *)
(* MOI_FSP_CUT_CORNER of pc_moi_fnd_split, for the annulus box: the corners *)
(* are the points of the four ends of the trace annuli).                     *)
(* ========================================================================= *)

let MOI_FSN_CUT_CTX = prove
 (`!(m:(real^3->bool)->bool) a v p q t la lm y B.
     FINITE m /\ combinatorial_manifold 2 m /\
     moi_fsp_box m a v p q t la lm /\
     simplicial_subcomplex y t /\ combinatorial_manifold_with_boundary 3 y /\
     la SUBSET y /\ complex_boundary y = UNIONS m UNION B /\ closed B /\
     DISJOINT B (derived_nbhd t la)
     ==> FINITE y /\ lf_simplicial_complex y /\ simplicial_subcomplex la y /\
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
         simplicial_subcomplex (derived_nbhd_complex y la)
                               (barycentric_subdivision (barycentric_subdivision y)) /\
         FINITE (derived_nbhd_complex y la) /\
         lf_simplicial_complex (derived_nbhd_complex y la) /\
         combinatorial_manifold_with_boundary 3 (derived_nbhd_complex y la) /\
         UNIONS (derived_nbhd_complex y la) = derived_nbhd t la INTER UNIONS y /\
         complex_boundary (derived_nbhd_complex y la) =
         (derived_frontier t la INTER UNIONS y) UNION (derived_nbhd t la INTER UNIONS m)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m a v p q t la (lm:(real^3->bool)->bool)`) (concl th))) THEN
  SUBGOAL_THEN `lf_simplicial_complex (y:(real^3->bool)->bool) /\ FINITE y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `simplicial_subcomplex la (y:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex la (t:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `la SUBSET (y:(real^3->bool)->bool)` THEN
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
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `y:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `la INTER y = (la:(real^3->bool)->bool)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `FINITE (la:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `y:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`y:(real^3->bool)->bool`; `la:(real^3->bool)->bool`]
                DERIVED_NBHD_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY (fun t -> MP_TAC(ASSUME t))
   [`UNIONS m SUBSET UNIONS (y:(real^3->bool)->bool)`;
    `DISJOINT B (derived_nbhd t (la:(real^3->bool)->bool))`] THEN
  SET_TAC[]);;


let MOI_FSN_CUT_CORNER = prove
 (`!(m:(real^3->bool)->bool) a j1 j2 v p q t la lm a1 a2 b1 b2 c1 c2 k11 k12 k21 k22 y B w.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     moi_fsp_box m a v p q t la lm /\
     moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22 /\
     simplicial_subcomplex y t /\ combinatorial_manifold_with_boundary 3 y /\
     la SUBSET y /\ complex_boundary y = UNIONS m UNION B /\ closed B /\
     DISJOINT B (derived_nbhd t la) /\
     {w} IN barycentric_subdivision (barycentric_subdivision y) /\
     w IN k11 UNION k12 UNION k21 UNION k22
     ==> pl_ball 2 (UNIONS (simplicial_link
           {s | s IN barycentric_subdivision (barycentric_subdivision y) /\
                s SUBSET closure (UNIONS (barycentric_subdivision (barycentric_subdivision y)) DIFF
                                  UNIONS (derived_nbhd_complex y la))} w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `v:real^3->bool`;
                 `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `y:(real^3->bool)->bool`; `B:real^3->bool`] MOI_FSN_CUT_CTX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `v:real^3->bool`;
                 `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSN_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m a v p q t la (lm:(real^3->bool)->bool)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsn_ends] o check (fun th ->
    can (term_match []
      `moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 (k22:real^3->bool)`)
      (concl th))) THEN
  MP_TAC(SPEC_ALL MOI_FSN_M_COMPL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:(real^3->bool)->bool` (X_CHOOSE_THEN `A1:(real^3->bool)->bool`
    (X_CHOOSE_THEN `A12:(real^3->bool)->bool` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `yT = barycentric_subdivision (barycentric_subdivision (y:(real^3->bool)->bool))` THEN
  ABBREV_TAC `A = derived_nbhd_complex y (la:(real^3->bool)->bool)` THEN
  ABBREV_TAC `T2 = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  MP_TAC(ISPECL [`yT:(real^3->bool)->bool`; `A:(real^3->bool)->bool`; `w:real^3`]
                MOI_FSP_COMP_LINK) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(w:real^3) IN derived_frontier t la /\ w IN UNIONS m /\
                w IN derived_nbhd t la /\ ~(w IN B) /\ w IN UNIONS y /\
                w IN interval(p:real^3,q)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`derived_frontier t la INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
      `derived_frontier t la SUBSET derived_nbhd t (la:(real^3->bool)->bool)`;
      `DISJOINT B (derived_nbhd t (la:(real^3->bool)->bool))`;
      `UNIONS m SUBSET UNIONS (y:(real^3->bool)->bool)`;
      `derived_nbhd t la SUBSET v INTER interval(p:real^3,q)`;
      `(w:real^3) IN k11 UNION k12 UNION k21 UNION k22`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (T2:(real^3->bool)->bool) /\
                combinatorial_manifold_with_boundary 3 T2 /\
                complex_boundary T2 = interval[p,q] DIFF interval(p:real^3,q) /\
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
      ASM_REWRITE_TAC[IN_UNION; IN_INTER] THEN
      MATCH_MP_TAC(TAUT `p ==> (p <=> q) /\ r ==> q`) THEN
      MAP_EVERY UNDISCH_TAC
       [`(w:real^3) IN derived_nbhd t la`; `(w:real^3) IN UNIONS m`;
        `derived_nbhd t la INTER UNIONS m = a1 UNION (a2:real^3->bool)`] THEN
      SET_TAC[]];
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
                UNIONS Ka = derived_nbhd t la INTER UNIONS (m:(real^3->bool)->bool) /\
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
        `DISJOINT B (derived_nbhd t (la:(real^3->bool)->bool))`;
        `derived_nbhd t la INTER UNIONS m = a1 UNION (a2:real^3->bool)`] THEN
      SET_TAC[];
      EXPAND_TAC "Ka" THEN GEN_REWRITE_TAC I [SUBSET] THEN
      REWRITE_TAC[IN_INTER; boundary_complex; IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(s:real^3->bool) SUBSET UNIONS A` MP_TAC THENL
       [UNDISCH_TAC `(s:real^3->bool) IN A` THEN SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(s:real^3->bool) SUBSET complex_boundary yT` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ASSUME `derived_nbhd t la INTER UNIONS m = a1 UNION (a2:real^3->bool)`) THEN
      UNDISCH_TAC `DISJOINT B (derived_nbhd t (la:(real^3->bool)->bool))` THEN SET_TAC[];
      EXPAND_TAC "Ka" THEN ASM_REWRITE_TAC[IN_INTER; boundary_complex; IN_ELIM_THM] THEN
      UNDISCH_TAC `(w:real^3) IN UNIONS m` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 2 (Ka:(real^3->bool)->bool) /\
                surface_boundary Ka = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A12:(real^3->bool)->bool`; `Ka:(real^3->bool)->bool`;
                   `\x:real^3. x`; `\x:real^3. x`] MOI_FRB_SURF_INVARIANT) THEN
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


(* ========================================================================= *)
(* The side lemma with four pieces.  The frontier F is the union            *)
(* of the parallel annuli b1, b2 and the rim annuli c1, c2; a rim witness   *)
(* Z0 joining the two ends of a trace annulus off Y must lie in the rim     *)
(* annulus of that rim, and the witnesses Z1, Z2 in Y then lie in b1, b2.   *)
(* ========================================================================= *)

(* A connected set missing M, covered by two closed sets meeting only in M, *)
(* lies in one of them.                                                      *)

let MOI_FSN_CONN_PIECE = prove
 (`!(Z:real^N->bool) X R M.
     connected Z /\ closed X /\ closed R /\ Z SUBSET X UNION R /\
     X INTER R SUBSET M /\ Z INTER M = {}
     ==> Z SUBSET X \/ Z INTER X = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `connected (Z:real^N->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`X:real^N->bool`; `R:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`(X:real^N->bool) INTER R SUBSET M`; `(Z:real^N->bool) INTER M = {}`;
    `(Z:real^N->bool) SUBSET X UNION R`] THEN
  SET_TAC[]);;

(* A connected set missing M inside the union of four closed pieces meeting *)
(* pairwise only in M lies in one piece.                                     *)

let MOI_FSN_PIECE_OF = prove
 (`!(Z:real^N->bool) b1 b2 c1 c2 M.
     connected Z /\ Z SUBSET b1 UNION b2 UNION c1 UNION c2 /\ Z INTER M = {} /\
     closed b1 /\ closed b2 /\ closed c1 /\ closed c2 /\
     b1 INTER b2 SUBSET M /\ b1 INTER c1 SUBSET M /\ b1 INTER c2 SUBSET M /\
     b2 INTER c1 SUBSET M /\ b2 INTER c2 SUBSET M /\ c1 INTER c2 SUBSET M
     ==> Z SUBSET b1 \/ Z SUBSET b2 \/ Z SUBSET c1 \/ Z SUBSET c2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`Z:real^N->bool`; `b1:real^N->bool`; `b2 UNION c1 UNION c2:real^N->bool`;
                 `M:real^N->bool`] MOI_FSN_CONN_PIECE) THEN
  ASM_SIMP_TAC[CLOSED_UNION] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`Z:real^N->bool`; `b2:real^N->bool`; `c1 UNION c2:real^N->bool`;
                 `M:real^N->bool`] MOI_FSN_CONN_PIECE) THEN
  ASM_SIMP_TAC[CLOSED_UNION] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`Z:real^N->bool`; `c1:real^N->bool`; `c2:real^N->bool`;
                 `M:real^N->bool`] MOI_FSN_CONN_PIECE) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The point-set side lemma for four pieces. *)

let MOI_FSN_SIDE_TOP4 = prove
 (`!(FR:real^N->bool) M Y b1 b2 c1 c2 k11 k12 k21 k22 Z0 Z1 Z2 m1 m2 W0 n1 n2.
     FR = b1 UNION b2 UNION c1 UNION c2 /\
     b1 INTER M = k11 UNION k21 /\ b2 INTER M = k12 UNION k22 /\
     c1 INTER M = k11 UNION k12 /\ c2 INTER M = k21 UNION k22 /\
     closed b1 /\ closed b2 /\ closed c1 /\ closed c2 /\
     b1 INTER b2 = {} /\ c1 INTER c2 = {} /\
     b1 INTER c1 SUBSET M /\ b1 INTER c2 SUBSET M /\
     b2 INTER c1 SUBSET M /\ b2 INTER c2 SUBSET M /\
     connected (b1 DIFF M) /\ connected (b2 DIFF M) /\
     connected (c1 DIFF M) /\ connected (c2 DIFF M) /\
     (!S. connected S /\ S SUBSET FR DIFF M ==> S SUBSET Y \/ S INTER Y = {}) /\
     connected Z0 /\ Z0 SUBSET FR DIFF M /\ Z0 INTER Y = {} /\
     m1 IN closure Z0 /\ m2 IN closure Z0 /\
     connected Z1 /\ Z1 SUBSET (FR DIFF M) INTER Y /\ m1 IN closure Z1 /\
     connected Z2 /\ Z2 SUBSET (FR DIFF M) INTER Y /\ m2 IN closure Z2 /\
     ~(m1 IN k11 /\ m2 IN k11) /\ ~(m1 IN k12 /\ m2 IN k12) /\
     m1 IN k11 UNION k12 /\ m2 IN k11 UNION k12 /\
     connected W0 /\ W0 SUBSET FR DIFF M /\ W0 INTER Y = {} /\
     n1 IN closure W0 /\ n2 IN closure W0 /\
     ~(n1 IN k21 /\ n2 IN k21) /\ ~(n1 IN k22 /\ n2 IN k22) /\
     n1 IN k21 UNION k22 /\ n2 IN k21 UNION k22
     ==> (FR DIFF M) INTER Y = (b1 UNION b2) DIFF (k11 UNION k12 UNION k21 UNION k22)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(b1:real^N->bool) INTER b2 SUBSET M /\ (c1:real^N->bool) INTER c2 SUBSET M`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
  (* each connected set off M in F lies in one piece *)
  SUBGOAL_THEN
   `!Z:real^N->bool. connected Z /\ Z SUBSET FR DIFF M
                     ==> Z SUBSET b1 \/ Z SUBSET b2 \/ Z SUBSET c1 \/ Z SUBSET c2`
  (LABEL_TAC "PC") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSN_PIECE_OF THEN
    EXISTS_TAC `M:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(Z:real^N->bool) SUBSET FR DIFF M` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!Z:real^N->bool. Z SUBSET b1 ==> closure Z SUBSET b1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!Z:real^N->bool. Z SUBSET b2 ==> closure Z SUBSET b2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!Z:real^N->bool. Z SUBSET c1 ==> closure Z SUBSET c1` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!Z:real^N->bool. Z SUBSET c2 ==> closure Z SUBSET c2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(Z0:real^N->bool = {}) /\ ~(Z1:real^N->bool = {}) /\
                ~(Z2:real^N->bool = {}) /\ ~(W0:real^N->bool = {})` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CLOSURE_EMPTY; NOT_IN_EMPTY]) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the rim witnesses off Y lie in the rim annuli *)
  SUBGOAL_THEN `(Z0:real^N->bool) SUBSET c1 /\ (W0:real^N->bool) SUBSET c2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "PC" (MP_TAC o C MP (CONJ (ASSUME `connected (Z0:real^N->bool)`)
        (ASSUME `(Z0:real^N->bool) SUBSET FR DIFF M`)) o SPEC `Z0:real^N->bool`) THEN
      MAP_EVERY (fun t -> MP_TAC(SPEC `Z0:real^N->bool` (ASSUME t)))
       [`!Z:real^N->bool. Z SUBSET b1 ==> closure Z SUBSET b1`;
        `!Z:real^N->bool. Z SUBSET b2 ==> closure Z SUBSET b2`;
        `!Z:real^N->bool. Z SUBSET c1 ==> closure Z SUBSET c1`;
        `!Z:real^N->bool. Z SUBSET c2 ==> closure Z SUBSET c2`] THEN
      MAP_EVERY UNDISCH_TAC
       [`(m1:real^N) IN closure Z0`; `(m2:real^N) IN closure Z0`;
        `~((m1:real^N) IN k11 /\ m2 IN k11)`; `~((m1:real^N) IN k12 /\ m2 IN k12)`;
        `(m1:real^N) IN k11 UNION k12`; `(m2:real^N) IN k11 UNION k12`;
        `(b1:real^N->bool) INTER M = k11 UNION k21`; `(b2:real^N->bool) INTER M = k12 UNION k22`;
        `(c1:real^N->bool) INTER M = k11 UNION k12`; `(c2:real^N->bool) INTER M = k21 UNION k22`;
        `(b1:real^N->bool) INTER b2 = {}`; `(c1:real^N->bool) INTER c2 = {}`] THEN
      SET_TAC[];
      USE_THEN "PC" (MP_TAC o C MP (CONJ (ASSUME `connected (W0:real^N->bool)`)
        (ASSUME `(W0:real^N->bool) SUBSET FR DIFF M`)) o SPEC `W0:real^N->bool`) THEN
      MAP_EVERY (fun t -> MP_TAC(SPEC `W0:real^N->bool` (ASSUME t)))
       [`!Z:real^N->bool. Z SUBSET b1 ==> closure Z SUBSET b1`;
        `!Z:real^N->bool. Z SUBSET b2 ==> closure Z SUBSET b2`;
        `!Z:real^N->bool. Z SUBSET c1 ==> closure Z SUBSET c1`;
        `!Z:real^N->bool. Z SUBSET c2 ==> closure Z SUBSET c2`] THEN
      MAP_EVERY UNDISCH_TAC
       [`(n1:real^N) IN closure W0`; `(n2:real^N) IN closure W0`;
        `~((n1:real^N) IN k21 /\ n2 IN k21)`; `~((n1:real^N) IN k22 /\ n2 IN k22)`;
        `(n1:real^N) IN k21 UNION k22`; `(n2:real^N) IN k21 UNION k22`;
        `(b1:real^N->bool) INTER M = k11 UNION k21`; `(b2:real^N->bool) INTER M = k12 UNION k22`;
        `(c1:real^N->bool) INTER M = k11 UNION k12`; `(c2:real^N->bool) INTER M = k21 UNION k22`;
        `(b1:real^N->bool) INTER b2 = {}`; `(c1:real^N->bool) INTER c2 = {}`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c1 DIFF M) INTER (Y:real^N->bool) = {} /\
                (c2 DIFF M) INTER (Y:real^N->bool) = {}` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `c1 DIFF M:real^N->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Y:real^N->bool`)) (concl th)));
      FIRST_X_ASSUM(MP_TAC o SPEC `c2 DIFF M:real^N->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Y:real^N->bool`)) (concl th)))] THEN
    ASM_REWRITE_TAC[] THEN
    (ANTS_TAC THENL [SET_TAC[]; ALL_TAC]) THEN
    MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`(Z0:real^N->bool) SUBSET c1`; `(Z0:real^N->bool) SUBSET FR DIFF M`;
      `(Z0:real^N->bool) INTER Y = {}`; `~(Z0:real^N->bool = {})`;
      `(W0:real^N->bool) SUBSET c2`; `(W0:real^N->bool) SUBSET FR DIFF M`;
      `(W0:real^N->bool) INTER Y = {}`; `~(W0:real^N->bool = {})`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the witnesses in Y lie in b1, b2 *)
  SUBGOAL_THEN
   `!Z (x:real^N). connected Z /\ Z SUBSET (FR DIFF M) INTER Y /\ x IN closure Z /\
                   ~(Z = {}) /\ x IN k11 UNION k12
                   ==> (x IN k11 ==> b1 DIFF M SUBSET Y) /\ (x IN k12 ==> b2 DIFF M SUBSET Y)`
  (LABEL_TAC "WY") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "PC" (MP_TAC o SPEC `Z:real^N->bool`) THEN
    ANTS_TAC THENL
     [MP_TAC(ASSUME `(Z:real^N->bool) SUBSET (FR DIFF M) INTER Y`) THEN
      MP_TAC(ASSUME `connected (Z:real^N->bool)`) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((Z:real^N->bool) SUBSET c1) /\ ~((Z:real^N->bool) SUBSET c2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `~(Z:real^N->bool = {})` THEN REWRITE_TAC[] THEN
      POP_ASSUM MP_TAC THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`(Z:real^N->bool) SUBSET (FR DIFF M) INTER Y`;
        `(c1 DIFF M) INTER (Y:real^N->bool) = {}`; `(c2 DIFF M) INTER (Y:real^N->bool) = {}`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^N->bool` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `closure:(real^N->bool)->real^N->bool`)) (concl th) &&
        can (find_term ((=) `b1:real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((x:real^N) IN k12)` ASSUME_TAC THENL
       [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
         [`(x:real^N) IN closure Z`; `closure Z SUBSET (b1:real^N->bool)`;
          `(b1:real^N->bool) INTER b2 = {}`; `(b2:real^N->bool) INTER M = k12 UNION k22`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `b1 DIFF M:real^N->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Y:real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`(Z:real^N->bool) SUBSET b1`; `(Z:real^N->bool) SUBSET (FR DIFF M) INTER Y`;
        `~(Z:real^N->bool = {})`] THEN
      SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `Z:real^N->bool` o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `closure:(real^N->bool)->real^N->bool`)) (concl th) &&
        can (find_term ((=) `b2:real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~((x:real^N) IN k11)` ASSUME_TAC THENL
       [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
         [`(x:real^N) IN closure Z`; `closure Z SUBSET (b2:real^N->bool)`;
          `(b1:real^N->bool) INTER b2 = {}`; `(b1:real^N->bool) INTER M = k11 UNION k21`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `b2 DIFF M:real^N->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `Y:real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`(Z:real^N->bool) SUBSET b2`; `(Z:real^N->bool) SUBSET (FR DIFF M) INTER Y`;
        `~(Z:real^N->bool = {})`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `b1 DIFF M SUBSET (Y:real^N->bool) /\ b2 DIFF M SUBSET (Y:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "WY" (fun th -> MP_TAC(MP (SPECL [`Z1:real^N->bool`; `m1:real^N`] th)
      (end_itlist CONJ (map ASSUME
        [`connected (Z1:real^N->bool)`; `Z1 SUBSET (FR DIFF M) INTER (Y:real^N->bool)`;
         `(m1:real^N) IN closure Z1`; `~(Z1:real^N->bool = {})`;
         `(m1:real^N) IN k11 UNION k12`])))) THEN
    USE_THEN "WY" (fun th -> MP_TAC(MP (SPECL [`Z2:real^N->bool`; `m2:real^N`] th)
      (end_itlist CONJ (map ASSUME
        [`connected (Z2:real^N->bool)`; `Z2 SUBSET (FR DIFF M) INTER (Y:real^N->bool)`;
         `(m2:real^N) IN closure Z2`; `~(Z2:real^N->bool = {})`;
         `(m2:real^N) IN k11 UNION k12`])))) THEN
    MAP_EVERY UNDISCH_TAC
     [`~((m1:real^N) IN k11 /\ m2 IN k11)`; `~((m1:real^N) IN k12 /\ m2 IN k12)`;
      `(m1:real^N) IN k11 UNION k12`; `(m2:real^N) IN k11 UNION k12`] THEN
    REWRITE_TAC[IN_UNION] THEN MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`FR = b1 UNION b2 UNION c1 UNION (c2:real^N->bool)`;
    `(b1:real^N->bool) INTER M = k11 UNION k21`; `(b2:real^N->bool) INTER M = k12 UNION k22`;
    `(c1 DIFF M) INTER (Y:real^N->bool) = {}`; `(c2 DIFF M) INTER (Y:real^N->bool) = {}`;
    `b1 DIFF M SUBSET (Y:real^N->bool)`; `b2 DIFF M SUBSET (Y:real^N->bool)`] THEN
  SET_TAC[]);;

(* The edge-fan cycle of MOI_FSP_SIDE_CYCLE through a given point x0 of the  *)
(* rim: an edge of ldT on the rim containing x0, with the fan around it.     *)

let MOI_FSN_SIDE_CYCLE_AT = prove
 (`!(t:(real^N->bool)->bool) ld lm (x0:real^N).
     FINITE t /\ lf_simplicial_complex t /\
     simplicial_subcomplex ld t /\ simplicial_subcomplex lm t /\
     FINITE (barycentric_subdivision (barycentric_subdivision ld)) /\
     combinatorial_manifold_with_boundary 2
       (barycentric_subdivision (barycentric_subdivision ld)) /\
     surface_boundary (barycentric_subdivision (barycentric_subdivision ld)) =
     UNIONS ld INTER UNIONS lm /\
     x0 IN UNIONS ld INTER UNIONS lm /\
     FINITE (barycentric_subdivision (barycentric_subdivision lm)) /\
     combinatorial_manifold 2 (barycentric_subdivision (barycentric_subdivision lm)) /\
     (!w. {w} IN barycentric_subdivision (barycentric_subdivision t) /\
          w IN UNIONS ld INTER UNIONS lm
          ==> pl_sphere 2 (UNIONS (simplicial_link
                (barycentric_subdivision (barycentric_subdivision t)) w)))
     ==> ?v0 y0 dd (U:num->real^N) c0 r1 r2.
           ~(v0 = y0) /\ x0 IN segment[v0,y0] /\
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
  SUBGOAL_THEN `~(J:real^N->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:real^N) IN J` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?e:real^N->bool. e IN ldT /\ aff_dim e = &1 /\
                  CARD {r | r IN ldT /\ aff_dim r = &2 /\ e SUBSET r} = 1 /\ e SUBSET J /\
                  x0 IN e`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x0:real^N) IN J` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `surface_boundary (ldT:(real^N->bool)->bool)`)) THEN
    REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
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

(* The two-dimensional fact at a rim edge (MOI_FSP_SIDE_2D for a trace      *)
(* annulus aa with ends q1, q2 around the rim J): the far vertices of the   *)
(* two triangles of M at the edge lie on different ends.                    *)

let MOI_FSN_SIDE_2D_GEN = prove
 (`!(t:(real^3->bool)->bool) ld lm (aa:real^3->bool) q1 q2 J v0 y0 (m1:real^3) m2.
     FINITE t /\ lf_simplicial_complex t /\
     simplicial_subcomplex ld t /\ simplicial_subcomplex lm t /\
     FINITE (barycentric_subdivision (barycentric_subdivision lm)) /\
     combinatorial_manifold 2 (barycentric_subdivision (barycentric_subdivision lm)) /\
     pl_annulus_with_ends aa q1 q2 /\ aa SUBSET UNIONS lm /\
     J SUBSET aa DIFF (q1 UNION q2) /\ J SUBSET UNIONS ld INTER UNIONS lm /\
     pl_sphere 1 J /\ pl_sphere 1 q1 /\ pl_sphere 1 q2 /\
     ~(v0 = y0) /\
     segment[v0,y0] IN barycentric_subdivision (barycentric_subdivision t) /\
     segment[v0,y0] SUBSET J /\
     convex hull {v0,y0,m1} IN barycentric_subdivision (barycentric_subdivision t) /\
     convex hull {v0,y0,m2} IN barycentric_subdivision (barycentric_subdivision t) /\
     aff_dim (convex hull {v0,y0,m1}) = &2 /\ aff_dim (convex hull {v0,y0,m2}) = &2 /\
     segment[v0,y0] SUBSET convex hull {v0,y0,m1} /\
     segment[v0,y0] SUBSET convex hull {v0,y0,m2} /\
     m1 IN UNIONS lm /\ ~(m1 IN UNIONS ld) /\ m2 IN UNIONS lm /\ ~(m2 IN UNIONS ld) /\
     ~(convex hull {v0,y0,m1} = convex hull {v0,y0,m2}) /\
     convex hull {v0,y0,m1} SUBSET aa /\ convex hull {v0,y0,m2} SUBSET aa
     ==> ~(m1 IN q1 /\ m2 IN q1) /\ ~(m1 IN q2 /\ m2 IN q2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `lmT = barycentric_subdivision (barycentric_subdivision (lm:(real^3->bool)->bool))` THEN
  SUBGOAL_THEN `lf_simplicial_complex (lmT:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v0:real^3) IN J /\ (y0:real^3) IN J` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `segment[v0:real^3,y0] SUBSET J` THEN MESON_TAC[ENDS_IN_SEGMENT; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(J:real^3->bool) SUBSET UNIONS lm /\ J SUBSET UNIONS ld` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(J:real^3->bool) SUBSET UNIONS ld INTER UNIONS lm` THEN SET_TAC[]; ALL_TAC] THEN
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
  SUBGOAL_THEN `?e2. &0 < e2 /\ ball(p:real^3,e2) INTER (q1 UNION q2) = {}` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `closed (q1 UNION q2:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC CLOSED_UNION THEN ASM_MESON_TAC[MOI_SLV_CIRCLE_CLOSED]; ALL_TAC] THEN
    REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
      UNDISCH_TAC `J SUBSET (aa) DIFF (q1 UNION q2:real^3->bool)` THEN
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
   [`aa:real^3->bool`; `J:real^3->bool`;
    `ball(p:real^3,r)`;
    `(ball(p,r) INTER (convex hull {v0,y0,m1} DIFF segment[v0,y0])) UNION
     (segment[p:real^3,m1] DELETE p)`;
    `(ball(p,r) INTER (convex hull {v0,y0,m2} DIFF segment[v0,y0])) UNION
     (segment[p:real^3,m2] DELETE p)`;
    `p:real^3`] THEN
  ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPEC `q1:real^3->bool` MOI_SLV_CIRCLE_CLOSED) THEN ASM_SIMP_TAC[];
    MP_TAC(ISPEC `q2:real^3->bool` MOI_SLV_CIRCLE_CLOSED) THEN ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`aa:real^3->bool`; `q1:real^3->bool`; `q2:real^3->bool`]
      MOI_S5C_ANN_ENDS_SUBSET) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    MP_TAC(ISPECL [`aa:real^3->bool`; `q1:real^3->bool`; `q2:real^3->bool`]
      MOI_S5C_ANN_ENDS_SUBSET) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    UNDISCH_TAC `ball(p:real^3,r) SUBSET ball(p,e2)` THEN
    UNDISCH_TAC `ball(p:real^3,e2) INTER (q1 UNION q2) = {}` THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_INTER; IN_UNION] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN UNIONS lm` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN aa` THEN UNDISCH_TAC `(aa:real^3->bool) SUBSET UNIONS lm` THEN
      SET_TAC[];
      ALL_TAC] THEN
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
      `convex hull {v0:real^3,y0,m1} SUBSET aa`; `(J:real^3->bool) SUBSET UNIONS ld`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`(ball(p,r) INTER (convex hull {v0,y0,m2} DIFF segment[v0,y0])) UNION
       (segment[p:real^3,m2] DELETE p) SUBSET convex hull {v0,y0,m2} DIFF UNIONS ld`;
      `convex hull {v0:real^3,y0,m2} SUBSET aa`; `(J:real^3->bool) SUBSET UNIONS ld`] THEN
    SET_TAC[]]);;

(* The witnesses of the side lemma at a rim J of the annulus (as            *)
(* MOI_FSP_SIDE_WIT of pc_moi_fnd_split, at a given point x0 of the rim):   *)
(* aa is the trace annulus around J, with ends q1, q2.                       *)

let MOI_FSN_SIDE_WIT_AT = prove
 (`!(m:(real^3->bool)->bool) a j1 j2 v p q t la lm a1 a2 b1 b2 c1 c2 k11 k12 k21 k22 y B
    aa aa' q1 q2 J J' (x0:real^3).
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     moi_fsp_box m a v p q t la lm /\
     moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22 /\
     simplicial_subcomplex y t /\ combinatorial_manifold_with_boundary 3 y /\
     la SUBSET y /\ complex_boundary y = UNIONS m UNION B /\ closed B /\
     DISJOINT B (derived_nbhd t la) /\
     a1 UNION a2 = aa UNION aa' /\ DISJOINT aa aa' /\ closed aa /\ closed aa' /\
     j1 UNION j2 = J UNION J' /\ DISJOINT J J' /\ closed J /\ closed J' /\
     pl_annulus_with_ends aa q1 q2 /\ J SUBSET aa DIFF (q1 UNION q2) /\ pl_sphere 1 J /\
     (k11 UNION k12 UNION k21 UNION k22) INTER aa = q1 UNION q2 /\
     x0 IN J
     ==> ?Z0 Z1 Z2 (m1:real^3) m2.
           connected Z0 /\ Z0 SUBSET derived_frontier t la DIFF UNIONS m /\
           Z0 INTER UNIONS y = {} /\ m1 IN closure Z0 /\ m2 IN closure Z0 /\
           connected Z1 /\ Z1 SUBSET (derived_frontier t la DIFF UNIONS m) INTER UNIONS y /\
           m1 IN closure Z1 /\
           connected Z2 /\ Z2 SUBSET (derived_frontier t la DIFF UNIONS m) INTER UNIONS y /\
           m2 IN closure Z2 /\
           ~(m1 IN q1 /\ m2 IN q1) /\ ~(m1 IN q2 /\ m2 IN q2) /\
           m1 IN q1 UNION q2 /\ m2 IN q1 UNION q2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `v:real^3->bool`;
                 `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `y:(real^3->bool)->bool`; `B:real^3->bool`] MOI_FSN_CUT_CTX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `v:real^3->bool`;
                 `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSN_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_FSN_M_COMPL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C0:(real^3->bool)->bool` (X_CHOOSE_THEN `A1:(real^3->bool)->bool`
    (X_CHOOSE_THEN `A12:(real^3->bool)->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(SPEC_ALL MOI_FSN_TRACES) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m a v p q t la (lm:(real^3->bool)->bool)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsn_ends] o check (fun th ->
    can (term_match []
      `moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 (k22:real^3->bool)`)
      (concl th))) THEN
  ABBREV_TAC `jj = j1 UNION (j2:real^3->bool)` THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> concl th = `jj = J UNION (J':real^3->bool)`)) THEN
  ABBREV_TAC `TT = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  ABBREV_TAC `ldT = barycentric_subdivision (barycentric_subdivision (la:(real^3->bool)->bool))` THEN
  ABBREV_TAC `lmT = barycentric_subdivision (barycentric_subdivision (lm:(real^3->bool)->bool))` THEN
  ABBREV_TAC `yT = barycentric_subdivision (barycentric_subdivision (y:(real^3->bool)->bool))` THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN DISCH_THEN(STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `lf_simplicial_complex (ldT:(real^3->bool)->bool) /\
                lf_simplicial_complex (lmT:(real^3->bool)->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
    EXISTS_TAC `TT:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS la INTER UNIONS lm = (jj:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x0:real^3) IN jj /\ (J:real^3->bool) SUBSET jj /\ ~(jj:real^3->bool = {})`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`J UNION J' = (jj:real^3->bool)`; `(x0:real^3) IN J`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the second derived of la: a combinatorial annulus with boundary jj *)
  SUBGOAL_THEN `FINITE (ldT:(real^3->bool)->bool) /\ FINITE (lmT:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["ldT"; "lmT"] THEN
    ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 2 (ldT:(real^3->bool)->bool) /\
                surface_boundary ldT = (jj:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`A1:(real^3->bool)->bool`; `k11:real^3->bool`; `k12:real^3->bool`;
                   `ldT:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
      MOI_FSN_ANN_COMPLEX_REF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
      DISCH_THEN(fun th -> REWRITE_TAC[th; ASSUME `j1 UNION j2 = (jj:real^3->bool)`])];
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
  SUBGOAL_THEN `!w. {w} IN TT /\ w IN jj ==> pl_sphere 2 (UNIONS (simplicial_link TT (w:real^3)))`
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
     [`(w:real^3) IN jj`; `a INTER UNIONS m = (jj:real^3->bool)`;
      `a UNION UNIONS m SUBSET interval(p:real^3,q)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `x0:real^3`] MOI_FSN_SIDE_CYCLE_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^3` (X_CHOOSE_THEN `y0:real^3` (X_CHOOSE_THEN `dd:num`
    (X_CHOOSE_THEN `U:num->real^3` (X_CHOOSE_THEN `c0:num` (X_CHOOSE_THEN `r1:num`
    (X_CHOOSE_THEN `r2:num` STRIP_ASSUME_TAC))))))) THEN
  (* the edge lies on the rim J *)
  SUBGOAL_THEN `segment[v0:real^3,y0] SUBSET J` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`segment[v0:real^3,y0]`; `J:real^3->bool`; `J':real^3->bool`;
                   `{}:real^3->bool`] MOI_FSN_CONN_PIECE) THEN
    REWRITE_TAC[CONNECTED_SEGMENT; INTER_EMPTY; ASSUME `closed (J:real^3->bool)`;
                ASSUME `closed (J':real^3->bool)`] THEN
    ANTS_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`segment[v0:real^3,y0] SUBSET jj`; `J UNION J' = (jj:real^3->bool)`;
        `DISJOINT (J:real^3->bool) J'`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(x0:real^3) IN segment[v0,y0]` THEN UNDISCH_TAC `(x0:real^3) IN J` THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* simplices of the fan are in the neighbourhood *)
  SUBGOAL_THEN `(v0:real^3) IN a /\ (y0:real^3) IN a /\ v0 IN UNIONS m /\ y0 IN UNIONS m`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `segment[v0:real^3,y0] SUBSET jj` THEN
    UNDISCH_TAC `a INTER UNIONS m = (jj:real^3->bool)` THEN
    MP_TAC(ISPECL [`v0:real^3`; `y0:real^3`] ENDS_IN_SEGMENT) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. convex hull {v0,y0,(U:num->real^3) i,U(SUC i)} SUBSET derived_nbhd t la`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[derived_nbhd] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^3->bool) IN c ==> s SUBSET UNIONS c`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `v0:real^3` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. segment[(U:num->real^3) i,U(SUC i)] IN derived_nbhd_complex t la /\
                    {(U:num->real^3) i} IN derived_nbhd_complex t la`
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
      `!i. convex hull {v0,y0,(U:num->real^3) i,U(SUC i)} SUBSET derived_nbhd t la`)) THEN
    UNDISCH_TAC `DISJOINT B (derived_nbhd t (la:(real^3->bool)->bool))` THEN
    UNDISCH_TAC `segment[(U:num->real^3) i,U(SUC i)] SUBSET convex hull {v0, y0, U i, U(SUC i)}` THEN
    REWRITE_TAC[DISJOINT] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
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
        (~((U:num->real^3) i IN a) /\ ~(U(SUC i) IN a)
         ==> segment[U i,U(SUC i)] INTER a = {})`
  (LABEL_TAC "SF") THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                   `(U:num->real^3) i`; `(U:num->real^3) (SUC i)`] MOI_FSP_SEG_FULL) THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision (la:(real^3->bool)->bool)`;
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
    (!i. ~((U:num->real^3) i IN a) /\ ~(U(SUC i) IN a)
         ==> segment[U i,U(SUC i)] SUBSET derived_frontier t la)`
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
     [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
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
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                     `(U:num->real^3) (c0 + r2)`; `(U:num->real^3) (SUC(c0 + r2))`]
        MOI_FSP_NO_CROSS) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `SUC(c0 + r2) = c0 + dd` SUBST1_TAC THENL [MOI_FSP_NUM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^3) c0 IN UNIONS y` ASSUME_TAC THENL
   [UNDISCH_TAC `(U:num->real^3) c0 IN a` THEN
    UNDISCH_TAC `UNIONS la = (a:real^3->bool)` THEN
    UNDISCH_TAC `la SUBSET (y:(real^3->bool)->bool)` THEN SET_TAC[];
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
  MP_TAC(ISPECL [`derived_frontier t (la:(real^3->bool)->bool)`; `UNIONS (m:(real^3->bool)->bool)`;
                 `B:real^3->bool`; `UNIONS (y:(real^3->bool)->bool)`; `a:real^3->bool`;
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
  (* the two triangles of M at the edge lie in the trace annulus aa *)
  SUBGOAL_THEN `convex hull {v0,y0,(U:num->real^3)(c0 + r2)} SUBSET UNIONS m` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                   `{v0:real^3,y0,(U:num->real^3)(c0 + r2)}`] MOI_FSP_HULL_FULL) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(aa:real^3->bool) SUBSET UNIONS m /\
                derived_nbhd t la INTER UNIONS m = aa UNION (aa':real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`derived_nbhd t la INTER UNIONS m = a1 UNION (a2:real^3->bool)`;
      `a1 UNION a2 = aa UNION (aa':real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. convex hull {v0,y0,(U:num->real^3) k} SUBSET UNIONS m
                    ==> convex hull {v0,y0,(U:num->real^3) k} SUBSET aa`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_ASSUM((fun th -> STRIP_ASSUME_TAC(SPEC `k:num` th)) o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `aff_dim:(real^3->bool)->int`)) (concl th))) THEN
    MP_TAC(SPEC `k:num` (ASSUME
      `!i. convex hull {v0,y0,(U:num->real^3) i,U(SUC i)} SUBSET derived_nbhd t la`)) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`convex hull {v0,y0,(U:num->real^3) k}`; `aa:real^3->bool`;
                   `aa':real^3->bool`; `{}:real^3->bool`] MOI_FSN_CONN_PIECE) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[INTER_EMPTY; ASSUME `closed (aa:real^3->bool)`;
                  ASSUME `closed (aa':real^3->bool)`] THEN
      SIMP_TAC[CONVEX_CONNECTED; CONVEX_CONVEX_HULL] THEN
      MAP_EVERY UNDISCH_TAC
       [`convex hull {v0,y0,(U:num->real^3) k} SUBSET convex hull {v0,y0,U k,U(SUC k)}`;
        `convex hull {v0,y0,(U:num->real^3) k,U(SUC k)} SUBSET derived_nbhd t la`;
        `convex hull {v0,y0,(U:num->real^3) k} SUBSET UNIONS m`;
        `derived_nbhd t la INTER UNIONS m = aa UNION (aa':real^3->bool)`;
        `DISJOINT (aa:real^3->bool) aa'`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
    MP_TAC(ISPECL [`v0:real^3`; `y0:real^3`] ENDS_IN_SEGMENT) THEN
    MAP_EVERY UNDISCH_TAC
     [`segment[v0:real^3,y0] SUBSET J`; `(J:real^3->bool) SUBSET aa DIFF (q1 UNION q2)`;
      `segment[v0:real^3,y0] SUBSET convex hull {v0,y0,(U:num->real^3) k}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {v0,y0,(U:num->real^3)(c0 + r1)} SUBSET aa /\
                convex hull {v0,y0,(U:num->real^3)(c0 + r2)} SUBSET aa`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(ASSUME
     `!k. convex hull {v0,y0,(U:num->real^3) k} SUBSET UNIONS m
          ==> convex hull {v0,y0,(U:num->real^3) k} SUBSET aa`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (q1:real^3->bool) /\ pl_sphere 1 (q2:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S5C_ANN_END_SPHERES THEN EXISTS_TAC `aa:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `convex hull {vec 0:real^3, basis 1, basis 2}` THEN
    REWRITE_TAC[MOI_S5C_SIMPLEX2_R3];
    ALL_TAC] THEN
  (* the 2D fact at the edge *)
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `aa:real^3->bool`; `q1:real^3->bool`; `q2:real^3->bool`; `J:real^3->bool`;
                 `v0:real^3`; `y0:real^3`;
                 `(U:num->real^3)(c0 + r1)`; `(U:num->real^3)(c0 + r2)`] MOI_FSN_SIDE_2D_GEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* cycle points off a are in the frontier, so the two points are on the ends *)
  SUBGOAL_THEN `!i. ~((U:num->real^3) i IN a) ==> U i IN derived_frontier t la` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `{(U:num->real^3) i}`] MOI_FSP_NC_FR) THEN
    ASM_REWRITE_TAC[] THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `~((U:num->real^3) i IN a)` THEN SET_TAC[];
      REWRITE_TAC[SING_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^3)(c0 + r1) IN q1 UNION q2 /\ (U:num->real^3)(c0 + r2) IN q1 UNION q2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(SPEC `c0 + r1:num` (ASSUME
      `!i. ~((U:num->real^3) i IN a) ==> U i IN derived_frontier t la`)) THEN
    MP_TAC(SPEC `c0 + r2:num` (ASSUME
      `!i. ~((U:num->real^3) i IN a) ==> U i IN derived_frontier t la`)) THEN
    MP_TAC(ISPECL [`convex:(real^3->bool)->bool`; `{v0:real^3,y0,(U:num->real^3)(c0 + r1)}`]
      HULL_SUBSET) THEN
    MP_TAC(ISPECL [`convex:(real^3->bool)->bool`; `{v0:real^3,y0,(U:num->real^3)(c0 + r2)}`]
      HULL_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`derived_frontier t la INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
      `(k11 UNION k12 UNION k21 UNION k22) INTER aa = q1 UNION (q2:real^3->bool)`;
      `convex hull {v0,y0,(U:num->real^3)(c0 + r1)} SUBSET aa`;
      `convex hull {v0,y0,(U:num->real^3)(c0 + r2)} SUBSET aa`;
      `~((U:num->real^3)(c0 + r1) IN a)`; `~((U:num->real^3)(c0 + r2) IN a)`;
      `(U:num->real^3)(c0 + r1) IN UNIONS m`; `(U:num->real^3)(c0 + r2) IN UNIONS m`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`Z0:real^3->bool`; `Z1:real^3->bool`; `Z2:real^3->bool`;
                        `(U:num->real^3)(c0 + r1)`; `(U:num->real^3)(c0 + r2)`] THEN
  REWRITE_TAC[SYM(ASSUME `derived_frontier t la = b1 UNION b2 UNION c1 UNION (c2:real^3->bool)`)] THEN
  REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC);;

(* ========================================================================= *)
(* The cut along N for the annulus.  The side lemma (the part of F           *)
(* off M inside a 3-manifold y with M in its boundary is the union of the   *)
(* parallel annuli b1, b2 minus the ends), and the cut complex of y along N *)
(* with its boundary ((M UNION B) - N) UNION b1 UNION b2.                    *)
(* ========================================================================= *)

(* The side lemma for the annulus: the part of F off M inside y is the      *)
(* union of the parallel annuli b1, b2 minus the four ends.                 *)

let MOI_FSN_CUT_SIDE = prove
 (`!(m:(real^3->bool)->bool) a j1 j2 v p q t la lm a1 a2 b1 b2 c1 c2 k11 k12 k21 k22 y B.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     moi_fsp_box m a v p q t la lm /\
     moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22 /\
     simplicial_subcomplex y t /\ combinatorial_manifold_with_boundary 3 y /\
     la SUBSET y /\ complex_boundary y = UNIONS m UNION B /\ closed B /\
     DISJOINT B (derived_nbhd t la)
     ==> (derived_frontier t la DIFF UNIONS m) INTER UNIONS y =
         (b1 UNION b2) DIFF (k11 UNION k12 UNION k21 UNION k22)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `v:real^3->bool`;
                 `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSN_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the rim data *)
  SUBGOAL_THEN
   `DISJOINT (a1:real^3->bool) a2 /\ DISJOINT a2 a1 /\ closed a1 /\ closed a2 /\
    closed (j1:real^3->bool) /\ closed j2 /\ DISJOINT j1 j2 /\ DISJOINT j2 j1 /\
    pl_annulus_with_ends a1 k11 k12 /\ pl_annulus_with_ends a2 k21 k22 /\
    j1 SUBSET a1 DIFF (k11 UNION k12) /\ j2 SUBSET a2 DIFF (k21 UNION k22) /\
    pl_sphere 1 j1 /\ pl_sphere 1 j2 /\ ~(j1 = {}) /\ ~(j2 = {}) /\
    (k11 UNION k12 UNION k21 UNION k22) INTER a1 = k11 UNION k12 /\
    (k11 UNION k12 UNION k21 UNION k22) INTER a2 = k21 UNION k22`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsn_ends] o check (fun th ->
      can (term_match []
        `moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 (k22:real^3->bool)`)
        (concl th))) THEN
    MP_TAC(ISPECL [`a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`] MOI_S5C_ANN_PARTS) THEN
    MP_TAC(ISPECL [`a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`] MOI_S5C_ANN_COMPACT) THEN
    MP_TAC(ISPECL [`a1:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`] MOI_S5C_ANN_PARTS) THEN
    MP_TAC(ISPECL [`a2:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`] MOI_S5C_ANN_PARTS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `pl_sphere 1 (j1:real^3->bool) /\ pl_sphere 1 (j2:real^3->bool)`
    STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S5C_ANN_END_SPHERES THEN EXISTS_TAC `a:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `convex hull {vec 0:real^3, basis 1, basis 2}` THEN
      REWRITE_TAC[MOI_S5C_SIMPLEX2_R3];
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; MOI_FSP_SPHERE1_NONEMPTY] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (a1:real^3->bool) a2`; `j1 INTER j2 = {}:real^3->bool`;
      `(k11:real^3->bool) SUBSET a1`; `(k12:real^3->bool) SUBSET a1`;
      `(k21:real^3->bool) SUBSET a2`; `(k22:real^3->bool) SUBSET a2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the witnesses at both rims *)
  SUBGOAL_THEN `?x1:real^3. x1 IN j1` (X_CHOOSE_TAC `x1:real^3`) THENL
   [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `?x2:real^3. x2 IN j2` (X_CHOOSE_TAC `x2:real^3`) THENL
   [ASM_REWRITE_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`; `b1:real^3->bool`; `b2:real^3->bool`;
                 `c1:real^3->bool`; `c2:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`;
                 `k21:real^3->bool`; `k22:real^3->bool`; `y:(real^3->bool)->bool`;
                 `B:real^3->bool`; `a1:real^3->bool`; `a2:real^3->bool`;
                 `k11:real^3->bool`; `k12:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `x1:real^3`] MOI_FSN_SIDE_WIT_AT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE SET_TAC[]); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Z0:real^3->bool` (X_CHOOSE_THEN `Z1:real^3->bool`
    (X_CHOOSE_THEN `Z2:real^3->bool` (X_CHOOSE_THEN `m1:real^3` (X_CHOOSE_THEN `m2:real^3`
    STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`; `b1:real^3->bool`; `b2:real^3->bool`;
                 `c1:real^3->bool`; `c2:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`;
                 `k21:real^3->bool`; `k22:real^3->bool`; `y:(real^3->bool)->bool`;
                 `B:real^3->bool`; `a2:real^3->bool`; `a1:real^3->bool`;
                 `k21:real^3->bool`; `k22:real^3->bool`; `j2:real^3->bool`; `j1:real^3->bool`;
                 `x2:real^3`] MOI_FSN_SIDE_WIT_AT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN (FIRST_ASSUM ACCEPT_TAC ORELSE SET_TAC[]); ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W0:real^3->bool` (X_CHOOSE_THEN `W1:real^3->bool`
    (X_CHOOSE_THEN `W2:real^3->bool` (X_CHOOSE_THEN `n1:real^3` (X_CHOOSE_THEN `n2:real^3`
    STRIP_ASSUME_TAC))))) THEN
  (* the four pieces *)
  SUBGOAL_THEN
   `derived_frontier t la = b1 UNION b2 UNION c1 UNION (c2:real^3->bool) /\
    b1 INTER UNIONS m = k11 UNION (k21:real^3->bool) /\ b2 INTER UNIONS m = k12 UNION k22 /\
    c1 INTER UNIONS m = k11 UNION k12 /\ c2 INTER UNIONS m = k21 UNION k22 /\
    closed b1 /\ closed b2 /\ closed c1 /\ closed c2 /\
    b1 INTER b2 = {} /\ c1 INTER c2 = {} /\
    b1 INTER c1 SUBSET UNIONS m /\ b1 INTER c2 SUBSET UNIONS m /\
    b2 INTER c1 SUBSET UNIONS m /\ b2 INTER c2 SUBSET UNIONS m /\
    connected (b1 DIFF UNIONS m) /\ connected (b2 DIFF UNIONS m) /\
    connected (c1 DIFF UNIONS m) /\ connected (c2 DIFF UNIONS m)`
  MP_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsn_ends] o check (fun th ->
      can (term_match []
        `moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 (k22:real^3->bool)`)
        (concl th))) THEN
    MP_TAC(ISPECL [`b1:real^3->bool`; `k11:real^3->bool`; `k21:real^3->bool`] MOI_S5C_ANN_PARTS) THEN
    MP_TAC(ISPECL [`b2:real^3->bool`; `k12:real^3->bool`; `k22:real^3->bool`] MOI_S5C_ANN_PARTS) THEN
    MP_TAC(ISPECL [`c1:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`] MOI_S5C_ANN_PARTS) THEN
    MP_TAC(ISPECL [`c2:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`] MOI_S5C_ANN_PARTS) THEN
    ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `b1 INTER UNIONS m = k11 UNION (k21:real^3->bool) /\
                  b2 INTER UNIONS m = k12 UNION (k22:real^3->bool) /\
                  c1 INTER UNIONS m = k11 UNION (k12:real^3->bool) /\
                  c2 INTER UNIONS m = k21 UNION (k22:real^3->bool)`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`derived_frontier t la INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
        `derived_frontier t la = b1 UNION b2 UNION c1 UNION (c2:real^3->bool)`;
        `DISJOINT (b1:real^3->bool) b2`; `DISJOINT (c1:real^3->bool) c2`;
        `(k11:real^3->bool) SUBSET b1`; `(k21:real^3->bool) SUBSET b1`;
        `(k12:real^3->bool) SUBSET b2`; `(k22:real^3->bool) SUBSET b2`;
        `(k11:real^3->bool) SUBSET c1`; `(k12:real^3->bool) SUBSET c1`;
        `(k21:real^3->bool) SUBSET c2`; `(k22:real^3->bool) SUBSET c2`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `b1 DIFF UNIONS m = b1 DIFF (k11 UNION (k21:real^3->bool)) /\
                  b2 DIFF UNIONS m = b2 DIFF (k12 UNION (k22:real^3->bool)) /\
                  c1 DIFF UNIONS m = c1 DIFF (k11 UNION (k12:real^3->bool)) /\
                  c2 DIFF UNIONS m = c2 DIFF (k21 UNION (k22:real^3->bool))`
    (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC
       [`b1 INTER UNIONS m = k11 UNION (k21:real^3->bool)`;
        `b2 INTER UNIONS m = k12 UNION (k22:real^3->bool)`;
        `c1 INTER UNIONS m = k11 UNION (k12:real^3->bool)`;
        `c2 INTER UNIONS m = k21 UNION (k22:real^3->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (b1:real^3->bool) b2`; `DISJOINT (c1:real^3->bool) c2`;
      `b1 INTER c1 = k11:real^3->bool`; `b1 INTER c2 = k21:real^3->bool`;
      `b2 INTER c1 = k12:real^3->bool`; `b2 INTER c2 = k22:real^3->bool`;
      `derived_frontier t la INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`] THEN
    SET_TAC[];
    STRIP_TAC] THEN
  (* the side principle *)
  SUBGOAL_THEN `lf_simplicial_complex (y:(real^3->bool)->bool) /\ FINITE y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
    UNDISCH_TAC `moi_fsp_box m a v p q t la (lm:(real^3->bool)->bool)` THEN
    REWRITE_TAC[moi_fsp_box] THEN STRIP_TAC THEN
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `frontier (UNIONS y) = UNIONS m UNION (B:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `y:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!S. connected S /\ S SUBSET derived_frontier t la DIFF UNIONS m
                    ==> S SUBSET UNIONS (y:(real^3->bool)->bool) \/ S INTER UNIONS y = {}`
  ASSUME_TAC THENL
   [X_GEN_TAC `S:real^3->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> q) ==> p \/ q`) THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`S:real^3->bool`; `UNIONS (y:(real^3->bool)->bool)`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(S:real^3->bool) SUBSET derived_frontier t la DIFF UNIONS m`;
      `~((S:real^3->bool) SUBSET UNIONS y)`;
      `derived_frontier t la SUBSET derived_nbhd t (la:(real^3->bool)->bool)`;
      `DISJOINT B (derived_nbhd t (la:(real^3->bool)->bool))`] THEN
    REWRITE_TAC[DISJOINT] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`derived_frontier t (la:(real^3->bool)->bool)`; `UNIONS (m:(real^3->bool)->bool)`;
                 `UNIONS (y:(real^3->bool)->bool)`;
                 `b1:real^3->bool`; `b2:real^3->bool`; `c1:real^3->bool`; `c2:real^3->bool`;
                 `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                 `Z0:real^3->bool`; `Z1:real^3->bool`; `Z2:real^3->bool`; `m1:real^3`; `m2:real^3`;
                 `W0:real^3->bool`; `n1:real^3`; `n2:real^3`] MOI_FSN_SIDE_TOP4) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]);;

(* An annulus is the closure of its part off the ends. *)

let MOI_FSN_ANN_CLOSURE = prove
 (`!(e:real^N->bool) e0 e1.
     pl_annulus_with_ends e e0 e1 ==> closure (e DIFF (e0 UNION e1)) = e`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL
     [SET_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP MOI_S5C_ANN_COMPACT th])];
    MP_TAC(ISPECL [`e:real^N->bool`; `e0:real^N->bool`; `e1:real^N->bool`]
      MOI_S5C_ANN_ENDS_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `e DIFF (e0 UNION e1):real^N->bool` CLOSURE_SUBSET) THEN
    SET_TAC[]]);;

(* The cut of a 3-manifold y in the box along N, for the annulus. *)

let MOI_FSN_CUT = prove
 (`!(m:(real^3->bool)->bool) a j1 j2 v p q t la lm a1 a2 b1 b2 c1 c2 k11 k12 k21 k22 y B.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     moi_fsp_box m a v p q t la lm /\
     moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22 /\
     simplicial_subcomplex y t /\ combinatorial_manifold_with_boundary 3 y /\
     la SUBSET y /\ complex_boundary y = UNIONS m UNION B /\ closed B /\
     DISJOINT B (derived_nbhd t la)
     ==> FINITE {s | s IN barycentric_subdivision (barycentric_subdivision y) /\
                     s SUBSET closure (UNIONS y DIFF derived_nbhd t la)} /\
         combinatorial_manifold_with_boundary 3
           {s | s IN barycentric_subdivision (barycentric_subdivision y) /\
                s SUBSET closure (UNIONS y DIFF derived_nbhd t la)} /\
         UNIONS {s | s IN barycentric_subdivision (barycentric_subdivision y) /\
                     s SUBSET closure (UNIONS y DIFF derived_nbhd t la)} =
         closure (UNIONS y DIFF derived_nbhd t la) /\
         complex_boundary
           {s | s IN barycentric_subdivision (barycentric_subdivision y) /\
                s SUBSET closure (UNIONS y DIFF derived_nbhd t la)} =
         ((UNIONS m UNION B) DIFF derived_nbhd t la) UNION b1 UNION b2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`; `b1:real^3->bool`; `b2:real^3->bool`;
                 `c1:real^3->bool`; `c2:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`;
                 `k21:real^3->bool`; `k22:real^3->bool`; `y:(real^3->bool)->bool`;
                 `B:real^3->bool`] MOI_FSN_CUT_SIDE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `v:real^3->bool`;
                 `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSN_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m a v p q t la (lm:(real^3->bool)->bool)`) (concl th))) THEN
  SUBGOAL_THEN `derived_frontier t la INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 (k22:real^3->bool)` THEN
    REWRITE_TAC[moi_fsn_ends] THEN STRIP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (y:(real^3->bool)->bool) /\ FINITE y` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
    ASM_MESON_TAC[FINITE_SUBSET; simplicial_subcomplex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `y:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `la INTER y = (la:(real^3->bool)->bool)` SUBST1_TAC THENL
   [UNDISCH_TAC `la SUBSET (y:(real^3->bool)->bool)` THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `simplicial_subcomplex la (y:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex la (t:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `la SUBSET (y:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`y:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`y:(real^3->bool)->bool`; `la:(real^3->bool)->bool`]
                DERIVED_NBHD_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `yT = barycentric_subdivision (barycentric_subdivision (y:(real^3->bool)->bool))` THEN
  ABBREV_TAC `A = derived_nbhd_complex y (la:(real^3->bool)->bool)` THEN
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
  SUBGOAL_THEN `closure (UNIONS y DIFF derived_nbhd t la) =
                closure (UNIONS yT DIFF UNIONS (A:(real^3->bool)->bool))` SUBST1_TAC THENL
   [AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_subcomplex A (yT:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "A" THEN EXPAND_TAC "yT" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `interior (derived_nbhd t la) =
                derived_nbhd t la DIFF derived_frontier t (la:(real^3->bool)->bool) /\
                closure (interior (derived_nbhd t la)) = derived_nbhd t (la:(real^3->bool)->bool) /\
                frontier (derived_nbhd t la) = derived_frontier t (la:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `derived_nbhd_complex t (la:(real^3->bool)->bool)` MOI_FSP_REG_CLOSED) THEN
    MP_TAC(ISPEC `derived_nbhd_complex t (la:(real^3->bool)->bool)`
                 COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `derived_nbhd t (la:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `C = {s | s IN yT /\ s SUBSET
                        closure (UNIONS yT DIFF UNIONS (A:(real^3->bool)->bool))}` THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3 (C:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC MOI_FSP_COMP_CMWB THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^3) IN k11 UNION k12 UNION k21 UNION k22` ASSUME_TAC THENL
     [SUBGOAL_THEN `~((w:real^3) IN interior (derived_nbhd t la))` ASSUME_TAC THENL
       [DISCH_TAC THEN
        SUBGOAL_THEN `interior (derived_nbhd t la) INTER
                      closure (UNIONS y DIFF derived_nbhd t la INTER UNIONS y) =
                      {}:real^3->bool` MP_TAC THENL
         [SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY; OPEN_INTERIOR] THEN
          MP_TAC(ISPEC `derived_nbhd t (la:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN
          SET_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `(w:real^3) IN interior (derived_nbhd t la)` THEN
        UNDISCH_TAC `(w:real^3) IN closure (UNIONS y DIFF derived_nbhd t la INTER UNIONS y)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY (fun t -> MP_TAC(ASSUME t))
       [`derived_frontier t la INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
        `derived_frontier t la SUBSET derived_nbhd t (la:(real^3->bool)->bool)`;
        `interior (derived_nbhd t la) =
         derived_nbhd t la DIFF derived_frontier t (la:(real^3->bool)->bool)`;
        `DISJOINT B (derived_nbhd t (la:(real^3->bool)->bool))`;
        `(w:real^3) IN UNIONS m UNION B`] THEN
      UNDISCH_TAC `(w:real^3) IN derived_frontier t la INTER UNIONS y UNION
                   (derived_nbhd t la INTER UNIONS y) INTER (UNIONS m UNION B)` THEN
      UNDISCH_TAC `~((w:real^3) IN interior (derived_nbhd t la))` THEN SET_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "C" THEN EXPAND_TAC "yT" THEN EXPAND_TAC "A" THEN
    MATCH_MP_TAC MOI_FSN_CUT_CORNER THEN
    MAP_EVERY EXISTS_TAC [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`;
      `j2:real^3->bool`; `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
      `lm:(real^3->bool)->bool`; `a1:real^3->bool`; `a2:real^3->bool`;
      `b1:real^3->bool`; `b2:real^3->bool`; `c1:real^3->bool`; `c2:real^3->bool`;
      `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
      `B:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (C:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS C = closure (UNIONS yT DIFF UNIONS (A:(real^3->bool)->bool))`
  ASSUME_TAC THENL [EXPAND_TAC "C" THEN ASM_SIMP_TAC[MOI_FSP_COMP_UNIONS2]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `C:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `UNIONS y DIFF derived_nbhd t la INTER UNIONS y =
                UNIONS y DIFF derived_nbhd t (la:(real^3->bool)->bool)` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  (* the frontier of the cut *)
  SUBGOAL_THEN `frontier (UNIONS y) = UNIONS m UNION (B:real^3->bool) /\ closed (UNIONS y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPEC `y:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[MOI_FM3_LF_COMPACT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_annulus_with_ends (b1:real^3->bool) k11 k21 /\ pl_annulus_with_ends (b2:real^3->bool) k12 k22 /\
    DISJOINT b1 b2 /\ derived_frontier t la = b1 UNION b2 UNION c1 UNION (c2:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 (k22:real^3->bool)` THEN
    REWRITE_TAC[moi_fsn_ends] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S5C_ANN_ENDS_SUBSET
    (ASSUME `pl_annulus_with_ends (b1:real^3->bool) k11 k21`)) THEN
  MP_TAC(MATCH_MP MOI_S5C_ANN_ENDS_SUBSET
    (ASSUME `pl_annulus_with_ends (b2:real^3->bool) k12 k22`)) THEN
  MP_TAC(MATCH_MP MOI_FSN_ANN_CLOSURE
    (ASSUME `pl_annulus_with_ends (b1:real^3->bool) k11 k21`)) THEN
  MP_TAC(MATCH_MP MOI_FSN_ANN_CLOSURE
    (ASSUME `pl_annulus_with_ends (b2:real^3->bool) k12 k22`)) THEN
  REPEAT DISCH_TAC THEN
  MP_TAC(ISPECL [`UNIONS (y:(real^3->bool)->bool)`; `derived_nbhd t (la:(real^3->bool)->bool)`;
                 `derived_frontier t (la:(real^3->bool)->bool)`; `UNIONS (m:(real^3->bool)->bool)`;
                 `B:real^3->bool`; `b1:real^3->bool`; `b2:real^3->bool`;
                 `k11 UNION (k21:real^3->bool)`; `k12 UNION (k22:real^3->bool)`]
    MOI_FSP_CUT_FRONTIER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN NO_TAC) THEN
    MAP_EVERY UNDISCH_TAC
     [`derived_frontier t la INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
      `(derived_frontier t la DIFF UNIONS m) INTER UNIONS y =
       (b1 UNION b2) DIFF (k11 UNION k12 UNION k21 UNION (k22:real^3->bool))`;
      `derived_frontier t la = b1 UNION b2 UNION c1 UNION (c2:real^3->bool)`;
      `DISJOINT (b1:real^3->bool) b2`;
      `(k11:real^3->bool) SUBSET b1 /\ k21 SUBSET b1`;
      `(k12:real^3->bool) SUBSET b2 /\ k22 SUBSET b2`] THEN
    SET_TAC[];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* The x-clause.  Case a SUBSET X: x' is the cut of X along N.              *)
(* Case a meets X only in its ends: Y is the closed complement of X in the  *)
(* box, Y' its cut, and x' the closed complement of Y' in the box, which is *)
(* X UNION N.  (As in pc_moi_fnd_split.)                                     *)
(* ========================================================================= *)

(* The annulus either lies in X or meets it only in its ends, when M is the *)
(* frontier of the closed set X (as MOI_FSP_X_CASES).                        *)

let MOI_FSN_X_CASES = prove
 (`!(a:real^N->bool) j1 j2 X M.
     pl_annulus_with_ends a j1 j2 /\ a INTER M = j1 UNION j2 /\ closed X /\ frontier X = M
     ==> a SUBSET X \/ a INTER X = j1 UNION j2`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S5C_ANN_PARTS) THEN
  SUBGOAL_THEN `(M:real^N->bool) SUBSET X` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `frontier (X:real^N->bool)`)) THEN
    ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED];
    ALL_TAC] THEN
  ASM_CASES_TAC `(a DIFF (j1 UNION j2)) INTER (X:real^N->bool) = {}` THENL
   [DISJ2_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(a DIFF (j1 UNION j2)) INTER (X:real^N->bool) = {}`;
      `a INTER M = j1 UNION (j2:real^N->bool)`; `(M:real^N->bool) SUBSET X`;
      `(j1:real^N->bool) SUBSET a`; `(j2:real^N->bool) SUBSET a`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISJ1_TAC THEN
  SUBGOAL_THEN `a DIFF (j1 UNION j2) SUBSET (X:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a DIFF (j1 UNION j2):real^N->bool`; `X:real^N->bool`]
      CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [UNDISCH_TAC `~(a DIFF (j1 UNION j2) SUBSET (X:real^N->bool))` THEN SET_TAC[];
      UNDISCH_TAC `a INTER M = j1 UNION (j2:real^N->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP MOI_FSN_ANN_CLOSURE) THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]);;

(* Facts shared by both cases of the x-clause.                               *)

let MOI_FSN_X_CONTEXT = prove
 (`!(m:(real^3->bool)->bool) a j1 j2 v p q t la lm x.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     moi_fsp_box m a v p q t la lm /\
     FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
     frontier (UNIONS x) = UNIONS m
     ==> UNIONS x SUBSET interval(p,q) /\ compact (UNIONS x) /\
         closure (interior (UNIONS x)) = UNIONS x /\
         simplicial_subcomplex {s | s IN t /\ s SUBSET UNIONS x} t /\
         UNIONS {s | s IN t /\ s SUBSET UNIONS x} = UNIONS x /\
         FINITE {s | s IN t /\ s SUBSET UNIONS x} /\
         combinatorial_manifold_with_boundary 3 {s | s IN t /\ s SUBSET UNIONS x} /\
         complex_boundary {s | s IN t /\ s SUBSET UNIONS x} = UNIONS m /\
         closure (interior (derived_nbhd t la)) = derived_nbhd t la /\
         interior (derived_nbhd t la) = derived_nbhd t la DIFF derived_frontier t la /\
         a SUBSET interior (derived_nbhd t la) /\
         (a SUBSET UNIONS x \/ a INTER UNIONS x = j1 UNION j2) /\
         ~(a SUBSET UNIONS x /\ a INTER UNIONS x = j1 UNION j2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `v:real^3->bool`;
                 `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSN_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_fsp_box m a v p q t la (lm:(real^3->bool)->bool)` THEN
  REWRITE_TAC[moi_fsp_box] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (x:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS x:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[MOI_FM3_LF_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS x SUBSET interval(p:real^3,q)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSP_X_IN_BOX THEN EXISTS_TAC `UNIONS m:real^3->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    UNDISCH_TAC `a UNION UNIONS m SUBSET interval(p:real^3,q)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `x:(real^3->bool)->bool`] MOI_FSP_XCX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`p:real^3`; `q:real^3`]
      INTERVAL_OPEN_SUBSET_CLOSED) THEN
    UNDISCH_TAC `UNIONS x SUBSET interval(p:real^3,q)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` MOI_FSP_REG_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `derived_nbhd_complex t (la:(real^3->bool)->bool)` MOI_FSP_REG_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `interior (derived_nbhd t la) =
                derived_nbhd t la DIFF derived_frontier t (la:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `derived_nbhd_complex t (la:(real^3->bool)->bool)`
                 COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    MP_TAC(ISPEC `derived_nbhd t (la:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`a INTER derived_frontier t la = {}:real^3->bool`;
      `a SUBSET derived_nbhd t (la:(real^3->bool)->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FSN_X_CASES THEN EXISTS_TAC `UNIONS m:real^3->bool` THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP MOI_S5C_ANN_PARTS (ASSUME `pl_annulus_with_ends (a:real^3->bool) j1 j2`)) THEN
  SET_TAC[]);;

(* Case a SUBSET X: x' is the cut of X along N.                              *)

let MOI_FSN_XCASE_B = prove
 (`!(m:(real^3->bool)->bool) a j1 j2 v p q t la lm a1 a2 b1 b2 c1 c2 k11 k12 k21 k22 x.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     moi_fsp_box m a v p q t la lm /\
     moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22 /\
     FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
     frontier (UNIONS x) = UNIONS m /\ a SUBSET UNIONS x
     ==> ?x':(real^3->bool)->bool.
           FINITE x' /\ combinatorial_manifold_with_boundary 3 x' /\
           frontier (UNIONS x') =
           (UNIONS m DIFF (derived_nbhd t la INTER UNIONS m)) UNION b1 UNION b2 /\
           (UNIONS x DIFF UNIONS x') UNION (UNIONS x' DIFF UNIONS x) SUBSET v /\
           UNIONS x' SUBSET UNIONS x /\ DISJOINT a (UNIONS x')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `x:(real^3->bool)->bool`] MOI_FSN_X_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `v:real^3->bool`;
                 `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSN_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `xt = {s | s IN t /\ s SUBSET UNIONS (x:(real^3->bool)->bool)}` THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`; `b1:real^3->bool`; `b2:real^3->bool`;
                 `c1:real^3->bool`; `c2:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`;
                 `k21:real^3->bool`; `k22:real^3->bool`;
                 `xt:(real^3->bool)->bool`; `{}:real^3->bool`] MOI_FSN_CUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[UNION_EMPTY; CLOSED_EMPTY; DISJOINT_EMPTY] THEN
    UNDISCH_TAC `moi_fsp_box m a v p q t la (lm:(real^3->bool)->bool)` THEN
    REWRITE_TAC[moi_fsp_box] THEN STRIP_TAC THEN
    EXPAND_TAC "xt" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
      UNDISCH_TAC `a SUBSET UNIONS (x:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `UNIONS la = (a:real^3->bool)` THEN
      UNDISCH_TAC `(s:real^3->bool) IN la` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[UNION_EMPTY] THEN
  ABBREV_TAC `cx = {s | s IN barycentric_subdivision (barycentric_subdivision xt) /\
                        s SUBSET closure (UNIONS x DIFF derived_nbhd t (la:(real^3->bool)->bool))}` THEN
  STRIP_TAC THEN EXISTS_TAC `cx:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `cx:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closure (UNIONS x DIFF derived_nbhd t la) SUBSET
                UNIONS (x:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure (UNIONS x DIFF derived_nbhd t la) SUBSET
                (:real^3) DIFF interior (derived_nbhd t (la:(real^3->bool)->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN
    SIMP_TAC[GSYM OPEN_CLOSED; OPEN_INTERIOR] THEN
    MP_TAC(ISPEC `derived_nbhd t (la:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    MP_TAC(ISPEC `UNIONS x DIFF derived_nbhd t (la:(real^3->bool)->bool)` CLOSURE_SUBSET) THEN
    UNDISCH_TAC `derived_nbhd t la SUBSET v INTER interval(p:real^3,q)` THEN
    UNDISCH_TAC `closure (UNIONS x DIFF derived_nbhd t la) SUBSET
                 UNIONS (x:(real^3->bool)->bool)` THEN
    SET_TAC[];
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `a SUBSET interior (derived_nbhd t (la:(real^3->bool)->bool))` THEN
    UNDISCH_TAC `closure (UNIONS x DIFF derived_nbhd t la) SUBSET
                 (:real^3) DIFF interior (derived_nbhd t (la:(real^3->bool)->bool))` THEN
    SET_TAC[]]);;

(* Case a INTER X = j1 UNION j2: x' is the closed complement in the box   *)
(* of the cut of the closed complement of X.                               *)

let MOI_FSN_XCASE_A = prove
 (`!(m:(real^3->bool)->bool) a j1 j2 v p q t la lm a1 a2 b1 b2 c1 c2 k11 k12 k21 k22 x.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     moi_fsp_box m a v p q t la lm /\
     moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22 /\
     FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
     frontier (UNIONS x) = UNIONS m /\ a INTER UNIONS x = j1 UNION j2
     ==> ?x':(real^3->bool)->bool.
           FINITE x' /\ combinatorial_manifold_with_boundary 3 x' /\
           frontier (UNIONS x') =
           (UNIONS m DIFF (derived_nbhd t la INTER UNIONS m)) UNION b1 UNION b2 /\
           (UNIONS x DIFF UNIONS x') UNION (UNIONS x' DIFF UNIONS x) SUBSET v /\
           UNIONS x SUBSET UNIONS x' /\ a SUBSET interior (UNIONS x')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `x:(real^3->bool)->bool`] MOI_FSN_X_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `v:real^3->bool`;
                 `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSN_N_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsp_box] o check (fun th ->
    can (term_match [] `moi_fsp_box m a v p q t la (lm:(real^3->bool)->bool)`) (concl th))) THEN
  ABBREV_TAC `X = UNIONS (x:(real^3->bool)->bool)` THEN
  ABBREV_TAC `N = derived_nbhd t (la:(real^3->bool)->bool)` THEN
  ABBREV_TAC `xt = {s | s IN t /\ s SUBSET (X:real^3->bool)}` THEN
  ABBREV_TAC `yA = {s | s IN t /\ s SUBSET closure (UNIONS t DIFF UNIONS (xt:(real^3->bool)->bool))}` THEN
  SUBGOAL_THEN `interior (interval[p:real^3,q]) = interval(p,q)` ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL]; ALL_TAC] THEN
  (* the closed complement Y of X in the box *)
  SUBGOAL_THEN
   `simplicial_subcomplex yA (t:(real^3->bool)->bool) /\
    UNIONS yA = closure (interval[p,q] DIFF X) /\ FINITE yA /\
    combinatorial_manifold_with_boundary 3 yA /\
    complex_boundary yA = UNIONS m UNION (interval[p,q] DIFF interval(p:real^3,q)) /\
    closure (interval[p,q] DIFF X) = interval[p,q] DIFF interior X`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `simplicial_subcomplex yA (t:(real^3->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "yA" THEN MATCH_MP_TAC MOI_FSP_COMP_SUBCX THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `UNIONS yA = closure (interval[p,q] DIFF (X:real^3->bool))` ASSUME_TAC THENL
     [EXPAND_TAC "yA" THEN ASM_SIMP_TAC[MOI_FSP_COMP_UNIONS2]; ALL_TAC] THEN
    SUBGOAL_THEN `FINITE (yA:(real^3->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; simplicial_subcomplex]; ALL_TAC] THEN
    MP_TAC(ISPECL [`X:real^3->bool`; `interval[p:real^3,q]`] MOI_FSP_FRONTIER_COMPL_BOX) THEN
    ASM_SIMP_TAC[CLOSED_INTERVAL; COMPACT_IMP_CLOSED] THEN
    DISCH_THEN(fun th -> let th1 = CONJUNCT1 th and th2 = CONJUNCT2 th in
      ASSUME_TAC th1 THEN ASSUME_TAC (REWRITE_RULE[th1] th2)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `combinatorial_manifold_with_boundary 3 (yA:(real^3->bool)->bool)`
    ASSUME_TAC THENL
     [EXPAND_TAC "yA" THEN MATCH_MP_TAC MOI_FSP_COMP_CMWB THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `(w:real^3) IN UNIONS m` THEN
      UNDISCH_TAC `(w:real^3) IN interval[p,q] DIFF interval(p,q)` THEN
      UNDISCH_TAC `a UNION UNIONS m SUBSET interval(p:real^3,q)` THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `yA:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  (* la lies in Y *)
  SUBGOAL_THEN `la SUBSET (yA:(real^3->bool)->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `a SUBSET closure (interval[p,q] DIFF (X:real^3->bool))` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(MATCH_MP MOI_FSN_ANN_CLOSURE
        (ASSUME `pl_annulus_with_ends (a:real^3->bool) j1 j2`))) THEN
      MATCH_MP_TAC SUBSET_CLOSURE THEN
      MP_TAC(ISPECL [`p:real^3`; `q:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
      UNDISCH_TAC `a UNION UNIONS m SUBSET interval(p:real^3,q)` THEN
      UNDISCH_TAC `a INTER X = j1 UNION (j2:real^3->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "yA" THEN GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `simplicial_subcomplex la (t:(real^3->bool)->bool)`) THEN
      REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `closure (UNIONS t DIFF UNIONS xt) =
                    closure (interval[p,q] DIFF (X:real^3->bool))` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `a:real^3->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `UNIONS la = (a:real^3->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(s:real^3->bool) IN la` THEN SET_TAC[]];
    ALL_TAC] THEN
  (* the cut of Y and its closed complement *)
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`; `b1:real^3->bool`; `b2:real^3->bool`;
                 `c1:real^3->bool`; `c2:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`;
                 `k21:real^3->bool`; `k22:real^3->bool`;
                 `yA:(real^3->bool)->bool`; `interval[p,q] DIFF interval(p:real^3,q)`]
                MOI_FSN_CUT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_INTERVAL; OPEN_INTERVAL];
      UNDISCH_TAC `N SUBSET v INTER interval(p:real^3,q)` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Z = closure ((interval[p,q] DIFF interior X) DIFF (N:real^3->bool))` THEN
  ABBREV_TAC `cy = {s | s IN barycentric_subdivision (barycentric_subdivision yA) /\
                        s SUBSET (Z:real^3->bool)}` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `yA:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `T2 = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  SUBGOAL_THEN `FINITE (T2:(real^3->bool)->bool) /\ combinatorial_manifold_with_boundary 3 T2 /\
                complex_boundary T2 = interval[p,q] DIFF interval(p:real^3,q)`
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
     [REWRITE_TAC[GSYM(ASSUME `closure ((interval[p,q] DIFF interior X) DIFF N) =
                               (Z:real^3->bool)`); CLOSED_CLOSURE];
      MP_TAC(ISPEC `cy:(real^3->bool)->bool` MOI_FSP_REG_CLOSED) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[p,q] DIFF interval(p,q) SUBSET (Z:real^3->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `closure ((interval[p,q] DIFF interior X) DIFF N) =
                               (Z:real^3->bool)`)] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(interval[p,q] DIFF interior X) DIFF (N:real^3->bool)` THEN
    REWRITE_TAC[CLOSURE_SUBSET] THEN
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `X SUBSET interval(p:real^3,q)` THEN
    UNDISCH_TAC `N SUBSET v INTER interval(p:real^3,q)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure (interval[p,q] DIFF Z) = X UNION (N:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN
      ASM_SIMP_TAC[CLOSED_UNION; COMPACT_IMP_CLOSED] THEN
      REWRITE_TAC[GSYM(ASSUME `closure ((interval[p,q] DIFF interior X) DIFF N) =
                               (Z:real^3->bool)`)] THEN
      MP_TAC(ISPEC `(interval[p,q] DIFF interior X) DIFF (N:real^3->bool)` CLOSURE_SUBSET) THEN
      MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(Z:real^3->bool) SUBSET (:real^3) DIFF interior X /\
                  Z SUBSET (:real^3) DIFF interior N` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `closure ((interval[p,q] DIFF interior X) DIFF N) =
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
      MP_TAC(ISPECL [`p:real^3`; `q:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
      UNDISCH_TAC `X SUBSET interval(p:real^3,q)` THEN
      UNDISCH_TAC `(Z:real^3->bool) SUBSET (:real^3) DIFF interior X` THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure (interior N:real^3->bool)` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[SUBSET_REFL]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_CLOSURE THEN
      MP_TAC(ISPEC `N:real^3->bool` INTERIOR_SUBSET) THEN
      MP_TAC(ISPECL [`p:real^3`; `q:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
      UNDISCH_TAC `N SUBSET v INTER interval(p:real^3,q)` THEN
      UNDISCH_TAC `(Z:real^3->bool) SUBSET (:real^3) DIFF interior N` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS T2 = interval[p:real^3,q] /\ lf_simplicial_complex (T2:(real^3->bool)->bool)`
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
    UNDISCH_TAC `(w:real^3) IN interval[p,q] DIFF interval(p,q)` THEN
    UNDISCH_TAC `(w:real^3) IN X UNION N` THEN
    UNDISCH_TAC `X SUBSET interval(p:real^3,q)` THEN
    UNDISCH_TAC `N SUBSET v INTER interval(p:real^3,q)` THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `xx:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `frontier (X UNION N) = frontier Z INTER interval(p:real^3,q)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM(ASSUME `closure (interval[p,q] DIFF Z) = X UNION (N:real^3->bool)`);
                GSYM(ASSUME `interior (interval[p:real^3,q]) = interval(p,q)`)] THEN
    MATCH_MP_TAC MOI_FSP_FRONTIER_COMP THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `X SUBSET interval(p:real^3,q)` THEN
    UNDISCH_TAC `N SUBSET v INTER interval(p:real^3,q)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `cy:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 (k22:real^3->bool)` THEN
  REWRITE_TAC[moi_fsn_ends] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY (fun t -> MP_TAC(ASSUME t))
     [`derived_frontier t la = b1 UNION b2 UNION c1 UNION (c2:real^3->bool)`;
      `derived_frontier t la SUBSET (N:real^3->bool)`;
      `N SUBSET v INTER interval(p:real^3,q)`;
      `a UNION UNIONS m SUBSET interval(p:real^3,q)`] THEN
    SET_TAC[];
    UNDISCH_TAC `N SUBSET v INTER interval(p:real^3,q)` THEN SET_TAC[];
    SET_TAC[];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior N:real^3->bool` THEN
    REWRITE_TAC[ASSUME `a SUBSET interior (N:real^3->bool)`] THEN
    MATCH_MP_TAC SUBSET_INTERIOR THEN SET_TAC[]]);;

(* The x-clause.                                                              *)

let MOI_FSN_XCLAUSE = prove
 (`!(m:(real^3->bool)->bool) a j1 j2 v p q t la lm a1 a2 b1 b2 c1 c2 k11 k12 k21 k22.
     FINITE m /\ combinatorial_manifold 2 m /\
     pl_annulus_with_ends a j1 j2 /\ a INTER UNIONS m = j1 UNION j2 /\
     moi_fsp_box m a v p q t la lm /\
     moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22
     ==> !x:(real^3->bool)->bool.
           FINITE x /\ combinatorial_manifold_with_boundary 3 x /\
           frontier (UNIONS x) = UNIONS m
           ==> ?x':(real^3->bool)->bool.
                 FINITE x' /\ combinatorial_manifold_with_boundary 3 x' /\
                 frontier (UNIONS x') =
                 (UNIONS m DIFF (derived_nbhd t la INTER UNIONS m)) UNION b1 UNION b2 /\
                 (UNIONS x DIFF UNIONS x') UNION (UNIONS x' DIFF UNIONS x) SUBSET v /\
                 (a SUBSET UNIONS x
                  ==> UNIONS x' SUBSET UNIONS x /\ DISJOINT a (UNIONS x')) /\
                 (a INTER UNIONS x = j1 UNION j2
                  ==> UNIONS x SUBSET UNIONS x' /\ a SUBSET interior (UNIONS x'))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `x:(real^3->bool)->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `x:(real^3->bool)->bool`] MOI_FSN_X_CONTEXT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> let ths = CONJUNCTS th in
    ASSUME_TAC (el 11 ths) THEN ASSUME_TAC (el 12 ths)) THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
   [MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                   `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                   `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                   `a1:real^3->bool`; `a2:real^3->bool`; `b1:real^3->bool`; `b2:real^3->bool`;
                   `c1:real^3->bool`; `c2:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`;
                   `k21:real^3->bool`; `k22:real^3->bool`;
                   `x:(real^3->bool)->bool`] MOI_FSN_XCASE_B) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                   `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                   `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                   `a1:real^3->bool`; `a2:real^3->bool`; `b1:real^3->bool`; `b2:real^3->bool`;
                   `c1:real^3->bool`; `c2:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`;
                   `k21:real^3->bool`; `k22:real^3->bool`;
                   `x:(real^3->bool)->bool`] MOI_FSN_XCASE_A) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `x':(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* The split at an annulus (Moise 33.1 Lemma 4, p.232), from the antecedent  *)
(* MOI_FSN_ANNULUS_NBHD (the structure of the second-derived neighbourhood   *)
(* of the annulus, proved in pc_moi_fnd_annnbhd).                            *)
(* ========================================================================= *)

(* Consequences of the ends predicate used in the conclusion. *)

let MOI_FSN_ENDS_FACTS = prove
 (`!(m:(real^3->bool)->bool) t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22.
     moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 k22
     ==> derived_nbhd t la INTER UNIONS m = a1 UNION a2 /\
         b1 SUBSET derived_frontier t la /\ b2 SUBSET derived_frontier t la /\
         b1 INTER UNIONS m = k11 UNION k21 /\ b2 INTER UNIONS m = k12 UNION k22`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fsn_ends] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`b1:real^3->bool`; `k11:real^3->bool`; `k21:real^3->bool`]
    MOI_S5C_ANN_ENDS_SUBSET) THEN
  MP_TAC(ISPECL [`b2:real^3->bool`; `k12:real^3->bool`; `k22:real^3->bool`]
    MOI_S5C_ANN_ENDS_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`derived_frontier t la INTER UNIONS m = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
    `derived_frontier t la = b1 UNION b2 UNION c1 UNION (c2:real^3->bool)`;
    `DISJOINT (b1:real^3->bool) b2`] THEN
  SET_TAC[]);;

(* The main theorem: the split at an annulus, given MOI_FSN_ANNULUS_NBHD. *)

let SPLIT_ANNULUS_R3_COND = prove
 (mk_imp(MOI_FSN_ANNULUS_NBHD, MOI_FND_SPLIT_ANNULUS_R3),
  DISCH_THEN(LABEL_TAC "NB") THEN
  MAP_EVERY X_GEN_TAC [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`;
                       `j2:real^3->bool`; `v:real^3->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`;
                 `j2:real^3->bool`; `v:real^3->bool`] MOI_FSN_ANN_BOX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3`
    (X_CHOOSE_THEN `t:(real^3->bool)->bool` (X_CHOOSE_THEN `la:(real^3->bool)->bool`
      (X_CHOOSE_THEN `lm:(real^3->bool)->bool` ASSUME_TAC))))) THEN
  USE_THEN "NB" (fun nb ->
    MP_TAC(SPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`;
                  `j2:real^3->bool`; `v:real^3->bool`; `p:real^3`; `q:real^3`;
                  `t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                  `lm:(real^3->bool)->bool`] (MP MOI_FSN_ENDS_EXIST nb))) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^3->bool` (X_CHOOSE_THEN `a2:real^3->bool`
    (X_CHOOSE_THEN `b1:real^3->bool` (X_CHOOSE_THEN `b2:real^3->bool`
    (X_CHOOSE_THEN `c1:real^3->bool` (X_CHOOSE_THEN `c2:real^3->bool`
    (X_CHOOSE_THEN `k11:real^3->bool` (X_CHOOSE_THEN `k12:real^3->bool`
    (X_CHOOSE_THEN `k21:real^3->bool` (X_CHOOSE_THEN `k22:real^3->bool`
      ASSUME_TAC)))))))))) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`; `b1:real^3->bool`; `b2:real^3->bool`;
                 `c1:real^3->bool`; `c2:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`;
                 `k21:real^3->bool`; `k22:real^3->bool`] MOI_FSN_MPRIME) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `v:real^3->bool`;
                 `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSN_N_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`; `a1:real^3->bool`; `a2:real^3->bool`;
                 `b1:real^3->bool`; `b2:real^3->bool`; `c1:real^3->bool`; `c2:real^3->bool`;
                 `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`]
    MOI_FSN_ENDS_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(UNIONS m DIFF (derived_nbhd t la INTER UNIONS m)) UNION b1 UNION b2 =
                UNIONS (m':(real^3->bool)->bool)` (LABEL_TAC "MP") THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `a:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `v:real^3->bool`; `p:real^3`; `q:real^3`; `t:(real^3->bool)->bool`;
                 `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`; `b1:real^3->bool`; `b2:real^3->bool`;
                 `c1:real^3->bool`; `c2:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`;
                 `k21:real^3->bool`; `k22:real^3->bool`] MOI_FSN_XCLAUSE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[]; USE_THEN "MP" (fun th -> REWRITE_TAC[th]) THEN DISCH_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fsn_ends] o check (fun th ->
    can (term_match []
      `moi_fsn_ends m t la j1 j2 a1 a2 b1 b2 c1 c2 k11 k12 k21 (k22:real^3->bool)`)
      (concl th))) THEN
  MAP_EVERY EXISTS_TAC [`a1:real^3->bool`; `a2:real^3->bool`; `b1:real^3->bool`;
                        `b2:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`;
                        `k21:real^3->bool`; `k22:real^3->bool`; `m':(real^3->bool)->bool`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MAP_EVERY UNDISCH_TAC
   [`derived_nbhd t la INTER UNIONS m = a1 UNION (a2:real^3->bool)`;
    `derived_nbhd t la SUBSET v INTER interval(p:real^3,q)`;
    `(b1:real^3->bool) SUBSET derived_frontier t la`;
    `(b2:real^3->bool) SUBSET derived_frontier t la`;
    `derived_frontier t la SUBSET derived_nbhd t (la:(real^3->bool)->bool)`;
    `a INTER derived_frontier t la = {}:real^3->bool`] THEN
  SET_TAC[]);;

