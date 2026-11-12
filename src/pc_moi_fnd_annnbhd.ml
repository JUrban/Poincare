(* ========================================================================= *)
(* pc_moi_fnd_annnbhd: stage 2 of MOI_FND_SPLIT_ANNULUS_R3, the              *)
(* second-derived neighbourhood of an annulus meeting a closed surface in    *)
(* its rims:                                                                 *)
(*   ANNULUS_NBHD : |- MOI_FSN_ANNULUS_NBHD                                  *)
(* (the statement term is in pc_moi_fnd_splitannstmt.ml).  The parts:        *)
(*   generic lemmas (connected splits, frontiers of disjoint unions,         *)
(*       splitting a subcomplex, derived neighbourhoods of disjoint unions); *)
(*   closed combinatorial surfaces in real^3 are orientable, and the         *)
(*       derived neighbourhood of a polygon in one is an annulus;            *)
(*   step A: the two-rim trace;                                              *)
(*   step B: the frontier is a closed surface with Euler number 0;           *)
(*   step C: the sides B and Cc of F minus M and the side surfaces;          *)
(*   the frontier is connected (MOI_FAN_FRONTIER_CONNECTED);                 *)
(*   step D tools: edge cycles, the far vertices W(tau) lie in B;            *)
(*   the Euler count of step E (MOI_FAN_COUNT);                              *)
(*   step D: B is clopen in F minus M, arc paths, adjacent triangles; the    *)
(*       transport of the far vertices along ldT; the rim data (edge,        *)
(*       cycle, positions); the crossing at rim 1 (edge star, int-a side);   *)
(*       rim witnesses, reach of the B-pieces, step D3;                      *)
(*   the final labelling of step E (MOI_FAN_FINAL);                          *)
(*   step E (Euler sum, side annuli) and ANNULUS_NBHD.                       *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_splitannstmt.ml";;
needs "src/pc_moi_fnd_split.ml";;
needs "src/pc_moi_fnd_cbicol.ml";;
needs "src/pc_moi_s26_sep.ml";;
needs "src/pc_moi_fnd_sides.ml";;
needs "src/pc_moi_fnd_tubed.ml";;
needs "src/pc_moi_s33_frame.ml";;
needs "src/pc_moi_s28_plane.ml";;
needs "src/pc_moi_fnd_splitann.ml";;
needs "src/pc_moi_fnd_clsides.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Generic lemmas.                                                           *)
(* ========================================================================= *)

(* A connected set inside the union of two disjoint closed sets lies in one *)
(* of them.                                                                   *)

let MOI_FAN_CONNECTED_SPLIT = prove
 (`!s a b:real^N->bool.
     connected s /\ s SUBSET a UNION b /\ closed a /\ closed b /\ DISJOINT a b
     ==> s SUBSET a \/ s SUBSET b`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [CONNECTED_CLOSED] o
    check (fun th -> concl th = `connected (s:real^N->bool)`)) THEN
  REWRITE_TAC[NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`a:real^N->bool`; `b:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* The frontier of a union of two disjoint closed sets.                      *)

let MOI_FAN_FRONTIER_OF_UNION = prove
 (`!top a b:A->bool.
     closed_in top a /\ closed_in top b /\ DISJOINT a b
     ==> top frontier_of (a UNION b) = top frontier_of a UNION top frontier_of b`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  REWRITE_TAC[FRONTIER_OF_UNION_SUBSET] THEN
  SUBGOAL_THEN
   `!a b:A->bool. closed_in top a /\ closed_in top b /\ DISJOINT a b
                  ==> top frontier_of a SUBSET top frontier_of (a UNION b)`
  (fun th -> REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC th THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[UNION_COMM] THEN MATCH_MP_TAC th THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]) THEN
  MAP_EVERY X_GEN_TAC [`c:A->bool`; `d:A->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[frontier_of] THEN
  ASM_SIMP_TAC[CLOSURE_OF_CLOSED_IN; CLOSED_IN_UNION] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNION] THEN X_GEN_TAC `x:A` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~((x:A) IN d)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[interior_of; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  X_GEN_TAC `u:A->bool` THEN STRIP_TAC THEN
  UNDISCH_TAC `~((x:A) IN top interior_of c)` THEN
  REWRITE_TAC[interior_of; IN_ELIM_THM] THEN
  EXISTS_TAC `u DIFF d:A->bool` THEN ASM_REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_DIFF THEN ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* Splitting a subcomplex whose union is two disjoint closed sets.           *)

let MOI_FAN_RIM_SPLIT = prove
 (`!(m:(real^N->bool)->bool) l j1 j2.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     UNIONS l = j1 UNION j2 /\ closed j1 /\ closed j2 /\ DISJOINT j1 j2
     ==> simplicial_subcomplex {s | s IN l /\ s SUBSET j1} m /\
         simplicial_subcomplex {s | s IN l /\ s SUBSET j2} m /\
         UNIONS {s | s IN l /\ s SUBSET j1} = j1 /\
         UNIONS {s | s IN l /\ s SUBSET j2} = j2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN l ==> s SUBSET j1 \/ s SUBSET j2` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FAN_CONNECTED_SPLIT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN
      SUBGOAL_THEN `(s:real^N->bool) IN m` ASSUME_TAC THENL
       [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
      ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j:real^N->bool. (j = j1 \/ j = j2)
        ==> simplicial_subcomplex {s | s IN l /\ s SUBSET j} m /\
            UNIONS {s | s IN l /\ s SUBSET j} = j`
  (fun th -> MP_TAC(SPEC `j1:real^N->bool` th) THEN MP_TAC(SPEC `j2:real^N->bool` th) THEN
             SIMP_TAC[]) THEN
  X_GEN_TAC `j:real^N->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) m` THEN
    REWRITE_TAC[simplicial_subcomplex; IN_ELIM_THM] THEN STRIP_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[];
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]]];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [MESON_TAC[SUBSET]; ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?s:real^N->bool. s IN l /\ x IN s` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS l = (j1:real^N->bool) UNION j2` THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS; IN_UNION] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
      is_forall(concl th) && is_disj(snd(dest_imp(snd(dest_forall(concl th))))))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* The derived neighbourhood depends only on the union of the subcomplex.   *)

let MOI_FAN_DN_UNION = prove
 (`!(m:(real^N->bool)->bool) l l1 l2.
     UNIONS l = UNIONS l1 UNION UNIONS l2
     ==> derived_nbhd m l = derived_nbhd m l1 UNION derived_nbhd m l2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[derived_nbhd; GSYM UNIONS_UNION] THEN
  AP_TERM_TAC THEN ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_UNION] THEN SET_TAC[]);;

(* Derived neighbourhoods of subcomplexes with disjoint closed unions are    *)
(* disjoint (no simplex of bsd m has vertices in both).                     *)

let MOI_FAN_DN_DISJOINT = prove
 (`!(m:(real^N->bool)->bool) l l1 l2.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     simplicial_subcomplex l1 m /\ simplicial_subcomplex l2 m /\
     UNIONS l = UNIONS l1 UNION UNIONS l2 /\
     closed (UNIONS l1) /\ closed (UNIONS l2) /\ DISJOINT (UNIONS l1) (UNIONS l2)
     ==> DISJOINT (derived_nbhd m l1) (derived_nbhd m l2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l1:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l2:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* no simplex of bsd m contains points of both *)
  SUBGOAL_THEN
   `!r u w:real^N. r IN barycentric_subdivision m /\ u IN r /\ w IN r /\
                   u IN UNIONS l1 /\ w IN UNIONS l2 ==> F`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `r:real^N->bool`] MOI_FRN_FULL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `segment[u:real^N,w] SUBSET UNIONS l1 UNION UNIONS l2` ASSUME_TAC THENL
     [SUBGOAL_THEN `convex (r INTER (UNIONS l1 UNION UNIONS l2):real^N->bool)` MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_CONVEX]; ALL_TAC] THEN
      REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
      DISCH_THEN(MP_TAC o SPECL [`u:real^N`; `w:real^N`]) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`segment[u:real^N,w]`; `UNIONS l1:real^N->bool`;
                   `UNIONS l2:real^N->bool`] MOI_FAN_CONNECTED_SPLIT) THEN
    ASM_REWRITE_TAC[CONNECTED_SEGMENT] THEN
    MP_TAC(ISPECL [`u:real^N`; `w:real^N`] ENDS_IN_SEGMENT) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l1:(real^N->bool)->bool`]
    MOI_FN2_NBHD_STARS) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l2:(real^N->bool)->bool`]
    MOI_FN2_NBHD_STARS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; NOT_IN_EMPTY; IN_INTER] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `A:real^N->bool` (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) ASSUME_TAC))
    (X_CHOOSE_THEN `B:real^N->bool` (CONJUNCTS_THEN2
       (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `(x:real^N) IN
    UNIONS (moi_fm3_cstar (barycentric_subdivision (barycentric_subdivision m)) u) INTER
    UNIONS (moi_fm3_cstar (barycentric_subdivision (barycentric_subdivision m)) w)`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N) IN UNIONS l1 /\ (w:real^N) IN UNIONS l2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(MESON[IN_UNIONS; IN_SING]
      `!x:A u v. {x} IN u /\ UNIONS u = v ==> x IN v`) THENL
     [EXISTS_TAC `barycentric_subdivision l1:(real^N->bool)->bool`;
      EXISTS_TAC `barycentric_subdivision l2:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u:real^N = w)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN barycentric_subdivision m /\ {w} IN barycentric_subdivision m`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision m:(real^N->bool)->bool`; `u:real^N`; `w:real^N`]
    MOI_FN2_STAR_INTER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `moi_fn2_dual (barycentric_subdivision m) (segment[u:real^N,w]) = {}`
  (fun th -> REWRITE_TAC[th; NOT_IN_EMPTY]) THEN
  MATCH_MP_TAC MOI_FN2_DUAL_EMPTY THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:real^N->bool`; `u:real^N`; `w:real^N`] o
    check (fun th -> is_forall(concl th) &&
                     snd(dest_imp(snd(strip_forall(concl th)))) = `F`)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`u:real^N`; `w:real^N`] ENDS_IN_SEGMENT) THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* Closed combinatorial surfaces in real^3 are orientable; the derived       *)
(* neighbourhood of a polygon in one is an annulus whose ends are the        *)
(* derived frontier.                                                         *)
(* ========================================================================= *)

(* A complex whose component subcomplexes are orientable is orientable.     *)

let MOI_FAN_ORIENT_COMPONENTS = prove
 (`!(c:(real^N->bool)->bool).
     lf_simplicial_complex c /\
     (!k. k IN components (UNIONS c)
          ==> orientable_surface_complex {s | s IN c /\ s SUBSET k})
     ==> orientable_surface_complex c`,
  GEN_TAC THEN REWRITE_TAC[orientable_surface_complex] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN
    `sg:(real^N->bool)->real^N->real^N->real^N->real` (LABEL_TAC "SG")) THEN
  EXISTS_TAC `\a b d:real^N.
     (sg:(real^N->bool)->real^N->real^N->real^N->real)
       (connected_component (UNIONS c) a) a b d` THEN
  REWRITE_TAC[] THEN
  (* a triangle of c lies in the component of each of its vertices *)
  SUBGOAL_THEN
   `!a b d:real^N.
       convex hull {a,b,d} IN c
       ==> connected_component (UNIONS c) a IN components (UNIONS c) /\
           convex hull {a,b,d} IN
             {s | s IN c /\ s SUBSET connected_component (UNIONS c) a} /\
           connected_component (UNIONS c) b = connected_component (UNIONS c) a /\
           connected_component (UNIONS c) d = connected_component (UNIONS c) a`
  (LABEL_TAC "CC") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `convex hull {a,b,d} SUBSET UNIONS (c:(real^N->bool)->bool)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^N) IN convex hull {a,b,d} /\ b IN convex hull {a,b,d} /\
                  d IN convex hull {a,b,d}` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    SUBGOAL_THEN `convex hull {a,b,d} SUBSET connected_component (UNIONS c) (a:real^N)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN
      ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_CONVEX_HULL];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[components; IN_ELIM_THM] THEN EXISTS_TAC `a:real^N` THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM];
      MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN ASM SET_TAC[];
      MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "CC" (MP_TAC o SPECL [`a:real^N`; `b:real^N`; `d:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "SG" (MP_TAC o SPEC `connected_component (UNIONS c) (a:real^N)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "CC" (MP_TAC o SPECL [`a:real^N`; `b:real^N`; `d:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "CC" (MP_TAC o SPECL [`a:real^N`; `b:real^N`; `d':real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "SG" (MP_TAC o SPEC `connected_component (UNIONS c) (a:real^N)`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]]);;

(* Closed combinatorial surfaces in real^3 are orientable (Moise 26.8 on    *)
(* each component).                                                          *)

let MOI_FAN_ORIENTABLE_R3 = prove
 (`!s:(real^3->bool)->bool.
     FINITE s /\ combinatorial_manifold 2 s ==> orientable_surface_complex s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(MP MOI_FD_268_GLUE (CONJ SURFACE_SIDES_ORIENTABLE_3
    (MP SEP_266 (CONJ EVEN_CROSSING (CONJ LOCAL_TRI LOCAL_EDGE))))) THEN
  REWRITE_TAC[MOISE_268_STATEMENT] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_FAN_ORIENT_COMPONENTS THEN
  CONJ_TAC THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:(real^3->bool)->bool`; `k:real^3->bool`] MOI_FCL_CM2_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[IN_COMPONENTS_CONNECTED]);;

(* The derived neighbourhood of a polygon in a closed combinatorial surface *)
(* in real^3 is an annulus whose ends are the derived frontier.             *)

let MOI_FAN_BSD_ORIENT = prove
 (`!m:(real^3->bool)->bool.
     FINITE m /\ combinatorial_manifold 2 m /\ ~(m = {})
     ==> orientable_surface_complex (barycentric_subdivision m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `m:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[simplicial_subcomplex; SUBSET_REFL] THEN
    ASM_MESON_TAC[MOI_FM3_LF_FACE];
    STRIP_TAC] THEN
  MATCH_MP_TAC MOI_FCB_ORIENT_REFINE THEN EXISTS_TAC `m:(real^3->bool)->bool` THEN
  ASM_SIMP_TAC[MOI_FAN_ORIENTABLE_R3] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (m:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `FINITE (m:(real^3->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex; simplicial_complex] THEN MESON_TAC[];
    ASM_MESON_TAC[MOI_FSB_DIM; MOI_FBC_CM2_CMWB2];
    UNDISCH_TAC `lf_simplicial_complex (barycentric_subdivision m:(real^3->bool)->bool)` THEN
    MP_TAC(ISPEC `m:(real^3->bool)->bool` MOI_BAR_SUBDIVISION_FINITE) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[lf_simplicial_complex; simplicial_complex] THEN MESON_TAC[];
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^3->bool = {}` THENL
     [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
        check (fun th -> concl th = `~(m:(real^3->bool)->bool = {})`)) THEN
      DISCH_THEN(X_CHOOSE_TAC `s0:real^3->bool`) THEN
      EXISTS_TAC `s0:real^3->bool` THEN ASM_REWRITE_TAC[EMPTY_SUBSET];
      MP_TAC(ISPEC `m:(real^3->bool)->bool` BARYCENTRIC_SUBDIVISION_REFINES) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_FAN_RIM_ANNULUS = prove
 (`!(m:(real^3->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> ?k1 k2. pl_annulus_with_ends (derived_nbhd m l) k1 k2 /\
                 derived_frontier m l = k1 UNION k2 /\
                 UNIONS l SUBSET derived_nbhd m l DIFF (k1 UNION k2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `~(m:(real^3->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `UNIONS (l:(real^3->bool)->bool) = {}` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex (l:(real^3->bool)->bool) m` THEN
      ASM_REWRITE_TAC[simplicial_subcomplex; SUBSET_EMPTY] THEN
      SIMP_TAC[UNIONS_0];
      ASM_MESON_TAC[MOI_FTA_PL_SPHERE_NONEMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `m:(real^3->bool)->bool` MOI_FAN_BSD_ORIENT) THEN
  ASM_REWRITE_TAC[orientable_surface_complex] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg0:real^3->real^3->real^3->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "O1") (LABEL_TAC "O2"))) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
    DERIVED_NBHD_POLYGON_2) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `FINITE (components (derived_nbhd m l DIFF
                                    UNIONS (l:(real^3->bool)->bool)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
      MOI_FN2_COMPONENTS_NL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `barycentric_subdivision (m:(real^3->bool)->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_SUBDIVISION_FINITE THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_frn_vp] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~connected (derived_nbhd m l DIFF UNIONS (l:(real^3->bool)->bool))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                   `\w:real^3. (sg0:real^3->real^3->real^3->real)`] MOI_FSTR_TWO_SIDED) THEN
    BETA_TAC THEN REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [USE_THEN "O1" MATCH_MP_TAC; USE_THEN "O2" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (components (derived_frontier m (l:(real^3->bool)->bool))) = 2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `~(CARD (components (derived_nbhd m l DIFF
                                      UNIONS (l:(real^3->bool)->bool))) = 1)`
    MP_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `components (derived_nbhd m l DIFF
                                UNIONS (l:(real^3->bool)->bool)) HAS_SIZE 1`
      MP_TAC THENL [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
      REWRITE_TAC[COMPONENTS_EQ_SING_EXISTS] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c &&
      (try fst(dest_const(rator(lhs c))) = "CARD" &&
           fst(dest_const(rator(rhs c))) = "CARD" with Failure _ -> false))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    can (find_term (fun u -> is_const u && fst(dest_const u) = "pl_annulus_with_ends"))
        (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^3->bool` (X_CHOOSE_THEN `k2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k1:real^3->bool`; `k2:real^3->bool`] THEN
  REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
     rhs(concl th) = `(k1:real^3->bool) UNION k2`)) THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REWRITE_TAC[derived_frontier; frontier_of] THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS (m:(real^3->bool)->bool))`;
                 `derived_nbhd m (l:(real^3->bool)->bool)`] INTERIOR_OF_SUBSET) THEN
  UNDISCH_TAC `UNIONS (l:(real^3->bool)->bool) SUBSET
               (subtopology euclidean (UNIONS m)) interior_of (derived_nbhd m l)` THEN
  SET_TAC[]);;

(* ========================================================================= *)
(* Step A, the two-rim trace.                                                *)
(* ========================================================================= *)

(* The two-rim trace: N INTER M is two disjoint annuli around the rims,    *)
(* whose ends are the four circles of F INTER M.                           *)

let MOI_FAN_TRACE = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2.
     lf_simplicial_complex t /\
     simplicial_subcomplex la t /\ simplicial_subcomplex lm t /\
     FINITE lm /\ combinatorial_manifold 2 lm /\
     pl_annulus_with_ends (UNIONS la) j1 j2 /\
     UNIONS la INTER UNIONS lm = j1 UNION j2
     ==> ?a1 a2 k11 k12 k21 k22.
           derived_nbhd t la INTER UNIONS lm = a1 UNION a2 /\ DISJOINT a1 a2 /\
           pl_annulus_with_ends a1 k11 k12 /\ pl_annulus_with_ends a2 k21 k22 /\
           j1 SUBSET a1 DIFF (k11 UNION k12) /\ j2 SUBSET a2 DIFF (k21 UNION k22) /\
           derived_frontier t la INTER UNIONS lm = k11 UNION k12 UNION k21 UNION k22 /\
           a1 = derived_nbhd lm {s | s IN la INTER lm /\ s SUBSET j1} /\
           a2 = derived_nbhd lm {s | s IN la INTER lm /\ s SUBSET j2} /\
           derived_frontier lm {s | s IN la INTER lm /\ s SUBSET j1} = k11 UNION k12 /\
           derived_frontier lm {s | s IN la INTER lm /\ s SUBSET j2} = k21 UNION k22`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 SUBST1_TAC SUBST1_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`] MOI_FN2_SUBCOMPLEX_INTER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`UNIONS la:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_FCB_ANN_ENDS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS la:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_S5C_ANN_END_SPHERES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S5C_SIMPLEX2_R3]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `(la:(real^3->bool)->bool) INTER lm`;
                 `j1:real^3->bool`; `j2:real^3->bool`] MOI_FAN_RIM_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; DISJOINT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `l1 = {s | s IN (la:(real^3->bool)->bool) INTER lm /\ s SUBSET j1}` THEN
  ABBREV_TAC `l2 = {s | s IN (la:(real^3->bool)->bool) INTER lm /\ s SUBSET j2}` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l1:(real^3->bool)->bool`] MOI_FAN_RIM_ANNULUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k11:real^3->bool` (X_CHOOSE_THEN `k12:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l2:(real^3->bool)->bool`] MOI_FAN_RIM_ANNULUS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k21:real^3->bool` (X_CHOOSE_THEN `k22:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `UNIONS ((la:(real^3->bool)->bool) INTER lm) =
                UNIONS l1 UNION UNIONS (l2:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `(la:(real^3->bool)->bool) INTER lm`;
                 `l1:(real^3->bool)->bool`; `l2:(real^3->bool)->bool`] MOI_FAN_DN_UNION) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `(la:(real^3->bool)->bool) INTER lm`;
                 `l1:(real^3->bool)->bool`; `l2:(real^3->bool)->bool`] MOI_FAN_DN_DISJOINT) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; DISJOINT]; DISCH_TAC] THEN
  SUBGOAL_THEN
   `derived_frontier lm ((la:(real^3->bool)->bool) INTER lm) =
    derived_frontier lm l1 UNION derived_frontier lm l2`
  ASSUME_TAC THENL
   [REWRITE_TAC[derived_frontier] THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) &&
       lhs(concl th) = `derived_nbhd lm ((la:(real^3->bool)->bool) INTER lm)`
      then REWRITE_TAC[th] else failwith "no") THEN
    MATCH_MP_TAC MOI_FAN_FRONTIER_OF_UNION THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC(MESON[DERIVED_NBHD_BASIC]
     `!t l:(real^3->bool)->bool. lf_simplicial_complex t /\ simplicial_subcomplex l t
         ==> closed_in (subtopology euclidean (UNIONS t)) (derived_nbhd t l)`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`derived_nbhd lm (l1:(real^3->bool)->bool)`; `derived_nbhd lm (l2:(real^3->bool)->bool)`;
    `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`] THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[UNION_ASSOC]]);;

(* ========================================================================= *)
(* Step B, the frontier is a closed surface with Euler number 0.             *)
(* ========================================================================= *)

(* A complex in real^3 whose union is a PL annulus has dimension <= 2       *)
(* (invariance of dimension).                                                *)

let MOI_FAN_LA_DIM = prove
 (`!(la:(real^3->bool)->bool) j1 j2.
     lf_simplicial_complex la /\ pl_annulus_with_ends (UNIONS la) j1 j2
     ==> !s. s IN la ==> aff_dim s <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex (s:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (s:real^3->bool) = &(dimindex(:3))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^3->bool` AFF_DIM_LE_UNIV) THEN
    REWRITE_TAC[DIMINDEX_3] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(interior (s:real^3->bool) = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_NONEMPTY_INTERIOR_EQ]; ALL_TAC] THEN
  UNDISCH_TAC `pl_annulus_with_ends (UNIONS la) (j1:real^3->bool) j2` THEN
  REWRITE_TAC[pl_annulus_with_ends; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_THEN `g:real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `interior s SUBSET UNIONS (la:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^3->bool` THEN
    REWRITE_TAC[INTERIOR_SUBSET] THEN
    MATCH_MP_TAC(SET_RULE `!x:A->bool u. x IN u ==> x SUBSET UNIONS u`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->real^2`; `interior s:real^3->bool`]
    INVARIANCE_OF_DIMENSION) THEN
  REWRITE_TAC[OPEN_INTERIOR; DIMINDEX_2; DIMINDEX_3; ARITH] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[SUBSET]]);;

(* The Euler characteristic of such a complex is 0.                         *)

let MOI_FAN_LA_EULER = prove
 (`!(la:(real^3->bool)->bool) j1 j2.
     FINITE la /\ lf_simplicial_complex la /\ pl_annulus_with_ends (UNIONS la) j1 j2
     ==> complex_euler la = &0`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `la:(real^3->bool)->bool` COMPLEX_EULER_VALUES) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (la:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `FINITE (la:(real^3->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex; simplicial_complex] THEN MESON_TAC[];
      MATCH_MP_TAC MOI_FAN_LA_DIM THEN
      MAP_EVERY EXISTS_TAC [`j1:real^3->bool`; `j2:real^3->bool`] THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(MATCH_MP_TAC o el 4 o CONJUNCTS) THEN
    UNDISCH_TAC `pl_annulus_with_ends (UNIONS la) (j1:real^3->bool) j2` THEN
    REWRITE_TAC[pl_annulus_with_ends; pl_annulus] THEN MESON_TAC[]]);;

(* Step B: K = boundary_complex Nc is a finite closed surface, UNIONS K = F, *)
(* chi K = 0.                                                                 *)

let MOI_FAN_FRONTIER_SURFACE = prove
 (`!(t:(real^3->bool)->bool) la j1 j2.
     FINITE t /\ combinatorial_manifold_with_boundary 3 t /\
     simplicial_subcomplex la t /\
     pl_annulus_with_ends (UNIONS la) j1 j2 /\
     DISJOINT (derived_nbhd t la) (complex_boundary t)
     ==> FINITE (derived_nbhd_complex t la) /\
         combinatorial_manifold_with_boundary 3 (derived_nbhd_complex t la) /\
         complex_boundary (derived_nbhd_complex t la) = derived_frontier t la /\
         FINITE (boundary_complex (derived_nbhd_complex t la)) /\
         combinatorial_manifold 2 (boundary_complex (derived_nbhd_complex t la)) /\
         UNIONS (boundary_complex (derived_nbhd_complex t la)) = derived_frontier t la /\
         simplicial_subcomplex (boundary_complex (derived_nbhd_complex t la))
                               (derived_nbhd_complex t la) /\
         complex_euler (boundary_complex (derived_nbhd_complex t la)) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (la:(real^3->bool)->bool) /\ lf_simplicial_complex la`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; FINITE_SUBSET; MOI_FDN_LF_SUBCOMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`]
    DERIVED_NBHD_COMBINATORIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  SUBGOAL_THEN `derived_nbhd t la INTER complex_boundary (t:(real^3->bool)->bool) = {}`
  (fun th -> REWRITE_TAC[th; UNION_EMPTY]) THENL
   [UNDISCH_TAC `DISJOINT (derived_nbhd t la) (complex_boundary (t:(real^3->bool)->bool))` THEN
    SET_TAC[];
    DISCH_TAC] THEN
  MP_TAC(ISPEC `derived_nbhd_complex t (la:(real^3->bool)->bool)` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `derived_nbhd_complex t (la:(real^3->bool)->bool)` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  MP_TAC(ISPEC `derived_nbhd_complex t (la:(real^3->bool)->bool)` MOI_FTD_EULER_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] MOI_FTD_NBHD_EULER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`la:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_FAN_LA_EULER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Step C: the sides of the surface components through the rims.             *)
(* ------------------------------------------------------------------------- *)

(* Moise 26.6 (from the chain s26_cross, s26_local, s26_sep).                *)

let MOI_FAN_266 = prove
 (`MOISE_266_STATEMENT`,
  ACCEPT_TAC(MP SEP_266 (CONJ EVEN_CROSSING (CONJ LOCAL_TRI LOCAL_EDGE))));;

(* The component of the surface containing a connected set, and the side of *)
(* that component containing another connected set.                         *)

let moi_fan_mc = new_definition
 `moi_fan_mc (lm:(real^3->bool)->bool) (j:real^3->bool) =
    @k. k IN components (UNIONS lm) /\ j SUBSET k`;;

let moi_fan_side = new_definition
 `moi_fan_side (lm:(real^3->bool)->bool) (j:real^3->bool) (X:real^3->bool) =
    @S. S IN components ((:real^3) DIFF moi_fan_mc lm j) /\ X SUBSET S`;;

let moi_fan_far = new_definition
 `moi_fan_far (lm:(real^3->bool)->bool) (j:real^3->bool) (X:real^3->bool) =
    (:real^3) DIFF (moi_fan_mc lm j UNION moi_fan_side lm j X)`;;

let MOI_FAN_MC = prove
 (`!(lm:(real^3->bool)->bool) j.
     FINITE lm /\ combinatorial_manifold 2 lm /\
     connected j /\ ~(j = {}) /\ j SUBSET UNIONS lm
     ==> moi_fan_mc lm j IN components (UNIONS lm) /\ j SUBSET moi_fan_mc lm j /\
         compact (moi_fan_mc lm j) /\ connected (moi_fan_mc lm j) /\
         ~(moi_fan_mc lm j = {}) /\ moi_fan_mc lm j SUBSET UNIONS lm`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?k:real^3->bool. k IN components (UNIONS lm) /\ j SUBSET k`
  MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(j:real^3->bool = {})`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^3`) THEN
    EXISTS_TAC `connected_component (UNIONS lm) (x:real^3)` THEN CONJ_TAC THENL
     [REWRITE_TAC[components; IN_ELIM_THM] THEN EXISTS_TAC `x:real^3` THEN ASM SET_TAC[];
      MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SELECT_RULE) THEN REWRITE_TAC[GSYM moi_fan_mc] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `compact (UNIONS lm:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[combinatorial_manifold; lf_simplicial_complex; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_IN_COMPACT THEN EXISTS_TAC `UNIONS lm:real^3->bool` THEN
    ASM_SIMP_TAC[CLOSED_IN_COMPONENT];
    ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
    ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
    ASM_MESON_TAC[IN_COMPONENTS_SUBSET]]);;

let MOI_FAN_SIDES = prove
 (`!(lm:(real^3->bool)->bool) j X.
     FINITE lm /\ combinatorial_manifold 2 lm /\
     connected j /\ ~(j = {}) /\ j SUBSET UNIONS lm /\
     connected X /\ ~(X = {}) /\ DISJOINT X (moi_fan_mc lm j)
     ==> open (moi_fan_side lm j X) /\ open (moi_fan_far lm j X) /\
         connected (moi_fan_side lm j X) /\ connected (moi_fan_far lm j X) /\
         DISJOINT (moi_fan_side lm j X) (moi_fan_far lm j X) /\
         DISJOINT (moi_fan_side lm j X) (moi_fan_mc lm j) /\
         DISJOINT (moi_fan_far lm j X) (moi_fan_mc lm j) /\
         moi_fan_side lm j X UNION moi_fan_far lm j X = (:real^3) DIFF moi_fan_mc lm j /\
         frontier (moi_fan_side lm j X) = moi_fan_mc lm j /\
         frontier (moi_fan_far lm j X) = moi_fan_mc lm j /\
         X SUBSET moi_fan_side lm j X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j:real^3->bool`] MOI_FAN_MC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `k = moi_fan_mc (lm:(real^3->bool)->bool) j` THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `k:real^3->bool`] MOI_FCL_CM2_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC MOI_FAN_266 THEN REWRITE_TAC[MOISE_266_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `{s | s IN lm /\ s SUBSET (k:real^3->bool)}`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `moi_fan_side (lm:(real^3->bool)->bool) j X IN components ((:real^3) DIFF k) /\
    X SUBSET moi_fan_side lm j X`
  MP_TAC THENL
   [REWRITE_TAC[moi_fan_side;
                ASSUME `moi_fan_mc (lm:(real^3->bool)->bool) j = k`] THEN
    CONV_TAC SELECT_CONV THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
      check (fun th -> concl th = `~(X:real^3->bool = {})`)) THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^3`) THEN
    EXISTS_TAC `connected_component ((:real^3) DIFF k) (x:real^3)` THEN CONJ_TAC THENL
     [REWRITE_TAC[components; IN_ELIM_THM] THEN EXISTS_TAC `x:real^3` THEN ASM SET_TAC[];
      MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `S = moi_fan_side (lm:(real^3->bool)->bool) j X` THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_fan_far (lm:(real^3->bool)->bool) j X =
                (:real^3) DIFF (k UNION S)` SUBST1_TAC THENL
   [REWRITE_TAC[moi_fan_far] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open ((:real^3) DIFF k)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open (b:real^3->bool) /\ open (outside k:real^3->bool) /\
    connected (b:real^3->bool) /\ connected (outside k:real^3->bool) /\
    DISJOINT b (outside k) /\ DISJOINT (outside k) b /\
    DISJOINT b k /\ DISJOINT (outside k) k /\
    b UNION outside k = (:real^3) DIFF k /\ outside k UNION b = (:real^3) DIFF k`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `b IN components ((:real^3) DIFF k) /\
                  outside k IN components ((:real^3) DIFF k)` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    SUBGOAL_THEN `UNIONS (components ((:real^3) DIFF k)) = (:real^3) DIFF k`
    MP_TAC THENL [REWRITE_TAC[GSYM UNIONS_COMPONENTS]; ALL_TAC] THEN
    ASM_REWRITE_TAC[UNIONS_2] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(:real^3) DIFF k`; `b:real^3->bool`; `outside k:real^3->bool`]
      COMPONENTS_NONOVERLAP) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(:real^3) DIFF k`; `b:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
    MP_TAC(ISPECL [`(:real^3) DIFF k`; `outside k:real^3->bool`] IN_COMPONENTS_SUBSET) THEN
    REWRITE_TAC[ASSUME `b IN components ((:real^3) DIFF k)`;
                ASSUME `outside k IN components ((:real^3) DIFF k)`] THEN
    REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THEN
    FIRST [FIRST_ASSUM ACCEPT_TAC;
           MATCH_MP_TAC OPEN_COMPONENTS THEN EXISTS_TAC `(:real^3) DIFF k` THEN
           ASM_REWRITE_TAC[] THEN NO_TAC;
           MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN EXISTS_TAC `(:real^3) DIFF k` THEN
           ASM_REWRITE_TAC[] THEN NO_TAC;
           ASM_REWRITE_TAC[DISJOINT] THEN NO_TAC;
           ASM_REWRITE_TAC[DISJOINT; INTER_COMM] THEN NO_TAC;
           ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[] THEN NO_TAC;
           ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(S = b /\ (:real^3) DIFF (k UNION b) = outside k) \/
    (S = outside k /\ (:real^3) DIFF (k UNION outside k) = b)`
  MP_TAC THENL
   [SUBGOAL_THEN `(:real^3) DIFF (k UNION b) = outside k /\
                  (:real^3) DIFF (k UNION outside k) = b` (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC
       [`DISJOINT (b:real^3->bool) (outside k)`; `DISJOINT (b:real^3->bool) k`;
        `DISJOINT (outside k:real^3->bool) k`;
        `(b:real^3->bool) UNION outside k = (:real^3) DIFF k`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
      UNDISCH_TAC `(S:real^3->bool) IN components ((:real^3) DIFF k)` THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
    DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Step C, the curve complex L (abstract): simplices of the second derived   *)
(* complex inside the derived neighbourhood, one rim, both rims.             *)
(* ========================================================================= *)

(* A nonempty simplex of the second derived complex inside the derived      *)
(* neighbourhood is in the derived neighbourhood complex.                   *)

let MOI_FAN_SUB_NC = prove
 (`!(t:(real^N->bool)->bool) l s.
     lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision t)) /\
     s IN barycentric_subdivision (barycentric_subdivision t) /\ ~(s = {}) /\
     s SUBSET derived_nbhd t l
     ==> s IN derived_nbhd_complex t l`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `t2 = barycentric_subdivision (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `convex (s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^N. x IN relative_interior s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `?r:real^N->bool. r IN t2 /\ ~(r INTER UNIONS l = {}) /\ x IN r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) SUBSET derived_nbhd t l` THEN
    ASM_REWRITE_TAC[derived_nbhd; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s INTER r:real^N->bool) face_of s /\ (s INTER r) face_of r`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `s INTER r:real^N->bool = s` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s INTER r:real^N->bool`; `s:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior s` THEN UNDISCH_TAC `(x:real^N) IN r` THEN
    MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* One rim of the trace: the part of L on a boundary component fr of the    *)
(* trace complex d has no triangles, and its vertices have degree 2.        *)

let MOI_FAN_LRIM = prove
 (`!(c:(real^N->bool)->bool) d fr l.
     FINITE d /\ combinatorial_manifold_with_boundary 2 d /\
     simplicial_subcomplex d c /\ surface_boundary d = fr /\
     (!s. s IN c /\ ~(s = {}) /\ s SUBSET UNIONS d ==> s IN d) /\
     (!s. s IN l ==> s IN c) /\
     (!s. s IN c /\ ~(s = {}) /\ s SUBSET fr ==> s IN l)
     ==> (!s. s IN l /\ s SUBSET fr ==> ~(aff_dim s = &2)) /\
         (!v. {v} IN l /\ v IN fr /\
              (!e. e IN l /\ aff_dim e = &1 /\ v IN e ==> e SUBSET fr)
              ==> CARD {e | e IN l /\ aff_dim e = &1 /\ v IN e} = 2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (d:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `(fr:real^N->bool) SUBSET UNIONS d` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSP_SB_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) IN d` ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_SIMP_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSP_TRI_NOT_IN_SB) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} IN d` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
    REWRITE_TAC[NOT_INSERT_EMPTY] THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{e | e IN l /\ aff_dim e = &1 /\ (v:real^N) IN e} =
    {e | e IN d /\ aff_dim e = &1 /\ v IN e /\
         CARD {r | r IN d /\ aff_dim r = &2 /\ e SUBSET r} = 1}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `e:real^N->bool` THEN
    EQ_TAC THEN STRIP_TAC THENL
     [SUBGOAL_THEN `(e:real^N->bool) SUBSET fr` ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(e:real^N->bool) IN d` ASSUME_TAC THENL
       [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FSP_BD_EDGE THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(e:real^N->bool) SUBSET surface_boundary d` MP_TAC THENL
       [REWRITE_TAC[surface_boundary] THEN
        MATCH_MP_TAC(SET_RULE `!x:real^N->bool s. x IN s ==> x SUBSET UNIONS s`) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM];
        ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSB_BD_DEGREE THEN ASM_REWRITE_TAC[]);;

(* The part L of a closed surface k on the polyhedron mm of a full          *)
(* subcomplex c, when k meets mm in two disjoint boundary curves of trace   *)
(* complexes d1, d2 in c: a full subcomplex of k of dimension at most 1     *)
(* with all vertex degrees 2 (the hypotheses of MOI_FCS_CLOPEN_SIDES).      *)

let MOI_FAN_LFACTS = prove
 (`!(c2:(real^N->bool)->bool) k c d1 d2 fr1 fr2 ff mm.
     lf_simplicial_complex c2 /\ simplicial_subcomplex k c2 /\
     FINITE k /\ combinatorial_manifold 2 k /\ UNIONS k = ff /\
     (!s. s IN c2 /\ ~(s = {}) /\ s SUBSET ff ==> s IN k) /\
     simplicial_subcomplex c c2 /\ UNIONS c = mm /\
     (!q. q IN c2 ==> q INTER mm IN c /\ (q INTER mm) face_of q) /\
     ff INTER mm = fr1 UNION fr2 /\ closed fr1 /\ closed fr2 /\ DISJOINT fr1 fr2 /\
     FINITE d1 /\ combinatorial_manifold_with_boundary 2 d1 /\
     simplicial_subcomplex d1 c /\ surface_boundary d1 = fr1 /\
     (!s. s IN c /\ ~(s = {}) /\ s SUBSET UNIONS d1 ==> s IN d1) /\
     FINITE d2 /\ combinatorial_manifold_with_boundary 2 d2 /\
     simplicial_subcomplex d2 c /\ surface_boundary d2 = fr2 /\
     (!s. s IN c /\ ~(s = {}) /\ s SUBSET UNIONS d2 ==> s IN d2)
     ==> simplicial_subcomplex {q | q IN k /\ q SUBSET mm} k /\
         UNIONS {q | q IN k /\ q SUBSET mm} = ff INTER mm /\
         (!s. s IN {q | q IN k /\ q SUBSET mm} ==> aff_dim s <= &1) /\
         (!v. {v} IN {q | q IN k /\ q SUBSET mm}
              ==> CARD {e | e IN {q | q IN k /\ q SUBSET mm} /\
                            aff_dim e = &1 /\ v IN e} = 2) /\
         (!q. q IN k
              ==> q INTER UNIONS {q | q IN k /\ q SUBSET mm} IN
                  {q | q IN k /\ q SUBSET mm} /\
                  (q INTER UNIONS {q | q IN k /\ q SUBSET mm}) face_of q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `l = {q | q IN k /\ (q:real^N->bool) SUBSET mm}` THEN
  SUBGOAL_THEN
   `(!q:real^N->bool. q IN l ==> q IN k /\ q SUBSET mm) /\
    (!q:real^N->bool. q IN k /\ q SUBSET mm ==> q IN l)`
  (CONJUNCTS_THEN2 (LABEL_TAC "l1") (LABEL_TAC "l2")) THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!q:real^N->bool. q IN k
      ==> q IN c2 /\ q SUBSET ff /\ connected q /\ (!f. f face_of q ==> f IN k)`
  (LABEL_TAC "kf") THENL
   [X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:real^N->bool) IN c2` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SET_RULE `!q:real^N->bool k. q IN k ==> q SUBSET UNIONS k`];
      ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
      ASM_MESON_TAC[simplicial_subcomplex]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^N->bool. q IN k ==> q INTER mm IN l` (LABEL_TAC "kl") THENL
   [X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN USE_THEN "l2" MATCH_MP_TAC THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    USE_THEN "kf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(q:real^N->bool) IN k`))) THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `!q:real^N->bool. q IN c2 ==> q INTER mm IN c /\ (q INTER mm) face_of q` THEN
    DISCH_THEN(MP_TAC o SPEC `q:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS l = (ff:real^N->bool) INTER mm` ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIONS; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "l1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(q:real^N->bool) IN l`))) THEN
      USE_THEN "kf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(q:real^N->bool) IN k`))) THEN
      UNDISCH_TAC `(q:real^N->bool) SUBSET ff` THEN UNDISCH_TAC `(q:real^N->bool) SUBSET mm` THEN
      UNDISCH_TAC `(x:real^N) IN q` THEN SET_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `?q:real^N->bool. q IN k /\ x IN q` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN ff` THEN
        FIRST_X_ASSUM(fun th -> if concl th = `UNIONS k = (ff:real^N->bool)`
          then REWRITE_TAC[SYM th] else failwith "no") THEN
        REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `q INTER mm:real^N->bool` THEN ASM_SIMP_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN l ==> s IN c` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "l1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(s:real^N->bool) IN l`))) THEN
    SUBGOAL_THEN `s INTER mm:real^N->bool = s` ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^N->bool) SUBSET mm` THEN SET_TAC[]; ALL_TAC] THEN
    USE_THEN "kf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(s:real^N->bool) IN k`))) THEN
    UNDISCH_TAC `!q:real^N->bool. q IN c2 ==> q INTER mm IN c /\ (q INTER mm) face_of q` THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:(real^N->bool)->bool) SUBSET c2` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN c /\ ~(s = {}) /\ s SUBSET fr1 UNION fr2 ==> s IN l`
  (LABEL_TAC "cl") THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN USE_THEN "l2" MATCH_MP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET ff /\ s SUBSET mm` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^N->bool) SUBSET fr1 UNION fr2` THEN
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `ff INTER mm:real^N->bool`
        then REWRITE_TAC[SYM th] else failwith "no") THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!s:real^N->bool. s IN c2 /\ ~(s = {}) /\ s SUBSET ff ==> s IN k` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(c:(real^N->bool)->bool) SUBSET c2` THEN
    UNDISCH_TAC `(s:real^N->bool) IN c` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!s:real^N->bool. s IN c /\ ~(s = {}) /\ s SUBSET fr1 ==> s IN l) /\
    (!s:real^N->bool. s IN c /\ ~(s = {}) /\ s SUBSET fr2 ==> s IN l)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!s a b:real^N->bool. s SUBSET a \/ s SUBSET b ==> s SUBSET a UNION b`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN l ==> connected s /\ (s SUBSET fr1 \/ s SUBSET fr2)`
  (LABEL_TAC "sp") THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "l1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(s:real^N->bool) IN l`))) THEN
    USE_THEN "kf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(s:real^N->bool) IN k`))) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FAN_CONNECTED_SPLIT THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `ff INTER mm:real^N->bool`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET ff` THEN UNDISCH_TAC `(s:real^N->bool) SUBSET mm` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `d1:(real^N->bool)->bool`;
                 `fr1:real^N->bool`; `l:(real^N->bool)->bool`] MOI_FAN_LRIM) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "t1") (LABEL_TAC "v1"))] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `d2:(real^N->bool)->bool`;
                 `fr2:real^N->bool`; `l:(real^N->bool)->bool`] MOI_FAN_LRIM) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "t2") (LABEL_TAC "v2"))] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N->bool` THEN DISCH_TAC THEN
      USE_THEN "l1" (fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(x:real^N->bool) IN l`)]);
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:real^N->bool`] THEN STRIP_TAC THEN
    USE_THEN "l1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(s:real^N->bool) IN l`))) THEN
    USE_THEN "kf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(s:real^N->bool) IN k`))) THEN
    USE_THEN "l2" MATCH_MP_TAC THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_SIMP_TAC[FACE_OF_IMP_SUBSET]];
    FIRST_ASSUM ACCEPT_TAC;
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "l1" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(s:real^N->bool) IN l`))) THEN
    SUBGOAL_THEN `aff_dim (s:real^N->bool) <= &2` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FSB_DIM THEN EXISTS_TAC `k:(real^N->bool)->bool` THEN
      ASM_SIMP_TAC[MOI_S8TA_CM_CMB];
      ALL_TAC] THEN
    MATCH_MP_TAC(INT_ARITH `x:int <= &2 /\ ~(x = &2) ==> x <= &1`) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "sp" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(s:real^N->bool) IN l`))) THENL
     [USE_THEN "t1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "t2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^N) IN fr1 UNION fr2` MP_TAC THENL
     [SUBGOAL_THEN `(v:real^N) IN UNIONS l` MP_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [USE_THEN "v1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
      USE_THEN "sp" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(e:real^N->bool) IN l`))) THEN
      UNDISCH_TAC `DISJOINT (fr1:real^N->bool) fr2` THEN
      UNDISCH_TAC `(v:real^N) IN e` THEN UNDISCH_TAC `(v:real^N) IN fr1` THEN SET_TAC[];
      USE_THEN "v2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
      USE_THEN "sp" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(e:real^N->bool) IN l`))) THEN
      UNDISCH_TAC `DISJOINT (fr1:real^N->bool) fr2` THEN
      UNDISCH_TAC `(v:real^N) IN e` THEN UNDISCH_TAC `(v:real^N) IN fr2` THEN SET_TAC[]];
    X_GEN_TAC `q:real^N->bool` THEN DISCH_TAC THEN
    FIRST_ASSUM(fun th -> if is_eq(concl th) && lhs(concl th) = `UNIONS l:real^N->bool`
      then REWRITE_TAC[th] else failwith "no") THEN
    USE_THEN "kf" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `(q:real^N->bool) IN k`))) THEN
    SUBGOAL_THEN `(q:real^N->bool) INTER (ff INTER mm) = q INTER mm` SUBST1_TAC THENL
     [UNDISCH_TAC `(q:real^N->bool) SUBSET ff` THEN SET_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "kl" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      UNDISCH_TAC `!q:real^N->bool. q IN c2 ==> q INTER mm IN c /\ (q INTER mm) face_of q` THEN
      DISCH_THEN(MP_TAC o SPEC `q:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]]]);;

(* ========================================================================= *)
(* The context of steps C-E and its basic facts; the curve complex L in      *)
(* context form.                                                             *)
(* ========================================================================= *)

(* The context of steps C-E: the hypotheses of MOI_FSN_ANNULUS_NBHD and the *)
(* trace data of MOI_FAN_TRACE (equations oriented towards the variables). *)

let moi_fan_ctx = new_definition
 `moi_fan_ctx (t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 <=>
    FINITE t /\ combinatorial_manifold_with_boundary 3 t /\
    simplicial_subcomplex la t /\ simplicial_subcomplex lm t /\
    FINITE lm /\ combinatorial_manifold 2 lm /\
    pl_annulus_with_ends (UNIONS la) j1 j2 /\
    UNIONS la INTER UNIONS lm = j1 UNION j2 /\
    DISJOINT (derived_nbhd t la) (complex_boundary t) /\
    derived_nbhd t la INTER UNIONS lm = a1 UNION a2 /\ DISJOINT a1 a2 /\
    pl_annulus_with_ends a1 k11 k12 /\ pl_annulus_with_ends a2 k21 k22 /\
    j1 SUBSET a1 DIFF (k11 UNION k12) /\ j2 SUBSET a2 DIFF (k21 UNION k22) /\
    derived_frontier t la INTER UNIONS lm = k11 UNION k12 UNION k21 UNION k22 /\
    derived_nbhd lm {s | s IN la INTER lm /\ s SUBSET j1} = a1 /\
    derived_nbhd lm {s | s IN la INTER lm /\ s SUBSET j2} = a2 /\
    derived_frontier lm {s | s IN la INTER lm /\ s SUBSET j1} = k11 UNION k12 /\
    derived_frontier lm {s | s IN la INTER lm /\ s SUBSET j2} = k21 UNION k22`;;

let MOI_FAN_CTX_EXISTS = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2.
     FINITE t /\ combinatorial_manifold_with_boundary 3 t /\
     simplicial_subcomplex la t /\ simplicial_subcomplex lm t /\
     FINITE lm /\ combinatorial_manifold 2 lm /\
     pl_annulus_with_ends (UNIONS la) j1 j2 /\
     UNIONS la INTER UNIONS lm = j1 UNION j2 /\
     DISJOINT (derived_nbhd t la) (complex_boundary t)
     ==> ?a1 a2 k11 k12 k21 k22. moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_FAN_TRACE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  REWRITE_TAC[moi_fan_ctx] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC);;

(* Facts on the 3-dimensional side: N, its complex, F and its complex K.    *)

let MOI_FAN_CTX_T = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> lf_simplicial_complex t /\
         lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision t)) /\
         UNIONS (barycentric_subdivision (barycentric_subdivision t)) = UNIONS t /\
         simplicial_subcomplex (derived_nbhd_complex t la)
           (barycentric_subdivision (barycentric_subdivision t)) /\
         UNIONS (derived_nbhd_complex t la) = derived_nbhd t la /\
         compact (derived_nbhd t la) /\ derived_nbhd t la SUBSET UNIONS t /\
         closed_in (subtopology euclidean (UNIONS t)) (derived_nbhd t la) /\
         derived_frontier t la SUBSET derived_nbhd t la /\
         compact (derived_frontier t la) /\
         FINITE (derived_nbhd_complex t la) /\
         combinatorial_manifold_with_boundary 3 (derived_nbhd_complex t la) /\
         complex_boundary (derived_nbhd_complex t la) = derived_frontier t la /\
         FINITE (boundary_complex (derived_nbhd_complex t la)) /\
         combinatorial_manifold 2 (boundary_complex (derived_nbhd_complex t la)) /\
         UNIONS (boundary_complex (derived_nbhd_complex t la)) = derived_frontier t la /\
         simplicial_subcomplex (boundary_complex (derived_nbhd_complex t la))
           (barycentric_subdivision (barycentric_subdivision t)) /\
         complex_euler (boundary_complex (derived_nbhd_complex t la)) = &0 /\
         (!s. s IN barycentric_subdivision (barycentric_subdivision t) /\ ~(s = {}) /\
              s SUBSET derived_frontier t la
              ==> s IN boundary_complex (derived_nbhd_complex t la))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fan_ctx] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (la:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET; simplicial_subcomplex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`] MOI_FAN_FRONTIER_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `derived_frontier t la SUBSET derived_nbhd t (la:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[derived_frontier] THEN MATCH_MP_TAC FRONTIER_OF_SUBSET_CLOSED_IN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
       lhs(concl th) = `UNIONS (boundary_complex (derived_nbhd_complex t
                                   (la:(real^3->bool)->bool)))`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_FM3_LF_COMPACT; combinatorial_manifold];
    MATCH_MP_TAC MOI_FSP_SUBCX_TRANS THEN
    EXISTS_TAC `derived_nbhd_complex t (la:(real^3->bool)->bool)` THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FAN_SUB_NC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET_TRANS]]);;

(* Facts on the surface side: the second derived complex of lm, its        *)
(* fullness in that of t, the rims and their trace complexes D1, D2.       *)

let MOI_FAN_CTX_M = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> lf_simplicial_complex lm /\
         FINITE (barycentric_subdivision (barycentric_subdivision lm)) /\
         combinatorial_manifold 2 (barycentric_subdivision (barycentric_subdivision lm)) /\
         lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision lm)) /\
         UNIONS (barycentric_subdivision (barycentric_subdivision lm)) = UNIONS lm /\
         simplicial_subcomplex (barycentric_subdivision (barycentric_subdivision lm))
           (barycentric_subdivision (barycentric_subdivision t)) /\
         (!q. q IN barycentric_subdivision (barycentric_subdivision t)
              ==> q INTER UNIONS lm IN barycentric_subdivision (barycentric_subdivision lm) /\
                  (q INTER UNIONS lm) face_of q) /\
         simplicial_subcomplex {s | s IN la INTER lm /\ s SUBSET j1} lm /\
         UNIONS {s | s IN la INTER lm /\ s SUBSET j1} = j1 /\
         simplicial_subcomplex {s | s IN la INTER lm /\ s SUBSET j2} lm /\
         UNIONS {s | s IN la INTER lm /\ s SUBSET j2} = j2 /\
         FINITE (derived_nbhd_complex lm {s | s IN la INTER lm /\ s SUBSET j1}) /\
         combinatorial_manifold_with_boundary 2
           (derived_nbhd_complex lm {s | s IN la INTER lm /\ s SUBSET j1}) /\
         surface_boundary (derived_nbhd_complex lm {s | s IN la INTER lm /\ s SUBSET j1}) =
           k11 UNION k12 /\
         UNIONS (derived_nbhd_complex lm {s | s IN la INTER lm /\ s SUBSET j1}) = a1 /\
         simplicial_subcomplex (derived_nbhd_complex lm {s | s IN la INTER lm /\ s SUBSET j1})
           (barycentric_subdivision (barycentric_subdivision lm)) /\
         (!s. s IN barycentric_subdivision (barycentric_subdivision lm) /\ ~(s = {}) /\
              s SUBSET a1
              ==> s IN derived_nbhd_complex lm {s | s IN la INTER lm /\ s SUBSET j1}) /\
         FINITE (derived_nbhd_complex lm {s | s IN la INTER lm /\ s SUBSET j2}) /\
         combinatorial_manifold_with_boundary 2
           (derived_nbhd_complex lm {s | s IN la INTER lm /\ s SUBSET j2}) /\
         surface_boundary (derived_nbhd_complex lm {s | s IN la INTER lm /\ s SUBSET j2}) =
           k21 UNION k22 /\
         UNIONS (derived_nbhd_complex lm {s | s IN la INTER lm /\ s SUBSET j2}) = a2 /\
         simplicial_subcomplex (derived_nbhd_complex lm {s | s IN la INTER lm /\ s SUBSET j2})
           (barycentric_subdivision (barycentric_subdivision lm)) /\
         (!s. s IN barycentric_subdivision (barycentric_subdivision lm) /\ ~(s = {}) /\
              s SUBSET a2
              ==> s IN derived_nbhd_complex lm {s | s IN la INTER lm /\ s SUBSET j2}) /\
         k11 UNION k12 SUBSET a1 /\ k21 UNION k22 SUBSET a2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fan_ctx] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPEC `lm:(real^3->bool)->bool` MOI_FC2_BARYCENTRIC_CM2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `barycentric_subdivision (lm:(real^3->bool)->bool)` MOI_FC2_BARYCENTRIC_CM2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`] MOI_FN2_SUBCOMPLEX_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS la:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_FCB_ANN_ENDS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS la:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_S5C_ANN_END_SPHERES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_S5C_SIMPLEX2_R3]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `(la:(real^3->bool)->bool) INTER lm`;
                 `j1:real^3->bool`; `j2:real^3->bool`] MOI_FAN_RIM_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED; DISJOINT];
    ALL_TAC] THEN
  ABBREV_TAC `l1 = {s | s IN (la:(real^3->bool)->bool) INTER lm /\ s SUBSET j1}` THEN
  ABBREV_TAC `l2 = {s | s IN (la:(real^3->bool)->bool) INTER lm /\ s SUBSET j2}` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l1:(real^3->bool)->bool`]
    DERIVED_NBHD_POLYGON_2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)))] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l2:(real^3->bool)->bool`]
    DERIVED_NBHD_POLYGON_2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o CONJUNCT1)))] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l1:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `l2:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold];
    X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision (lm:(real^3->bool)->bool)`; `q:real^3->bool`]
      MOI_FRN_FULL) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FAN_SUB_NC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[combinatorial_manifold];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FAN_SUB_NC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[combinatorial_manifold];
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
       lhs(concl th) = `derived_frontier lm (l1:(real^3->bool)->bool)`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    REWRITE_TAC[derived_frontier] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FRONTIER_OF_SUBSET_CLOSED_IN THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
       lhs(concl th) = `derived_frontier lm (l2:(real^3->bool)->bool)`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    REWRITE_TAC[derived_frontier] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FRONTIER_OF_SUBSET_CLOSED_IN THEN ASM_REWRITE_TAC[]]);;

(* Step C, the curve complex L = the part of K on M: hypotheses of         *)
(* MOI_FCS_CLOPEN_SIDES on L.                                               *)

let MOI_FAN_CTX_L = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> simplicial_subcomplex
           {q | q IN boundary_complex (derived_nbhd_complex t la) /\ q SUBSET UNIONS lm}
           (boundary_complex (derived_nbhd_complex t la)) /\
         UNIONS {q | q IN boundary_complex (derived_nbhd_complex t la) /\ q SUBSET UNIONS lm} =
           derived_frontier t la INTER UNIONS lm /\
         (!s. s IN {q | q IN boundary_complex (derived_nbhd_complex t la) /\ q SUBSET UNIONS lm}
              ==> aff_dim s <= &1) /\
         (!v. {v} IN {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                          q SUBSET UNIONS lm}
              ==> CARD {e | e IN {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                                      q SUBSET UNIONS lm} /\ aff_dim e = &1 /\ v IN e} = 2) /\
         (!q. q IN boundary_complex (derived_nbhd_complex t la)
              ==> q INTER UNIONS {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                                      q SUBSET UNIONS lm} IN
                  {q | q IN boundary_complex (derived_nbhd_complex t la) /\ q SUBSET UNIONS lm} /\
                  (q INTER UNIONS {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                                       q SUBSET UNIONS lm}) face_of q)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_M th)) THEN
  MP_TAC(ISPECL [`a1:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`]
    MOI_FCB_ANN_ENDS_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`a2:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`]
    MOI_FCB_ANN_ENDS_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC MOI_FAN_LFACTS THEN
  MAP_EVERY EXISTS_TAC
   [`barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))`;
    `barycentric_subdivision (barycentric_subdivision (lm:(real^3->bool)->bool))`;
    `derived_nbhd_complex lm {s | s IN (la:(real^3->bool)->bool) INTER lm /\ s SUBSET j1}`;
    `derived_nbhd_complex lm {s | s IN (la:(real^3->bool)->bool) INTER lm /\ s SUBSET j2}`;
    `k11 UNION k12:real^3->bool`; `k21 UNION k22:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[UNION_ASSOC];
    ASM_SIMP_TAC[CLOSED_UNION; COMPACT_IMP_CLOSED];
    ASM_SIMP_TAC[CLOSED_UNION; COMPACT_IMP_CLOSED];
    UNDISCH_TAC `DISJOINT (a1:real^3->bool) a2` THEN
    UNDISCH_TAC `k11 UNION k12 SUBSET (a1:real^3->bool)` THEN
    UNDISCH_TAC `k21 UNION k22 SUBSET (a2:real^3->bool)` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Step C, local topology for the transversality at the ends.                *)
(* ========================================================================= *)

(* Step C, transversality at the ends: local topology.                      *)

let MOI_FAN_CONN_OPEN_SPLIT = prove
 (`!s u v:real^N->bool.
     connected s /\ open u /\ open v /\ DISJOINT u v /\ s SUBSET u UNION v
     ==> s SUBSET u \/ s SUBSET v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[connected] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `v:real^N->bool`] o
    REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `DISJOINT (u:real^N->bool) v` THEN
  UNDISCH_TAC `(s:real^N->bool) SUBSET u UNION v` THEN SET_TAC[]);;

(* Near a point y of the common frontier mc of two complementary open      *)
(* sides, two connected pieces filling the small ball minus mc lie on      *)
(* opposite sides.                                                           *)

let MOI_FAN_TWO_SIDES_LOCAL = prove
 (`!(sd:real^N->bool) fa mc y r u v.
     open sd /\ open fa /\ DISJOINT sd fa /\ sd UNION fa = (:real^N) DIFF mc /\
     y IN closure sd /\ y IN closure fa /\ &0 < r /\
     connected u /\ connected v /\ u UNION v = ball(y,r) DIFF mc
     ==> (u SUBSET sd /\ v SUBSET fa) \/ (u SUBSET fa /\ v SUBSET sd)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(ball(y:real^N,r) INTER sd = {}) /\ ~(ball(y,r) INTER fa = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    W(fun (_,w) -> MP_TAC(ISPECL [`ball(y:real^N,r)`; rand(lhand(rand w))]
      OPEN_INTER_CLOSURE_EQ_EMPTY)) THEN
    REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET sd UNION fa /\ v SUBSET sd UNION fa`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `u UNION v = ball(y:real^N,r) DIFF mc` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET sd \/ u SUBSET fa` MP_TAC THENL
   [MATCH_MP_TAC MOI_FAN_CONN_OPEN_SPLIT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N->bool) SUBSET sd \/ v SUBSET fa` MP_TAC THENL
   [MATCH_MP_TAC MOI_FAN_CONN_OPEN_SPLIT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `ball(y:real^N,r) INTER sd SUBSET u UNION v /\
                ball(y,r) INTER fa SUBSET u UNION v`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `sd UNION fa = (:real^N) DIFF mc` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(ball(y:real^N,r) INTER sd = {})` THEN
  UNDISCH_TAC `~(ball(y:real^N,r) INTER fa = {})` THEN
  UNDISCH_TAC `DISJOINT (sd:real^N->bool) fa` THEN SET_TAC[]);;

(* A connected set accumulating on a point with a ball inside nn and on a  *)
(* point with a ball outside nn meets the frontier of nn.                  *)

let MOI_FAN_MEETS_FRONTIER = prove
 (`!(tt:real^N->bool) nn w z z' d1 d2.
     connected w /\ w SUBSET tt /\ z IN closure w /\ z' IN closure w /\
     &0 < d1 /\ ball(z,d1) SUBSET nn /\ &0 < d2 /\ ball(z',d2) INTER nn = {}
     ==> ~(w INTER (subtopology euclidean tt) frontier_of nn = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC CONNECTED_IN_INTER_FRONTIER_OF THEN
  ASM_REWRITE_TAC[CONNECTED_IN_SUBTOPOLOGY; CONNECTED_IN_EUCLIDEAN] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`ball(z:real^N,d1)`; `w:real^N->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    REWRITE_TAC[OPEN_BALL] THEN
    SUBGOAL_THEN `~(ball(z:real^N,d1) INTER closure w = {})` MP_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `z:real^N` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    UNDISCH_TAC `ball(z:real^N,d1) SUBSET nn` THEN SET_TAC[];
    MP_TAC(ISPECL [`ball(z':real^N,d2)`; `w:real^N->bool`] OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    REWRITE_TAC[OPEN_BALL] THEN
    SUBGOAL_THEN `~(ball(z':real^N,d2) INTER closure w = {})` MP_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `z':real^N` THEN
      ASM_REWRITE_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    UNDISCH_TAC `ball(z':real^N,d2) INTER nn = {}` THEN SET_TAC[]]);;

(* A point of nn off its relative frontier and in the interior of tt has a *)
(* ball inside nn.                                                          *)

let MOI_FAN_INTERIOR_BALL = prove
 (`!(tt:real^N->bool) nn z.
     closed_in (subtopology euclidean tt) nn /\ z IN nn /\
     ~(z IN (subtopology euclidean tt) frontier_of nn) /\ z IN interior tt
     ==> ?d. &0 < d /\ ball(z,d) SUBSET nn`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN (subtopology euclidean tt) interior_of nn` ASSUME_TAC THENL
   [UNDISCH_TAC `~((z:real^N) IN (subtopology euclidean tt) frontier_of nn)` THEN
    ASM_SIMP_TAC[frontier_of; CLOSURE_OF_CLOSED_IN; IN_DIFF];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (tt:real^N->bool)`; `nn:real^N->bool`]
    OPEN_IN_INTERIOR_OF) THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `g INTER interior tt:real^N->bool` OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_INTER; OPEN_INTERIOR] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`subtopology euclidean (tt:real^N->bool)`; `nn:real^N->bool`]
    INTERIOR_OF_SUBSET) THEN
  MP_TAC(ISPEC `tt:real^N->bool` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `ball(z:real^N,d) SUBSET g INTER interior tt` THEN
  UNDISCH_TAC `(subtopology euclidean tt) interior_of nn = (tt:real^N->bool) INTER g` THEN
  SET_TAC[]);;

(* In a complex of dimension at most 2, a simplex containing a relative    *)
(* interior point of a triangle is that triangle.                           *)

let MOI_FAN_RELINT_TRI = prove
 (`!(c:(real^N->bool)->bool) q r z.
     lf_simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     q IN c /\ aff_dim q = &2 /\ r IN c /\ z IN relative_interior q /\ z IN r
     ==> r = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(q INTER r:real^N->bool) face_of q /\ (q INTER r) face_of r`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `q INTER r:real^N->bool = q` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`q INTER r:real^N->bool`; `q:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^N) IN relative_interior q` THEN UNDISCH_TAC `(z:real^N) IN r` THEN
    MP_TAC(ISPEC `q:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`q:real^N->bool`; `r:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (r:real^N->bool) <= &2` MP_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

(* Transversality at a point y of an edge where the surface M is locally   *)
(* the two triangles q (inside N, off F) and q' (outside N): every ball    *)
(* around y meets F minus M on both sides of the component mc of M.        *)

let MOI_FAN_TRANSV_LOCAL = prove
 (`!(tt:real^N->bool) nn mm mc sd fa sd2 q q' y.
     closed_in (subtopology euclidean tt) nn /\ closed nn /\
     nn SUBSET interior tt /\
     open sd /\ open fa /\ DISJOINT sd fa /\ sd UNION fa = (:real^N) DIFF mc /\
     frontier sd = mc /\ frontier fa = mc /\
     open sd2 /\ (~(sd2 = sd) ==> y IN sd2) /\
     mc SUBSET mm /\ q UNION q' SUBSET mc /\
     y IN q /\ y IN q' /\ y IN nn /\ convex q /\ convex q' /\ closed q /\ closed q' /\
     relative_interior q SUBSET nn DIFF (subtopology euclidean tt) frontier_of nn /\
     relative_interior q' INTER nn = {} /\
     (?r0. &0 < r0 /\
           !r. &0 < r /\ r <= r0
               ==> ball(y,r) INTER mm = ball(y,r) INTER (q UNION q') /\
                   ?u v. open u /\ open v /\ connected u /\ connected v /\
                         DISJOINT u v /\
                         u UNION v = ball(y,r) DIFF (q UNION q') /\
                         ball(y,r) INTER (q UNION q') SUBSET closure u INTER closure v)
     ==> y IN closure (((subtopology euclidean tt) frontier_of nn DIFF mm) INTER sd INTER sd2) /\
         y IN closure (((subtopology euclidean tt) frontier_of nn DIFF mm) DIFF (sd INTER sd2))`,
  REPEAT GEN_TAC THEN
  ABBREV_TAC `ff = (subtopology euclidean tt) frontier_of (nn:real^N->bool)` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN mc` ASSUME_TAC THENL
   [UNDISCH_TAC `q UNION q' SUBSET (mc:real^N->bool)` THEN
    UNDISCH_TAC `(y:real^N) IN q` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r1. &0 < r1 /\ ball(y:real^N,r1) SUBSET interior tt /\
                     (y IN sd2 ==> ball(y,r1) SUBSET sd2)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `interior tt:real^N->bool` OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL
     [UNDISCH_TAC `(nn:real^N->bool) SUBSET interior tt` THEN
      UNDISCH_TAC `(y:real^N) IN nn` THEN SET_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC)] THEN
    ASM_CASES_TAC `(y:real^N) IN sd2` THENL
     [MP_TAC(ISPEC `sd2:real^N->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `min e1 e2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
      CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THENL
       [EXISTS_TAC `ball(y:real^N,e1)`; EXISTS_TAC `ball(y:real^N,e2)`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN
      REWRITE_TAC[REAL_MIN_LE; REAL_LE_REFL];
      EXISTS_TAC `e1:real` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  MATCH_MP_TAC(MESON[]
   `(!e:real. P e ==> Q e /\ R e) ==> (!e. P e ==> Q e) /\ (!e. P e ==> R e)`) THEN
  X_GEN_TAC `e:real` THEN DISCH_TAC THEN
  ABBREV_TAC `r = min e (min r0 r1)` THEN
  SUBGOAL_THEN `&0 < r /\ r <= e /\ r <= r0 /\ r <= r1` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `ball(y:real^N,r) SUBSET ball(y,e) /\ ball(y,r) SUBSET ball(y,r1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `u UNION v = ball(y:real^N,r) DIFF mc` ASSUME_TAC THENL
   [UNDISCH_TAC `u UNION v = ball(y:real^N,r) DIFF (q UNION q')` THEN
    UNDISCH_TAC `ball(y:real^N,r) INTER mm = ball(y,r) INTER (q UNION q')` THEN
    UNDISCH_TAC `q UNION q' SUBSET (mc:real^N->bool)` THEN
    UNDISCH_TAC `(mc:real^N->bool) SUBSET mm` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN closure sd /\ y IN closure fa` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `frontier (sd:real^N->bool) = mc` THEN
    UNDISCH_TAC `frontier (fa:real^N->bool) = mc` THEN
    REWRITE_TAC[frontier] THEN UNDISCH_TAC `(y:real^N) IN mc` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`sd:real^N->bool`; `fa:real^N->bool`; `mc:real^N->bool`; `y:real^N`;
                 `r:real`; `u:real^N->bool`; `v:real^N->bool`] MOI_FAN_TWO_SIDES_LOCAL) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN
   `!w:real^N->bool. connected w /\ w SUBSET ball(y,r) /\
                     ball(y,r) INTER (q UNION q') SUBSET closure w
                     ==> ~(w INTER ff = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?z:real^N. z IN relative_interior q /\ z IN ball(y,r)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^N) IN closure(relative_interior q)` ASSUME_TAC THENL
       [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
      MP_TAC(ISPECL [`ball(y:real^N,r)`; `relative_interior q:real^N->bool`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      REWRITE_TAC[OPEN_BALL] THEN
      SUBGOAL_THEN `~(ball(y:real^N,r) INTER closure(relative_interior q) = {})` MP_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN
        ASM_REWRITE_TAC[CENTRE_IN_BALL];
        SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `?z':real^N. z' IN relative_interior q' /\ z' IN ball(y,r)`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^N) IN closure(relative_interior q')` ASSUME_TAC THENL
       [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
      MP_TAC(ISPECL [`ball(y:real^N,r)`; `relative_interior q':real^N->bool`]
        OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
      REWRITE_TAC[OPEN_BALL] THEN
      SUBGOAL_THEN `~(ball(y:real^N,r) INTER closure(relative_interior q') = {})` MP_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^N` THEN
        ASM_REWRITE_TAC[CENTRE_IN_BALL];
        SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN q /\ (z':real^N) IN q'` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `q:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC(ISPEC `q':real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(z:real^N) IN relative_interior q` THEN
      UNDISCH_TAC `(z':real^N) IN relative_interior q'` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?d1. &0 < d1 /\ ball(z:real^N,d1) SUBSET nn` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FAN_INTERIOR_BALL THEN EXISTS_TAC `tt:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `relative_interior q SUBSET nn DIFF (ff:real^N->bool)` THEN
      UNDISCH_TAC `(z:real^N) IN relative_interior q` THEN
      UNDISCH_TAC `(z:real^N) IN ball(y,r)` THEN
      UNDISCH_TAC `ball(y:real^N,r) SUBSET ball(y,r1)` THEN
      UNDISCH_TAC `ball(y:real^N,r1) SUBSET interior tt` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?d2. &0 < d2 /\ ball(z':real^N,d2) INTER nn = {}` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `open((:real^N) DIFF nn)` MP_TAC THENL
       [ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV]; ALL_TAC] THEN
      REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `z':real^N`) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `relative_interior q' INTER (nn:real^N->bool) = {}` THEN
        UNDISCH_TAC `(z':real^N) IN relative_interior q'` THEN SET_TAC[];
        MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[]];
      ALL_TAC] THEN
    EXPAND_TAC "ff" THEN MATCH_MP_TAC MOI_FAN_MEETS_FRONTIER THEN
    MAP_EVERY EXISTS_TAC [`z:real^N`; `z':real^N`; `d1:real`; `d2:real`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPEC `tt:real^N->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(w:real^N->bool) SUBSET ball(y,r)` THEN
      UNDISCH_TAC `ball(y:real^N,r) SUBSET ball(y,r1)` THEN
      UNDISCH_TAC `ball(y:real^N,r1) SUBSET interior tt` THEN SET_TAC[];
      UNDISCH_TAC `ball(y:real^N,r) INTER (q UNION q') SUBSET closure w` THEN
      UNDISCH_TAC `(z:real^N) IN q` THEN UNDISCH_TAC `(z:real^N) IN ball(y,r)` THEN SET_TAC[];
      UNDISCH_TAC `ball(y:real^N,r) INTER (q UNION q') SUBSET closure w` THEN
      UNDISCH_TAC `(z':real^N) IN q'` THEN UNDISCH_TAC `(z':real^N) IN ball(y,r)` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((u:real^N->bool) INTER ff = {}) /\ ~(v INTER ff = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL
      [UNDISCH_TAC `u UNION v = ball(y:real^N,r) DIFF mc` THEN SET_TAC[];
       UNDISCH_TAC `ball(y:real^N,r) INTER (q UNION q') SUBSET closure u INTER closure v` THEN
       SET_TAC[]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->bool) INTER mm = {} /\ v INTER mm = {}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `u UNION v = ball(y:real^N,r) DIFF (q UNION q')` THEN
    UNDISCH_TAC `ball(y:real^N,r) INTER mm = ball(y,r) INTER (q UNION q')` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sd2 = (sd:real^N->bool) \/ ball(y,r) SUBSET sd2` ASSUME_TAC THENL
   [ASM_CASES_TAC `sd2 = (sd:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(y:real^N,r1)` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[GSYM IN_BALL] THEN
  UNDISCH_TAC `(u SUBSET sd /\ v SUBSET fa) \/ (u SUBSET fa /\ v SUBSET (sd:real^N->bool))` THEN
  UNDISCH_TAC `sd2 = (sd:real^N->bool) \/ ball(y,r) SUBSET sd2` THEN
  UNDISCH_TAC `DISJOINT (sd:real^N->bool) fa` THEN
  UNDISCH_TAC `(u:real^N->bool) INTER mm = {}` THEN UNDISCH_TAC `(v:real^N->bool) INTER mm = {}` THEN
  UNDISCH_TAC `~((u:real^N->bool) INTER ff = {})` THEN
  UNDISCH_TAC `~((v:real^N->bool) INTER ff = {})` THEN
  UNDISCH_TAC `u UNION v = ball(y:real^N,r) DIFF mc` THEN
  UNDISCH_TAC `ball(y:real^N,r) SUBSET ball(y,e)` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC) THEN
  ASM SET_TAC[]);;

(* ========================================================================= *)
(* Step C, the sides B and Cc of F minus M and the transversality at the     *)
(* four ends (UNIONS L lies in the closure of both sides).                   *)
(* ========================================================================= *)

(* Step C, transversality at the ends: the combinatorial data.               *)

let MOI_FAN_PAIR_SPLIT = prove
 (`!(A:(real^N->bool)->bool) B.
     A HAS_SIZE 2 /\ B HAS_SIZE 1 /\ B SUBSET A
     ==> ?q q'. A = {q,q'} /\ ~(q = q') /\ B = {q}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (MP_TAC o CONV_RULE HAS_SIZE_CONV)
    (CONJUNCTS_THEN2 (MP_TAC o CONV_RULE HAS_SIZE_CONV) ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^N->bool` SUBST_ALL_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N->bool` (X_CHOOSE_THEN `z:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `(b:real^N->bool) = x \/ b = z` MP_TAC THENL
   [UNDISCH_TAC `{b:real^N->bool} SUBSET {x,z}` THEN SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`x:real^N->bool`; `z:real^N->bool`] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`z:real^N->bool`; `x:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(x:real^N->bool = z)` THEN SET_TAC[]]);;

(* The sides of the two rim components of M, seen from int a.              *)

let MOI_FAN_CTX_SIDES = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> connected (UNIONS la DIFF (j1 UNION j2)) /\ ~(UNIONS la DIFF (j1 UNION j2) = {}) /\
         DISJOINT (UNIONS la DIFF (j1 UNION j2)) (UNIONS lm) /\
         connected j1 /\ ~(j1 = {}) /\ j1 SUBSET UNIONS lm /\
         connected j2 /\ ~(j2 = {}) /\ j2 SUBSET UNIONS lm /\
         a1 SUBSET moi_fan_mc lm j1 /\ a2 SUBSET moi_fan_mc lm j2 /\
         (~(moi_fan_side lm j2 (UNIONS la DIFF (j1 UNION j2)) =
            moi_fan_side lm j1 (UNIONS la DIFF (j1 UNION j2)))
          ==> moi_fan_mc lm j1 SUBSET moi_fan_side lm j2 (UNIONS la DIFF (j1 UNION j2)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th)) THEN
  MP_TAC(ISPECL [`UNIONS la:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_S5C_ANN_PARTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`UNIONS la:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_FCB_ANN_ENDS_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `X = UNIONS la DIFF (j1 UNION j2:real^3->bool)` THEN
  SUBGOAL_THEN `j1 SUBSET UNIONS lm /\ j2 SUBSET UNIONS (lm:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS la INTER UNIONS lm = j1 UNION (j2:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (X:real^3->bool) (UNIONS lm)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    UNDISCH_TAC `UNIONS la INTER UNIONS lm = j1 UNION (j2:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j1:real^3->bool`] MOI_FAN_MC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j2:real^3->bool`] MOI_FAN_MC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j2:real^3->bool`; `X:real^3->bool`]
    MOI_FAN_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (X:real^3->bool) (UNIONS lm)` THEN
    UNDISCH_TAC `moi_fan_mc lm j2 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `a1 SUBSET UNIONS lm /\ a2 SUBSET UNIONS (lm:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `derived_nbhd t la INTER UNIONS lm = a1 UNION (a2:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `UNIONS lm:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[MOI_S5C_ANN_CONNECTED]; ALL_TAC] THEN
    UNDISCH_TAC `(j1:real^3->bool) SUBSET moi_fan_mc lm j1` THEN
    UNDISCH_TAC `(j1:real^3->bool) SUBSET a1 DIFF (k11 UNION k12)` THEN
    UNDISCH_TAC `~(j1:real^3->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `UNIONS lm:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[MOI_S5C_ANN_CONNECTED]; ALL_TAC] THEN
    UNDISCH_TAC `(j2:real^3->bool) SUBSET moi_fan_mc lm j2` THEN
    UNDISCH_TAC `(j2:real^3->bool) SUBSET a2 DIFF (k21 UNION k22)` THEN
    UNDISCH_TAC `~(j2:real^3->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `~(moi_fan_mc lm j1 = moi_fan_mc lm (j2:real^3->bool))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(moi_fan_side lm j2 X = moi_fan_side lm j1 (X:real^3->bool))` THEN
    REWRITE_TAC[moi_fan_side] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (moi_fan_mc lm j1) (moi_fan_mc lm (j2:real^3->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT] THEN ASM_MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS la DIFF j2 SUBSET moi_fan_side lm j2 (X:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS la DIFF j2:real^3->bool`; `moi_fan_side lm j2 (X:real^3->bool)`;
                   `moi_fan_far lm j2 (X:real^3->bool)`] MOI_FAN_CONN_OPEN_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (moi_fan_mc lm j1) (moi_fan_mc lm (j2:real^3->bool))` THEN
      UNDISCH_TAC `(j1:real^3->bool) SUBSET moi_fan_mc lm j1` THEN
      UNDISCH_TAC `moi_fan_mc lm j2 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN
      UNDISCH_TAC `UNIONS la INTER UNIONS lm = j1 UNION (j2:real^3->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `(X:real^3->bool) SUBSET moi_fan_side lm j2 X` THEN
    UNDISCH_TAC `DISJOINT (moi_fan_side lm j2 X) (moi_fan_far lm j2 (X:real^3->bool))` THEN
    UNDISCH_TAC `UNIONS la DIFF j2 SUBSET moi_fan_far lm j2 (X:real^3->bool)` THEN
    UNDISCH_TAC `~(X:real^3->bool = {})` THEN EXPAND_TAC "X" THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_fan_mc lm (j1:real^3->bool)`; `moi_fan_side lm j2 (X:real^3->bool)`;
                 `moi_fan_far lm j2 (X:real^3->bool)`] MOI_FAN_CONN_OPEN_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (moi_fan_mc lm j1) (moi_fan_mc lm (j2:real^3->bool))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `UNIONS la DIFF j2 SUBSET moi_fan_side lm j2 (X:real^3->bool)` THEN
  UNDISCH_TAC `DISJOINT (moi_fan_side lm j2 X) (moi_fan_far lm j2 (X:real^3->bool))` THEN
  UNDISCH_TAC `moi_fan_mc lm j1 SUBSET moi_fan_far lm j2 (X:real^3->bool)` THEN
  UNDISCH_TAC `(j1:real^3->bool) SUBSET moi_fan_mc lm j1` THEN
  UNDISCH_TAC `(j1:real^3->bool) SUBSET UNIONS la` THEN
  UNDISCH_TAC `(j1:real^3->bool) INTER j2 = {}` THEN
  UNDISCH_TAC `~(j1:real^3->bool = {})` THEN SET_TAC[]);;

(* The two sides of F minus M: B (between the two rim components, on the  *)
(* side of int a) and its complement Cc in F minus M.                     *)

let moi_fan_bside = new_definition
 `moi_fan_bside (t:(real^3->bool)->bool) la lm j1 j2 =
    (derived_frontier t la DIFF UNIONS lm) INTER
    moi_fan_side lm j1 (UNIONS la DIFF (j1 UNION j2)) INTER
    moi_fan_side lm j2 (UNIONS la DIFF (j1 UNION j2))`;;

let moi_fan_cside = new_definition
 `moi_fan_cside (t:(real^3->bool)->bool) la lm j1 j2 =
    (derived_frontier t la DIFF UNIONS lm) DIFF moi_fan_bside t la lm j1 j2`;;

(* An edge e of L on the rim-1 ends: e lies in exactly two triangles q, q' *)
(* of the second derived complex of lm; q is in the trace complex D1 (its  *)
(* relative interior is inside N, off F) and the relative interior of q'   *)
(* misses N.                                                                 *)

let MOI_FAN_EDGE_DATA = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 e.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     e IN boundary_complex (derived_nbhd_complex t la) /\ e SUBSET UNIONS lm /\
     aff_dim e = &1 /\ e SUBSET k11 UNION k12
     ==> e IN barycentric_subdivision (barycentric_subdivision lm) /\
         ?q q'. {r | r IN barycentric_subdivision (barycentric_subdivision lm) /\
                     aff_dim r = &2 /\ e SUBSET r} = {q,q'} /\ ~(q = q') /\
                q SUBSET a1 /\ q' SUBSET UNIONS lm /\
                relative_interior q SUBSET derived_nbhd t la DIFF derived_frontier t la /\
                relative_interior q' INTER derived_nbhd t la = {}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_M th)) STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `lmT = barycentric_subdivision (barycentric_subdivision (lm:(real^3->bool)->bool))` THEN
  ABBREV_TAC `d1 = derived_nbhd_complex lm {s | s IN (la:(real^3->bool)->bool) INTER lm /\
                                               s SUBSET j1}` THEN
  ABBREV_TAC `d2 = derived_nbhd_complex lm {s | s IN (la:(real^3->bool)->bool) INTER lm /\
                                               s SUBSET j2}` THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN lmT ==> aff_dim s <= &2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FSB_DIM THEN EXISTS_TAC `lmT:(real^3->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_S8TA_CM_CMB];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->bool) IN lmT` ASSUME_TAC THENL
   [SUBGOAL_THEN `(e:real^3->bool) IN barycentric_subdivision (barycentric_subdivision t)`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `e INTER UNIONS lm:real^3->bool = e` (fun th -> ASM_MESON_TAC[th]) THEN
    UNDISCH_TAC `(e:real^3->bool) SUBSET UNIONS lm` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(e:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^3->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->bool) SUBSET a1` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->bool) IN d1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> MATCH_MP_TAC th) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (d1:(real^3->bool)->bool) /\ d1 SUBSET lmT /\
                lf_simplicial_complex (d2:(real^3->bool)->bool) /\ d2 SUBSET lmT`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary; simplicial_subcomplex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{r | r IN lmT /\ aff_dim r = &2 /\ (e:real^3->bool) SUBSET r}`;
                 `{r | r IN d1 /\ aff_dim r = &2 /\ (e:real^3->bool) SUBSET r}`]
    MOI_FAN_PAIR_SPLIT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FSA_CM_EDGE2 THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FSP_BD_EDGE THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(d1:(real^3->bool)->bool) SUBSET lmT` THEN SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q:real^3->bool` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `q':real^3->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(q:real^3->bool) IN lmT /\ aff_dim q = &2 /\ e SUBSET q /\
    (q':real^3->bool) IN lmT /\ aff_dim q' = &2 /\ e SUBSET q' /\
    q IN d1 /\ ~(q' IN d1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(q:real^3->bool) IN {r | r IN lmT /\ aff_dim r = &2 /\ e SUBSET r} /\
      (q':real^3->bool) IN {r | r IN lmT /\ aff_dim r = &2 /\ e SUBSET r} /\
      q IN {r | r IN d1 /\ aff_dim r = &2 /\ e SUBSET r} /\
      ~(q' IN {r | r IN d1 /\ aff_dim r = &2 /\ (e:real^3->bool) SUBSET r})`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      UNDISCH_TAC `~(q:real^3->bool = q')` THEN MESON_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((q':real^3->bool) IN d1 /\ aff_dim q' = &2 /\ e SUBSET q')` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3->bool) SUBSET a1 /\ q' SUBSET UNIONS lm /\ q SUBSET UNIONS lm`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SET_RULE `!q:real^3->bool k. q IN k ==> q SUBSET UNIONS k`];
      ASM_MESON_TAC[SET_RULE `!q:real^3->bool k. q IN k ==> q SUBSET UNIONS k`];
      ASM_MESON_TAC[SET_RULE `!q:real^3->bool k. q IN k ==> q SUBSET UNIONS k`]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN q` ASSUME_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `derived_nbhd t la INTER UNIONS lm = a1 UNION (a2:real^3->bool)` THEN
      UNDISCH_TAC `(q:real^3->bool) SUBSET a1` THEN UNDISCH_TAC `(z:real^3) IN q` THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN k11 UNION k12 \/ z IN k21 UNION k22` MP_TAC THENL
     [UNDISCH_TAC `derived_frontier t la INTER UNIONS lm = k11 UNION k12 UNION k21 UNION
                   (k22:real^3->bool)` THEN
      UNDISCH_TAC `(z:real^3) IN derived_frontier t la` THEN
      UNDISCH_TAC `(q:real^3->bool) SUBSET UNIONS lm` THEN UNDISCH_TAC `(z:real^3) IN q` THEN
      SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN k11 UNION k12` THEN
      FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
         lhs(concl th) = `surface_boundary (d1:(real^3->bool)->bool)`
        then REWRITE_TAC[SYM th] else failwith "no") THEN
      REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `e':real^3->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`lmT:(real^3->bool)->bool`; `q:real^3->bool`; `e':real^3->bool`;
                     `z:real^3`] MOI_FAN_RELINT_TRI) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim (q:real^3->bool) = &1` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      UNDISCH_TAC `DISJOINT (a1:real^3->bool) a2` THEN
      UNDISCH_TAC `k21 UNION k22 SUBSET (a2:real^3->bool)` THEN
      UNDISCH_TAC `(q:real^3->bool) SUBSET a1` THEN UNDISCH_TAC `(z:real^3) IN q` THEN
      UNDISCH_TAC `(z:real^3) IN k21 UNION k22` THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN q'` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN UNIONS d1 \/ z IN UNIONS d2` MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `derived_nbhd t la INTER UNIONS lm = a1 UNION (a2:real^3->bool)` THEN
    UNDISCH_TAC `(z:real^3) IN derived_nbhd t la` THEN
    UNDISCH_TAC `(q':real^3->bool) SUBSET UNIONS lm` THEN UNDISCH_TAC `(z:real^3) IN q'` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`lmT:(real^3->bool)->bool`; `q':real^3->bool`; `r:real^3->bool`;
                 `z:real^3`] MOI_FAN_RELINT_TRI) THEN
  (ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC]) THEN
  DISCH_THEN SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(q':real^3->bool) SUBSET a2` ASSUME_TAC THENL
   [ASM_MESON_TAC[SET_RULE `!q:real^3->bool k. q IN k ==> q SUBSET UNIONS k`]; ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (a1:real^3->bool) a2` THEN
  UNDISCH_TAC `(q':real^3->bool) SUBSET a2` THEN UNDISCH_TAC `(e:real^3->bool) SUBSET q'` THEN
  UNDISCH_TAC `(e:real^3->bool) SUBSET a1` THEN UNDISCH_TAC `~(e:real^3->bool = {})` THEN
  SET_TAC[]);;

(* Transversality at the rim-1 ends: every relative interior point of an   *)
(* edge of L on k11 UNION k12 is in the closure of both sides B and Cc.    *)

let MOI_FAN_TRANSV1 = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 e y.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     e IN boundary_complex (derived_nbhd_complex t la) /\ e SUBSET UNIONS lm /\
     aff_dim e = &1 /\ e SUBSET k11 UNION k12 /\ y IN relative_interior e
     ==> y IN closure (moi_fan_bside t la lm j1 j2) /\
         y IN closure (moi_fan_cside t la lm j1 j2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPEC_ALL MOI_FAN_EDGE_DATA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `q:real^3->bool` (X_CHOOSE_THEN `q':real^3->bool` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `moi_fan_ctx (t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22` THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_M th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_SIDES th)) THEN
  REWRITE_TAC[moi_fan_bside; moi_fan_cside; derived_frontier;
              SET_RULE `!a b:real^3->bool. a DIFF (a INTER b) = a DIFF b`] THEN
  ABBREV_TAC `X = UNIONS la DIFF (j1 UNION j2:real^3->bool)` THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j1:real^3->bool`] MOI_FAN_MC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j2:real^3->bool`] MOI_FAN_MC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j1:real^3->bool`; `X:real^3->bool`]
    MOI_FAN_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (X:real^3->bool) (UNIONS lm)` THEN
    UNDISCH_TAC `moi_fan_mc lm j1 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j2:real^3->bool`; `X:real^3->bool`]
    MOI_FAN_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (X:real^3->bool) (UNIONS lm)` THEN
    UNDISCH_TAC `moi_fan_mc lm j2 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
    DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  SUBGOAL_THEN
   `(q:real^3->bool) IN barycentric_subdivision (barycentric_subdivision lm) /\
    (q':real^3->bool) IN barycentric_subdivision (barycentric_subdivision lm) /\
    e SUBSET q /\ e SUBSET q'`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(q:real^3->bool) IN {r | r IN barycentric_subdivision (barycentric_subdivision lm) /\
                               aff_dim r = &2 /\ e SUBSET r} /\
      (q':real^3->bool) IN {r | r IN barycentric_subdivision (barycentric_subdivision lm) /\
                                aff_dim r = &2 /\ e SUBSET r}`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INSERT]; REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex (q:real^3->bool) /\ closed q /\ connected q /\
    convex (q':real^3->bool) /\ closed q' /\ connected q'`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED;
                  MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN e /\ ~(e:real^3->bool = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^3->bool) SUBSET moi_fan_mc lm j1` ASSUME_TAC THENL
   [UNDISCH_TAC `(e:real^3->bool) SUBSET k11 UNION k12` THEN
    UNDISCH_TAC `k11 UNION k12 SUBSET (a1:real^3->bool)` THEN
    UNDISCH_TAC `(a1:real^3->bool) SUBSET moi_fan_mc lm j1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3->bool) SUBSET UNIONS lm` ASSUME_TAC THENL
   [UNDISCH_TAC `(q:real^3->bool) SUBSET a1` THEN
    UNDISCH_TAC `(a1:real^3->bool) SUBSET moi_fan_mc lm j1` THEN
    UNDISCH_TAC `moi_fan_mc lm j1 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3->bool) UNION q' SUBSET moi_fan_mc lm j1` ASSUME_TAC THENL
   [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
    MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `UNIONS lm:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e:real^3->bool) SUBSET moi_fan_mc lm j1` THEN
    UNDISCH_TAC `~(e:real^3->bool = {})` THEN
    UNDISCH_TAC `(e:real^3->bool) SUBSET q` THEN UNDISCH_TAC `(e:real^3->bool) SUBSET q'` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `derived_nbhd t la SUBSET interior (UNIONS (t:(real^3->bool)->bool))`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    UNDISCH_TAC `DISJOINT (derived_nbhd t la) (complex_boundary (t:(real^3->bool)->bool))` THEN
    UNDISCH_TAC `derived_nbhd t la SUBSET UNIONS (t:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN derived_nbhd t la` ASSUME_TAC THENL
   [SUBGOAL_THEN `(e:real^3->bool) SUBSET derived_frontier t la` MP_TAC THENL
     [ASM_MESON_TAC[SET_RULE `!q:real^3->bool k. q IN k ==> q SUBSET UNIONS k`]; ALL_TAC] THEN
    UNDISCH_TAC `derived_frontier t la SUBSET derived_nbhd t (la:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `(y:real^3) IN e` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (lm:(real^3->bool)->bool))`;
                 `e:real^3->bool`; `q:real^3->bool`; `q':real^3->bool`; `y:real^3`]
    LOCAL_EDGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FSB_DIM THEN
    EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (lm:(real^3->bool)->bool))` THEN
    ASM_SIMP_TAC[MOI_S8TA_CM_CMB];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_FAN_TRANSV_LOCAL THEN
  MAP_EVERY EXISTS_TAC [`moi_fan_mc lm (j1:real^3->bool)`; `moi_fan_far lm j1 (X:real^3->bool)`;
                        `q:real^3->bool`; `q':real^3->bool`] THEN
  REWRITE_TAC[GSYM derived_frontier] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    DISCH_TAC THEN
    SUBGOAL_THEN `moi_fan_mc lm j1 SUBSET moi_fan_side lm j2 (X:real^3->bool)` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(q:real^3->bool) UNION q' SUBSET moi_fan_mc lm j1` THEN
    UNDISCH_TAC `(y:real^3) IN e` THEN UNDISCH_TAC `(e:real^3->bool) SUBSET q` THEN
    SET_TAC[];
    ASM_MESON_TAC[SUBSET];
    ASM_MESON_TAC[SUBSET]]);;

(* Symmetry of the context in the two rims.                                  *)

let MOI_FAN_CTX_SYM = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> moi_fan_ctx t la lm j2 j1 a2 a1 k21 k22 k11 k12`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fan_ctx] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S5C_ANN_SWAP THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[UNION_COMM];
    REWRITE_TAC[UNION_COMM];
    ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[UNION_ACI]]);;

let MOI_FAN_BSIDE_SYM = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2.
     moi_fan_bside t la lm j2 j1 = moi_fan_bside t la lm j1 j2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fan_bside] THEN
  SUBGOAL_THEN `j2 UNION j1 = j1 UNION (j2:real^3->bool)` SUBST1_TAC THENL
   [SET_TAC[]; SET_TAC[]]);;

let MOI_FAN_CSIDE_SYM = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2.
     moi_fan_cside t la lm j2 j1 = moi_fan_cside t la lm j1 j2`,
  REWRITE_TAC[moi_fan_cside; MOI_FAN_BSIDE_SYM]);;

let MOI_FAN_TRANSV2 = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 e y.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     e IN boundary_complex (derived_nbhd_complex t la) /\ e SUBSET UNIONS lm /\
     aff_dim e = &1 /\ e SUBSET k21 UNION k22 /\ y IN relative_interior e
     ==> y IN closure (moi_fan_bside t la lm j1 j2) /\
         y IN closure (moi_fan_cside t la lm j1 j2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[GSYM MOI_FAN_BSIDE_SYM; GSYM MOI_FAN_CSIDE_SYM] THEN
  MATCH_MP_TAC MOI_FAN_TRANSV1 THEN
  MAP_EVERY EXISTS_TAC [`a2:real^3->bool`; `a1:real^3->bool`; `k21:real^3->bool`;
                        `k22:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`;
                        `e:real^3->bool`] THEN
  ASM_SIMP_TAC[MOI_FAN_CTX_SYM]);;

(* Transversality on all of L: UNIONS L lies in the closures of both sides. *)

let MOI_FAN_TRANSV = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> UNIONS {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                     q SUBSET UNIONS lm} SUBSET
         closure (moi_fan_bside t la lm j1 j2) INTER
         closure (moi_fan_cside t la lm j1 j2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_L) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_T) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fan_ctx]) THEN STRIP_TAC THEN
  ABBREV_TAC `l = {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                       q SUBSET UNIONS (lm:(real^3->bool)->bool)}` THEN
  ABBREV_TAC `cl = closure (moi_fan_bside t la lm j1 j2) INTER
                   closure (moi_fan_cside t la lm (j1:real^3->bool) j2)` THEN
  SUBGOAL_THEN `closed (cl:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "cl" THEN SIMP_TAC[CLOSED_INTER; CLOSED_CLOSURE]; ALL_TAC] THEN
  SUBGOAL_THEN `!e:real^3->bool. e IN l /\ aff_dim e = &1 ==> e SUBSET cl` ASSUME_TAC THENL
   [X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e:real^3->bool) IN boundary_complex (derived_nbhd_complex t la) /\
                  e SUBSET UNIONS lm` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(e:real^3->bool) IN l` THEN EXPAND_TAC "l" THEN REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex (e:real^3->bool) /\ closed e` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `lf_simplicial_complex (boundary_complex (derived_nbhd_complex t
                      (la:(real^3->bool)->bool)))` ASSUME_TAC THENL
       [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
      ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX; MOI_FM3_LF_COMPACT;
                    COMPACT_IMP_CLOSED];
      ALL_TAC] THEN
    SUBGOAL_THEN `relative_interior (e:real^3->bool) SUBSET cl` ASSUME_TAC THENL
     [SUBGOAL_THEN `(e:real^3->bool) SUBSET k11 UNION k12 \/ e SUBSET k21 UNION k22`
      MP_TAC THENL
       [MATCH_MP_TAC MOI_FAN_CONNECTED_SPLIT THEN
        ASM_SIMP_TAC[CONVEX_CONNECTED] THEN
        MP_TAC(ISPECL [`a1:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`]
          MOI_FCB_ANN_ENDS_FACTS) THEN
        MP_TAC(ISPECL [`a2:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`]
          MOI_FCB_ANN_ENDS_FACTS) THEN
        ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        ASM_SIMP_TAC[CLOSED_UNION; COMPACT_IMP_CLOSED] THENL
         [SUBGOAL_THEN `(e:real^3->bool) SUBSET UNIONS l` MP_TAC THENL
           [ASM_MESON_TAC[SET_RULE `!q:real^3->bool k. q IN k ==> q SUBSET UNIONS k`];
            ALL_TAC] THEN
          ASM_REWRITE_TAC[UNION_ASSOC];
          MP_TAC(SPEC_ALL MOI_FAN_CTX_M) THEN ASM_REWRITE_TAC[moi_fan_ctx] THEN
          STRIP_TAC THEN
          UNDISCH_TAC `DISJOINT (a1:real^3->bool) a2` THEN
          UNDISCH_TAC `k11 UNION k12 SUBSET (a1:real^3->bool)` THEN
          UNDISCH_TAC `k21 UNION k22 SUBSET (a2:real^3->bool)` THEN SET_TAC[]];
        ALL_TAC] THEN
      STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      EXPAND_TAC "cl" THEN REWRITE_TAC[IN_INTER] THENL
       [MATCH_MP_TAC MOI_FAN_TRANSV1; MATCH_MP_TAC MOI_FAN_TRANSV2] THEN
      MAP_EVERY EXISTS_TAC [`a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                            `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                            `e:real^3->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `closure(relative_interior e) SUBSET (cl:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `x:real^3` THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `aff_dim (s:real^3->bool) = -- &1 \/ aff_dim s = &0 \/ aff_dim s = &1`
  MP_TAC THENL
   [MP_TAC(ISPEC `s:real^3->bool` AFF_DIM_GE) THEN
    SUBGOAL_THEN `aff_dim (s:real^3->bool) <= &1` MP_TAC THENL
     [ASM_MESON_TAC[]; INT_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[AFF_DIM_EQ_MINUS1; AFF_DIM_EQ_0] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[NOT_IN_EMPTY];
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    UNDISCH_TAC `(x:real^3) IN {a}` THEN REWRITE_TAC[IN_SING] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
    SUBGOAL_THEN `~({e | e IN l /\ aff_dim e = &1 /\ (x:real^3) IN e} = {})` MP_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `!v:real^3. {v} IN l
                     ==> CARD {e | e IN l /\ aff_dim e = &1 /\ v IN e} = 2` THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[CARD_CLAUSES] THEN
      ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC)] THEN
    ASM_MESON_TAC[SUBSET];
    ASM_MESON_TAC[SUBSET]]);;

(* ========================================================================= *)
(* Step C, the side surfaces closure B and closure Cc, from                  *)
(* MOI_FCS_CLOPEN_SIDES (pc_moi_fnd_clsides).                                *)
(* ========================================================================= *)

(* Step C, the side surfaces.  The statement of MOI_FCS_CLOPEN_SIDES         *)
(* (pc_moi_fnd_clsides) is the antecedent of the proof below, discharged by  *)
(* that theorem.                                                             *)

let moi_fan_clopen_ant = concl MOI_FCS_CLOPEN_SIDES;;

(* The hypotheses of MOI_FCS_CLOPEN_SIDES for (K, L, B, Cc), and the two   *)
(* side surfaces: closure B and closure Cc are compact surfaces whose      *)
(* boundary is the four end circles.                                         *)

let MOI_FAN_CTX_SIDE_SURFACES = MP (prove
 (mk_imp(inst [`:3`,`:N`] moi_fan_clopen_ant,
  `!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> FINITE {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                     q SUBSET closure (moi_fan_bside t la lm j1 j2)} /\
         combinatorial_manifold_with_boundary 2
           {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                q SUBSET closure (moi_fan_bside t la lm j1 j2)} /\
         UNIONS {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                     q SUBSET closure (moi_fan_bside t la lm j1 j2)} =
           closure (moi_fan_bside t la lm j1 j2) /\
         surface_boundary {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                               q SUBSET closure (moi_fan_bside t la lm j1 j2)} =
           k11 UNION k12 UNION k21 UNION k22 /\
         FINITE {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                     q SUBSET closure (moi_fan_cside t la lm j1 j2)} /\
         combinatorial_manifold_with_boundary 2
           {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                q SUBSET closure (moi_fan_cside t la lm j1 j2)} /\
         UNIONS {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                     q SUBSET closure (moi_fan_cside t la lm j1 j2)} =
           closure (moi_fan_cside t la lm j1 j2) /\
         surface_boundary {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                               q SUBSET closure (moi_fan_cside t la lm j1 j2)} =
           k11 UNION k12 UNION k21 UNION k22`),
  DISCH_THEN(LABEL_TAC "cl") THEN
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_T) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_L) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_SIDES) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_FAN_TRANSV) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fan_ctx]) THEN STRIP_TAC THEN
  ABBREV_TAC `kk = boundary_complex (derived_nbhd_complex t (la:(real^3->bool)->bool))` THEN
  ABBREV_TAC `ll = {q | q IN kk /\ q SUBSET UNIONS (lm:(real^3->bool)->bool)}` THEN
  ABBREV_TAC `X = UNIONS la DIFF (j1 UNION j2:real^3->bool)` THEN
  ABBREV_TAC `bb = moi_fan_bside t la lm (j1:real^3->bool) j2` THEN
  ABBREV_TAC `cc = moi_fan_cside t la lm (j1:real^3->bool) j2` THEN
  SUBGOAL_THEN
   `bb UNION cc = derived_frontier t la DIFF UNIONS lm /\ DISJOINT bb (cc:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["bb"; "cc"] THEN REWRITE_TAC[moi_fan_cside] THEN
    REWRITE_TAC[moi_fan_bside] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `surface_boundary (kk:(real^3->bool)->bool) = {}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `kk:(real^3->bool)->bool` SURF_CHARTS) THEN
    ASM_SIMP_TAC[MOI_S8TA_CM_CMB];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j1:real^3->bool`] MOI_FAN_MC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j2:real^3->bool`] MOI_FAN_MC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j1:real^3->bool`; `X:real^3->bool`]
    MOI_FAN_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (X:real^3->bool) (UNIONS lm)` THEN
    UNDISCH_TAC `moi_fan_mc lm j1 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j2:real^3->bool`; `X:real^3->bool`]
    MOI_FAN_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (X:real^3->bool) (UNIONS lm)` THEN
    UNDISCH_TAC `moi_fan_mc lm j2 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN
   `bb = (derived_frontier t la DIFF UNIONS lm) INTER
         (moi_fan_side lm j1 X INTER moi_fan_side lm j2 (X:real^3->bool)) /\
    cc = (derived_frontier t la DIFF UNIONS lm) INTER
         (moi_fan_far lm j1 X UNION moi_fan_far lm j2 (X:real^3->bool))`
  (CONJUNCTS_THEN (ASSUME_TAC o SYM)) THENL
   [MAP_EVERY EXPAND_TAC ["bb"; "cc"] THEN REWRITE_TAC[moi_fan_cside; moi_fan_bside] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_fan_side lm j1 X UNION moi_fan_far lm j1 X =
                 (:real^3) DIFF moi_fan_mc lm j1` THEN
    UNDISCH_TAC `moi_fan_side lm j2 X UNION moi_fan_far lm j2 X =
                 (:real^3) DIFF moi_fan_mc lm j2` THEN
    UNDISCH_TAC `DISJOINT (moi_fan_side lm j1 X) (moi_fan_far lm j1 (X:real^3->bool))` THEN
    UNDISCH_TAC `DISJOINT (moi_fan_side lm j2 X) (moi_fan_far lm j2 (X:real^3->bool))` THEN
    UNDISCH_TAC `moi_fan_mc lm j1 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `moi_fan_mc lm j2 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS kk DIFF UNIONS ll =
                derived_frontier (t:(real^3->bool)->bool) la DIFF UNIONS lm`
  ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS kk = derived_frontier (t:(real^3->bool)->bool) la` THEN
    UNDISCH_TAC `UNIONS ll = derived_frontier (t:(real^3->bool)->bool) la INTER UNIONS lm` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!K1 K2. K1 UNION K2 = derived_frontier t la DIFF UNIONS lm /\ DISJOINT K1 K2 /\
            open_in (subtopology euclidean (derived_frontier t la DIFF UNIONS lm)) K1 /\
            open_in (subtopology euclidean (derived_frontier t la DIFF UNIONS lm)) K2 /\
            UNIONS ll SUBSET closure K1 /\ UNIONS ll SUBSET closure K2
            ==> FINITE {q | q IN kk /\ q SUBSET closure K1} /\
                combinatorial_manifold_with_boundary 2 {q | q IN kk /\ q SUBSET closure K1} /\
                UNIONS {q | q IN kk /\ q SUBSET closure K1} = closure K1 /\
                surface_boundary {q | q IN kk /\ q SUBSET closure K1} =
                k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`
  (LABEL_TAC "sf") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "cl" (MP_TAC o ISPECL [`kk:(real^3->bool)->bool`; `ll:(real^3->bool)->bool`;
                                    `K1:real^3->bool`; `K2:real^3->bool`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[MOI_S8TA_CM_CMB; DISJOINT_EMPTY];
      ASM_REWRITE_TAC[INTER_EMPTY; UNION_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open (moi_fan_side lm j1 X INTER moi_fan_side lm j2 (X:real^3->bool)) /\
    open (moi_fan_far lm j1 X UNION moi_fan_far lm j2 (X:real^3->bool))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; OPEN_UNION]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (derived_frontier t la DIFF UNIONS lm)) bb /\
    open_in (subtopology euclidean (derived_frontier t la DIFF UNIONS lm)) (cc:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(derived_frontier t la DIFF UNIONS lm) INTER
                 (moi_fan_side lm j1 X INTER moi_fan_side lm j2 (X:real^3->bool)) = bb` THEN
    UNDISCH_TAC `(derived_frontier t la DIFF UNIONS lm) INTER
                 (moi_fan_far lm j1 X UNION moi_fan_far lm j2 (X:real^3->bool)) = cc` THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
    CONJ_TAC THEN MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS ll SUBSET closure bb /\ UNIONS ll SUBSET closure (cc:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS ll SUBSET closure bb INTER closure (cc:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "sf" (MP_TAC o SPECL [`bb:real^3->bool`; `cc:real^3->bool`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "sf" (MP_TAC o SPECL [`cc:real^3->bool`; `bb:real^3->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `bb UNION cc = derived_frontier t la DIFF UNIONS (lm:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `DISJOINT bb (cc:real^3->bool)` THEN SET_TAC[];
    STRIP_TAC] THEN
  ASM_REWRITE_TAC[]))
 (INST_TYPE [`:3`,`:N`] MOI_FCS_CLOPEN_SIDES);;

(* ========================================================================= *)
(* The statement MOI_FAN_FRONTIER_CONNECTED_TERM: the frontier is connected  *)
(* (proved below as MOI_FAN_FRONTIER_CONNECTED).  The rim analysis of step D *)
(* uses MOI_FAN_EDGE_CYCLE, which also lists all simplices on the edge.      *)
(* ========================================================================= *)

let MOI_FAN_FRONTIER_CONNECTED_TERM =
 `!(t:(real^3->bool)->bool) la j1 j2.
     FINITE t /\ combinatorial_manifold_with_boundary 3 t /\
     simplicial_subcomplex la t /\
     pl_annulus_with_ends (UNIONS la) j1 j2 /\
     DISJOINT (derived_nbhd t la) (complex_boundary t)
     ==> connected (derived_frontier t la)`;;

let moi_fan_iface_ok =
  type_of MOI_FAN_FRONTIER_CONNECTED_TERM = bool_ty &&
  frees MOI_FAN_FRONTIER_CONNECTED_TERM = [];;

if not moi_fan_iface_ok then failwith "moi_fan_iface_ok";;

(* ========================================================================= *)
(* MOI_FAN_FRONTIER_CONNECTED: the frontier of the second derived            *)
(* neighbourhood N of a PL annulus in the interior of a compact              *)
(* combinatorial 3-manifold in real^3 is connected (the statement            *)
(* MOI_FAN_FRONTIER_CONNECTED_TERM).  Route: N lies in the interior of       *)
(* UNIONS t, so its derived frontier is its frontier; N deformation retracts *)
(* onto the annulus, which is homeomorphic to the square annulus, which      *)
(* deformation retracts onto the inner square (MOI_FH1_ANNULUS_RETRACT), a   *)
(* PL circle and so homeomorphic to the union of three segments; hence the   *)
(* complement of N is connected (MOI_S3FR_COMPLEMENT_CONNECTED) and          *)
(* unicoherence (CONNECTED_FRONTIER_SIMPLE) gives the claim.  Files used:    *)
(* pc_moi_s33_frame.ml (MOI_S3FR_COMPLEMENT_CONNECTED; it also brings        *)
(* pc_moi_fnd_tubeb.ml with MOI_FTB_FRONTIER_OF_OPEN_PART), pc_moi_fnd_h1.ml *)
(* (MOI_FH1_ANNULUS_RETRACT), pc_moi_fnd_rn.ml                               *)
(* (DERIVED_NBHD_DEFORMATION_RETRACT), pc_moi_s35_minc.ml                    *)
(* (MOI_S5C_ANN_CONNECTED), pc_moi_fnd_m3a.ml (COMPLEX_BOUNDARY_FRONTIER_3), *)
(* pc_moi_fnd_dn.ml (DERIVED_NBHD_BASIC), pc_moi_fnd_plst.ml                 *)
(* (MOI_FPS_SQ_PL_SPHERE, MOI_FPS_VEC1_2), pc_moi_pl2.ml                     *)
(* (MOI_PL2_SIMPLEX_2).                                                      *)
(* ========================================================================= *)

(* The square annulus is homotopy equivalent to its inner square. *)

let MOI_FAN_I1_SQ_ANN_HEQ = prove
 (`(interval[--vector[&2;&2],vector[&2;&2]] DIFF
    interval(--vector[&1;&1],vector[&1;&1]):real^2->bool)
   homotopy_equivalent relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`,
  MATCH_MP_TAC DEFORMATION_RETRACT_IMP_HOMOTOPY_EQUIVALENT THEN
  EXISTS_TAC `\x:real^2. (&1 * inv(infnorm x)) % x` THEN
  MP_TAC(SPEC `&1` MOI_FH1_ANNULUS_RETRACT) THEN REWRITE_TAC[] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN ASM_REWRITE_TAC[CONTINUOUS_ON_ID];
    ASM_REWRITE_TAC[retraction]]);;

(* A PL circle is homeomorphic to a union of three segments. *)

let MOI_FAN_I1_SPHERE1_SEGS = prove
 (`!s:real^N->bool.
     pl_sphere 1 s
     ==> ?k:(real^N->bool)->bool.
           FINITE k /\ (!c. c IN k ==> ?a b. c = segment[a,b]) /\
           s homeomorphic UNIONS k`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `kk:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_2]) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `{segment[a:real^N,b], segment[b,c], segment[c,a]}` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THENL [MESON_TAC[]; MESON_TAC[]; MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[UNIONS_INSERT; UNIONS_0; UNION_EMPTY] THEN
  SUBGOAL_THEN `segment[a,b] UNION segment[b,c] UNION segment[c,a] =
                relative_frontier(kk:real^N->bool)`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC RELATIVE_FRONTIER_OF_TRIANGLE THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
  MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_MESON_TAC[pl_homeomorphism]);;

(* A PL annulus is homotopy equivalent to a finite union of segments. *)

let MOI_FAN_I1_ANN_HEQ = prove
 (`!(a:real^N->bool) j1 j2.
     pl_annulus_with_ends a j1 j2
     ==> ?k:(real^2->bool)->bool.
           FINITE k /\ (!c. c IN k ==> ?u v. c = segment[u,v]) /\
           a homotopy_equivalent UNIONS k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_annulus_with_ends] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPEC `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`
    MOI_FAN_I1_SPHERE1_SEGS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[GSYM MOI_FPS_VEC1_2; GSYM moi_fps_sq; MOI_FPS_SQ_PL_SPHERE]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:(real^2->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(ISPECL
   [`a:real^N->bool`;
    `interval[--vector[&2;&2],vector[&2;&2]] DIFF
     interval(--vector[&1;&1],vector[&1;&1]):real^2->bool`;
    `UNIONS k:real^2->bool`] HOMOTOPY_EQUIVALENT_TRANS) THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^2->real^N`; `g:real^N->real^2`] THEN
    ASM_MESON_TAC[pl_homeomorphism];
    ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`interval[--vector[&2;&2],vector[&2;&2]] DIFF
     interval(--vector[&1;&1],vector[&1;&1]):real^2->bool`;
    `relative_frontier(interval[--vector[&1;&1]:real^2,vector[&1;&1]])`;
    `UNIONS k:real^2->bool`] HOMOTOPY_EQUIVALENT_TRANS) THEN
  REWRITE_TAC[MOI_FAN_I1_SQ_ANN_HEQ] THEN
  MATCH_MP_TAC HOMEOMORPHIC_IMP_HOMOTOPY_EQUIVALENT THEN FIRST_ASSUM ACCEPT_TAC);;

(* MOI_FAN_FRONTIER_CONNECTED. *)

let MOI_FAN_FRONTIER_CONNECTED = prove
 (MOI_FAN_FRONTIER_CONNECTED_TERM,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (la:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `N = derived_nbhd t (la:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `(N:real^3->bool) SUBSET interior(UNIONS t)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    UNDISCH_TAC `DISJOINT (N:real^3->bool) (complex_boundary t)` THEN
    UNDISCH_TAC `(N:real^3->bool) SUBSET UNIONS t` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `derived_frontier t la = frontier (N:real^3->bool)` SUBST1_TAC THENL
   [EXPAND_TAC "N" THEN REWRITE_TAC[derived_frontier] THEN
    MATCH_MP_TAC MOI_FTB_FRONTIER_OF_OPEN_PART THEN
    EXISTS_TAC `interior(UNIONS (t:(real^3->bool)->bool))` THEN
    ASM_SIMP_TAC[OPEN_INTERIOR; INTERIOR_SUBSET; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(N:real^3->bool) homotopy_equivalent UNIONS (la:(real^3->bool)->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "N" THEN MATCH_MP_TAC DEFORMATION_RETRACT_IMP_HOMOTOPY_EQUIVALENT THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`]
      DERIVED_NBHD_DEFORMATION_RETRACT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->real^3` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    EXISTS_TAC `r:real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN
    EXISTS_TAC `\h:real^3->real^3. !x. x IN UNIONS la ==> h x = x` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_FRONTIER_SIMPLE THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`N:real^3->bool`; `UNIONS la:real^3->bool`]
      HOMOTOPY_EQUIVALENT_CONNECTEDNESS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_S5C_ANN_CONNECTED THEN
    MAP_EVERY EXISTS_TAC [`j1:real^3->bool`; `j2:real^3->bool`] THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`UNIONS la:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
      MOI_FAN_I1_ANN_HEQ) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC(ISPECL [`N:real^3->bool`; `k:(real^2->bool)->bool`]
      MOI_S3FR_COMPLEMENT_CONNECTED) THEN
    ASM_REWRITE_TAC[DIMINDEX_3; LE_REFL] THEN
    MATCH_MP_TAC(ISPECL [`N:real^3->bool`; `UNIONS la:real^3->bool`;
                         `UNIONS k:real^2->bool`] HOMOTOPY_EQUIVALENT_TRANS) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Step D tools: the cycle around an edge at an interior vertex, the far     *)
(* vertices W(tau) of the tetrahedra on a triangle of ldT, which lie in B.   *)
(* ========================================================================= *)

(* ========================================================================= *)
(* Step D tools: the cycle around an edge of a 3-complex at a vertex with  *)
(* a 2-sphere link (the cycle part of MOI_FSP_SIDE_CYCLE, for any edge),   *)
(* with every triangle and every tetrahedron on the edge in the fan.       *)
(* ========================================================================= *)

(* A tetrahedron of a complex containing an edge [v0,y0] of the complex is *)
(* the hull of v0, y0 and two further vertices.                              *)

let MOI_FAN_TET_EDGE = prove
 (`!(tt:(real^N->bool)->bool) r v0 y0.
     lf_simplicial_complex tt /\ r IN tt /\ aff_dim r = &3 /\
     segment[v0,y0] IN tt /\ ~(v0 = y0) /\ segment[v0,y0] SUBSET r
     ==> ?a b. r = convex hull {v0,y0,a,b} /\ ~affine_dependent {v0,y0,a,b} /\
               ~(a = b) /\ ~(a = v0) /\ ~(a = y0) /\ ~(b = v0) /\ ~(b = y0) /\
               {a} IN tt /\ {b} IN tt`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&3 simplex (r:real^N->bool)` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `aff_dim (r:real^N->bool) = &3`)) THEN
    MATCH_MP_TAC MOI_FM3_LF_SIMPLEX THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool) /\ CARD V = 4` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD (V:real^N->bool)):int = &3 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v0:real^N,y0] face_of r` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN EXISTS_TAC `tt:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v0:real^N) IN V /\ (y0:real^N) IN V` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL THEN
    FIRST_ASSUM(fun th -> if concl th = `r = convex hull (V:real^N->bool)`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    ASM_MESON_TAC[EXTREME_POINT_OF_FACE; EXTREME_POINT_OF_SEGMENT; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(V DELETE (v0:real^N) DELETE y0) HAS_SIZE 2` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN ASM_SIMP_TAC[FINITE_DELETE; CARD_DELETE; IN_DELETE] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `V = {v0:real^N,y0,a,b}` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `V DELETE (v0:real^N) DELETE y0 = {a,b}` THEN
    UNDISCH_TAC `(v0:real^N) IN V` THEN UNDISCH_TAC `(y0:real^N) IN V` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(a:real^N = v0) /\ ~(a = y0) /\ ~(b = v0) /\ ~(b = y0)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{v0:real^N,y0,a,b} DELETE v0 DELETE y0 = {a,b}` THEN SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `r:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THENL
   [EXISTS_TAC `{a:real^N}`; EXISTS_TAC `{b:real^N}`] THEN
  REWRITE_TAC[CONVEX_HULL_SING] THEN SET_TAC[]);;

(* The cycle U around an edge [v0,y0] of tt at a vertex v0 whose link is a *)
(* 2-sphere: the fan of triangles and tetrahedra on the edge.               *)

let MOI_FAN_EDGE_CYCLE = prove
 (`!(tt:(real^N->bool)->bool) v0 y0.
     lf_simplicial_complex tt /\ {v0} IN tt /\ segment[v0,y0] IN tt /\ ~(v0 = y0) /\
     pl_sphere 2 (UNIONS (simplicial_link tt v0))
     ==> ?dd (U:num->real^N).
           3 <= dd /\ (!i. U(i + dd) = U i) /\
           (!i j. i < dd /\ j < dd /\ U i = U j ==> i = j) /\
           (!i. ~(U i = U(SUC i))) /\ (!i. ~(U i = y0)) /\
           (!i. convex hull {v0, y0, U i} IN tt /\ aff_dim (convex hull {v0, y0, U i}) = &2 /\
                segment[v0,y0] SUBSET convex hull {v0, y0, U i} /\
                ~(U i = v0) /\ {U i} IN tt /\ segment[U i,U(SUC i)] IN tt /\
                convex hull {v0, y0, U i, U(SUC i)} IN tt /\
                aff_dim (convex hull {v0, y0, U i, U(SUC i)}) = &3 /\
                segment[U i,U(SUC i)] SUBSET convex hull {v0, y0, U i, U(SUC i)} /\
                convex hull {v0, y0, U i} SUBSET convex hull {v0, y0, U i, U(SUC i)} /\
                convex hull {v0, y0, U(SUC i)} SUBSET convex hull {v0, y0, U i, U(SUC i)}) /\
           (!r. r IN tt /\ aff_dim r = &2 /\ segment[v0,y0] SUBSET r
                ==> ?i. i < dd /\ r = convex hull {v0, y0, U i}) /\
           (!i j. convex hull {v0, y0, U i} = convex hull {v0, y0, U j} ==> U i = U j) /\
           (!r. r IN tt /\ aff_dim r = &3 /\ segment[v0,y0] SUBSET r
                ==> ?i. i < dd /\ r = convex hull {v0, y0, U i, U(SUC i)})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (simplicial_link tt (v0:real^N)) /\
                combinatorial_manifold 2 (simplicial_link tt (v0:real^N))`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSP_LINK_CM2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{y0:real^N} IN simplicial_link tt v0` ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[IN_SING] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `segment[v0:real^N,y0]` THEN
      ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      EXISTS_TAC `segment[v0:real^N,y0]` THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT; FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`simplicial_link tt (v0:real^N)`; `y0:real^N`] MOI_FN2_ROT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:num` (X_CHOOSE_THEN `U:num->real^N` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `v0:real^N`; `y0:real^N`; `dd:num`; `U:num->real^N`]
    MOI_FSP_FAN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  SUBGOAL_THEN `3 <= dd /\ (!i. (U:num->real^N)(i + dd) = U i) /\
                (!i j. i < dd /\ j < dd /\ (U:num->real^N) i = U j ==> i = j)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fn2_kcyc (simplicial_link (simplicial_link tt v0) y0) dd (U:num->real^N)` THEN
    REWRITE_TAC[moi_fn2_kcyc] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. ~((U:num->real^N) i = U(SUC i))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC_ALL THEN EXISTS_TAC `dd:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`dd:num`; `U:num->real^N`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `r:real^N->bool`; `v0:real^N`; `y0:real^N`]
    MOI_FAN_TET_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `convex hull {y0:real^N,a,b} face_of r /\ segment[a:real^N,b] face_of r`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN CONJ_TAC THENL
     [EXISTS_TAC `{y0:real^N,a,b}` THEN SET_TAC[];
      EXISTS_TAC `{a:real^N,b}` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {y0:real^N,a,b} IN tt /\ segment[a:real^N,b] IN tt`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v0:real^N) IN convex hull {y0,a,b}) /\ ~((y0:real^N) IN segment[a,b])`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    UNDISCH_TAC `~affine_dependent {v0:real^N,y0,a,b}` THEN
    REWRITE_TAC[affine_dependent; NOT_EXISTS_THM] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `v0:real^N` th) THEN MP_TAC(SPEC `y0:real^N` th)) THEN
    REWRITE_TAC[IN_INSERT] THEN
    SUBGOAL_THEN `{v0:real^N,y0,a,b} DELETE v0 = {y0,a,b} /\
                  {v0:real^N,y0,a,b} DELETE y0 = {v0,a,b}` (fun th -> REWRITE_TAC[th]) THENL
     [MAP_EVERY UNDISCH_TAC [`~(v0:real^N = y0)`; `~(a:real^N = v0)`; `~(a:real^N = y0)`;
                             `~(b:real^N = v0)`; `~(b:real^N = y0)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `{y0:real^N,a,b}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
    MP_TAC(ISPEC `{a:real^N,b}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
    MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `{a:real^N,b}`; `{v0:real^N,a,b}`] HULL_MONO) THEN
    ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[a:real^N,b] IN simplicial_link (simplicial_link tt v0) y0`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(v0:real^N) IN r /\ (y0:real^N) IN convex hull {y0,a,b} /\
                  segment[a:real^N,b] SUBSET convex hull {y0,a,b} /\
                  convex hull {y0:real^N,a,b} SUBSET r /\ ~((v0:real^N) IN segment[a,b])`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET];
        MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
        UNDISCH_TAC `~((v0:real^N) IN convex hull {y0,a,b})` THEN
        MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `{a:real^N,b}`; `{y0:real^N,a,b}`]
          HULL_MONO) THEN
        ANTS_TAC THENL [SET_TAC[]; REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN SET_TAC[]]];
      ALL_TAC] THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `convex hull {y0:real^N,a,b}` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC FACE_OF_SUBSET THEN EXISTS_TAC `r:real^N->bool` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_fn2_kcyc (simplicial_link (simplicial_link tt v0) y0) dd (U:num->real^N)` THEN
  REWRITE_TAC[moi_fn2_kcyc] THEN
  DISCH_THEN(MP_TAC o SPEC `segment[a:real^N,b]` o el 5 o CONJUNCTS) THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `i:num` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `segment[a:real^N,b] = segment[U(i:num),U(SUC i)]` THEN
  REWRITE_TAC[SEGMENT_EQ] THEN DISCH_TAC THEN
  AP_TERM_TAC THEN ASM SET_TAC[]);;

(* ========================================================================= *)
(* Step D context: the second derived complexes of t and la, vertex links  *)
(* at the annulus, and the far vertices W(tau) of the two tetrahedra of     *)
(* T = bsd(bsd t) on a triangle tau of ldT = bsd(bsd la).                   *)
(* ========================================================================= *)

let moi_fan_w = new_definition
 `moi_fan_w (t:(real^3->bool)->bool) (la:(real^3->bool)->bool) (tau:real^3->bool) =
    {w | {w} IN barycentric_subdivision (barycentric_subdivision t) /\
         ~(w IN UNIONS la) /\
         ?d. d IN barycentric_subdivision (barycentric_subdivision t) /\
             aff_dim d = &3 /\ tau SUBSET d /\ w IN d}`;;

let MOI_FAN_CTX_D = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> FINITE (barycentric_subdivision (barycentric_subdivision t)) /\
         combinatorial_manifold_with_boundary 3
           (barycentric_subdivision (barycentric_subdivision t)) /\
         (!w. {w} IN barycentric_subdivision (barycentric_subdivision t) /\ w IN UNIONS la
              ==> pl_sphere 2 (UNIONS (simplicial_link
                    (barycentric_subdivision (barycentric_subdivision t)) w))) /\
         FINITE (barycentric_subdivision (barycentric_subdivision la)) /\
         combinatorial_manifold_with_boundary 2
           (barycentric_subdivision (barycentric_subdivision la)) /\
         surface_boundary (barycentric_subdivision (barycentric_subdivision la)) =
           j1 UNION j2 /\
         UNIONS (barycentric_subdivision (barycentric_subdivision la)) = UNIONS la /\
         simplicial_subcomplex (barycentric_subdivision (barycentric_subdivision la))
           (barycentric_subdivision (barycentric_subdivision t)) /\
         lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision la)) /\
         connected (UNIONS la)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th)) THEN
  ABBREV_TAC `tt = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  ABBREV_TAC `ldT = barycentric_subdivision (barycentric_subdivision (la:(real^3->bool)->bool))` THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] MOI_FSP_BSD2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (tt:(real^3->bool)->bool) /\ FINITE (ldT:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tt"; "ldT"] THEN CONJ_TAC THEN
    REPEAT(MATCH_MP_TAC MOI_BAR_SUBDIVISION_FINITE) THEN
    ASM_MESON_TAC[FINITE_SUBSET; simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3 (tt:(real^3->bool)->bool) /\
                complex_boundary tt = complex_boundary (t:(real^3->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:(real^3->bool)->bool` COMBINATORIAL_WB_BARYCENTRIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPEC `barycentric_subdivision (t:(real^3->bool)->bool)`
      COMBINATORIAL_WB_BARYCENTRIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `lf_simplicial_complex (ldT:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `tt:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (UNIONS la:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S5C_ANN_CONNECTED]; ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 2 (ldT:(real^3->bool)->bool) /\
                surface_boundary ldT = j1 UNION (j2:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS la:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
      ANNULUS_COMPLEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `ldT:(real^3->bool)->bool`;
                   `\x:real^3. x`; `\x:real^3. x`] MOI_FRB_SURF_INVARIANT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF; HOMEOMORPHISM_ID];
      REWRITE_TAC[IMAGE_ID] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rhs(concl th) = `surface_boundary (ldT:(real^3->bool)->bool)`)) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPEC `tt:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `w:real^3` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  SUBGOAL_THEN `UNIONS la SUBSET derived_nbhd t (la:(real^3->bool)->bool)` MP_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(MP_TAC o el 5 o CONJUNCTS)] THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS (t:(real^3->bool)->bool))`;
                   `derived_nbhd t (la:(real^3->bool)->bool)`] INTERIOR_OF_SUBSET) THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `DISJOINT (derived_nbhd t la) (complex_boundary (t:(real^3->bool)->bool))` THEN
  UNDISCH_TAC `(w:real^3) IN UNIONS la` THEN SET_TAC[]);;

(* Two vertices of a simplex of a complex span an edge of the complex.      *)

let MOI_FAN_VERTEX_EDGE = prove
 (`!(c:(real^N->bool)->bool) d p w.
     lf_simplicial_complex c /\ d IN c /\ {p} IN c /\ {w} IN c /\ p IN d /\ w IN d
     ==> segment[p,w] IN c /\ {p} face_of d /\ {w} face_of d`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{p:real^N} face_of d /\ {w:real^N} face_of d` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `aff_dim d simplex (d:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SIMPLEX THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(p:real^N) IN V /\ (w:real^N) IN V` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL THEN
    FIRST_ASSUM(fun th -> if concl th = `d = convex hull (V:real^N->bool)`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    ASM_MESON_TAC[FACE_OF_SING];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `d:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(fun th -> if concl th = `d = convex hull (V:real^N->bool)`
    then REWRITE_TAC[th] else failwith "no") THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  EXISTS_TAC `{p:real^N,w}` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN ASM SET_TAC[]);;

(* Every triangle of ldT has a vertex off the rims (a triangle in the      *)
(* surface boundary j1 UNION j2 is impossible).                             *)

let MOI_FAN_TRI_OFF_RIM = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 tau.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     tau IN barycentric_subdivision (barycentric_subdivision la) /\ aff_dim tau = &2
     ==> ?p. p IN tau /\ {p} IN barycentric_subdivision (barycentric_subdivision t) /\
             p IN UNIONS la /\ ~(p IN UNIONS lm)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_D th)) STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `tt = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  ABBREV_TAC `ldT = barycentric_subdivision (barycentric_subdivision (la:(real^3->bool)->bool))` THEN
  SUBGOAL_THEN `(tau:real^3->bool) IN tt` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&2 simplex (tau:real^3->bool)` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `aff_dim (tau:real^3->bool) = &2`)) THEN
    MATCH_MP_TAC MOI_FM3_LF_SIMPLEX THEN EXISTS_TAC `ldT:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((V:real^3->bool) SUBSET j1 UNION j2)` MP_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`ldT:(real^3->bool)->bool`; `tau:real^3->bool`] MOI_FSP_TRI_NOT_IN_SB) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`] MOI_FN2_SUBCOMPLEX_INTER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `(la:(real^3->bool)->bool) INTER lm`]
      MOI_FRN_SETUP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision ((la:(real^3->bool)->bool) INTER lm)`;
                   `V:real^3->bool`] MOI_FSP_HULL_FULL) THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `tau = convex hull (V:real^3->bool)`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p:real^3` THEN
  SUBGOAL_THEN `(p:real^3) IN tau` ASSUME_TAC THENL
   [ASM_MESON_TAC[HULL_SUBSET; SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(p:real^3) IN UNIONS la` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `UNIONS (ldT:(real^3->bool)->bool) = UNIONS la`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `tau:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `tau:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if concl th = `tau = convex hull (V:real^3->bool)`
      then REWRITE_TAC[th] else failwith "no") THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{p:real^3}` THEN REWRITE_TAC[CONVEX_HULL_SING] THEN ASM SET_TAC[];
    UNDISCH_TAC `~((p:real^3) IN j1 UNION j2)` THEN
    UNDISCH_TAC `UNIONS la INTER UNIONS lm = j1 UNION (j2:real^3->bool)` THEN
    UNDISCH_TAC `(p:real^3) IN UNIONS la` THEN SET_TAC[]]);;

(* The far vertices W(tau) of the tetrahedra on a triangle tau of ldT lie  *)
(* in F minus M, on the int a side of both rim components: they are in B. *)

let MOI_FAN_W_IN_B = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 tau.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     tau IN barycentric_subdivision (barycentric_subdivision la) /\ aff_dim tau = &2
     ==> moi_fan_w t la tau SUBSET moi_fan_bside t la lm j1 j2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    MP_TAC(MATCH_MP MOI_FAN_TRI_OFF_RIM th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `moi_fan_ctx (t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22` THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_D th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_SIDES th)) THEN
  REWRITE_TAC[SUBSET; moi_fan_w; IN_ELIM_THM] THEN
  X_GEN_TAC `w:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `d:real^3->bool` STRIP_ASSUME_TAC))) THEN
  ABBREV_TAC `tt = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  ABBREV_TAC `X = UNIONS la DIFF (j1 UNION j2:real^3->bool)` THEN
  SUBGOAL_THEN `(p:real^3) IN d` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^3->bool)->bool`; `d:real^3->bool`; `p:real^3`; `w:real^3`]
    MOI_FAN_VERTEX_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(p:real^3 = w)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((w:real^3) IN UNIONS la)` THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((w:real^3) IN UNIONS lm)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`; `p:real^3`; `w:real^3`] MOI_FSP_NO_CROSS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[p:real^3,w] INTER UNIONS lm = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                   `p:real^3`; `w:real^3`] MOI_FSP_SEG_FULL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN derived_frontier t la` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `{w:real^3}`]
      MOI_FSP_NC_FR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `d:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `p:real^3` THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `~((w:real^3) IN UNIONS la)` THEN SET_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN X` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN
    UNDISCH_TAC `UNIONS la INTER UNIONS lm = j1 UNION (j2:real^3->bool)` THEN
    UNDISCH_TAC `~((p:real^3) IN UNIONS lm)` THEN UNDISCH_TAC `(p:real^3) IN UNIONS la` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j:real^3->bool. connected j /\ ~(j = {}) /\ j SUBSET UNIONS lm
                     ==> (w:real^3) IN moi_fan_side lm j X`
  ASSUME_TAC THENL
   [X_GEN_TAC `j:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j:real^3->bool`] MOI_FAN_MC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j:real^3->bool`; `X:real^3->bool`]
      MOI_FAN_SIDES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (X:real^3->bool) (UNIONS lm)` THEN
      UNDISCH_TAC `moi_fan_mc lm j SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`segment[p:real^3,w]`; `moi_fan_side lm j (X:real^3->bool)`;
                   `moi_fan_far lm j (X:real^3->bool)`] MOI_FAN_CONN_OPEN_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CONNECTED_SEGMENT] THEN
      UNDISCH_TAC `segment[p:real^3,w] INTER UNIONS lm = {}` THEN
      UNDISCH_TAC `moi_fan_mc lm j SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:real^3`; `w:real^3`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `(X:real^3->bool) SUBSET moi_fan_side lm j X` THEN
    UNDISCH_TAC `(p:real^3) IN X` THEN
    UNDISCH_TAC `DISJOINT (moi_fan_side lm j X) (moi_fan_far lm j (X:real^3->bool))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fan_bside; IN_INTER; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The statement MOI_FAN_COUNT_TERM, the Euler count of step E.              *)
(* ========================================================================= *)

let MOI_FAN_COUNT_TERM =
 `!(kb:(real^N->bool)->bool) kc e1 e2 e3 e4.
     FINITE kb /\ combinatorial_manifold_with_boundary 2 kb /\
     FINITE kc /\ combinatorial_manifold_with_boundary 2 kc /\
     surface_boundary kb = e1 UNION e2 UNION e3 UNION e4 /\
     surface_boundary kc = e1 UNION e2 UNION e3 UNION e4 /\
     connected e1 /\ connected e2 /\ connected e3 /\ connected e4 /\
     compact e1 /\ compact e2 /\ compact e3 /\ compact e4 /\
     ~(e1 = {}) /\ ~(e2 = {}) /\ ~(e3 = {}) /\ ~(e4 = {}) /\
     DISJOINT e1 e2 /\ DISJOINT e1 e3 /\ DISJOINT e1 e4 /\
     DISJOINT e2 e3 /\ DISJOINT e2 e4 /\ DISJOINT e3 e4 /\
     complex_euler kb + complex_euler kc = &0 /\
     (!c. c IN components (UNIONS kb)
          ==> ~(c INTER (e1 UNION e2 UNION e3 UNION e4) = {})) /\
     (!c. c IN components (UNIONS kc)
          ==> ~(c INTER (e1 UNION e2 UNION e3 UNION e4) = {})) /\
     (?g. connected g /\ g SUBSET UNIONS kb /\
          ~(g INTER e1 = {}) /\ ~(g INTER (e3 UNION e4) = {})) /\
     (?g. connected g /\ g SUBSET UNIONS kb /\
          ~(g INTER e2 = {}) /\ ~(g INTER (e3 UNION e4) = {})) /\
     (?g. connected g /\ g SUBSET UNIONS kb /\
          ~(g INTER e3 = {}) /\ ~(g INTER (e1 UNION e2) = {})) /\
     (?g. connected g /\ g SUBSET UNIONS kb /\
          ~(g INTER e4 = {}) /\ ~(g INTER (e1 UNION e2) = {})) /\
     (?g. connected g /\ g SUBSET UNIONS kc /\
          ~(g INTER e1 = {}) /\ ~(g INTER e2 = {})) /\
     (?g. connected g /\ g SUBSET UNIONS kc /\
          ~(g INTER e3 = {}) /\ ~(g INTER e4 = {}))
     ==> ?b1 b2 c1 c2 f3 f4.
           ((f3 = e3 /\ f4 = e4) \/ (f3 = e4 /\ f4 = e3)) /\
           UNIONS kb = b1 UNION b2 /\ DISJOINT b1 b2 /\
           pl_annulus_with_ends b1 e1 f3 /\ pl_annulus_with_ends b2 e2 f4 /\
           UNIONS kc = c1 UNION c2 /\ DISJOINT c1 c2 /\
           pl_annulus_with_ends c1 e1 e2 /\ pl_annulus_with_ends c2 e3 e4`;;

let moi_fan_iface2_ok =
  type_of MOI_FAN_COUNT_TERM = bool_ty && frees MOI_FAN_COUNT_TERM = [];;

if not moi_fan_iface2_ok then failwith "moi_fan_iface2_ok";;


(* ------------------------------------------------------------------------- *)
(* MOI_FAN_COUNT proves MOI_FAN_COUNT_TERM.  Uses SURFACE_EULER_PLANAR       *)
(* (pc_moi_fnd_surfb), MOI_FCB_PLANAR_ANNULUS, MOI_FCB_END_CHOICE and        *)
(* MOI_FCB_TWO_COMPS (pc_moi_fnd_bcollar), COMPLEX_EULER_UNION               *)
(* (pc_moi_fnd_euler) and MOI_S5C_ANN_SWAP (pc_moi_s35_minc), all in the     *)
(* load closure of pc_moi_fnd_annnbhd.  Route: a component of a finite cm_wb *)
(* 2 complex gives a subcomplex with boundary the old boundary inside the    *)
(* component (cm_wb 2 version of MOI_FCL_CM2_COMPONENT); the witnesses       *)
(* leave, for each surface, one piece with all four end circles (Euler       *)
(* number at most -2) or two pieces with two circles each (Euler numbers at  *)
(* most 0, summing to that of the surface); the sum 0 forces two pieces of   *)
(* Euler number 0, which are annuli with the given ends.                     *)
(* ------------------------------------------------------------------------- *)

let MOI_FAN_I3_SB_SUBSET = prove
 (`!c:(real^N->bool)->bool. surface_boundary c SUBSET UNIONS c`,
  REWRITE_TAC[surface_boundary] THEN SET_TAC[]);;

(* The subcomplex at a component of a compact surface with boundary; the     *)
(* first three conclusions follow the proof of MOI_FCL_CM2_COMPONENT.        *)

let MOI_FAN_I3_COMPONENT = prove
 (`!(s:(real^N->bool)->bool) k.
     FINITE s /\ combinatorial_manifold_with_boundary 2 s /\ k IN components (UNIONS s)
     ==> FINITE {t | t IN s /\ t SUBSET k} /\
         combinatorial_manifold_with_boundary 2 {t | t IN s /\ t SUBSET k} /\
         UNIONS {t | t IN s /\ t SUBSET k} = k /\
         surface_boundary {t | t IN s /\ t SUBSET k} = surface_boundary s INTER k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (s:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
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
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    REWRITE_TAC[surface_boundary; IN_ELIM_THM] THEN
    SUBGOAL_THEN
     `!e:real^N->bool. e IN s /\ e SUBSET k /\ aff_dim e = &1
        ==> {r | (r IN s /\ r SUBSET k) /\ aff_dim r = &2 /\ e SUBSET r} =
            {r | r IN s /\ aff_dim r = &2 /\ e SUBSET r}`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
      X_GEN_TAC `r:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      EQ_TAC THENL [SIMP_TAC[]; STRIP_TAC THEN ASM_REWRITE_TAC[]] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~(e:real^N->bool = {})` MP_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
        ASM SET_TAC[]];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_UNIONS; IN_INTER; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC
       `CARD {r | (r IN s /\ r SUBSET k) /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = 1` THEN
      ASM_SIMP_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)
                                 ASSUME_TAC) THEN
      EXISTS_TAC `e:real^N->bool` THEN
      SUBGOAL_THEN `(e:real^N->bool) SUBSET k` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[]]] THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONJ_TAC THENL
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
    ASM_MESON_TAC[combinatorial_manifold_with_boundary]]);;

(* A complex all of whose cells are empty has Euler number 0. *)

let MOI_FAN_I3_EULER0 = prove
 (`!c:(real^N->bool)->bool. (!t. t IN c ==> t = {}) ==> complex_euler c = &0`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[complex_euler] THEN
  MATCH_MP_TAC SUM_EQ_0 THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `{s:real^N->bool | s IN c /\ aff_dim s = &n} = {}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN X_GEN_TAC `s:real^N->bool` THEN
    STRIP_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &n` THEN
    SUBGOAL_THEN `s:real^N->bool = {}` SUBST1_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    REWRITE_TAC[CARD_CLAUSES; REAL_MUL_RZERO]]);;

(* The Euler number of a surface with two components is the sum over them. *)

let MOI_FAN_I3_EULER2 = prove
 (`!(s:(real^N->bool)->bool) K1 K2.
     FINITE s /\ combinatorial_manifold_with_boundary 2 s /\
     K1 IN components (UNIONS s) /\ K2 IN components (UNIONS s) /\ ~(K1 = K2) /\
     UNIONS s = K1 UNION K2
     ==> complex_euler s =
         complex_euler {t | t IN s /\ t SUBSET K1} +
         complex_euler {t | t IN s /\ t SUBSET K2}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN s ==> connected t` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[lf_simplicial_complex; combinatorial_manifold_with_boundary];
      ALL_TAC] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K1:real^N->bool) INTER K2 = {}` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPONENTS_NONOVERLAP]; ALL_TAC] THEN
  SUBGOAL_THEN
   `s = {t | t IN s /\ t SUBSET (K1:real^N->bool)} UNION {t | t IN s /\ t SUBSET K2}`
  (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N->bool` THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN EQ_TAC THENL [ALL_TAC; MESON_TAC[]] THEN
    DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `t:real^N->bool = {}` THENL [ASM_REWRITE_TAC[EMPTY_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(t:real^N->bool) SUBSET UNIONS s` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(K1:real^N->bool) INTER t = {}` THENL
     [DISJ2_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
      EXISTS_TAC `UNIONS s:real^N->bool` THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      DISJ1_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
      EXISTS_TAC `UNIONS s:real^N->bool` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{t | t IN s /\ t SUBSET (K1:real^N->bool)}`;
                 `{t | t IN s /\ t SUBSET (K2:real^N->bool)}`] COMPLEX_EULER_UNION) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN DISCH_THEN(K ALL_TAC) THEN
  MATCH_MP_TAC(REAL_ARITH `c = &0 ==> a + b - c = a + b`) THEN
  MATCH_MP_TAC MOI_FAN_I3_EULER0 THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN ASM SET_TAC[]);;

(* Choice of the order of the two ends of an annulus. *)

let MOI_FAN_I3_ORIENT = prove
 (`!(a:real^N->bool) j0 j1 J R.
     pl_annulus_with_ends a j0 j1 /\ j0 UNION j1 = J UNION R /\
     connected J /\ ~(J = {}) /\ closed J /\ connected R /\ ~(R = {}) /\ closed R /\
     J INTER R = {}
     ==> pl_annulus_with_ends a J R`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `j0:real^N->bool`; `j1:real^N->bool`;
                 `J:real^N->bool`; `R:real^N->bool`] MOI_FCB_END_CHOICE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`a:real^N->bool`; `j0:real^N->bool`; `j1:real^N->bool`;
                 `R:real^N->bool`; `J:real^N->bool`] MOI_FCB_END_CHOICE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REPEAT(DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC)) THEN
  ASM_MESON_TAC[MOI_S5C_ANN_SWAP; INTER_IDEMPOT]);;

(* A piece with two boundary circles: Euler number at most 0, and an annulus *)
(* with the two circles as ends when it is 0.                                *)

let MOI_FAN_I3_PIECE = prove
 (`!(s:(real^N->bool)->bool) K J R.
     FINITE s /\ combinatorial_manifold_with_boundary 2 s /\ K IN components (UNIONS s) /\
     surface_boundary s INTER K = J UNION R /\
     connected J /\ ~(J = {}) /\ compact J /\ connected R /\ ~(R = {}) /\ compact R /\
     DISJOINT J R
     ==> complex_euler {t | t IN s /\ t SUBSET K} <= &0 /\
         (complex_euler {t | t IN s /\ t SUBSET K} = &0
          ==> pl_annulus_with_ends K J R)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `K:real^N->bool`] MOI_FAN_I3_COMPONENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected (K:real^N->bool) /\ ~(K = {})` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
  MP_TAC(SPEC `{t | t IN s /\ t SUBSET (K:real^N->bool)}` SURFACE_EULER_PLANAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`J:real^N->bool`; `R:real^N->bool`] MOI_FCB_TWO_COMPS) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM_MESON_TAC[DISJOINT]; STRIP_TAC] THEN
  SUBGOAL_THEN `&2 <= &(CARD (components ((J:real^N->bool) UNION R)))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_OF_NUM_LE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `!b. a + b <= &2 /\ &2 <= b ==> a <= &0`) THEN
    EXISTS_TAC `&(CARD (components ((J:real^N->bool) UNION R)))` THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC] THEN
  SUBGOAL_THEN `CARD (components ((J:real^N->bool) UNION R)) = 2` ASSUME_TAC THENL
   [UNDISCH_TAC `complex_euler {t | t IN s /\ t SUBSET (K:real^N->bool)} +
                 &(CARD (components ((J:real^N->bool) UNION R))) <= &2` THEN
    ASM_REWRITE_TAC[REAL_ADD_LID; REAL_OF_NUM_LE] THEN
    UNDISCH_TAC `2 <= CARD (components ((J:real^N->bool) UNION R))` THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(SPEC `{t | t IN s /\ t SUBSET (K:real^N->bool)}`
    (MATCH_MP MOI_FCB_PLANAR_ANNULUS SURFACE_EULER_PLANAR)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j0:real^N->bool` (X_CHOOSE_THEN `j1:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC MOI_FAN_I3_ORIENT THEN
  MAP_EVERY EXISTS_TAC [`j0:real^N->bool`; `j1:real^N->bool`] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM_MESON_TAC[DISJOINT]);;

(* A closed connected set separated from the rest of a union is one of its  *)
(* components.                                                               *)

let MOI_FAN_I3_IN_COMPONENTS = prove
 (`!(J:real^N->bool) R.
     connected J /\ ~(J = {}) /\ compact J /\ compact R /\ DISJOINT J R
     ==> J IN components (J UNION R)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_COMPONENTS_MAXIMAL] THEN
  ASM_REWRITE_TAC[SUBSET_UNION] THEN X_GEN_TAC `d:real^N->bool` THEN STRIP_TAC THEN
  UNDISCH_TAC `connected (d:real^N->bool)` THEN
  REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`J:real^N->bool`; `R:real^N->bool`]) THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[]);;

(* A connected surface whose boundary is four disjoint circles has Euler    *)
(* number at most -2.                                                        *)

let MOI_FAN_I3_PIECE4 = prove
 (`!(s:(real^N->bool)->bool) e1 e2 e3 e4.
     FINITE s /\ combinatorial_manifold_with_boundary 2 s /\
     connected (UNIONS s) /\ ~(UNIONS s = {}) /\
     surface_boundary s = e1 UNION e2 UNION e3 UNION e4 /\
     connected e1 /\ connected e2 /\ connected e3 /\ connected e4 /\
     compact e1 /\ compact e2 /\ compact e3 /\ compact e4 /\
     ~(e1 = {}) /\ ~(e2 = {}) /\ ~(e3 = {}) /\ ~(e4 = {}) /\
     DISJOINT e1 e2 /\ DISJOINT e1 e3 /\ DISJOINT e1 e4 /\
     DISJOINT e2 e3 /\ DISJOINT e2 e4 /\ DISJOINT e3 e4
     ==> complex_euler s <= -- &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!J R:real^N->bool.
      connected J /\ ~(J = {}) /\ compact J /\ compact R /\ DISJOINT J R /\
      J UNION R = e1 UNION e2 UNION e3 UNION e4
      ==> J IN components (e1 UNION e2 UNION e3 UNION e4)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_FAN_I3_IN_COMPONENTS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{e1,e2,e3,e4} SUBSET components ((e1:real^N->bool) UNION e2 UNION e3 UNION e4)`
  ASSUME_TAC THENL
   [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN REPEAT CONJ_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THENL
     [EXISTS_TAC `e2 UNION e3 UNION e4:real^N->bool`;
      EXISTS_TAC `e1 UNION e3 UNION e4:real^N->bool`;
      EXISTS_TAC `e1 UNION e2 UNION e4:real^N->bool`;
      EXISTS_TAC `e1 UNION e2 UNION e3:real^N->bool`] THEN
    ASM_SIMP_TAC[COMPACT_UNION] THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      can (find_term (fun t -> t = `DISJOINT:(real^N->bool)->(real^N->bool)->bool`))
          (concl th)))) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {e1,e2,e3,e4:real^N->bool} = 4` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `~(e1:real^N->bool = e2) /\ ~(e1 = e3) /\ ~(e1 = e4) /\ ~(e2 = e3) /\ ~(e2 = e4) /\
      ~(e3 = e4)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(SPEC `s:(real^N->bool)->bool` SURFACE_EULER_PLANAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `4 <= CARD (components ((e1:real^N->bool) UNION e2 UNION e3 UNION e4))`
  MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th =
      `CARD {e1,e2,e3,e4:real^N->bool} = 4`)) THEN
    MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN DISCH_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `!b. a + b <= &2 /\ &4 <= b ==> a <= -- &2`) THEN
    EXISTS_TAC `&(CARD (components ((e1:real^N->bool) UNION e2 UNION e3 UNION e4)))` THEN
    ASM_REWRITE_TAC[]]);;

(* A surface with exactly two components, each with two boundary circles. *)

let MOI_FAN_I3_TWO = prove
 (`!(s:(real^N->bool)->bool) K1 K2 J1 R1 J2 R2.
     FINITE s /\ combinatorial_manifold_with_boundary 2 s /\
     K1 IN components (UNIONS s) /\ K2 IN components (UNIONS s) /\ ~(K1 = K2) /\
     (!c. c IN components (UNIONS s) ==> c = K1 \/ c = K2) /\
     surface_boundary s INTER K1 = J1 UNION R1 /\
     surface_boundary s INTER K2 = J2 UNION R2 /\
     connected J1 /\ ~(J1 = {}) /\ compact J1 /\ connected R1 /\ ~(R1 = {}) /\
     compact R1 /\ DISJOINT J1 R1 /\
     connected J2 /\ ~(J2 = {}) /\ compact J2 /\ connected R2 /\ ~(R2 = {}) /\
     compact R2 /\ DISJOINT J2 R2
     ==> UNIONS s = K1 UNION K2 /\ DISJOINT K1 K2 /\
         ?a1 a2. complex_euler s = a1 + a2 /\ a1 <= &0 /\ a2 <= &0 /\
                 (a1 = &0 ==> pl_annulus_with_ends K1 J1 R1) /\
                 (a2 = &0 ==> pl_annulus_with_ends K2 J2 R2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS s = (K1:real^N->bool) UNION K2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `UNIONS s:real^N->bool` UNIONS_COMPONENTS) THEN
    UNDISCH_TAC `(K1:real^N->bool) IN components (UNIONS s)` THEN
    UNDISCH_TAC `(K2:real^N->bool) IN components (UNIONS s)` THEN
    UNDISCH_TAC `!c:real^N->bool. c IN components (UNIONS s) ==> c = K1 \/ c = K2` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[COMPONENTS_NONOVERLAP; DISJOINT]; ALL_TAC] THEN
  EXISTS_TAC `complex_euler {t | t IN s /\ t SUBSET (K1:real^N->bool)}` THEN
  EXISTS_TAC `complex_euler {t | t IN s /\ t SUBSET (K2:real^N->bool)}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FAN_I3_EULER2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `K1:real^N->bool`; `J1:real^N->bool`;
                 `R1:real^N->bool`] MOI_FAN_I3_PIECE) THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `K2:real^N->bool`; `J2:real^N->bool`;
                 `R2:real^N->bool`] MOI_FAN_I3_PIECE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

(* Witness arguments: a connected set meeting two sets in components forces *)
(* the components to agree.                                                  *)

let MOI_FAN_I3_WIT1 = prove
 (`!(u:real^N->bool) C D e e'.
     C IN components u /\ D IN components u /\ e SUBSET C /\ e' SUBSET D /\
     (?g. connected g /\ g SUBSET u /\ ~(g INTER e = {}) /\ ~(g INTER e' = {}))
     ==> C = D`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `(g:real^N->bool) SUBSET C /\ g SUBSET D` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[COMPONENTS_EQ; SET_RULE
   `~(g INTER e = {}) /\ g SUBSET C /\ g SUBSET D ==> ~(C INTER D:real^N->bool = {})`]);;

let MOI_FAN_I3_WIT2 = prove
 (`!(u:real^N->bool) C D1 D2 e e1' e2'.
     C IN components u /\ D1 IN components u /\ D2 IN components u /\
     e SUBSET C /\ e1' SUBSET D1 /\ e2' SUBSET D2 /\
     (?g. connected g /\ g SUBSET u /\ ~(g INTER e = {}) /\
          ~(g INTER (e1' UNION e2') = {}))
     ==> C = D1 \/ C = D2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC))))))) THEN
  SUBGOAL_THEN `~((g:real^N->bool) INTER e1' = {}) \/ ~(g INTER e2' = {})` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC MOI_FAN_I3_WIT1 THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `e:real^N->bool`; `e1':real^N->bool`];
    DISJ2_TAC THEN MATCH_MP_TAC MOI_FAN_I3_WIT1 THEN
    MAP_EVERY EXISTS_TAC [`u:real^N->bool`; `e:real^N->bool`; `e2':real^N->bool`]] THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* A component meeting a set inside another component is that component. *)

let MOI_FAN_I3_MEETS = prove
 (`!(u:real^N->bool) c C e.
     c IN components u /\ C IN components u /\ e SUBSET C /\ ~(c INTER e = {})
     ==> c = C`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`u:real^N->bool`; `c:real^N->bool`; `C:real^N->bool`] COMPONENTS_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[]);;

(* Each of the four circles lies in a component. *)

let MOI_FAN_I3_COMPONENT_OF = prove
 (`!(u:real^N->bool) e.
     connected e /\ ~(e = {}) /\ e SUBSET u ==> ?C. C IN components u /\ e SUBSET C`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `p:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> is_neg(concl th))) THEN
  EXISTS_TAC `connected_component u (p:real^N)` THEN
  REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS] THEN CONJ_TAC THENL
   [ASM SET_TAC[]; MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]]);;

(* The surface kb of the count: one piece with four circles, or two      *)
(* annulus candidates with ends e1, f3 and e2, f4.                          *)

let MOI_FAN_I3_KB = prove
 (`!(s:(real^N->bool)->bool) e1 e2 e3 e4.
     FINITE s /\ combinatorial_manifold_with_boundary 2 s /\
     surface_boundary s = e1 UNION e2 UNION e3 UNION e4 /\
     connected e1 /\ connected e2 /\ connected e3 /\ connected e4 /\
     compact e1 /\ compact e2 /\ compact e3 /\ compact e4 /\
     ~(e1 = {}) /\ ~(e2 = {}) /\ ~(e3 = {}) /\ ~(e4 = {}) /\
     DISJOINT e1 e2 /\ DISJOINT e1 e3 /\ DISJOINT e1 e4 /\
     DISJOINT e2 e3 /\ DISJOINT e2 e4 /\ DISJOINT e3 e4 /\
     (!c. c IN components (UNIONS s)
          ==> ~(c INTER (e1 UNION e2 UNION e3 UNION e4) = {})) /\
     (?g. connected g /\ g SUBSET UNIONS s /\
          ~(g INTER e1 = {}) /\ ~(g INTER (e3 UNION e4) = {})) /\
     (?g. connected g /\ g SUBSET UNIONS s /\
          ~(g INTER e2 = {}) /\ ~(g INTER (e3 UNION e4) = {})) /\
     (?g. connected g /\ g SUBSET UNIONS s /\
          ~(g INTER e3 = {}) /\ ~(g INTER (e1 UNION e2) = {})) /\
     (?g. connected g /\ g SUBSET UNIONS s /\
          ~(g INTER e4 = {}) /\ ~(g INTER (e1 UNION e2) = {}))
     ==> complex_euler s <= -- &2 \/
         ?K1 K2 f3 f4.
           ((f3 = e3 /\ f4 = e4) \/ (f3 = e4 /\ f4 = e3)) /\
           UNIONS s = K1 UNION K2 /\ DISJOINT K1 K2 /\
           ?a1 a2. complex_euler s = a1 + a2 /\ a1 <= &0 /\ a2 <= &0 /\
                   (a1 = &0 ==> pl_annulus_with_ends K1 e1 f3) /\
                   (a2 = &0 ==> pl_annulus_with_ends K2 e2 f4)`,
  REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(e1:real^N->bool) UNION e2 UNION e3 UNION e4 SUBSET UNIONS s`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `surface_boundary (s:(real^N->bool)->bool)`)) THEN
    REWRITE_TAC[MOI_FAN_I3_SB_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `e1:real^N->bool`] MOI_FAN_I3_COMPONENT_OF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `e2:real^N->bool`] MOI_FAN_I3_COMPONENT_OF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `e3:real^N->bool`] MOI_FAN_I3_COMPONENT_OF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C3:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `e4:real^N->bool`] MOI_FAN_I3_COMPONENT_OF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C4:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `C1:real^N->bool`; `C3:real^N->bool`;
                 `C4:real^N->bool`; `e1:real^N->bool`; `e3:real^N->bool`;
                 `e4:real^N->bool`] MOI_FAN_I3_WIT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `C2:real^N->bool`; `C3:real^N->bool`;
                 `C4:real^N->bool`; `e2:real^N->bool`; `e3:real^N->bool`;
                 `e4:real^N->bool`] MOI_FAN_I3_WIT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `C3:real^N->bool`; `C1:real^N->bool`;
                 `C2:real^N->bool`; `e3:real^N->bool`; `e1:real^N->bool`;
                 `e2:real^N->bool`] MOI_FAN_I3_WIT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `C4:real^N->bool`; `C1:real^N->bool`;
                 `C2:real^N->bool`; `e4:real^N->bool`; `e1:real^N->bool`;
                 `e2:real^N->bool`] MOI_FAN_I3_WIT2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!c:real^N->bool. c IN components (UNIONS s) ==> c = C1 \/ c = C2 \/ c = C3 \/ c = C4`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((c:real^N->bool) INTER e1 = {}) \/ ~(c INTER e2 = {}) \/
                  ~(c INTER e3 = {}) \/ ~(c INTER e4 = {})` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP
        (ASSUME `(c:real^N->bool) IN components (UNIONS s)`) o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `e1:real^N->bool`)) (concl th) &&
        can (find_term ((=) `components:(real^N->bool)->(real^N->bool)->bool`)) (concl th))) THEN
      SET_TAC[];
      ASM_MESON_TAC[MOI_FAN_I3_MEETS]];
    ALL_TAC] THEN
  ASM_CASES_TAC `C1:real^N->bool = C2` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `C3:real^N->bool = C1 /\ C4 = C1` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `UNIONS s = (C1:real^N->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `UNIONS s:real^N->bool` UNIONS_COMPONENTS) THEN
      SUBGOAL_THEN `!c:real^N->bool. c IN components (UNIONS s) ==> c = C1` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(C1:real^N->bool) IN components (UNIONS s)` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FAN_I3_PIECE4 THEN
    MAP_EVERY EXISTS_TAC [`e1:real^N->bool`; `e2:real^N->bool`; `e3:real^N->bool`;
                          `e4:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_NONEMPTY];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN `DISJOINT (C1:real^N->bool) C2` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPONENTS_NONOVERLAP; DISJOINT]; ALL_TAC] THEN
  SUBGOAL_THEN `(C3:real^N->bool) = C1 /\ C4 = C2 \/ C3 = C2 /\ C4 = C1` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN (CONJUNCTS_THEN SUBST_ALL_TAC)) THENL
   [MAP_EVERY EXISTS_TAC [`C1:real^N->bool`; `C2:real^N->bool`; `e3:real^N->bool`;
                          `e4:real^N->bool`];
    MAP_EVERY EXISTS_TAC [`C1:real^N->bool`; `C2:real^N->bool`; `e4:real^N->bool`;
                          `e3:real^N->bool`]] THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FAN_I3_TWO THEN ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [ASM_MESON_TAC[];
     REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
       is_binary "SUBSET" (concl th) || is_binary "DISJOINT" (concl th)))) THEN
     SET_TAC[]]));;

(* The surface kc of the count: one piece with four circles, or two      *)
(* annulus candidates with ends e1, e2 and e3, e4.                          *)

let MOI_FAN_I3_KC = prove
 (`!(s:(real^N->bool)->bool) e1 e2 e3 e4.
     FINITE s /\ combinatorial_manifold_with_boundary 2 s /\
     surface_boundary s = e1 UNION e2 UNION e3 UNION e4 /\
     connected e1 /\ connected e2 /\ connected e3 /\ connected e4 /\
     compact e1 /\ compact e2 /\ compact e3 /\ compact e4 /\
     ~(e1 = {}) /\ ~(e2 = {}) /\ ~(e3 = {}) /\ ~(e4 = {}) /\
     DISJOINT e1 e2 /\ DISJOINT e1 e3 /\ DISJOINT e1 e4 /\
     DISJOINT e2 e3 /\ DISJOINT e2 e4 /\ DISJOINT e3 e4 /\
     (!c. c IN components (UNIONS s)
          ==> ~(c INTER (e1 UNION e2 UNION e3 UNION e4) = {})) /\
     (?g. connected g /\ g SUBSET UNIONS s /\
          ~(g INTER e1 = {}) /\ ~(g INTER e2 = {})) /\
     (?g. connected g /\ g SUBSET UNIONS s /\
          ~(g INTER e3 = {}) /\ ~(g INTER e4 = {}))
     ==> complex_euler s <= -- &2 \/
         ?K1 K2.
           UNIONS s = K1 UNION K2 /\ DISJOINT K1 K2 /\
           ?a1 a2. complex_euler s = a1 + a2 /\ a1 <= &0 /\ a2 <= &0 /\
                   (a1 = &0 ==> pl_annulus_with_ends K1 e1 e2) /\
                   (a2 = &0 ==> pl_annulus_with_ends K2 e3 e4)`,
  REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(e1:real^N->bool) UNION e2 UNION e3 UNION e4 SUBSET UNIONS s`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `surface_boundary (s:(real^N->bool)->bool)`)) THEN
    REWRITE_TAC[MOI_FAN_I3_SB_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `e1:real^N->bool`] MOI_FAN_I3_COMPONENT_OF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `e2:real^N->bool`] MOI_FAN_I3_COMPONENT_OF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C2:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `e3:real^N->bool`] MOI_FAN_I3_COMPONENT_OF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C3:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `e4:real^N->bool`] MOI_FAN_I3_COMPONENT_OF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `C4:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `C1:real^N->bool`; `C2:real^N->bool`;
                 `e1:real^N->bool`; `e2:real^N->bool`] MOI_FAN_I3_WIT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`UNIONS s:real^N->bool`; `C3:real^N->bool`; `C4:real^N->bool`;
                 `e3:real^N->bool`; `e4:real^N->bool`] MOI_FAN_I3_WIT1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `!c:real^N->bool. c IN components (UNIONS s) ==> c = C1 \/ c = C2 \/ c = C3 \/ c = C4`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((c:real^N->bool) INTER e1 = {}) \/ ~(c INTER e2 = {}) \/
                  ~(c INTER e3 = {}) \/ ~(c INTER e4 = {})` MP_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o C MATCH_MP
        (ASSUME `(c:real^N->bool) IN components (UNIONS s)`) o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `e1:real^N->bool`)) (concl th) &&
        can (find_term ((=) `components:(real^N->bool)->(real^N->bool)->bool`)) (concl th))) THEN
      SET_TAC[];
      ASM_MESON_TAC[MOI_FAN_I3_MEETS]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `C1:real^N->bool = C2`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th -> concl th = `C3:real^N->bool = C4`)) THEN
  ASM_CASES_TAC `C1:real^N->bool = C3` THENL
   [DISJ1_TAC THEN
    SUBGOAL_THEN `UNIONS s = (C1:real^N->bool)` ASSUME_TAC THENL
     [MP_TAC(ISPEC `UNIONS s:real^N->bool` UNIONS_COMPONENTS) THEN
      SUBGOAL_THEN `!c:real^N->bool. c IN components (UNIONS s) ==> c = C1` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(C1:real^N->bool) IN components (UNIONS s)` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FAN_I3_PIECE4 THEN
    MAP_EVERY EXISTS_TAC [`e1:real^N->bool`; `e2:real^N->bool`; `e3:real^N->bool`;
                          `e4:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IN_COMPONENTS_CONNECTED; IN_COMPONENTS_NONEMPTY];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN `DISJOINT (C1:real^N->bool) C3` ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPONENTS_NONOVERLAP; DISJOINT]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`C1:real^N->bool`; `C3:real^N->bool`] THEN
  MATCH_MP_TAC MOI_FAN_I3_TWO THEN ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [ASM_MESON_TAC[];
     REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
       is_binary "SUBSET" (concl th) || is_binary "DISJOINT" (concl th)))) THEN
     SET_TAC[]]));;

(* The count. *)

let MOI_FAN_COUNT = prove
 (MOI_FAN_COUNT_TERM,
  REPEAT GEN_TAC THEN REPEAT(DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`kb:(real^N->bool)->bool`; `e1:real^N->bool`; `e2:real^N->bool`;
                 `e3:real^N->bool`; `e4:real^N->bool`] MOI_FAN_I3_KB) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`kc:(real^N->bool)->bool`; `e1:real^N->bool`; `e2:real^N->bool`;
                 `e3:real^N->bool`; `e4:real^N->bool`] MOI_FAN_I3_KC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `c1:real^N->bool` (X_CHOOSE_THEN `c2:real^N->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `y1:real` (X_CHOOSE_THEN `y2:real` STRIP_ASSUME_TAC))))))) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `b1:real^N->bool` (X_CHOOSE_THEN `b2:real^N->bool`
      (X_CHOOSE_THEN `f3:real^N->bool` (X_CHOOSE_THEN `f4:real^N->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 ASSUME_TAC
            (X_CHOOSE_THEN `x1:real` (X_CHOOSE_THEN `x2:real` STRIP_ASSUME_TAC)))))))))) THENL
   [SUBGOAL_THEN `F` CONTR_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`complex_euler (kb:(real^N->bool)->bool) + complex_euler (kc:(real^N->bool)->bool) = &0`;
      `complex_euler (kc:(real^N->bool)->bool) <= -- &2`;
      `complex_euler (kb:(real^N->bool)->bool) <= -- &2`] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `F` CONTR_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`complex_euler (kb:(real^N->bool)->bool) + complex_euler (kc:(real^N->bool)->bool) = &0`;
      `complex_euler (kc:(real^N->bool)->bool) <= -- &2`;
      `complex_euler (kb:(real^N->bool)->bool) = x1 + x2`; `x1 <= &0`; `x2 <= &0`] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `F` CONTR_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`complex_euler (kb:(real^N->bool)->bool) + complex_euler (kc:(real^N->bool)->bool) = &0`;
      `complex_euler (kb:(real^N->bool)->bool) <= -- &2`;
      `complex_euler (kc:(real^N->bool)->bool) = y1 + y2`; `y1 <= &0`; `y2 <= &0`] THEN
    REAL_ARITH_TAC;
    SUBGOAL_THEN `x1 = &0 /\ x2 = &0 /\ y1 = &0 /\ y2 = &0` STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`complex_euler (kb:(real^N->bool)->bool) + complex_euler (kc:(real^N->bool)->bool) = &0`;
        `complex_euler (kb:(real^N->bool)->bool) = x1 + x2`; `x1 <= &0`; `x2 <= &0`;
        `complex_euler (kc:(real^N->bool)->bool) = y1 + y2`; `y1 <= &0`; `y2 <= &0`] THEN
      REAL_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`b1:real^N->bool`; `b2:real^N->bool`; `c1:real^N->bool`;
                          `c2:real^N->bool`; `f3:real^N->bool`; `f4:real^N->bool`] THEN
    ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Step D, the transport tools: B is clopen in F minus M, paths along an     *)
(* edge cycle, edges in at most two triangles, adjacent triangles of ldT.    *)
(* ========================================================================= *)

(* B is relatively clopen in F minus M: a connected subset of F minus M    *)
(* meeting B lies in B.                                                      *)

let MOI_FAN_B_CLOPEN = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 P.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     connected P /\ P SUBSET derived_frontier t la DIFF UNIONS lm /\
     ~(P INTER moi_fan_bside t la lm j1 j2 = {})
     ==> P SUBSET moi_fan_bside t la lm j1 j2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_SIDES th)) STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `~(P INTER moi_fan_bside t la lm j1 j2 = {})` THEN
  REWRITE_TAC[moi_fan_bside] THEN
  ABBREV_TAC `X = UNIONS la DIFF (j1 UNION j2:real^3->bool)` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j1:real^3->bool`] MOI_FAN_MC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j2:real^3->bool`] MOI_FAN_MC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j1:real^3->bool`; `X:real^3->bool`]
    MOI_FAN_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (X:real^3->bool) (UNIONS lm)` THEN
    UNDISCH_TAC `moi_fan_mc lm j1 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j2:real^3->bool`; `X:real^3->bool`]
    MOI_FAN_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (X:real^3->bool) (UNIONS lm)` THEN
    UNDISCH_TAC `moi_fan_mc lm j2 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`P:real^3->bool`;
                 `moi_fan_side lm j1 X INTER moi_fan_side lm j2 (X:real^3->bool)`;
                 `moi_fan_far lm j1 X UNION moi_fan_far lm j2 (X:real^3->bool)`]
    MOI_FAN_CONN_OPEN_SPLIT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER; OPEN_UNION] THEN
    UNDISCH_TAC `P SUBSET derived_frontier t la DIFF UNIONS (lm:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `moi_fan_side lm j1 X UNION moi_fan_far lm j1 X =
                 (:real^3) DIFF moi_fan_mc lm j1` THEN
    UNDISCH_TAC `moi_fan_side lm j2 X UNION moi_fan_far lm j2 X =
                 (:real^3) DIFF moi_fan_mc lm j2` THEN
    UNDISCH_TAC `DISJOINT (moi_fan_side lm j1 X) (moi_fan_far lm j1 (X:real^3->bool))` THEN
    UNDISCH_TAC `DISJOINT (moi_fan_side lm j2 X) (moi_fan_far lm j2 (X:real^3->bool))` THEN
    UNDISCH_TAC `moi_fan_mc lm j1 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `moi_fan_mc lm j2 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(P INTER
                 (derived_frontier t la DIFF UNIONS lm) INTER
                 moi_fan_side lm j1 X INTER moi_fan_side lm j2 (X:real^3->bool) = {})` THEN
  UNDISCH_TAC `P SUBSET derived_frontier t la DIFF UNIONS (lm:(real^3->bool)->bool)` THEN
  UNDISCH_TAC `DISJOINT (moi_fan_side lm j1 X) (moi_fan_far lm j1 (X:real^3->bool))` THEN
  UNDISCH_TAC `DISJOINT (moi_fan_side lm j2 X) (moi_fan_far lm j2 (X:real^3->bool))` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[]);;

(* A path along the cycle around an edge [v0,y0] at the annulus, through   *)
(* vertices off the annulus and off M, lies in F minus M.                   *)

let MOI_FAN_ARC_PATH = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 v0 y0 (U:num->real^3) a n.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\ v0 IN UNIONS la /\
     (!i. segment[U i,U(SUC i)] IN barycentric_subdivision (barycentric_subdivision t) /\
          convex hull {v0,y0,U i,U(SUC i)} IN
            barycentric_subdivision (barycentric_subdivision t) /\
          segment[U i,U(SUC i)] SUBSET convex hull {v0,y0,U i,U(SUC i)} /\
          ~(U i = U(SUC i))) /\
     (!r. r <= n ==> ~(U(a + r) IN UNIONS la) /\ ~(U(a + r) IN UNIONS lm))
     ==> connected ({U a} UNION UNIONS {segment[U(a + j),U(SUC(a + j))] | j | j < n}) /\
         {U a} UNION UNIONS {segment[U(a + j),U(SUC(a + j))] | j | j < n} SUBSET
           derived_frontier t la DIFF UNIONS lm /\
         U a IN {U a} UNION UNIONS {segment[U(a + j),U(SUC(a + j))] | j | j < n} /\
         U(a + n) IN {U a} UNION UNIONS {segment[U(a + j),U(SUC(a + j))] | j | j < n}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th)) STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[MOI_FSP_PATH_CONN; IN_UNION; IN_SING] THEN
  SUBGOAL_THEN `lf_simplicial_complex (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[SUBSET; MOI_FSP_PATH_MEMBER] THEN X_GEN_TAC `x:real^3` THEN STRIP_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `{(U:num->real^3) a}`]
      MOI_FSP_NC_FR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
        EXISTS_TAC `convex hull {v0:real^3,y0,U(a:num),U(SUC a)}` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `v0:real^3` THEN
          ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
          MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
          EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
          ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `segment[(U:num->real^3) a,U(SUC a)]` THEN
            ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
            REWRITE_TAC[SING_SUBSET] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
            SET_TAC[]]];
        FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `n:num`)) (concl th))) THEN
        REWRITE_TAC[ADD_CLAUSES; LE_0] THEN SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `n:num`)) (concl th))) THEN
    REWRITE_TAC[ADD_CLAUSES; LE_0] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((U:num->real^3)(a + j) IN UNIONS la) /\ ~(U(a + j) IN UNIONS lm) /\
                ~(U(SUC(a + j)) IN UNIONS la) /\ ~(U(SUC(a + j)) IN UNIONS lm)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term (fun t -> t = `n:num`)) (concl th)
      then MP_TAC(SPEC `j:num` th) THEN MP_TAC(SPEC `SUC j` th) else failwith "no") THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    ASM_SIMP_TAC[ARITH_RULE `j < n ==> j <= n /\ SUC j <= n`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                 `barycentric_subdivision (la:(real^3->bool)->bool)`;
                 `(U:num->real^3)(a + j)`; `(U:num->real^3)(SUC(a + j))`] MOI_FSP_SEG_FULL) THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                 `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                 `(U:num->real^3)(a + j)`; `(U:num->real^3)(SUC(a + j))`] MOI_FSP_SEG_FULL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[IN_DIFF] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `segment[(U:num->real^3)(a + j),U(SUC(a + j))]`] MOI_FSP_NC_FR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
      EXISTS_TAC `convex hull {v0:real^3,y0,U(a + j:num),U(SUC(a + j))}` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `v0:real^3` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
        MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
        EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
        ASM_REWRITE_TAC[]];
      ASM SET_TAC[]];
    ASM SET_TAC[]]);;

(* In a compact combinatorial surface an edge lies in at most two          *)
(* triangles.                                                               *)

let MOI_FAN_EDGE_TWO = prove
 (`!(c:(real^N->bool)->bool) e r1 r2 r.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c /\ e IN c /\ aff_dim e = &1 /\
     r1 IN c /\ aff_dim r1 = &2 /\ e SUBSET r1 /\
     r2 IN c /\ aff_dim r2 = &2 /\ e SUBSET r2 /\ ~(r1 = r2) /\
     r IN c /\ aff_dim r = &2 /\ e SUBSET r
     ==> r = r1 \/ r = r2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_S8TB_EDGE_CARD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
    MP_TAC(ISPEC `c:(real^N->bool)->bool` SURF_CHARTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^N) IN surface_boundary c` THEN ASM_SIMP_TAC[IN_DIFF];
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `FINITE {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t}`
  ASSUME_TAC THENL [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(r1:real^N->bool) IN {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} /\
                (r2:real^N->bool) IN {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} /\
                (r:real^N->bool) IN {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t}`
  MP_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ABBREV_TAC `S = {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t}` THEN
  SUBGOAL_THEN `S HAS_SIZE 1 \/ (S:(real^N->bool)->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[]);;

(* The common edge of two adjacent triangles of ldT has an endpoint off M. *)

let MOI_FAN_ADJ_EDGE = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 tau tau'.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     tau IN barycentric_subdivision (barycentric_subdivision la) /\ aff_dim tau = &2 /\
     tau' IN barycentric_subdivision (barycentric_subdivision la) /\ aff_dim tau' = &2 /\
     ~(tau = tau') /\ aff_dim (tau INTER tau') = &1
     ==> ?v0 y0. tau INTER tau' = segment[v0,y0] /\ ~(v0 = y0) /\
                 segment[v0,y0] IN barycentric_subdivision (barycentric_subdivision la) /\
                 segment[v0,y0] IN barycentric_subdivision (barycentric_subdivision t) /\
                 {v0} IN barycentric_subdivision (barycentric_subdivision t) /\
                 v0 IN UNIONS la /\ y0 IN UNIONS la /\ ~(v0 IN UNIONS lm)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_D th)) STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `tt = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  ABBREV_TAC `ldT = barycentric_subdivision (barycentric_subdivision (la:(real^3->bool)->bool))` THEN
  SUBGOAL_THEN `(tau INTER tau':real^3->bool) IN ldT` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `tau:real^3->bool` THEN
    ASM_MESON_TAC[lf_simplicial_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a0 b0:real^3. ~(a0 = b0) /\ tau INTER tau' = segment[a0,b0]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_PL2_SIMPLEX_1] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `aff_dim (tau INTER tau':real^3->bool) = &1`)) THEN
    MATCH_MP_TAC MOI_FM3_LF_SIMPLEX THEN EXISTS_TAC `ldT:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^3. x IN segment[a0,b0] ==> x IN UNIONS la` (LABEL_TAC "inla") THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if concl th = `UNIONS (ldT:(real^3->bool)->bool) = UNIONS la`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `tau:real^3->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((a0:real^3) IN UNIONS lm /\ (b0:real^3) IN UNIONS lm)` ASSUME_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `segment[a0:real^3,b0] SUBSET j1 UNION j2` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                     `lm:(real^3->bool)->bool`] MOI_FN2_SUBCOMPLEX_INTER) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `(la:(real^3->bool)->bool) INTER lm`]
        MOI_FRN_SETUP) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                     `lm:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                     `barycentric_subdivision ((la:(real^3->bool)->bool) INTER lm)`;
                     `{a0:real^3,b0}`] MOI_FSP_HULL_FULL) THEN
      ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [FIRST_X_ASSUM(fun th -> if concl th = `tau INTER tau' = segment[a0:real^3,b0]`
            then REWRITE_TAC[SYM th] else failwith "no") THEN
          ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
          REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
          ASM_MESON_TAC[ENDS_IN_SEGMENT; IN_INTER]];
        SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[a0:real^3,b0] SUBSET tau /\ segment[a0,b0] SUBSET tau'`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `tau INTER tau' = segment[a0:real^3,b0]` THEN SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`ldT:(real^3->bool)->bool`; `segment[a0:real^3,b0]`] MOI_FSP_BD_EDGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN `{r | r IN ldT /\ aff_dim r = &2 /\ segment[a0:real^3,b0] SUBSET r} HAS_SIZE 1`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE] THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` ASSUME_TAC) THEN
    SUBGOAL_THEN `(tau:real^3->bool) IN {q} /\ (tau':real^3->bool) IN {q}` MP_TAC THENL
     [FIRST_X_ASSUM(fun th -> REWRITE_TAC[SYM th]) THEN ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    REWRITE_TAC[IN_SING] THEN STRIP_TAC THEN
    UNDISCH_TAC `~(tau:real^3->bool = tau')` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v0 y0:real^3. segment[a0,b0] = segment[v0,y0] /\ ~(v0 = y0) /\
                               ~(v0 IN UNIONS lm) /\ y0 IN segment[a0,b0] /\
                               v0 IN segment[a0,b0]`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(a0:real^3) IN UNIONS lm` THENL
     [MAP_EVERY EXISTS_TAC [`b0:real^3`; `a0:real^3`] THEN
      ASM_MESON_TAC[SEGMENT_SYM; ENDS_IN_SEGMENT];
      MAP_EVERY EXISTS_TAC [`a0:real^3`; `b0:real^3`] THEN
      ASM_MESON_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v0:real^3`; `y0:real^3`] THEN
  SUBGOAL_THEN `tau INTER tau' = segment[v0:real^3,y0]` ASSUME_TAC THENL
   [UNDISCH_TAC `tau INTER tau' = segment[a0:real^3,b0]` THEN
    UNDISCH_TAC `segment[a0:real^3,b0] = segment[v0,y0]` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v0:real^3,y0] IN ldT` ASSUME_TAC THENL
   [UNDISCH_TAC `(tau INTER tau':real^3->bool) IN ldT` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[v0:real^3,y0] IN tt` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (ldT:(real^3->bool)->bool) tt` THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `{v0:real^3} IN tt` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `segment[v0:real^3,y0]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v0:real^3) IN UNIONS la /\ (y0:real^3) IN UNIONS la` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN USE_THEN "inla" MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Step D, the transport of the far vertices along ldT: the fan vertices of  *)
(* a tetrahedron on a triangle, adjacent triangles (two arcs of the cycle    *)
(* around the common edge), and the dual connectivity.                       *)
(* ========================================================================= *)

(* A vertex w of a tetrahedron d on the triangle conv{v0,y0,U i0} of an    *)
(* edge fan, other than the triangle's vertices, is U(i0 + 1) or           *)
(* U(i0 + dd - 1).                                                           *)

let MOI_FAN_FAN_W = prove
 (`!(tt:(real^N->bool)->bool) v0 y0 dd (U:num->real^N) i0 w d.
     lf_simplicial_complex tt /\
     3 <= dd /\ (!i. U(i + dd) = U i) /\ (!i j. i < dd /\ j < dd /\ U i = U j ==> i = j) /\
     (!i. ~(U i = v0) /\ ~(U i = y0) /\ {U i} IN tt /\
          segment[v0,y0] SUBSET convex hull {v0, y0, U i}) /\
     (!r. r IN tt /\ aff_dim r = &3 /\ segment[v0,y0] SUBSET r
          ==> ?i. i < dd /\ r = convex hull {v0, y0, U i, U(SUC i)}) /\
     i0 < dd /\ d IN tt /\ aff_dim d = &3 /\ convex hull {v0,y0,U i0} SUBSET d /\
     w IN d /\ {w} IN tt /\ ~(w = v0) /\ ~(w = y0) /\ ~(w = U i0)
     ==> w = U(i0 + 1) \/ w = U(i0 + dd - 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `segment[v0:real^N,y0] SUBSET d` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `d:real^N->bool` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `&3:int`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `!z:real^N. z IN d /\ {z} IN tt ==> z IN {v0, y0, U(i:num), U(SUC i)}`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL THEN
    FIRST_ASSUM(fun th -> if concl th = `convex hull {v0:real^N, y0, U(i:num), U(SUC i)} = d`
      then REWRITE_TAC[th] else failwith "no") THEN
    REWRITE_TAC[GSYM FACE_OF_SING] THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `tt:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[SING_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^N) i0 IN {v0, y0, U(i:num), U(SUC i)}` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d:real^N->bool`)) (concl th))) THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `convex hull {v0:real^N,y0,U(i0:num)} SUBSET d` THEN
      MATCH_MP_TAC(SET_RULE `(x:real^N) IN s ==> s SUBSET t ==> x IN t`) THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN {v0, y0, U(i:num), U(SUC i)}` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `d:real^N->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(U:num->real^N) dd = U 0` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `(U:num->real^N)(i + dd)`)) (concl th))) THEN
    REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  ABBREV_TAC `inj = !i j. i < dd /\ j < dd /\ (U:num->real^N) i = U j ==> i = j` THEN
  ABBREV_TAC `per = !i. (U:num->real^N)(i + dd) = U i` THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THEN DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [UNDISCH_TAC `~(w:real^N = U(i0:num))` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `SUC i < dd` THENL
     [SUBGOAL_THEN `SUC i = i0` ASSUME_TAC THENL
       [UNDISCH_TAC `inj:bool` THEN EXPAND_TAC "inj" THEN
        DISCH_THEN(MP_TAC o SPECL [`SUC i`; `i0:num`]) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `i0 + dd - 1 = i + dd` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `per:bool` THEN EXPAND_TAC "per" THEN SIMP_TAC[];
      SUBGOAL_THEN `SUC i = dd` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `i0 = 0` ASSUME_TAC THENL
       [UNDISCH_TAC `inj:bool` THEN EXPAND_TAC "inj" THEN
        DISCH_THEN(MP_TAC o SPECL [`i0:num`; `0`]) THEN ASM_REWRITE_TAC[] THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; SIMP_TAC[]] THEN
        UNDISCH_TAC `(U:num->real^N) i0 = U(SUC i)` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC];
    DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `i:num = i0` (fun th -> REWRITE_TAC[th; ADD1]) THEN
    UNDISCH_TAC `inj:bool` THEN EXPAND_TAC "inj" THEN
    DISCH_THEN(MP_TAC o SPECL [`i:num`; `i0:num`]) THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `~(w:real^N = U(i0:num))` THEN ASM_REWRITE_TAC[]]);;

(* The transport across an interior edge: every far vertex of a triangle   *)
(* tau of ldT is joined inside B to a far vertex of an adjacent triangle    *)
(* tau' (along one of the two arcs of the cycle around the common edge).   *)

let MOI_FAN_W_ADJ = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 tau tau' w.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     tau IN barycentric_subdivision (barycentric_subdivision la) /\ aff_dim tau = &2 /\
     tau' IN barycentric_subdivision (barycentric_subdivision la) /\ aff_dim tau' = &2 /\
     ~(tau = tau') /\ aff_dim (tau INTER tau') = &1 /\ w IN moi_fan_w t la tau
     ==> ?w' G. w' IN moi_fan_w t la tau' /\ connected G /\
                G SUBSET moi_fan_bside t la lm j1 j2 /\ w IN G /\ w' IN G`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`; `a1:real^3->bool`; `a2:real^3->bool`;
                 `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                 `tau:real^3->bool`; `tau':real^3->bool`] MOI_FAN_ADJ_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^3` (X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `j1:real^3->bool`; `j2:real^3->bool`; `a1:real^3->bool`; `a2:real^3->bool`;
                 `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                 `tau:real^3->bool`] MOI_FAN_W_IN_B) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_fan_ctx (t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_D th)) THEN
  ABBREV_TAC `tt = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  ABBREV_TAC `ldT = barycentric_subdivision (barycentric_subdivision (la:(real^3->bool)->bool))` THEN
  MP_TAC(ISPECL [`tt:(real^3->bool)->bool`; `v0:real^3`; `y0:real^3`] MOI_FAN_EDGE_CYCLE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:num` (X_CHOOSE_THEN `U:num->real^3` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(tau:real^3->bool) IN tt /\ (tau':real^3->bool) IN tt` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[v0:real^3,y0] SUBSET tau /\ segment[v0,y0] SUBSET tau'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `tau INTER tau' = segment[v0:real^3,y0]` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?i0. i0 < (dd:num) /\ tau = convex hull {v0:real^3,y0,(U:num->real^3) i0}` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&2:int`)) (concl th) &&
      can (find_term (fun t -> t = `dd:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?i1. i1 < (dd:num) /\ tau' = convex hull {v0:real^3,y0,(U:num->real^3) i1}` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `&2:int`)) (concl th) &&
      can (find_term (fun t -> t = `dd:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(i0:num = i1)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(tau:real^3->bool = tau')` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!i. (U:num->real^3) i IN UNIONS la ==> U i = U i0 \/ U i = U i1`
  (LABEL_TAC "lapos") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `convex hull {v0:real^3,y0,U(i:num)} IN ldT` ASSUME_TAC THENL
     [EXPAND_TAC "ldT" THEN
      MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                     `barycentric_subdivision (la:(real^3->bool)->bool)`;
                     `{v0:real^3,y0,U(i:num)}`] MOI_FSP_HULL_FULL) THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ldT:(real^3->bool)->bool`; `segment[v0:real^3,y0]`; `tau:real^3->bool`;
                   `tau':real^3->bool`; `convex hull {v0:real^3,y0,U(i:num)}`]
      MOI_FAN_EDGE_TWO) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[AFF_DIM_SEGMENT]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. (U:num->real^3) i IN UNIONS lm ==> U i IN UNIONS la`
  (LABEL_TAC "mpos") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`tt:(real^3->bool)->bool`; `convex hull {v0:real^3,y0,U(i:num)}`;
                   `v0:real^3`; `(U:num->real^3) i`] MOI_FAN_VERTEX_EDGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`; `v0:real^3`; `(U:num->real^3) i`]
      MOI_FSP_NO_CROSS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^3) i0 IN UNIONS la /\ U i1 IN UNIONS la` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `UNIONS (ldT:(real^3->bool)->bool) = UNIONS la`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    REWRITE_TAC[IN_UNIONS] THEN CONJ_TAC THENL
     [EXISTS_TAC `tau:real^3->bool`; EXISTS_TAC `tau':real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `w = (U:num->real^3)(i0 + 1) \/ w = U(i0 + dd - 1)` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^3) IN moi_fan_w t la tau` THEN
    REWRITE_TAC[moi_fan_w; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `d:real^3->bool` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC MOI_FAN_FAN_W THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^3->bool)->bool`; `v0:real^3`; `y0:real^3`;
                          `d:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?s. 0 < s /\ s < dd /\ (U:num->real^3)(i0 + s) = U i1` STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `i0 < i1:num` THENL
     [EXISTS_TAC `i1 - i0:num` THEN
      SUBGOAL_THEN `i0 + i1 - i0 = i1:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[] THEN ASM_ARITH_TAC;
      EXISTS_TAC `i1 + dd - i0:num` THEN
      SUBGOAL_THEN `i0 + i1 + dd - i0 = i1 + dd:num` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r < dd /\ ~(r = 0) /\ ~(r = s)
        ==> ~((U:num->real^3)(i0 + r) IN UNIONS la) /\ ~(U(i0 + r) IN UNIONS lm)`
  (LABEL_TAC "off") THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `~p /\ (q ==> p) ==> ~p /\ ~q`) THEN
    CONJ_TAC THENL [ALL_TAC; USE_THEN "mpos" MATCH_ACCEPT_TAC] THEN
    DISCH_TAC THEN
    USE_THEN "lapos" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(U:num->real^3)(i0 + r) IN UNIONS la`))) THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`dd:num`; `U:num->real^3`; `i0:num`; `r:num`; `0`] MOI_FSP_WINDOW_INJ) THEN
      ASM_REWRITE_TAC[ADD_CLAUSES] THEN ASM_ARITH_TAC;
      MP_TAC(ISPECL [`dd:num`; `U:num->real^3`; `i0:num`; `r:num`; `s:num`] MOI_FSP_WINDOW_INJ) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. (U:num->real^3) i IN UNIONS la /\ U(SUC i) IN UNIONS la ==> F`
  (LABEL_TAC "notwo") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `convex hull {v0:real^3,y0,U(i:num),U(SUC i)} IN ldT` ASSUME_TAC THENL
     [EXPAND_TAC "ldT" THEN
      MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                     `barycentric_subdivision (la:(real^3->bool)->bool)`;
                     `{v0:real^3,y0,U(i:num),U(SUC i)}`] MOI_FSP_HULL_FULL) THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`ldT:(real^3->bool)->bool`;
                   `convex hull {v0:real^3,y0,U(i:num),U(SUC i)}`] MOI_FSB_DIM) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `2 <= s /\ s + 2 <= dd` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(ARITH_RULE `(~(m <= n) ==> F) ==> m <= n:num`) THEN
    DISCH_TAC THEN USE_THEN "notwo" MATCH_MP_TAC THENL
     [EXISTS_TAC `i0:num` THEN
      SUBGOAL_THEN `SUC i0 = i0 + s` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `i0 + s:num` THEN
      SUBGOAL_THEN `SUC(i0 + s) = i0 + dd` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      FIRST_ASSUM(fun th -> if concl th = `!i. (U:num->real^3)(i + dd) = U i`
        then REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] th] else failwith "no") THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[ADD_SYM] THEN FIRST_ASSUM(fun th -> if concl th = `!i. (U:num->real^3)(i + dd) = U i`
        then REWRITE_TAC[th] else failwith "no") THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^3) IN moi_fan_bside t la lm j1 j2` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fan_w t la tau SUBSET moi_fan_bside t la lm j1 (j2:real^3->bool)` THEN
    UNDISCH_TAC `(w:real^3) IN moi_fan_w t la tau` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. segment[(U:num->real^3) i,U(SUC i)] IN
          barycentric_subdivision (barycentric_subdivision t) /\
        convex hull {v0:real^3,y0,U i,U(SUC i)} IN
          barycentric_subdivision (barycentric_subdivision t) /\
        segment[U i,U(SUC i)] SUBSET convex hull {v0,y0,U i,U(SUC i)} /\
        ~(U i = U(SUC i))`
  (LABEL_TAC "fan") THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
    can (find_term ((=) `w:real^3`)) (concl th))) THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                   `j1:real^3->bool`; `j2:real^3->bool`; `a1:real^3->bool`; `a2:real^3->bool`;
                   `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                   `v0:real^3`; `y0:real^3`; `U:num->real^3`; `i0 + 1`; `s - 2`]
      MOI_FAN_ARC_PATH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      REWRITE_TAC[ARITH_RULE `(i0 + 1) + r = i0 + (r + 1)`] THEN
      USE_THEN "off" MATCH_MP_TAC THEN UNDISCH_TAC `(r:num) <= s - 2` THEN (MAP_EVERY UNDISCH_TAC [`2 <= (s:num)`; `(s:num) + 2 <= dd`; `0 < (s:num)`; `(s:num) < dd`] THEN ARITH_TAC);
      STRIP_TAC] THEN
    EXISTS_TAC `(U:num->real^3)(i0 + s - 1)` THEN
    EXISTS_TAC `{(U:num->real^3)(i0 + 1)} UNION
                UNIONS {segment[U((i0 + 1) + j),U(SUC((i0 + 1) + j))] | j | j < s - 2}` THEN
    SUBGOAL_THEN `(i0 + 1) + (s - 2) = i0 + s - 1` (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL [(MAP_EVERY UNDISCH_TAC [`2 <= (s:num)`; `(s:num) + 2 <= dd`; `0 < (s:num)`; `(s:num) < dd`] THEN ARITH_TAC); ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_fan_w; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "off" (MP_TAC o SPEC `s - 1`) THEN ANTS_TAC THENL [(MAP_EVERY UNDISCH_TAC [`2 <= (s:num)`; `(s:num) + 2 <= dd`; `0 < (s:num)`; `(s:num) < dd`] THEN ARITH_TAC); ALL_TAC] THEN
        SUBGOAL_THEN `i0 + (s - 1) = i0 + s - 1` (fun th -> REWRITE_TAC[th]) THENL
         [(MAP_EVERY UNDISCH_TAC [`2 <= (s:num)`; `(s:num) + 2 <= dd`; `0 < (s:num)`; `(s:num) < dd`] THEN ARITH_TAC); SIMP_TAC[]];
        EXISTS_TAC `convex hull {v0:real^3,y0,U(i0 + s - 1),U(SUC(i0 + s - 1))}` THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `SUC(i0 + s - 1) = i0 + s` SUBST1_TAC THENL [(MAP_EVERY UNDISCH_TAC [`2 <= (s:num)`; `(s:num) + 2 <= dd`; `0 < (s:num)`; `(s:num) < dd`] THEN ARITH_TAC); ALL_TAC] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM(MP_TAC o SPEC `i0 + s - 1` o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> t = `&3:int`)) (concl th) &&
            not (can (find_term (fun t -> t = `dd:num`)) (concl th)))) THEN
          SUBGOAL_THEN `SUC(i0 + s - 1) = i0 + s` SUBST1_TAC THENL [(MAP_EVERY UNDISCH_TAC [`2 <= (s:num)`; `(s:num) + 2 <= dd`; `0 < (s:num)`; `(s:num) < dd`] THEN ARITH_TAC); ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[];
          MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[]]];
      SUBGOAL_THEN `(U:num->real^3)(i0 + 1) IN moi_fan_bside t la lm j1 j2` ASSUME_TAC THENL
       [UNDISCH_TAC `(w:real^3) IN moi_fan_bside t la lm j1 j2` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                     `j1:real^3->bool`; `j2:real^3->bool`; `a1:real^3->bool`; `a2:real^3->bool`;
                     `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                     `{(U:num->real^3)(i0 + 1)} UNION
                      UNIONS {segment[U((i0 + 1) + j),U(SUC((i0 + 1) + j))] | j | j < s - 2}`]
        MOI_FAN_B_CLOPEN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `(U:num->real^3)(i0 + 1)` THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]]];
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                   `j1:real^3->bool`; `j2:real^3->bool`; `a1:real^3->bool`; `a2:real^3->bool`;
                   `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                   `v0:real^3`; `y0:real^3`; `U:num->real^3`; `i0 + s + 1`; `dd - s - 2`]
      MOI_FAN_ARC_PATH) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `r:num` THEN DISCH_TAC THEN
      REWRITE_TAC[ARITH_RULE `(i0 + s + 1) + r = i0 + (s + r + 1)`] THEN
      USE_THEN "off" MATCH_MP_TAC THEN UNDISCH_TAC `(r:num) <= dd - s - 2` THEN (MAP_EVERY UNDISCH_TAC [`2 <= (s:num)`; `(s:num) + 2 <= dd`; `0 < (s:num)`; `(s:num) < dd`] THEN ARITH_TAC);
      STRIP_TAC] THEN
    EXISTS_TAC `(U:num->real^3)(i0 + s + 1)` THEN
    EXISTS_TAC `{(U:num->real^3)(i0 + s + 1)} UNION
                UNIONS {segment[U((i0 + s + 1) + j),U(SUC((i0 + s + 1) + j))] |
                        j | j < dd - s - 2}` THEN
    SUBGOAL_THEN `(i0 + s + 1) + (dd - s - 2) = i0 + dd - 1`
      (fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th]))
    THENL [(MAP_EVERY UNDISCH_TAC [`2 <= (s:num)`; `(s:num) + 2 <= dd`; `0 < (s:num)`; `(s:num) < dd`] THEN ARITH_TAC); ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_fan_w; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [USE_THEN "off" (MP_TAC o SPEC `s + 1`) THEN ANTS_TAC THENL [(MAP_EVERY UNDISCH_TAC [`2 <= (s:num)`; `(s:num) + 2 <= dd`; `0 < (s:num)`; `(s:num) < dd`] THEN ARITH_TAC); ALL_TAC] THEN
        REWRITE_TAC[ADD_ASSOC] THEN SIMP_TAC[];
        EXISTS_TAC `convex hull {v0:real^3,y0,U(i0 + s),U(SUC(i0 + s))}` THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `SUC(i0 + s) = i0 + s + 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
        CONJ_TAC THENL
         [FIRST_ASSUM(MP_TAC o SPEC `i0 + s:num` o check (fun th -> is_forall(concl th) &&
            can (find_term (fun t -> t = `&3:int`)) (concl th) &&
            not (can (find_term (fun t -> t = `dd:num`)) (concl th)))) THEN
          SUBGOAL_THEN `SUC(i0 + s) = i0 + s + 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
          ASM_REWRITE_TAC[] THEN SIMP_TAC[];
          MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[]]];
      SUBGOAL_THEN `(U:num->real^3)(i0 + dd - 1) IN moi_fan_bside t la lm j1 j2` ASSUME_TAC THENL
       [UNDISCH_TAC `(w:real^3) IN moi_fan_bside t la lm j1 j2` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                     `j1:real^3->bool`; `j2:real^3->bool`; `a1:real^3->bool`; `a2:real^3->bool`;
                     `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                     `{(U:num->real^3)(i0 + s + 1)} UNION
                      UNIONS {segment[U((i0 + s + 1) + j),U(SUC((i0 + s + 1) + j))] |
                              j | j < dd - s - 2}`]
        MOI_FAN_B_CLOPEN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `(U:num->real^3)(i0 + dd - 1)` THEN ASM_REWRITE_TAC[];
        SIMP_TAC[]]]]);;

(* The transport along ldT: a set R closed under connectivity inside B that *)
(* contains the far vertices of one triangle of ldT contains those of all.  *)

let MOI_FAN_TRANSPORT = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 R.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     (!x y G. x IN R /\ connected G /\ G SUBSET moi_fan_bside t la lm j1 j2 /\
              x IN G /\ y IN G ==> y IN R) /\
     (?tau. tau IN barycentric_subdivision (barycentric_subdivision la) /\
            aff_dim tau = &2 /\ moi_fan_w t la tau SUBSET R)
     ==> !tau. tau IN barycentric_subdivision (barycentric_subdivision la) /\
               aff_dim tau = &2 ==> moi_fan_w t la tau SUBSET R`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_D th)) STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (la:(real^3->bool)->bool))`;
                 `{tau:real^3->bool | tau IN barycentric_subdivision
                                        (barycentric_subdivision la) /\
                                      aff_dim tau = &2 /\ moi_fan_w t la tau SUBSET R}`]
    MOI_FRB_CMB2_DCONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real^3->bool`; `s':real^3->bool`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `w':real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(s':real^3->bool = s)` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `aff_dim (s INTER s:real^3->bool) = &1` THEN
        ASM_REWRITE_TAC[INTER_IDEMPOT] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                     `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                     `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                     `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                     `s':real^3->bool`; `s:real^3->bool`; `w':real^3`] MOI_FAN_W_ADJ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` (X_CHOOSE_THEN `G:real^3->bool` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `R:real^3->bool`)) (concl th) &&
        can (find_term (fun t -> t = `connected:(real^3->bool)->bool`)) (concl th))) THEN
      MAP_EVERY EXISTS_TAC [`w:real^3`; `G:real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;

(* ========================================================================= *)
(* Step D, the rim data: a boundary edge of ldT on j1 and the cycle around   *)
(* it, with the positions of the triangle of ldT and of the two triangles of *)
(* the second derived of lm on the edge.                                     *)
(* ========================================================================= *)

(* The rim-1 data: a boundary edge [v0,y0] of ldT on j1 (v0 off nothing in *)
(* particular), the cycle U around it (MOI_FAN_EDGE_CYCLE), the position   *)
(* c0 of the unique triangle of ldT on the edge, and the positions r1, r2   *)
(* of the two triangles of the second derived of lm on the edge.            *)

let MOI_FAN_RIM_EDGE = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> ?v0 y0. ~(v0 = y0) /\
                 segment[v0,y0] IN barycentric_subdivision (barycentric_subdivision la) /\
                 CARD {r | r IN barycentric_subdivision (barycentric_subdivision la) /\
                           aff_dim r = &2 /\ segment[v0,y0] SUBSET r} = 1 /\
                 segment[v0,y0] SUBSET j1`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_D th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_SIDES th)) THEN
  ABBREV_TAC `ldT = barycentric_subdivision (barycentric_subdivision (la:(real^3->bool)->bool))` THEN
  MP_TAC(ISPECL [`UNIONS la:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_FCB_ANN_ENDS_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `?x:real^3. x IN j1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN surface_boundary ldT` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  REWRITE_TAC[surface_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?v0 y0:real^3. ~(v0 = y0) /\ e = segment[v0,y0]` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_PL2_SIMPLEX_1] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `aff_dim (e:real^3->bool) = &1`)) THEN
    MATCH_MP_TAC MOI_FM3_LF_SIMPLEX THEN EXISTS_TAC `ldT:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`v0:real^3`; `y0:real^3`] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `segment[v0:real^3,y0] SUBSET j1 UNION j2` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `surface_boundary ldT = j1 UNION (j2:real^3->bool)`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    REWRITE_TAC[surface_boundary] THEN
    MATCH_MP_TAC(SET_RULE `!x:real^3->bool s. x IN s ==> x SUBSET UNIONS s`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`segment[v0:real^3,y0]`; `j1:real^3->bool`; `j2:real^3->bool`]
    MOI_FAN_CONNECTED_SPLIT) THEN
  ASM_SIMP_TAC[CONNECTED_SEGMENT; COMPACT_IMP_CLOSED; DISJOINT] THEN
  UNDISCH_TAC `(x:real^3) IN segment[v0,y0]` THEN UNDISCH_TAC `(x:real^3) IN j1` THEN
  UNDISCH_TAC `j1 INTER j2:real^3->bool = {}` THEN SET_TAC[]);;

(* Positions on a cycle: a vertex U(c0 + r) equal to U i is at the         *)
(* position of i relative to c0 (window injectivity).                       *)

let MOI_FAN_CYC_POS = prove
 (`!dd (U:num->A) c0 i.
     3 <= dd /\ (!i. U(i + dd) = U i) /\ (!i j. i < dd /\ j < dd /\ U i = U j ==> i = j) /\
     c0 < dd /\ i < dd
     ==> ?r. r < dd /\ U(c0 + r) = U i`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `c0 <= i:num` THENL
   [EXISTS_TAC `i - c0:num` THEN
    SUBGOAL_THEN `c0 + i - c0 = i:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_ARITH_TAC;
    EXISTS_TAC `i + dd - c0:num` THEN
    SUBGOAL_THEN `c0 + i + dd - c0 = i + dd:num` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* The rim-1 cycle data.                                                     *)

let MOI_FAN_RIM_DATA = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> ?v0 y0 dd (U:num->real^3) c0 r1 r2.
           ~(v0 = y0) /\ segment[v0,y0] SUBSET j1 /\
           segment[v0,y0] IN barycentric_subdivision (barycentric_subdivision t) /\
           3 <= dd /\ (!i. U(i + dd) = U i) /\
           (!i j. i < dd /\ j < dd /\ U i = U j ==> i = j) /\
           (!i. ~(U i = U(SUC i))) /\ (!i. ~(U i = y0)) /\
           (!i. convex hull {v0, y0, U i} IN
                  barycentric_subdivision (barycentric_subdivision t) /\
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
           (!r. r IN barycentric_subdivision (barycentric_subdivision t) /\ aff_dim r = &2 /\
                segment[v0,y0] SUBSET r
                ==> ?i. i < dd /\ r = convex hull {v0, y0, U i}) /\
           (!i j. convex hull {v0, y0, U i} = convex hull {v0, y0, U j} ==> U i = U j) /\
           (!r. r IN barycentric_subdivision (barycentric_subdivision t) /\ aff_dim r = &3 /\
                segment[v0,y0] SUBSET r
                ==> ?i. i < dd /\ r = convex hull {v0, y0, U i, U(SUC i)}) /\
           c0 < dd /\
           convex hull {v0,y0,U c0} IN barycentric_subdivision (barycentric_subdivision la) /\
           U c0 IN UNIONS la /\ ~(U c0 IN UNIONS lm) /\
           (!r. 0 < r /\ r < dd ==> ~(U(c0 + r) IN UNIONS la)) /\
           U(c0 + r1) IN UNIONS lm /\ U(c0 + r2) IN UNIONS lm /\
           (!r. r < dd /\ ~(r = r1) /\ ~(r = r2) ==> ~(U(c0 + r) IN UNIONS lm)) /\
           2 <= r1 /\ r1 + 2 <= r2 /\ r2 + 2 <= dd`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_M th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_D th) THEN
    MP_TAC(MATCH_MP MOI_FAN_RIM_EDGE th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^3` (X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `tt = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  ABBREV_TAC `ldT = barycentric_subdivision (barycentric_subdivision (la:(real^3->bool)->bool))` THEN
  ABBREV_TAC `lmT = barycentric_subdivision (barycentric_subdivision (lm:(real^3->bool)->bool))` THEN
  SUBGOAL_THEN `(v0:real^3) IN j1 /\ (y0:real^3) IN j1` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(v0:real^3) IN UNIONS la /\ (y0:real^3) IN UNIONS la /\
                v0 IN UNIONS lm /\ y0 IN UNIONS lm`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS la INTER UNIONS lm = j1 UNION (j2:real^3->bool)` THEN
    UNDISCH_TAC `(v0:real^3) IN j1` THEN UNDISCH_TAC `(y0:real^3) IN j1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v0:real^3,y0] IN tt /\ {v0:real^3} IN tt` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `segment[v0:real^3,y0] IN tt` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FM3_LF_FACE THEN
    EXISTS_TAC `segment[v0:real^3,y0]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^3->bool)->bool`; `v0:real^3`; `y0:real^3`] MOI_FAN_EDGE_CYCLE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `dd:num` (X_CHOOSE_THEN `U:num->real^3` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`v0:real^3`; `y0:real^3`; `dd:num`; `U:num->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!S:real^3->bool. FINITE S /\ S SUBSET UNIONS la /\ convex hull S IN tt
                     ==> convex hull S IN ldT`
  (LABEL_TAC "fla") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ldT" THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision (la:(real^3->bool)->bool)`;
                   `S:real^3->bool`] MOI_FSP_HULL_FULL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!S:real^3->bool. FINITE S /\ S SUBSET UNIONS lm /\ convex hull S IN tt
                     ==> convex hull S IN lmT`
  (LABEL_TAC "flm") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "lmT" THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                   `S:real^3->bool`] MOI_FSP_HULL_FULL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?c0. c0 < dd /\
         {r | r IN ldT /\ aff_dim r = &2 /\ segment[v0:real^3,y0] SUBSET r} =
         {convex hull {v0,y0,(U:num->real^3) c0}}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{r | r IN ldT /\ aff_dim r = &2 /\ segment[v0:real^3,y0] SUBSET r} HAS_SIZE 1`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE] THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` ASSUME_TAC) THEN
    SUBGOAL_THEN `(q:real^3->bool) IN ldT /\ aff_dim q = &2 /\ segment[v0:real^3,y0] SUBSET q`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(q:real^3->bool) IN {r | r IN ldT /\ aff_dim r = &2 /\
                                            segment[v0:real^3,y0] SUBSET r}` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_SING]; REWRITE_TAC[IN_ELIM_THM]];
      ALL_TAC] THEN
    SUBGOAL_THEN `?i. i < dd /\ q = convex hull {v0:real^3,y0,(U:num->real^3) i}`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `&2:int`)) (concl th) &&
        can (find_term (fun t -> t = `dd:num`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
      ALL_TAC] THEN
    EXISTS_TAC `i:num` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `c0:num` THEN
  SUBGOAL_THEN `convex hull {v0:real^3,y0,(U:num->real^3) c0} IN ldT /\
                segment[v0,y0] SUBSET convex hull {v0,y0,U c0}` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `convex hull {v0:real^3,y0,(U:num->real^3) c0} IN
                  {r | r IN ldT /\ aff_dim r = &2 /\ segment[v0:real^3,y0] SUBSET r}` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_SING]; REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^3) c0 IN UNIONS la` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if concl th = `UNIONS (ldT:(real^3->bool)->bool) = UNIONS la`
      then REWRITE_TAC[SYM th] else failwith "no") THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `convex hull {v0:real^3,y0,(U:num->real^3) c0}` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((U:num->real^3) c0 IN UNIONS lm)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                   `j1:real^3->bool`; `j2:real^3->bool`; `a1:real^3->bool`; `a2:real^3->bool`;
                   `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                   `convex hull {v0:real^3,y0,(U:num->real^3) c0}`] MOI_FAN_TRI_OFF_RIM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(p:real^3) IN {v0,y0,(U:num->real^3) c0}` MP_TAC THENL
     [MATCH_MP_TAC EXTREME_POINT_OF_CONVEX_HULL THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
      MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN EXISTS_TAC `tt:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[SING_SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((p:real^3) IN UNIONS lm)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!r. 0 < r /\ r < dd ==> ~((U:num->real^3)(c0 + r) IN UNIONS la)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `convex hull {v0:real^3,y0,(U:num->real^3)(c0 + r)} IN
                  {r | r IN ldT /\ aff_dim r = &2 /\ segment[v0:real^3,y0] SUBSET r}`
    MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN USE_THEN "fla" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SING] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(U:num->real^3)(c0 + r) = U(c0 + 0)` ASSUME_TAC THENL
     [REWRITE_TAC[ADD_CLAUSES] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `(U:num->real^3) j`)) (concl th) &&
        not (can (find_term (fun t -> t = `dd:num`)) (concl th)))) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`dd:num`; `U:num->real^3`; `c0:num`; `r:num`; `0`] MOI_FSP_WINDOW_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `3 <= (dd:num)` THEN ARITH_TAC;
      UNDISCH_TAC `0 < (r:num)` THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `segment[v0:real^3,y0] IN lmT` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN USE_THEN "flm" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET;
                    GSYM SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?i1 i2. i1 < dd /\ i2 < dd /\ ~((U:num->real^3) i1 = U i2) /\
            U i1 IN UNIONS lm /\ U i2 IN UNIONS lm /\
            !i. U i IN UNIONS lm ==> U i = U i1 \/ U i = U i2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lmT:(real^3->bool)->bool`; `segment[v0:real^3,y0]`] MOI_FSA_CM_EDGE2) THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN DISCH_TAC THEN
    SUBGOAL_THEN `{r | r IN lmT /\ aff_dim r = &2 /\ segment[v0:real^3,y0] SUBSET r} HAS_SIZE 2`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE] THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `q1:real^3->bool` (X_CHOOSE_THEN `q2:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `!q:real^3->bool. q IN lmT /\ aff_dim q = &2 /\ segment[v0,y0] SUBSET q <=>
                       q = q1 \/ q = q2`
    ASSUME_TAC THENL
     [GEN_TAC THEN
      SUBGOAL_THEN `(q:real^3->bool) IN {r | r IN lmT /\ aff_dim r = &2 /\
                                           segment[v0:real^3,y0] SUBSET r} <=> q IN {q1,q2}`
      MP_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY]];
      ALL_TAC] THEN
    SUBGOAL_THEN `!q:real^3->bool. q IN lmT ==> q IN tt` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `?i1. i1 < dd /\ q1 = convex hull {v0:real^3,y0,(U:num->real^3) i1}`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `&2:int`)) (concl th) &&
        can (find_term (fun t -> t = `dd:num`)) (concl th))) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `?i2. i2 < dd /\ q2 = convex hull {v0:real^3,y0,(U:num->real^3) i2}`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `&2:int`)) (concl th) &&
        can (find_term (fun t -> t = `dd:num`)) (concl th))) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`i1:num`; `i2:num`] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(q1:real^3->bool) IN lmT /\ (q2:real^3->bool) IN lmT` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(q1:real^3->bool = q2)` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(fun th -> if concl th = `UNIONS (lmT:(real^3->bool)->bool) = UNIONS lm`
        then REWRITE_TAC[SYM th] else failwith "no") THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `q1:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(q1:real^3->bool) IN lmT` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
      FIRST_X_ASSUM(fun th -> if concl th = `UNIONS (lmT:(real^3->bool)->bool) = UNIONS lm`
        then REWRITE_TAC[SYM th] else failwith "no") THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `q2:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(q2:real^3->bool) IN lmT` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      SUBGOAL_THEN `convex hull {v0:real^3,y0,(U:num->real^3) i} IN lmT` ASSUME_TAC THENL
       [USE_THEN "flm" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET];
        ALL_TAC] THEN
      SUBGOAL_THEN `convex hull {v0:real^3,y0,(U:num->real^3) i} = q1 \/
                    convex hull {v0,y0,U i} = q2` MP_TAC THENL
       [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
           can (find_term (fun t -> t = `q1:real^3->bool`)) (concl th)
          then REWRITE_TAC[GSYM th] else failwith "no") THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r < dd /\ (U:num->real^3)(c0 + r) IN UNIONS lm ==> U(c0 + r) = U i1 \/ U(c0 + r) = U i2`
  (LABEL_TAC "mp") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term (fun t -> t = `i2:num`)) (concl th))) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`dd:num`; `U:num->real^3`; `c0:num`; `i1:num`] MOI_FAN_CYC_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s1:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`dd:num`; `U:num->real^3`; `c0:num`; `i2:num`] MOI_FAN_CYC_POS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s2:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(s1 = 0) /\ ~(s2 = 0) /\ ~(s1:num = s2)` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~((U:num->real^3) c0 IN UNIONS lm)` THEN
      UNDISCH_TAC `(U:num->real^3)(c0 + s1) = U i1` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `~((U:num->real^3) c0 IN UNIONS lm)` THEN
      UNDISCH_TAC `(U:num->real^3)(c0 + s2) = U i2` THEN ASM_REWRITE_TAC[ADD_CLAUSES] THEN
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `~((U:num->real^3) i1 = U i2)` THEN
      UNDISCH_TAC `(U:num->real^3)(c0 + s1) = U i1` THEN
      UNDISCH_TAC `(U:num->real^3)(c0 + s2) = U i2` THEN ASM_REWRITE_TAC[] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. r < dd /\ (U:num->real^3)(c0 + r) IN UNIONS lm ==> r = s1 \/ r = s2`
  (LABEL_TAC "mpos2") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "mp" (fun th -> MP_TAC(MATCH_MP th (CONJ (ASSUME `r < (dd:num)`)
      (ASSUME `(U:num->real^3)(c0 + r) IN UNIONS lm`)))) THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN MATCH_MP_TAC(INST_TYPE [`:real^3`,`:A`] MOI_FSP_WINDOW_INJ) THEN
      MAP_EVERY EXISTS_TAC [`dd:num`; `U:num->real^3`; `c0:num`] THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN MATCH_MP_TAC(INST_TYPE [`:real^3`,`:A`] MOI_FSP_WINDOW_INJ) THEN
      MAP_EVERY EXISTS_TAC [`dd:num`; `U:num->real^3`; `c0:num`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q. p < q /\ q < dd /\ ~(p = 0) /\
          (U:num->real^3)(c0 + p) IN UNIONS lm /\ U(c0 + q) IN UNIONS lm
          ==> 2 <= p /\ p + 2 <= q /\ q + 2 <= dd`
  (LABEL_TAC "space") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC(ARITH_RULE `(~(m <= n) ==> F) ==> m <= n:num`) THEN DISCH_TAC THENL
     [SUBGOAL_THEN `(p:num) = 1` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `~(2 <= (p:num))` THEN UNDISCH_TAC `~((p:num) = 0)` THEN ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                     `(U:num->real^3) c0`; `(U:num->real^3)(c0 + 1)`] MOI_FSP_NO_CROSS) THEN
      ASM_REWRITE_TAC[GSYM ADD1] THEN
      FIRST_ASSUM(MP_TAC o SPEC `1` o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `UNIONS (la:(real^3->bool)->bool)`)) (concl th) &&
        can (find_term (fun t -> t = `0 < r`)) (concl th))) THEN
      REWRITE_TAC[ADD1] THEN ANTS_TAC THENL
       [UNDISCH_TAC `3 <= (dd:num)` THEN ARITH_TAC; SIMP_TAC[]];
      SUBGOAL_THEN `SUC(c0 + p) = c0 + q` ASSUME_TAC THENL
       [UNDISCH_TAC `~((p:num) + 2 <= q)` THEN UNDISCH_TAC `p < (q:num)` THEN ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `convex hull {v0:real^3,y0,(U:num->real^3)(c0 + p),U(SUC(c0 + p))} IN lmT`
      ASSUME_TAC THENL
       [USE_THEN "flm" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`lmT:(real^3->bool)->bool`;
                     `convex hull {v0:real^3,y0,(U:num->real^3)(c0 + p),U(SUC(c0 + p))}`]
        MOI_FSB_DIM) THEN
      ASM_SIMP_TAC[MOI_S8TA_CM_CMB] THEN INT_ARITH_TAC;
      SUBGOAL_THEN `(q:num) + 1 = dd` ASSUME_TAC THENL
       [UNDISCH_TAC `~((q:num) + 2 <= dd)` THEN UNDISCH_TAC `q < (dd:num)` THEN ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                     `(U:num->real^3) c0`; `(U:num->real^3)(c0 + q)`] MOI_FSP_NO_CROSS) THEN
      ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
        SUBGOAL_THEN `(U:num->real^3) c0 = U(SUC(c0 + q))` SUBST1_TAC THENL
         [SUBGOAL_THEN `SUC(c0 + q) = c0 + dd` SUBST1_TAC THENL
           [UNDISCH_TAC `(q:num) + 1 = dd` THEN ARITH_TAC; ALL_TAC] THEN
          ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[]];
        FIRST_ASSUM(MP_TAC o SPEC `q:num` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `UNIONS (la:(real^3->bool)->bool)`)) (concl th) &&
          can (find_term (fun t -> t = `0 < r`)) (concl th))) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `p < (q:num)` THEN ARITH_TAC; SIMP_TAC[]]]];
    ALL_TAC] THEN
  ASM_CASES_TAC `s1 < s2:num` THENL
   [MAP_EVERY EXISTS_TAC [`s1:num`; `s2:num`];
    MAP_EVERY EXISTS_TAC [`s2:num`; `s1:num`]] THEN
  ASM_REWRITE_TAC[] THEN
  (CONJ_TAC THENL
    [REPEAT STRIP_TAC THEN USE_THEN "mpos2" (MP_TAC o SPEC `r:num`) THEN ASM_REWRITE_TAC[];
     USE_THEN "space" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
     UNDISCH_TAC `~(s1 < s2:num)` THEN UNDISCH_TAC `~(s1:num = s2)` THEN ARITH_TAC]) THEN
  ASM_MESON_TAC[]);;

(* ========================================================================= *)
(* Step D, the crossing at rim 1: the rim data as a predicate, the closed    *)
(* star of a simplex is a neighbourhood of its relative interior points in   *)
(* the interior, and the cycle vertex just past the first triangle of M on   *)
(* the rim edge is off the int-a side.                                       *)
(* ========================================================================= *)

(* The rim data as a predicate (the conclusion of MOI_FAN_RIM_DATA).          *)

let moi_fan_rimdata = new_definition
 `moi_fan_rimdata (t:(real^3->bool)->bool) (la:(real^3->bool)->bool)
                  (lm:(real^3->bool)->bool) (j1:real^3->bool)
                  (v0:real^3) (y0:real^3) (dd:num) (U:num->real^3) (c0:num) (r1:num) (r2:num) <=>
           ~(v0 = y0) /\ segment[v0,y0] SUBSET j1 /\
           segment[v0,y0] IN barycentric_subdivision (barycentric_subdivision t) /\
           3 <= dd /\ (!i. U(i + dd) = U i) /\
           (!i j. i < dd /\ j < dd /\ U i = U j ==> i = j) /\
           (!i. ~(U i = U(SUC i))) /\ (!i. ~(U i = y0)) /\
           (!i. convex hull {v0, y0, U i} IN
                  barycentric_subdivision (barycentric_subdivision t) /\
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
           (!r. r IN barycentric_subdivision (barycentric_subdivision t) /\ aff_dim r = &2 /\
                segment[v0,y0] SUBSET r
                ==> ?i. i < dd /\ r = convex hull {v0, y0, U i}) /\
           (!i j. convex hull {v0, y0, U i} = convex hull {v0, y0, U j} ==> U i = U j) /\
           (!r. r IN barycentric_subdivision (barycentric_subdivision t) /\ aff_dim r = &3 /\
                segment[v0,y0] SUBSET r
                ==> ?i. i < dd /\ r = convex hull {v0, y0, U i, U(SUC i)}) /\
           c0 < dd /\
           convex hull {v0,y0,U c0} IN barycentric_subdivision (barycentric_subdivision la) /\
           U c0 IN UNIONS la /\ ~(U c0 IN UNIONS lm) /\
           (!r. 0 < r /\ r < dd ==> ~(U(c0 + r) IN UNIONS la)) /\
           U(c0 + r1) IN UNIONS lm /\ U(c0 + r2) IN UNIONS lm /\
           (!r. r < dd /\ ~(r = r1) /\ ~(r = r2) ==> ~(U(c0 + r) IN UNIONS lm)) /\
           2 <= r1 /\ r1 + 2 <= r2 /\ r2 + 2 <= dd`;;

let MOI_FAN_RIMDATA_EXISTS = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> ?v0 y0 dd U c0 r1 r2. moi_fan_rimdata t la lm j1 v0 y0 dd U c0 r1 r2`,
  REWRITE_TAC[moi_fan_rimdata; MOI_FAN_RIM_DATA]);;

(* The closed star of a simplex e at a relative interior point y of e that  *)
(* lies in the interior of the polyhedron is a neighbourhood of y.          *)

let MOI_FAN_STAR_BALL = prove
 (`!(tt:(real^N->bool)->bool) e y.
     FINITE tt /\ lf_simplicial_complex tt /\ e IN tt /\ y IN relative_interior e /\
     y IN interior (UNIONS tt)
     ==> ?d. &0 < d /\ ball(y,d) SUBSET UNIONS {s | s IN tt /\ e SUBSET s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (UNIONS {s | s IN tt /\ ~((y:real^N) IN s)})` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    CONJ_TAC THENL [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_FM3_LF_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d1. &0 < d1 /\
                ball(y:real^N,d1) INTER UNIONS {s | s IN tt /\ ~(y IN s)} = {}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open ((:real^N) DIFF UNIONS {s | s IN tt /\ ~((y:real^N) IN s)})` MP_TAC THENL
     [ASM_SIMP_TAC[OPEN_DIFF; OPEN_UNIV]; ALL_TAC] THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
                    ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?d2. &0 < d2 /\ ball(y:real^N,d2) SUBSET UNIONS tt` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `interior (UNIONS tt):real^N->bool` OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    MP_TAC(ISPEC `UNIONS tt:real^N->bool` INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min d1 d2:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN UNIONS tt` MP_TAC THENL
   [UNDISCH_TAC `ball(y:real^N,d2) SUBSET UNIONS tt` THEN
    MATCH_MP_TAC(SET_RULE `(z:real^N) IN s ==> s SUBSET t ==> z IN t`) THEN
    UNDISCH_TAC `(z:real^N) IN ball(y,min d1 d2)` THEN REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:real^N) IN s` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `ball(y:real^N,d1) INTER UNIONS {s | s IN tt /\ ~(y IN s)} = {}` THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
     [UNDISCH_TAC `(z:real^N) IN ball(y,min d1 d2)` THEN REWRITE_TAC[IN_BALL] THEN
      REAL_ARITH_TAC;
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e INTER s:real^N->bool) face_of e` ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `e INTER s = e ==> !x:real^N. x IN e ==> x IN s`) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`e INTER s:real^N->bool`; `e:real^N->bool`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(y:real^N) IN relative_interior e` THEN UNDISCH_TAC `(y:real^N) IN s` THEN
  MP_TAC(ISPEC `e:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]);;

(* The crossing at rim 1: the cycle vertex U(c0 + r1 + 1), just past the   *)
(* first triangle of M on the rim edge, is not on the int-a side of the     *)
(* rim-1 component.  Otherwise every tetrahedron of the edge star, minus M, *)
(* would lie on that side; the star covers a ball around a point of the     *)
(* edge, which meets the far side.                                          *)

let MOI_FAN_RIM_CROSS = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 v0 y0 dd U c0 r1 r2.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     moi_fan_rimdata t la lm j1 v0 y0 dd U c0 r1 r2
     ==> ~((U:num->real^3)(c0 + r1 + 1) IN
           moi_fan_side lm j1 (UNIONS la DIFF (j1 UNION j2)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_M th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_D th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_SIDES th))
   (STRIP_ASSUME_TAC o REWRITE_RULE[moi_fan_rimdata])) THEN
  ABBREV_TAC `X = UNIONS la DIFF (j1 UNION j2:real^3->bool)` THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j1:real^3->bool`] MOI_FAN_MC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j1:real^3->bool`; `X:real^3->bool`]
    MOI_FAN_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (X:real^3->bool) (UNIONS lm)` THEN
    UNDISCH_TAC `moi_fan_mc lm j1 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
    STRIP_TAC] THEN
  ABBREV_TAC `S1 = moi_fan_side lm j1 (X:real^3->bool)` THEN
  ABBREV_TAC `fa1 = moi_fan_far lm j1 (X:real^3->bool)` THEN
  ABBREV_TAC `mc1 = moi_fan_mc lm (j1:real^3->bool)` THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(U:num->real^3) c0 IN S1` ASSUME_TAC THENL
   [UNDISCH_TAC `(X:real^3->bool) SUBSET S1` THEN
    MATCH_MP_TAC(SET_RULE `(x:real^3) IN X ==> X SUBSET S ==> x IN S`) THEN
    EXPAND_TAC "X" THEN
    UNDISCH_TAC `UNIONS la INTER UNIONS lm = j1 UNION (j2:real^3->bool)` THEN
    UNDISCH_TAC `~((U:num->real^3) c0 IN UNIONS lm)` THEN
    UNDISCH_TAC `(U:num->real^3) c0 IN UNIONS la` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a n. (!r. r <= n ==> ~((U:num->real^3)(a + r) IN UNIONS lm)) /\
          (U a IN S1 \/ U(a + n) IN S1) ==> U a IN S1 /\ U(a + n) IN S1`
  (LABEL_TAC "pside") THENL
   [REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
    ABBREV_TAC `P = {(U:num->real^3) a} UNION
                    UNIONS {segment[U(a + j),U(SUC(a + j))] | j | j < n}` THEN
    SUBGOAL_THEN `connected (P:real^3->bool) /\ U a IN P /\ (U:num->real^3)(a + n) IN P`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN REWRITE_TAC[MOI_FSP_PATH_CONN; IN_UNION; IN_SING]; ALL_TAC] THEN
    SUBGOAL_THEN `(P:real^3->bool) INTER UNIONS lm = {}` ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:real^3` THEN REWRITE_TAC[MOI_FSP_PATH_MEMBER] THEN STRIP_TAC THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
          lhs(concl th) = `x:real^3`)) THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `n:num`)) (concl th))) THEN
        ASM_REWRITE_TAC[ADD_CLAUSES; LE_0];
        SUBGOAL_THEN `~((U:num->real^3)(a + j) IN UNIONS lm) /\ ~(U(SUC(a + j)) IN UNIONS lm)`
        STRIP_ASSUME_TAC THENL
         [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
              can (find_term (fun t -> t = `n:num`)) (concl th)
            then MP_TAC(SPEC `j:num` th) THEN MP_TAC(SPEC `SUC j` th) else failwith "no") THEN
          REWRITE_TAC[ADD_CLAUSES] THEN
          ASM_SIMP_TAC[ARITH_RULE `j < n ==> j <= n /\ SUC j <= n`];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                       `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                       `(U:num->real^3)(a + j)`; `(U:num->real^3)(SUC(a + j))`]
          MOI_FSP_SEG_FULL) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN UNDISCH_TAC `(x:real^3) IN segment[U(a + j),U(SUC(a + j))]` THEN
        UNDISCH_TAC `segment[(U:num->real^3)(a + j),U(SUC(a + j))] INTER UNIONS lm = {}` THEN
        UNDISCH_TAC `(x:real^3) IN UNIONS lm` THEN SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`P:real^3->bool`; `S1:real^3->bool`; `fa1:real^3->bool`]
      MOI_FAN_CONN_OPEN_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(P:real^3->bool) INTER UNIONS lm = {}` THEN
      UNDISCH_TAC `(mc1:real^3->bool) SUBSET UNIONS lm` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (S1:real^3->bool) fa1` THEN
    UNDISCH_TAC `(U:num->real^3) a IN S1 \/ U(a + n) IN S1` THEN
    UNDISCH_TAC `(U:num->real^3) a IN P` THEN UNDISCH_TAC `(U:num->real^3)(a + n) IN P` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^3)(c0 + dd) = U c0` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[ADD_SYM] THEN
    FIRST_ASSUM(fun th -> if concl th = `!i. (U:num->real^3)(i + dd) = U i`
      then REWRITE_TAC[ONCE_REWRITE_RULE[ADD_SYM] th] else failwith "no") THEN
    ONCE_REWRITE_TAC[ADD_SYM] THEN FIRST_ASSUM(fun th -> if concl th = `!i. (U:num->real^3)(i + dd) = U i`
      then REWRITE_TAC[th] else failwith "no");
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r < dd /\ ~(r = r1) /\ ~(r = r2) ==> (U:num->real^3)(c0 + r) IN S1`
  (LABEL_TAC "pos") THENL
   [X_GEN_TAC `r:num` THEN STRIP_TAC THEN
    ASM_CASES_TAC `r = 0:num` THENL [ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    ASM_CASES_TAC `r < r1:num` THENL
     [USE_THEN "pside" (MP_TAC o SPECL [`c0:num`; `r:num`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `r':num` THEN DISCH_TAC THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `r2:num`)) (concl th) &&
          can (find_term (fun t -> t = `UNIONS (lm:(real^3->bool)->bool)`)) (concl th))) THEN
        MAP_EVERY UNDISCH_TAC [`(r':num) <= r`; `r < (r1:num)`; `(r1:num) + 2 <= r2`;
                               `(r2:num) + 2 <= dd`] THEN ARITH_TAC;
        SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `r < r2:num` THENL
     [USE_THEN "pside" (MP_TAC o SPECL [`c0 + r1 + 1:num`; `r - r1 - 1:num`]) THEN
      SUBGOAL_THEN `(c0 + r1 + 1) + r - r1 - 1 = c0 + r:num` SUBST1_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`~(r < (r1:num))`; `~(r:num = r1)`] THEN ARITH_TAC;
        ALL_TAC] THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN X_GEN_TAC `r':num` THEN DISCH_TAC THEN
        REWRITE_TAC[ARITH_RULE `(c0 + r1 + 1) + r' = c0 + (r1 + 1 + r'):num`] THEN
        FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (find_term (fun t -> t = `r2:num`)) (concl th) &&
          can (find_term (fun t -> t = `UNIONS (lm:(real^3->bool)->bool)`)) (concl th))) THEN
        MAP_EVERY UNDISCH_TAC [`(r':num) <= r - r1 - 1`; `r < (r2:num)`; `~(r < (r1:num))`;
                               `~(r:num = r1)`; `(r2:num) + 2 <= dd`] THEN ARITH_TAC;
        SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "pside" (MP_TAC o SPECL [`c0 + r:num`; `dd - r:num`]) THEN
    SUBGOAL_THEN `(c0 + r) + dd - r = c0 + dd:num` SUBST1_TAC THENL
     [UNDISCH_TAC `r < (dd:num)` THEN ARITH_TAC; ALL_TAC] THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `r':num` THEN DISCH_TAC THEN
      REWRITE_TAC[ARITH_RULE `(c0 + r) + r' = c0 + (r + r'):num`] THEN
      ASM_CASES_TAC `r + r' = dd:num` THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
        can (find_term (fun t -> t = `r2:num`)) (concl th) &&
        can (find_term (fun t -> t = `UNIONS (lm:(real^3->bool)->bool)`)) (concl th))) THEN
      MAP_EVERY UNDISCH_TAC [`(r':num) <= dd - r`; `~(r + r' = dd:num)`; `~(r < (r2:num))`;
                             `~(r:num = r2)`; `r < (dd:num)`; `(r1:num) + 2 <= r2`] THEN
      ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. k <= dd /\ ~((U:num->real^3) k IN UNIONS lm) ==> U k IN S1`
  (LABEL_TAC "allk") THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?r. r < dd /\ (U:num->real^3) k = U(c0 + r)` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `?k'. k' < dd /\ (U:num->real^3) k = U k'` STRIP_ASSUME_TAC THENL
       [ASM_CASES_TAC `k = dd:num` THENL
         [EXISTS_TAC `0` THEN CONJ_TAC THENL
           [UNDISCH_TAC `3 <= (dd:num)` THEN ARITH_TAC; ALL_TAC] THEN
          FIRST_X_ASSUM SUBST_ALL_TAC THEN
          FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th -> concl th = `!i. (U:num->real^3)(i + dd) = U i`)) THEN
          REWRITE_TAC[ADD_CLAUSES];
          EXISTS_TAC `k:num` THEN REWRITE_TAC[] THEN
          UNDISCH_TAC `k <= (dd:num)` THEN UNDISCH_TAC `~(k = (dd:num))` THEN ARITH_TAC];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`dd:num`; `U:num->real^3`; `c0:num`; `k':num`] MOI_FAN_CYC_POS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `(U:num->real^3) k = U(c0 + r)`)) THEN
    USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THENL
     [UNDISCH_TAC `~((U:num->real^3)(c0 + r1) IN UNIONS lm)` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `~((U:num->real^3)(c0 + r2) IN UNIONS lm)` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < dd
        ==> convex hull {v0,y0,(U:num->real^3) i,U(SUC i)} DIFF UNIONS lm SUBSET S1`
  (LABEL_TAC "tet") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ABBREV_TAC `D = convex hull {v0,y0,(U:num->real^3) i,U(SUC i)}` THEN
    SUBGOAL_THEN `D IN barycentric_subdivision (barycentric_subdivision t) /\
                  aff_dim (D:real^3->bool) = &3` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "D" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `connected (D DIFF UNIONS lm:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN
      SUBGOAL_THEN `D DIFF UNIONS lm:real^3->bool = D DIFF (D INTER UNIONS lm)` SUBST1_TAC
      THENL [SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(D INTER UNIONS lm:real^3->bool) face_of D` MP_TAC THENL
       [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                       `barycentric_subdivision (lm:(real^3->bool)->bool)`; `D:real^3->bool`]
          MOI_FRN_FULL) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`D:real^3->bool`; `D INTER UNIONS lm:real^3->bool`] FACE_OF_STILLCONVEX) THEN
      ANTS_TAC THENL [EXPAND_TAC "D" THEN REWRITE_TAC[CONVEX_CONVEX_HULL]; ALL_TAC] THEN
      DISCH_THEN SUBST1_TAC THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((U:num->real^3) i IN UNIONS lm /\ U(SUC i) IN UNIONS lm)` ASSUME_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                     `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                     `{v0:real^3,y0,(U:num->real^3) i,U(SUC i)}`] MOI_FSP_HULL_FULL) THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      SUBGOAL_THEN `(v0:real^3) IN UNIONS lm /\ (y0:real^3) IN UNIONS lm` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `segment[v0:real^3,y0] SUBSET j1` THEN
        UNDISCH_TAC `UNIONS la INTER UNIONS lm = j1 UNION (j2:real^3->bool)` THEN
        MP_TAC(ISPECL [`v0:real^3`; `y0:real^3`] ENDS_IN_SEGMENT) THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (lm:(real^3->bool)->bool))`;
                     `D:real^3->bool`] MOI_FSB_DIM) THEN
      ASM_SIMP_TAC[MOI_S8TA_CM_CMB] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `?u:real^3. u IN D /\ ~(u IN UNIONS lm) /\ u IN S1` STRIP_ASSUME_TAC THENL
     [ASM_CASES_TAC `(U:num->real^3) i IN UNIONS lm` THENL
       [EXISTS_TAC `(U:num->real^3)(SUC i)` THEN
        SUBGOAL_THEN `~((U:num->real^3)(SUC i) IN UNIONS lm)` ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [EXPAND_TAC "D" THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
          USE_THEN "allk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `i < (dd:num)` THEN ARITH_TAC];
        EXISTS_TAC `(U:num->real^3) i` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [EXPAND_TAC "D" THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
          USE_THEN "allk" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `i < (dd:num)` THEN ARITH_TAC]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`D DIFF UNIONS lm:real^3->bool`; `S1:real^3->bool`; `fa1:real^3->bool`]
      MOI_FAN_CONN_OPEN_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(mc1:real^3->bool) SUBSET UNIONS lm` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (S1:real^3->bool) fa1` THEN UNDISCH_TAC `(u:real^3) IN S1` THEN
    UNDISCH_TAC `(u:real^3) IN D` THEN UNDISCH_TAC `~((u:real^3) IN UNIONS lm)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < dd
        ==> convex hull {v0,y0,(U:num->real^3) i,U(SUC i)} INTER UNIONS lm SUBSET mc1`
  (LABEL_TAC "tetm") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    ABBREV_TAC `D = convex hull {v0,y0,(U:num->real^3) i,U(SUC i)}` THEN
    SUBGOAL_THEN `(D:real^3->bool) IN barycentric_subdivision (barycentric_subdivision t)`
    ASSUME_TAC THENL
     [EXPAND_TAC "D" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(D INTER UNIONS lm:real^3->bool) face_of D` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                     `barycentric_subdivision (lm:(real^3->bool)->bool)`; `D:real^3->bool`]
        MOI_FRN_FULL) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(v0:real^3) IN D` ASSUME_TAC THENL
     [EXPAND_TAC "D" THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    SUBGOAL_THEN `(v0:real^3) IN mc1` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`v0:real^3`; `y0:real^3`] ENDS_IN_SEGMENT) THEN
      UNDISCH_TAC `segment[v0:real^3,y0] SUBSET j1` THEN
      UNDISCH_TAC `(j1:real^3->bool) SUBSET mc1` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `UNIONS lm:real^3->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC FACE_OF_IMP_CONVEX THEN
      EXISTS_TAC `D:real^3->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(mc1:real^3->bool) SUBSET UNIONS lm` THEN
      UNDISCH_TAC `(v0:real^3) IN D` THEN UNDISCH_TAC `(v0:real^3) IN mc1` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN barycentric_subdivision (barycentric_subdivision t) /\
        segment[v0,y0] SUBSET s
        ==> ?i. i < dd /\ s SUBSET convex hull {v0,y0,(U:num->real^3) i,U(SUC i)}`
  (LABEL_TAC "star") THENL
   [X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `s = segment[v0:real^3,y0]` THENL
     [EXISTS_TAC `0` THEN CONJ_TAC THENL
       [UNDISCH_TAC `3 <= (dd:num)` THEN ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[v0:real^3,y0] face_of s /\ convex(s:real^3->bool)` STRIP_ASSUME_TAC
    THENL
     [UNDISCH_TAC `lf_simplicial_complex
        (barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool)))` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `s:real^3->bool` (CONJUNCT1 th)) THEN
        MP_TAC(SPECL [`segment[v0:real^3,y0]`; `s:real^3->bool`]
          (CONJUNCT1(CONJUNCT2(CONJUNCT2 th))))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `segment[v0:real^3,y0] INTER s = segment[v0,y0]` SUBST1_TAC THENL
       [UNDISCH_TAC `segment[v0:real^3,y0] SUBSET s` THEN SET_TAC[]; ALL_TAC] THEN
      SIMP_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    SUBGOAL_THEN `&1 < aff_dim(s:real^3->bool)` ASSUME_TAC THENL
     [SUBGOAL_THEN `aff_dim(segment[v0:real^3,y0]) < aff_dim(s:real^3->bool)` MP_TAC THENL
       [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(s:real^3->bool) = &2 \/ aff_dim s = &3` MP_TAC THENL
     [MP_TAC(ISPEC `s:real^3->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_3] THEN
      UNDISCH_TAC `&1 < aff_dim(s:real^3->bool)` THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [MP_TAC(SPEC `s:real^3->bool` (ASSUME
        `!r. r IN barycentric_subdivision (barycentric_subdivision t) /\ aff_dim r = &2 /\
             segment[v0,y0] SUBSET r
             ==> ?i. i < dd /\ r = convex hull {v0, y0, (U:num->real^3) i}`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
      MP_TAC(SPEC `s:real^3->bool` (ASSUME
        `!r. r IN barycentric_subdivision (barycentric_subdivision t) /\ aff_dim r = &3 /\
             segment[v0,y0] SUBSET r
             ==> ?i. i < dd /\ r = convex hull {v0, y0, (U:num->real^3) i, U(SUC i)}`)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[SUBSET_REFL]];
    ALL_TAC] THEN
  ABBREV_TAC `ym = midpoint(v0:real^3,y0)` THEN
  SUBGOAL_THEN `(ym:real^3) IN segment[v0,y0]` ASSUME_TAC THENL
   [EXPAND_TAC "ym" THEN REWRITE_TAC[MIDPOINT_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(ym:real^3) IN relative_interior(segment[v0,y0])` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN EXPAND_TAC "ym" THEN
    REWRITE_TAC[MIDPOINT_IN_SEGMENT] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ym:real^3) IN j1` ASSUME_TAC THENL
   [UNDISCH_TAC `segment[v0:real^3,y0] SUBSET j1` THEN
    UNDISCH_TAC `(ym:real^3) IN segment[v0,y0]` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ym:real^3) IN interior(UNIONS t)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`]
      MOI_FTA_GRAPH_IN_NBHD) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MP_TAC(ISPEC `t:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
    SUBGOAL_THEN `(ym:real^3) IN UNIONS la` ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS la INTER UNIONS lm = j1 UNION (j2:real^3->bool)` THEN
      UNDISCH_TAC `(ym:real^3) IN j1` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `UNIONS la SUBSET derived_nbhd t (la:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `derived_nbhd t la SUBSET UNIONS (t:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `DISJOINT (derived_nbhd t la) (complex_boundary (t:(real^3->bool)->bool))` THEN
    UNDISCH_TAC `complex_boundary t = UNIONS t DIFF interior (UNIONS (t:(real^3->bool)->bool))` THEN
    UNDISCH_TAC `(ym:real^3) IN UNIONS la` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))`;
                 `segment[v0:real^3,y0]`; `ym:real^3`] MOI_FAN_STAR_BALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(ym:real^3) IN closure fa1` MP_TAC THENL
   [SUBGOAL_THEN `(ym:real^3) IN mc1` MP_TAC THENL
     [UNDISCH_TAC `(j1:real^3->bool) SUBSET mc1` THEN UNDISCH_TAC `(ym:real^3) IN j1` THEN
      SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `frontier fa1 = (mc1:real^3->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[frontier; IN_DIFF] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `d:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?i. i < dd /\ (z:real^3) IN convex hull {v0,y0,(U:num->real^3) i,U(SUC i)}`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `(z:real^3) IN UNIONS {s | s IN barycentric_subdivision (barycentric_subdivision t) /\
                                segment[v0,y0] SUBSET s}`
    MP_TAC THENL
     [UNDISCH_TAC `ball(ym:real^3,d) SUBSET
        UNIONS {s | s IN barycentric_subdivision (barycentric_subdivision t) /\
                    segment[v0,y0] SUBSET s}` THEN
      MATCH_MP_TAC(SET_RULE `(z:real^3) IN b ==> b SUBSET u ==> z IN u`) THEN
      REWRITE_TAC[IN_BALL] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "star" (MP_TAC o SPEC `s:real^3->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `s SUBSET convex hull {v0,y0,(U:num->real^3) i,U(SUC i)}` THEN
    UNDISCH_TAC `(z:real^3) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^3) IN UNIONS lm` THENL
   [USE_THEN "tetm" (MP_TAC o C MATCH_MP (ASSUME `i < (dd:num)`) o SPEC `i:num`) THEN
    UNDISCH_TAC `DISJOINT (fa1:real^3->bool) mc1` THEN
    UNDISCH_TAC `(z:real^3) IN fa1` THEN
    UNDISCH_TAC `(z:real^3) IN UNIONS lm` THEN
    UNDISCH_TAC `(z:real^3) IN convex hull {v0,y0,(U:num->real^3) i,U(SUC i)}` THEN
    SET_TAC[];
    USE_THEN "tet" (MP_TAC o C MATCH_MP (ASSUME `i < (dd:num)`) o SPEC `i:num`) THEN
    UNDISCH_TAC `DISJOINT (S1:real^3->bool) fa1` THEN
    UNDISCH_TAC `(z:real^3) IN fa1` THEN
    UNDISCH_TAC `~((z:real^3) IN UNIONS lm)` THEN
    UNDISCH_TAC `(z:real^3) IN convex hull {v0,y0,(U:num->real^3) i,U(SUC i)}` THEN
    SET_TAC[]]);;

(* ========================================================================= *)
(* Step D, the rim witnesses and the reach of the pieces: half-open cycle    *)
(* edges, the far vertices of the rim triangle, the paths Z1, Z2 in B and Z0 *)
(* in Cc, the ends they reach (MOI_FSN_SIDE_2D_GEN), the transport of the    *)
(* B-pieces to the other rim, and step D3 (every piece of each side surface  *)
(* meets the ends, since the frontier is connected).                         *)
(* ========================================================================= *)

(* A half-open edge of the cycle around an edge on the annulus: an edge    *)
(* [U i, U(SUC i)] of the cycle with both ends off the annulus lies in the *)
(* frontier, and with the end in M removed it misses M.                    *)

let MOI_FAN_HALF_SEG = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 v0 y0 (U:num->real^3) i.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\ v0 IN UNIONS la /\
     (!i. segment[U i,U(SUC i)] IN barycentric_subdivision (barycentric_subdivision t) /\
          convex hull {v0,y0,U i,U(SUC i)} IN
            barycentric_subdivision (barycentric_subdivision t) /\
          segment[U i,U(SUC i)] SUBSET convex hull {v0,y0,U i,U(SUC i)} /\
          ~(U i = U(SUC i))) /\
     ~(U i IN UNIONS la) /\ ~(U(SUC i) IN UNIONS la)
     ==> (~(U i IN UNIONS lm)
          ==> connected(segment[U i,U(SUC i)] DELETE U(SUC i)) /\
              segment[U i,U(SUC i)] DELETE U(SUC i) SUBSET
                derived_frontier t la DIFF UNIONS lm /\
              U i IN segment[U i,U(SUC i)] DELETE U(SUC i) /\
              U(SUC i) IN closure(segment[U i,U(SUC i)] DELETE U(SUC i))) /\
         (~(U(SUC i) IN UNIONS lm)
          ==> connected(segment[U i,U(SUC i)] DELETE U i) /\
              segment[U i,U(SUC i)] DELETE U i SUBSET
                derived_frontier t la DIFF UNIONS lm /\
              U(SUC i) IN segment[U i,U(SUC i)] DELETE U i /\
              U i IN closure(segment[U i,U(SUC i)] DELETE U i))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th)) STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) &&
    can (find_term (fun t -> t = `y0:real^3`)) (concl th))) THEN
  SUBGOAL_THEN `lf_simplicial_complex (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `segment[(U:num->real^3) i,U(SUC i)] INTER UNIONS la = {}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                   `barycentric_subdivision (la:(real^3->bool)->bool)`;
                   `(U:num->real^3) i`; `(U:num->real^3)(SUC i)`] MOI_FSP_SEG_FULL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[(U:num->real^3) i,U(SUC i)] SUBSET derived_frontier t la`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSP_NC_FR THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
    EXISTS_TAC `convex hull {v0:real^3,y0,U(i:num),U(SUC i)}` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `v0:real^3` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN SET_TAC[];
      MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
      EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                 `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                 `(U:num->real^3) i`; `(U:num->real^3)(SUC i)`] MOI_FSP_SEG_FULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(U:num->real^3) i IN segment[U i,U(SUC i)] /\ U(SUC i) IN segment[U i,U(SUC i)]`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^3)(SUC i) IN closure(segment(U i,U(SUC i))) /\
                U i IN closure(segment(U i,U(SUC i)))` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CLOSURE_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `segment((U:num->real^3) i,U(SUC i)) SUBSET segment[U i,U(SUC i)] DELETE U(SUC i) /\
                segment((U:num->real^3) i,U(SUC i)) SUBSET segment[U i,U(SUC i)] DELETE U i`
  STRIP_ASSUME_TAC THENL [REWRITE_TAC[open_segment] THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_SEMIOPEN_SEGMENT] THEN CONJ_TAC THEN DISCH_TAC THENL
   [SUBGOAL_THEN `segment[(U:num->real^3) i,U(SUC i)] INTER UNIONS lm SUBSET {U(SUC i)}`
    ASSUME_TAC THENL
     [ASM_CASES_TAC `(U:num->real^3)(SUC i) IN UNIONS lm` THEN
      ASM_SIMP_TAC[SUBSET_REFL; EMPTY_SUBSET];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `segment[(U:num->real^3) i,U(SUC i)] SUBSET derived_frontier t la` THEN
      UNDISCH_TAC `segment[(U:num->real^3) i,U(SUC i)] INTER UNIONS lm SUBSET {U(SUC i)}` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[IN_DELETE];
      MATCH_MP_TAC(SET_RULE `!(x:real^3) a b. x IN a /\ a SUBSET b ==> x IN b`) THEN
      EXISTS_TAC `closure(segment((U:num->real^3) i,U(SUC i)))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]];
    SUBGOAL_THEN `segment[(U:num->real^3) i,U(SUC i)] INTER UNIONS lm SUBSET {U i}`
    ASSUME_TAC THENL
     [ASM_CASES_TAC `(U:num->real^3) i IN UNIONS lm` THEN
      ASM_SIMP_TAC[SUBSET_REFL; EMPTY_SUBSET];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `segment[(U:num->real^3) i,U(SUC i)] SUBSET derived_frontier t la` THEN
      UNDISCH_TAC `segment[(U:num->real^3) i,U(SUC i)] INTER UNIONS lm SUBSET {U i}` THEN
      SET_TAC[];
      ASM_REWRITE_TAC[IN_DELETE];
      MATCH_MP_TAC(SET_RULE `!(x:real^3) a b. x IN a /\ a SUBSET b ==> x IN b`) THEN
      EXISTS_TAC `closure(segment((U:num->real^3) i,U(SUC i)))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]]]);;

(* The far vertices of the rim triangle conv{v0,y0,U c0} are the two cycle *)
(* neighbours U(c0 + 1) and U(c0 + dd - 1) of U c0.                         *)

let MOI_FAN_RIM_W = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 v0 y0 dd (U:num->real^3) c0 r1 r2.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     moi_fan_rimdata t la lm j1 v0 y0 dd U c0 r1 r2
     ==> convex hull {v0,y0,U c0} IN barycentric_subdivision (barycentric_subdivision la) /\
         aff_dim(convex hull {v0,y0,U c0}) = &2 /\
         moi_fan_w t la (convex hull {v0,y0,U c0}) = {U(c0 + 1), U(c0 + dd - 1)}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th))
    (STRIP_ASSUME_TAC o REWRITE_RULE[moi_fan_rimdata])) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(v0:real^3) IN UNIONS la /\ (y0:real^3) IN UNIONS la` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v0:real^3`; `y0:real^3`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `segment[v0:real^3,y0] SUBSET j1` THEN
    UNDISCH_TAC `UNIONS la INTER UNIONS lm = j1 UNION (j2:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `0 < 1 /\ 1 < (dd:num) /\ 0 < dd - 1 /\ dd - 1 < dd` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `3 <= (dd:num)` THEN ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY; moi_fan_w; IN_ELIM_THM] THEN
  X_GEN_TAC `w:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `d:real^3->bool` STRIP_ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))`;
                   `v0:real^3`; `y0:real^3`; `dd:num`; `U:num->real^3`; `c0:num`; `w:real^3`;
                   `d:real^3->bool`] MOI_FAN_FAN_W) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `~((w:real^3) IN UNIONS la)` THEN ASM_REWRITE_TAC[];
      SIMP_TAC[]];
    DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ASSUME `!r. 0 < r /\ r < dd ==> ~((U:num->real^3)(c0 + r) IN UNIONS la)`) THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `convex hull {v0,y0,(U:num->real^3) c0,U(SUC c0)}` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM ADD1] THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(ASSUME `!r. 0 < r /\ r < dd ==> ~((U:num->real^3)(c0 + r) IN UNIONS la)`) THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `convex hull {v0,y0,(U:num->real^3)(c0 + dd - 1),U(SUC(c0 + dd - 1))}` THEN
        ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [SUBGOAL_THEN `(U:num->real^3) c0 = U(SUC(c0 + dd - 1))` SUBST1_TAC THENL
           [SUBGOAL_THEN `SUC(c0 + dd - 1) = c0 + dd` SUBST1_TAC THENL
             [UNDISCH_TAC `3 <= (dd:num)` THEN ARITH_TAC; ALL_TAC] THEN
            ASM_REWRITE_TAC[];
            ASM_REWRITE_TAC[]];
          MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]]]]]);;

(* The rim witness paths.  Z1 runs along the cycle from U(c0 + 1) to the    *)
(* first triangle of M at U(c0 + r1), Z2 from U(c0 + dd - 1) back to the    *)
(* second one at U(c0 + r2); both lie in B.  Z0 runs between the two        *)
(* triangles of M on the other side and lies in Cc (MOI_FAN_RIM_CROSS).     *)

let MOI_FAN_RIMZ_TAC =
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_FAN_RIM_CROSS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_RIM_W) THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 (fun th -> ASSUME_TAC th THEN
      STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th))
    (STRIP_ASSUME_TAC o REWRITE_RULE[moi_fan_rimdata])) THEN
  SUBGOAL_THEN `(v0:real^3) IN UNIONS la` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v0:real^3`; `y0:real^3`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `segment[v0:real^3,y0] SUBSET j1` THEN
    UNDISCH_TAC `UNIONS la INTER UNIONS lm = j1 UNION (j2:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. segment[(U:num->real^3) i,U(SUC i)] IN
          barycentric_subdivision (barycentric_subdivision t) /\
        convex hull {v0,y0,U i,U(SUC i)} IN
          barycentric_subdivision (barycentric_subdivision t) /\
        segment[U i,U(SUC i)] SUBSET convex hull {v0,y0,U i,U(SUC i)} /\
        ~(U i = U(SUC i))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^3)(c0 + 1) IN moi_fan_bside t la lm j1 j2 /\
                U(c0 + dd - 1) IN moi_fan_bside t la lm j1 j2` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                   `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                   `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                   `convex hull {v0,y0,(U:num->real^3) c0}`] MOI_FAN_W_IN_B) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN SIMP_TAC[];
    ALL_TAC];;

let MOI_FAN_RIM_Z1 = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 v0 y0 dd (U:num->real^3) c0 r1 r2.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     moi_fan_rimdata t la lm j1 v0 y0 dd U c0 r1 r2
     ==> ?z1. connected z1 /\ z1 SUBSET moi_fan_bside t la lm j1 j2 /\ U(c0 + 1) IN z1 /\
              U(c0 + r1) IN closure z1`,
  MOI_FAN_RIMZ_TAC THEN
  SUBGOAL_THEN `!r. r <= r1 - 2 ==> ~((U:num->real^3)((c0 + 1) + r) IN UNIONS la) /\
                                    ~(U((c0 + 1) + r) IN UNIONS lm)` (LABEL_TAC "v1") THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(c0 + 1) + r = c0 + (r + 1)` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ASSUME `!r. 0 < r /\ r < dd ==> ~((U:num->real^3)(c0 + r) IN UNIONS la)`);
      MATCH_MP_TAC(ASSUME `!r. r < dd /\ ~(r = r1) /\ ~(r = r2)
                               ==> ~((U:num->real^3)(c0 + r) IN UNIONS lm)`)] THEN
    MAP_EVERY UNDISCH_TAC [`r <= (r1:num) - 2`; `2 <= (r1:num)`; `(r1:num) + 2 <= r2`;
                           `(r2:num) + 2 <= dd`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?P. connected P /\ P SUBSET derived_frontier t la DIFF UNIONS lm /\
                    (U:num->real^3)(c0 + 1) IN P /\ U((c0 + 1) + (r1 - 2)) IN P`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                   `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                   `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                   `v0:real^3`; `y0:real^3`; `U:num->real^3`; `(c0:num) + 1`; `(r1:num) - 2`]
      MOI_FAN_ARC_PATH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `SUC((c0 + 1) + (r1 - 2)) = c0 + r1` ASSUME_TAC THENL
   [UNDISCH_TAC `2 <= (r1:num)` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((U:num->real^3)(c0 + r1) IN UNIONS la)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ASSUME `!r. 0 < r /\ r < dd ==> ~((U:num->real^3)(c0 + r) IN UNIONS la)`) THEN
    MAP_EVERY UNDISCH_TAC [`2 <= (r1:num)`; `(r1:num) + 2 <= r2`; `(r2:num) + 2 <= dd`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "v1" (MP_TAC o SPEC `(r1:num) - 2`) THEN REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                 `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                 `v0:real^3`; `y0:real^3`; `U:num->real^3`; `((c0:num) + 1) + (r1 - 2)`]
    MOI_FAN_HALF_SEG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `H = segment[(U:num->real^3)((c0 + 1) + (r1 - 2)),U(c0 + r1)] DELETE U(c0 + r1)` THEN
  EXISTS_TAC `P UNION H:real^3->bool` THEN
  SUBGOAL_THEN `connected (P UNION H:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(U:num->real^3)((c0 + 1) + (r1 - 2))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `P UNION H SUBSET derived_frontier t la DIFF UNIONS (lm:(real^3->bool)->bool)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[UNION_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNION] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                   `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                   `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                   `P UNION H:real^3->bool`] MOI_FAN_B_CLOPEN) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(U:num->real^3)(c0 + 1)` THEN ASM_REWRITE_TAC[IN_UNION];
    MATCH_MP_TAC(SET_RULE `!(x:real^3) a b. x IN a /\ a SUBSET b ==> x IN b`) THEN
    EXISTS_TAC `closure(H:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[]]);;

let MOI_FAN_RIM_Z2 = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 v0 y0 dd (U:num->real^3) c0 r1 r2.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     moi_fan_rimdata t la lm j1 v0 y0 dd U c0 r1 r2
     ==> ?z2. connected z2 /\ z2 SUBSET moi_fan_bside t la lm j1 j2 /\ U(c0 + dd - 1) IN z2 /\
              U(c0 + r2) IN closure z2`,
  MOI_FAN_RIMZ_TAC THEN
  SUBGOAL_THEN `!r. r <= dd - r2 - 2 ==> ~((U:num->real^3)(SUC(c0 + r2) + r) IN UNIONS la) /\
                                         ~(U(SUC(c0 + r2) + r) IN UNIONS lm)` (LABEL_TAC "v2")
  THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `SUC(c0 + r2) + r = c0 + (r2 + 1 + r)` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ASSUME `!r. 0 < r /\ r < dd ==> ~((U:num->real^3)(c0 + r) IN UNIONS la)`);
      MATCH_MP_TAC(ASSUME `!r. r < dd /\ ~(r = r1) /\ ~(r = r2)
                               ==> ~((U:num->real^3)(c0 + r) IN UNIONS lm)`)] THEN
    MAP_EVERY UNDISCH_TAC [`r <= dd - (r2:num) - 2`; `2 <= (r1:num)`; `(r1:num) + 2 <= r2`;
                           `(r2:num) + 2 <= dd`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?P. connected P /\ P SUBSET derived_frontier t la DIFF UNIONS lm /\
                    (U:num->real^3)(SUC(c0 + r2)) IN P /\ U(c0 + dd - 1) IN P`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                   `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                   `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                   `v0:real^3`; `y0:real^3`; `U:num->real^3`; `SUC((c0:num) + r2)`;
                   `dd - (r2:num) - 2`] MOI_FAN_ARC_PATH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `SUC((c0:num) + r2) + (dd - r2 - 2) = c0 + dd - 1` SUBST1_TAC THENL
     [UNDISCH_TAC `(r2:num) + 2 <= dd` THEN ARITH_TAC; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((U:num->real^3)(c0 + r2) IN UNIONS la) /\ ~(U(SUC(c0 + r2)) IN UNIONS la) /\
                ~(U(SUC(c0 + r2)) IN UNIONS lm)` STRIP_ASSUME_TAC THENL
   [USE_THEN "v2" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_0; ADD_CLAUSES] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(ASSUME `!r. 0 < r /\ r < dd ==> ~((U:num->real^3)(c0 + r) IN UNIONS la)`) THEN
    MAP_EVERY UNDISCH_TAC [`2 <= (r1:num)`; `(r1:num) + 2 <= r2`; `(r2:num) + 2 <= dd`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                 `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                 `v0:real^3`; `y0:real^3`; `U:num->real^3`; `(c0:num) + r2`]
    MOI_FAN_HALF_SEG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `H = segment[(U:num->real^3)(c0 + r2),U(SUC(c0 + r2))] DELETE U(c0 + r2)` THEN
  EXISTS_TAC `H UNION P:real^3->bool` THEN
  SUBGOAL_THEN `connected (H UNION P:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(U:num->real^3)(SUC(c0 + r2))` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `H UNION P SUBSET derived_frontier t la DIFF UNIONS (lm:(real^3->bool)->bool)`
  ASSUME_TAC THENL [ASM_REWRITE_TAC[UNION_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_UNION] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                   `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                   `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                   `H UNION P:real^3->bool`] MOI_FAN_B_CLOPEN) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(U:num->real^3)(c0 + dd - 1)` THEN ASM_REWRITE_TAC[IN_UNION];
    MATCH_MP_TAC(SET_RULE `!(x:real^3) a b. x IN a /\ a SUBSET b ==> x IN b`) THEN
    EXISTS_TAC `closure(H:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[]]);;

let MOI_FAN_RIM_Z0 = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 v0 y0 dd (U:num->real^3) c0 r1 r2.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     moi_fan_rimdata t la lm j1 v0 y0 dd U c0 r1 r2
     ==> ?z0. connected z0 /\ z0 SUBSET moi_fan_cside t la lm j1 j2 /\
              U(c0 + r1) IN closure z0 /\ U(c0 + r2) IN closure z0`,
  MOI_FAN_RIMZ_TAC THEN
  SUBGOAL_THEN `!r. r <= r2 - r1 - 2 ==> ~((U:num->real^3)(SUC(c0 + r1) + r) IN UNIONS la) /\
                                         ~(U(SUC(c0 + r1) + r) IN UNIONS lm)` (LABEL_TAC "v3")
  THENL
   [X_GEN_TAC `r:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `SUC(c0 + r1) + r = c0 + (r1 + 1 + r)` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(ASSUME `!r. 0 < r /\ r < dd ==> ~((U:num->real^3)(c0 + r) IN UNIONS la)`);
      MATCH_MP_TAC(ASSUME `!r. r < dd /\ ~(r = r1) /\ ~(r = r2)
                               ==> ~((U:num->real^3)(c0 + r) IN UNIONS lm)`)] THEN
    MAP_EVERY UNDISCH_TAC [`r <= (r2:num) - r1 - 2`; `2 <= (r1:num)`; `(r1:num) + 2 <= r2`;
                           `(r2:num) + 2 <= dd`] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?P. connected P /\ P SUBSET derived_frontier t la DIFF UNIONS lm /\
                    (U:num->real^3)(SUC(c0 + r1)) IN P /\ U(SUC(c0 + r1) + (r2 - r1 - 2)) IN P`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                   `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                   `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                   `v0:real^3`; `y0:real^3`; `U:num->real^3`; `SUC((c0:num) + r1)`;
                   `(r2:num) - r1 - 2`] MOI_FAN_ARC_PATH) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `SUC(SUC((c0:num) + r1) + (r2 - r1 - 2)) = c0 + r2` ASSUME_TAC THENL
   [UNDISCH_TAC `(r1:num) + 2 <= r2` THEN ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((U:num->real^3)(c0 + r1) IN UNIONS la) /\ ~(U(c0 + r2) IN UNIONS la)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(ASSUME `!r. 0 < r /\ r < dd ==> ~((U:num->real^3)(c0 + r) IN UNIONS la)`) THEN
    MAP_EVERY UNDISCH_TAC [`2 <= (r1:num)`; `(r1:num) + 2 <= r2`; `(r2:num) + 2 <= dd`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  USE_THEN "v3" (MP_TAC o SPEC `0`) THEN REWRITE_TAC[LE_0; ADD_CLAUSES] THEN STRIP_TAC THEN
  USE_THEN "v3" (MP_TAC o SPEC `(r2:num) - r1 - 2`) THEN REWRITE_TAC[LE_REFL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                 `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                 `v0:real^3`; `y0:real^3`; `U:num->real^3`; `(c0:num) + r1`]
    MOI_FAN_HALF_SEG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `H1 = segment[(U:num->real^3)(c0 + r1),U(SUC(c0 + r1))] DELETE U(c0 + r1)` THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                 `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                 `v0:real^3`; `y0:real^3`; `U:num->real^3`;
                 `SUC((c0:num) + r1) + (r2 - r1 - 2)`] MOI_FAN_HALF_SEG) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `H2 = segment[(U:num->real^3)(SUC(c0 + r1) + (r2 - r1 - 2)),U(c0 + r2)] DELETE
                   U(c0 + r2)` THEN
  ABBREV_TAC `Z = (H1 UNION P) UNION H2:real^3->bool` THEN
  SUBGOAL_THEN `connected (Z:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN MATCH_MP_TAC CONNECTED_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `(U:num->real^3)(SUC(c0 + r1))` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNION] THEN
      EXISTS_TAC `(U:num->real^3)(SUC(c0 + r1) + (r2 - r1 - 2))` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `Z SUBSET derived_frontier t la DIFF UNIONS (lm:(real^3->bool)->bool)`
  ASSUME_TAC THENL [EXPAND_TAC "Z" THEN ASM_REWRITE_TAC[UNION_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(Z:real^3->bool) INTER moi_fan_bside t la lm j1 j2 = {}` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                   `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                   `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                   `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                   `Z:real^3->bool`] MOI_FAN_B_CLOPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `(U:num->real^3)(SUC(c0 + r1)) IN moi_fan_bside t la lm j1 j2` MP_TAC THENL
     [UNDISCH_TAC `(Z:real^3->bool) SUBSET moi_fan_bside t la lm j1 j2` THEN
      MATCH_MP_TAC(SET_RULE `(x:real^3) IN z ==> z SUBSET b ==> x IN b`) THEN
      EXPAND_TAC "Z" THEN ASM_REWRITE_TAC[IN_UNION];
      ALL_TAC] THEN
    REWRITE_TAC[moi_fan_bside; IN_INTER] THEN
    SUBGOAL_THEN `SUC(c0 + r1) = c0 + r1 + 1` SUBST1_TAC THENL [ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `Z:real^3->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_fan_cside] THEN
    UNDISCH_TAC `Z SUBSET derived_frontier t la DIFF UNIONS (lm:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `(Z:real^3->bool) INTER moi_fan_bside t la lm j1 j2 = {}` THEN SET_TAC[];
    MATCH_MP_TAC(SET_RULE `!(x:real^3) a b. x IN a /\ a SUBSET b ==> x IN b`) THEN
    EXISTS_TAC `closure(H1:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN EXPAND_TAC "Z" THEN SET_TAC[];
    MATCH_MP_TAC(SET_RULE `!(x:real^3) a b. x IN a /\ a SUBSET b ==> x IN b`) THEN
    EXISTS_TAC `closure(H2:real^3->bool)` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_CLOSURE THEN EXPAND_TAC "Z" THEN SET_TAC[]]);;

(* The two triangles of M at the rim edge reach the two different ends of   *)
(* the trace annulus a1 (MOI_FSN_SIDE_2D_GEN).                               *)

let MOI_FAN_RIM_ENDS = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22 v0 y0 dd (U:num->real^3) c0 r1 r2.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
     moi_fan_rimdata t la lm j1 v0 y0 dd U c0 r1 r2
     ==> (U(c0 + r1) IN k11 /\ U(c0 + r2) IN k12) \/
         (U(c0 + r1) IN k12 /\ U(c0 + r2) IN k11)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (fun th -> STRIP_ASSUME_TAC(REWRITE_RULE[moi_fan_ctx] th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_T th) THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FAN_CTX_M th))
    (STRIP_ASSUME_TAC o REWRITE_RULE[moi_fan_rimdata])) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(v0:real^3) IN j1 /\ (y0:real^3) IN j1` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`v0:real^3`; `y0:real^3`] ENDS_IN_SEGMENT) THEN
    UNDISCH_TAC `segment[v0:real^3,y0] SUBSET j1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j1:real^3->bool) SUBSET UNIONS la /\ j1 SUBSET UNIONS lm` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS la INTER UNIONS lm = j1 UNION (j2:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v0:real^3) IN UNIONS lm /\ (y0:real^3) IN UNIONS lm /\ v0 IN UNIONS la`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(j1:real^3->bool) SUBSET UNIONS la` THEN
    UNDISCH_TAC `(j1:real^3->bool) SUBSET UNIONS lm` THEN
    UNDISCH_TAC `(v0:real^3) IN j1` THEN UNDISCH_TAC `(y0:real^3) IN j1` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((U:num->real^3)(c0 + r1) IN UNIONS la) /\ ~(U(c0 + r2) IN UNIONS la)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    MATCH_MP_TAC(ASSUME `!r. 0 < r /\ r < dd ==> ~((U:num->real^3)(c0 + r) IN UNIONS la)`) THEN
    MAP_EVERY UNDISCH_TAC [`2 <= (r1:num)`; `(r1:num) + 2 <= r2`; `(r2:num) + 2 <= dd`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  (* each triangle of M at the edge lies in a1, with its far vertex on the ends *)
  SUBGOAL_THEN
   `!k. (U:num->real^3) k IN UNIONS lm /\ ~(U k IN UNIONS la)
        ==> convex hull {v0,y0,U k} SUBSET a1 /\ U k IN k11 UNION k12`
  (LABEL_TAC "tri") THENL
   [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    SUBGOAL_THEN `convex hull {v0,y0,(U:num->real^3) k} IN barycentric_subdivision
                    (barycentric_subdivision (lm:(real^3->bool)->bool))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                     `barycentric_subdivision (lm:(real^3->bool)->bool)`;
                     `{v0:real^3,y0,(U:num->real^3) k}`] MOI_FSP_HULL_FULL) THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex hull {v0,y0,(U:num->real^3) k} SUBSET a1` ASSUME_TAC THENL
     [SUBST1_TAC(SYM(ASSUME `UNIONS (derived_nbhd_complex lm
        {s | s IN la INTER lm /\ s SUBSET j1}) = (a1:real^3->bool)`)) THEN
      MATCH_MP_TAC(SET_RULE `!(s:real^3->bool) f. s IN f ==> s SUBSET UNIONS f`) THEN
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
      EXISTS_TAC `convex hull {v0:real^3,y0,(U:num->real^3) k}` THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[FACE_OF_REFL; CONVEX_CONVEX_HULL] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `v0:real^3` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
      REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(U:num->real^3) k IN derived_frontier t la` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                     `{(U:num->real^3) k}`] MOI_FSP_NC_FR) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
          EXISTS_TAC `convex hull {v0:real^3,y0,(U:num->real^3) k,U(SUC k)}` THEN
          ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
           [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `v0:real^3` THEN
            ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN
            REWRITE_TAC[IN_INSERT];
            MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
            EXISTS_TAC `barycentric_subdivision (barycentric_subdivision
                          (t:(real^3->bool)->bool))` THEN
            ASM_REWRITE_TAC[SING_SUBSET] THEN
            MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN REWRITE_TAC[IN_INSERT]];
          UNDISCH_TAC `~((U:num->real^3) k IN UNIONS la)` THEN SET_TAC[]];
        REWRITE_TAC[SING_SUBSET]];
      ALL_TAC] THEN
    UNDISCH_TAC `(U:num->real^3) k IN derived_frontier t la` THEN
    UNDISCH_TAC `(U:num->real^3) k IN UNIONS lm` THEN
    UNDISCH_TAC `convex hull {v0,y0,(U:num->real^3) k} SUBSET a1` THEN
    MP_TAC(ISPECL [`convex:(real^3->bool)->bool`; `{v0:real^3,y0,(U:num->real^3) k}`]
      HULL_SUBSET) THEN
    MAP_EVERY UNDISCH_TAC
     [`derived_frontier t la INTER UNIONS lm = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
      `DISJOINT (a1:real^3->bool) a2`; `k21 UNION k22 SUBSET (a2:real^3->bool)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  USE_THEN "tri" (MP_TAC o SPEC `(c0:num) + r1`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  USE_THEN "tri" (MP_TAC o SPEC `(c0:num) + r2`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (j1:real^3->bool) /\ pl_sphere 1 (k11:real^3->bool) /\
                pl_sphere 1 (k12:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`UNIONS la:real^3->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
      MOI_S5C_ANN_END_SPHERES) THEN
    MP_TAC(ISPECL [`a1:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`]
      MOI_S5C_ANN_END_SPHERES) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?k:real^3->bool. &2 simplex k` (fun th -> REWRITE_TAC[th]) THENL
     [EXISTS_TAC `convex hull {vec 0:real^3, basis 1, basis 2}` THEN
      REWRITE_TAC[MOI_S5C_SIMPLEX2_R3];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(convex hull {v0,y0,(U:num->real^3)(c0 + r1)} = convex hull {v0,y0,U(c0 + r2)})`
  ASSUME_TAC THENL
   [DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
      `!i j. convex hull {v0, y0, (U:num->real^3) i} = convex hull {v0, y0, U j} ==> U i = U j`)) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`dd:num`; `U:num->real^3`; `c0:num`; `r1:num`; `r2:num`] MOI_FSP_WINDOW_INJ) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`2 <= (r1:num)`; `(r1:num) + 2 <= r2`; `(r2:num) + 2 <= dd`] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`;
                 `a1:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`; `j1:real^3->bool`;
                 `v0:real^3`; `y0:real^3`;
                 `(U:num->real^3)(c0 + r1)`; `(U:num->real^3)(c0 + r2)`] MOI_FSN_SIDE_2D_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_INTER] THEN
    UNDISCH_TAC `derived_nbhd t la INTER UNIONS lm = a1 UNION (a2:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(U:num->real^3)(c0 + r1) IN k11 UNION k12`; `(U:num->real^3)(c0 + r2) IN k11 UNION k12`] THEN
  SET_TAC[]);;

(* The rim-1 witnesses in normalised form: a triangle tau of ldT on the rim *)
(* with far vertices w1, w2, connected z1, z2 in B through w1, w2 whose     *)
(* closures meet k11 and k12, and a connected z0 in Cc whose closure meets  *)
(* both k11 and k12.                                                         *)

let MOI_FAN_RIM_WIT = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> ?tau w1 w2 z1 z2 z0.
           tau IN barycentric_subdivision (barycentric_subdivision la) /\ aff_dim tau = &2 /\
           moi_fan_w t la tau = {w1, w2} /\
           connected z1 /\ z1 SUBSET moi_fan_bside t la lm j1 j2 /\ w1 IN z1 /\
           ~(closure z1 INTER k11 = {}) /\
           connected z2 /\ z2 SUBSET moi_fan_bside t la lm j1 j2 /\ w2 IN z2 /\
           ~(closure z2 INTER k12 = {}) /\
           connected z0 /\ z0 SUBSET moi_fan_cside t la lm j1 j2 /\
           ~(closure z0 INTER k11 = {}) /\ ~(closure z0 INTER k12 = {})`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FAN_RIMDATA_EXISTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `v0:real^3` (X_CHOOSE_THEN `y0:real^3` (X_CHOOSE_THEN `dd:num`
    (X_CHOOSE_THEN `U:num->real^3` (X_CHOOSE_THEN `c0:num` (X_CHOOSE_THEN `r1:num`
    (X_CHOOSE_THEN `r2:num` ASSUME_TAC))))))) THEN
  SUBGOAL_THEN
   `moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22 /\
    moi_fan_rimdata t la lm j1 v0 y0 dd (U:num->real^3) c0 r1 r2` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_RIM_W) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Z1:real^3->bool` STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_RIM_Z1) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Z2:real^3->bool` STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_RIM_Z2) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `Z0:real^3->bool` STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_RIM_Z0) THEN
  FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_RIM_ENDS) THENL
   [MAP_EVERY EXISTS_TAC [`convex hull {v0,y0,(U:num->real^3) c0}`;
                          `(U:num->real^3)(c0 + 1)`; `(U:num->real^3)(c0 + dd - 1)`;
                          `Z1:real^3->bool`; `Z2:real^3->bool`; `Z0:real^3->bool`] THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN REPEAT CONJ_TAC THENL
     [EXISTS_TAC `(U:num->real^3)(c0 + r1)` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(U:num->real^3)(c0 + r2)` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(U:num->real^3)(c0 + r1)` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(U:num->real^3)(c0 + r2)` THEN ASM_REWRITE_TAC[]];
    MAP_EVERY EXISTS_TAC [`convex hull {v0,y0,(U:num->real^3) c0}`;
                          `(U:num->real^3)(c0 + dd - 1)`; `(U:num->real^3)(c0 + 1)`;
                          `Z2:real^3->bool`; `Z1:real^3->bool`; `Z0:real^3->bool`] THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[INSERT_AC];
      EXISTS_TAC `(U:num->real^3)(c0 + r2)` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(U:num->real^3)(c0 + r1)` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(U:num->real^3)(c0 + r2)` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `(U:num->real^3)(c0 + r1)` THEN ASM_REWRITE_TAC[]]]);;

(* The closure of the B-component of a point w of a connected set z inside  *)
(* B contains the closure of z.                                              *)

let MOI_FAN_CC_CLOSURE = prove
 (`!(b:real^3->bool) z w.
     connected z /\ z SUBSET b /\ w IN z
     ==> closure z SUBSET closure(connected_component b w)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]);;

(* A union of two components of B is closed under connectivity in B.       *)

let MOI_FAN_CC2_CLOSED = prove
 (`!(b:real^3->bool) a1 a2 x y g.
     x IN connected_component b a1 UNION connected_component b a2 /\
     connected g /\ g SUBSET b /\ x IN g /\ y IN g
     ==> y IN connected_component b a1 UNION connected_component b a2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [DISJ1_TAC; DISJ2_TAC] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CONNECTED_COMPONENT_EQ) THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `g:real^3->bool`; `x:real^3`]
    CONNECTED_COMPONENT_MAXIMAL) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* If w lies in one of the B-components of u1, u2, the closure of the      *)
(* B-component of w is a connected set in the closure of B meeting the end  *)
(* reached from w and one of the ends reached from u1, u2.                  *)

let MOI_FAN_REACH = prove
 (`!(b:real^3->bool) z w u1 u2 y1 y2 e e1 e2.
     connected z /\ z SUBSET b /\ w IN z /\ ~(closure z INTER e = {}) /\
     connected y1 /\ y1 SUBSET b /\ u1 IN y1 /\ ~(closure y1 INTER e1 = {}) /\
     connected y2 /\ y2 SUBSET b /\ u2 IN y2 /\ ~(closure y2 INTER e2 = {}) /\
     w IN connected_component b u1 UNION connected_component b u2
     ==> ?g. connected g /\ g SUBSET closure b /\ ~(g INTER e = {}) /\
             ~(g INTER (e1 UNION e2) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `closure(connected_component b (w:real^3))` THEN
  SIMP_TAC[CONNECTED_CLOSURE; CONNECTED_CONNECTED_COMPONENT] THEN
  SIMP_TAC[SUBSET_CLOSURE; CONNECTED_COMPONENT_SUBSET] THEN
  MP_TAC(ISPECL [`b:real^3->bool`; `z:real^3->bool`; `w:real^3`] MOI_FAN_CC_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `~(closure z INTER (e:real^3->bool) = {})` THEN
    UNDISCH_TAC `closure z SUBSET closure(connected_component b (w:real^3))` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(w:real^3) IN connected_component b u1 UNION connected_component b u2` THEN
  REWRITE_TAC[IN_UNION] THEN
  DISCH_THEN(DISJ_CASES_THEN (SUBST1_TAC o MATCH_MP CONNECTED_COMPONENT_EQ)) THENL
   [MP_TAC(ISPECL [`b:real^3->bool`; `y1:real^3->bool`; `u1:real^3`] MOI_FAN_CC_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(closure y1 INTER (e1:real^3->bool) = {})` THEN SET_TAC[];
    MP_TAC(ISPECL [`b:real^3->bool`; `y2:real^3->bool`; `u2:real^3`] MOI_FAN_CC_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(closure y2 INTER (e2:real^3->bool) = {})` THEN SET_TAC[]]);;

(* The B-pieces at k11 and at k12 reach the rim-2 ends: transport of the    *)
(* far vertices from a rim-2 triangle to the rim-1 triangle.                *)

let MOI_FAN_B_REACH = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> (?g. connected g /\ g SUBSET closure(moi_fan_bside t la lm j1 j2) /\
              ~(g INTER k11 = {}) /\ ~(g INTER (k21 UNION k22) = {})) /\
         (?g. connected g /\ g SUBSET closure(moi_fan_bside t la lm j1 j2) /\
              ~(g INTER k12 = {}) /\ ~(g INTER (k21 UNION k22) = {}))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `tau1:real^3->bool` (X_CHOOSE_THEN `w1:real^3`
    (X_CHOOSE_THEN `w2:real^3` (X_CHOOSE_THEN `z1:real^3->bool` (X_CHOOSE_THEN `z2:real^3->bool`
    (X_CHOOSE_THEN `z0:real^3->bool` STRIP_ASSUME_TAC))))) o MATCH_MP MOI_FAN_RIM_WIT) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FAN_RIM_WIT o MATCH_MP MOI_FAN_CTX_SYM) THEN
  REWRITE_TAC[ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                      `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
                MOI_FAN_BSIDE_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau2:real^3->bool` (X_CHOOSE_THEN `u1:real^3`
    (X_CHOOSE_THEN `u2:real^3` (X_CHOOSE_THEN `y1:real^3->bool` (X_CHOOSE_THEN `y2:real^3->bool`
    (X_CHOOSE_THEN `y0:real^3->bool` STRIP_ASSUME_TAC)))))) THEN
  ABBREV_TAC `B = moi_fan_bside t la lm j1 j2` THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                 `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                 `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                 `connected_component B (u1:real^3) UNION connected_component B u2`]
    MOI_FAN_TRANSPORT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FAN_CC2_CLOSED THEN
      MAP_EVERY EXISTS_TAC [`x:real^3`; `G:real^3->bool`] THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `tau2:real^3->bool` THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_UNION] THEN
      REWRITE_TAC[IN; CONNECTED_COMPONENT_REFL_EQ] THEN
      UNDISCH_TAC `(y1:real^3->bool) SUBSET B` THEN UNDISCH_TAC `(u1:real^3) IN y1` THEN
      UNDISCH_TAC `(y2:real^3->bool) SUBSET B` THEN UNDISCH_TAC `(u2:real^3) IN y2` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `tau1:real^3->bool`) THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN STRIP_TAC THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_FAN_REACH THENL
   [MAP_EVERY EXISTS_TAC [`z1:real^3->bool`; `w1:real^3`; `u1:real^3`; `u2:real^3`;
                          `y1:real^3->bool`; `y2:real^3->bool`];
    MAP_EVERY EXISTS_TAC [`z2:real^3->bool`; `w2:real^3`; `u1:real^3`; `u2:real^3`;
                          `y1:real^3->bool`; `y2:real^3->bool`]] THEN
  ASM_REWRITE_TAC[]);;

(* Step D3: every component of each side surface meets the end circles.    *)
(* A component of the polyhedron of a finite complex of compact connected  *)
(* cells is open in it; a component missing the ends of a relatively open  *)
(* side would be clopen in the connected frontier.                          *)

let MOI_FAN_COMP_OPEN_IN = prove
 (`!(c:(real^N->bool)->bool) k.
     FINITE c /\ (!s. s IN c ==> compact s /\ connected s) /\ k IN components (UNIONS c)
     ==> open_in (subtopology euclidean (UNIONS c)) k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `k = UNIONS c DIFF UNIONS {s:real^N->bool | s IN c /\ ~(s SUBSET k)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `k:real^N->bool`] IN_COMPONENTS_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
        UNDISCH_TAC `~((s:real^N->bool) SUBSET k)` THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC COMPONENTS_MAXIMAL THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
        ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THEN ASM SET_TAC[]];
      MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_DIFF THEN
  REWRITE_TAC[OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN; SUBSET_UNIV] THEN
  MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
   [SET_TAC[];
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    ASM_MESON_TAC[COMPACT_IMP_CLOSED]]);;

let MOI_FAN_NO_FREE_PIECE = prove
 (`!(f:real^N->bool) e u p.
     connected f /\ closed f /\ e SUBSET f /\ ~(e = {}) /\ open u /\
     closure(f INTER u) SUBSET (f INTER u) UNION e /\
     p IN components(closure(f INTER u)) /\
     open_in (subtopology euclidean (closure(f INTER u))) p
     ==> ~(p INTER e = {})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^N->bool) SUBSET f INTER u` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`closure(f INTER u):real^N->bool`; `p:real^N->bool`]
      IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_IN_OPEN] o check (fun th ->
    concl th = `open_in (subtopology euclidean (closure(f INTER u))) (p:real^N->bool)`)) THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N->bool` (STRIP_ASSUME_TAC o GSYM)) THEN
  SUBGOAL_THEN `open_in (subtopology euclidean f) (p:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `p = f INTER (u INTER u1:real^N->bool)` SUBST1_TAC THENL
     [MP_TAC(ISPEC `f INTER u:real^N->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_SIMP_TAC[OPEN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed_in (subtopology euclidean f) (p:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MP_TAC(ISPECL [`closure(f INTER u):real^N->bool`; `p:real^N->bool`]
        CLOSED_IN_COMPONENT) THEN
      ASM_SIMP_TAC[CLOSED_IN_CLOSED_EQ; CLOSED_CLOSURE]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `f:real^N->bool` CONNECTED_CLOPEN) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `p:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`closure(f INTER u):real^N->bool`; `p:real^N->bool`]
    IN_COMPONENTS_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Cells of a combinatorial manifold with boundary are compact and          *)
(* connected.                                                                *)

let MOI_FAN_CMB_CELLS = prove
 (`!(c:(real^N->bool)->bool) n.
     combinatorial_manifold_with_boundary n c
     ==> !s. s IN c ==> compact s /\ connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
  STRIP_TAC THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?m. m simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED]);;

(* A side f INTER u of the connected compact frontier f, relatively open,   *)
(* whose closure is a compact surface and adds only points of e: each of   *)
(* the components of its closure meets e.                                   *)

let MOI_FAN_SIDE_PIECES = prove
 (`!(f:real^3->bool) e u u' kb.
     connected f /\ compact f /\ e SUBSET f /\ ~(e = {}) /\ open u /\ open u' /\
     (f INTER u) UNION (f INTER u') UNION e = f /\ DISJOINT (f INTER u) (f INTER u') /\
     FINITE kb /\ combinatorial_manifold_with_boundary 2 kb /\
     UNIONS kb = closure(f INTER u)
     ==> !p. p IN components (closure(f INTER u)) ==> ~(p INTER e = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `p:real^3->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_FAN_NO_FREE_PIECE THEN
  MAP_EVERY EXISTS_TAC [`f:real^3->bool`; `u:real^3->bool`] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `closure(f INTER u) SUBSET (f:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED; INTER_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `u' INTER closure(f INTER u) = {}:real^3->bool` ASSUME_TAC THENL
     [ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[];
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `UNIONS kb = closure (f INTER u:real^3->bool)`)) THEN
    MATCH_MP_TAC MOI_FAN_COMP_OPEN_IN THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FAN_CMB_CELLS THEN EXISTS_TAC `2` THEN ASM_REWRITE_TAC[]]);;

(* The sides B and Cc are the traces on the frontier of open sets.          *)

let MOI_FAN_SIDES_OPEN_REP = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> ?ub uc. open ub /\ open uc /\
                 moi_fan_bside t la lm j1 j2 = derived_frontier t la INTER ub /\
                 moi_fan_cside t la lm j1 j2 = derived_frontier t la INTER uc`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_SIDES) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fan_ctx]) THEN STRIP_TAC THEN
  ABBREV_TAC `X = UNIONS la DIFF (j1 UNION j2:real^3->bool)` THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j1:real^3->bool`] MOI_FAN_MC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j2:real^3->bool`] MOI_FAN_MC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j1:real^3->bool`; `X:real^3->bool`]
    MOI_FAN_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (X:real^3->bool) (UNIONS lm)` THEN
    UNDISCH_TAC `moi_fan_mc lm j1 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `j2:real^3->bool`; `X:real^3->bool`]
    MOI_FAN_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (X:real^3->bool) (UNIONS lm)` THEN
    UNDISCH_TAC `moi_fan_mc lm j2 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN SET_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS lm:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `2`] MOI_FAN_CMB_CELLS) THEN
    ASM_SIMP_TAC[MOI_S8TA_CM_CMB];
    ALL_TAC] THEN
  EXISTS_TAC `(moi_fan_side lm j1 X INTER moi_fan_side lm j2 X) DIFF
              UNIONS (lm:(real^3->bool)->bool)` THEN
  EXISTS_TAC `(moi_fan_far lm j1 X UNION moi_fan_far lm j2 X) DIFF
              UNIONS (lm:(real^3->bool)->bool)` THEN
  ASM_SIMP_TAC[OPEN_DIFF; OPEN_INTER; OPEN_UNION] THEN
  REWRITE_TAC[moi_fan_cside; moi_fan_bside] THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `moi_fan_side lm j1 X UNION moi_fan_far lm j1 X =
               (:real^3) DIFF moi_fan_mc lm j1` THEN
  UNDISCH_TAC `moi_fan_side lm j2 X UNION moi_fan_far lm j2 X =
               (:real^3) DIFF moi_fan_mc lm j2` THEN
  UNDISCH_TAC `DISJOINT (moi_fan_side lm j1 X) (moi_fan_far lm j1 (X:real^3->bool))` THEN
  UNDISCH_TAC `DISJOINT (moi_fan_side lm j2 X) (moi_fan_far lm j2 (X:real^3->bool))` THEN
  UNDISCH_TAC `moi_fan_mc lm j1 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN
  UNDISCH_TAC `moi_fan_mc lm j2 SUBSET UNIONS (lm:(real^3->bool)->bool)` THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[]);;

(* Step D3: every component of closure B and of closure Cc meets the ends.  *)

let MOI_FAN_PIECES_MEET_ENDS = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> (!c. c IN components (closure(moi_fan_bside t la lm j1 j2))
              ==> ~(c INTER (k11 UNION k12 UNION k21 UNION k22) = {})) /\
         (!c. c IN components (closure(moi_fan_cside t la lm j1 j2))
              ==> ~(c INTER (k11 UNION k12 UNION k21 UNION k22) = {}))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_T) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_SIDE_SURFACES) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fan_ctx]) THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected (derived_frontier t (la:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FAN_FRONTIER_CONNECTED THEN
    MAP_EVERY EXISTS_TAC [`j1:real^3->bool`; `j2:real^3->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k11 UNION k12 UNION k21 UNION k22 = {}:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a1:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`]
      MOI_FCB_ANN_ENDS_FACTS) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fan_bside t la lm j1 j2 UNION moi_fan_cside t la lm j1 j2 UNION
      (k11 UNION k12 UNION k21 UNION k22) = derived_frontier t la /\
    moi_fan_cside t la lm j1 j2 UNION moi_fan_bside t la lm j1 j2 UNION
      (k11 UNION k12 UNION k21 UNION k22) = derived_frontier t la /\
    DISJOINT (moi_fan_bside t la lm j1 j2) (moi_fan_cside t la lm j1 j2) /\
    DISJOINT (moi_fan_cside t la lm j1 j2) (moi_fan_bside t la lm j1 j2) /\
    k11 UNION k12 UNION k21 UNION k22 SUBSET derived_frontier t la`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_fan_cside; moi_fan_bside] THEN
    UNDISCH_TAC `derived_frontier t la INTER UNIONS lm =
                 k11 UNION k12 UNION k21 UNION (k22:real^3->bool)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `ub:real^3->bool` (X_CHOOSE_THEN `uc:real^3->bool`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_FAN_SIDES_OPEN_REP) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th =
    `moi_fan_bside t la lm j1 j2 = derived_frontier t la INTER (ub:real^3->bool)`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th =
    `moi_fan_cside t la lm j1 j2 = derived_frontier t la INTER (uc:real^3->bool)`)) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOI_FAN_SIDE_PIECES THENL
   [MAP_EVERY EXISTS_TAC
     [`uc:real^3->bool`;
      `{q | q IN boundary_complex (derived_nbhd_complex t la) /\
            q SUBSET closure (derived_frontier t la INTER (ub:real^3->bool))}`];
    MAP_EVERY EXISTS_TAC
     [`ub:real^3->bool`;
      `{q | q IN boundary_complex (derived_nbhd_complex t la) /\
            q SUBSET closure (derived_frontier t la INTER (uc:real^3->bool))}`]] THEN
  ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* The statement MOI_FAN_FINAL_TERM, the final labelling of step E.          *)
(* ========================================================================= *)

let MOI_FAN_FINAL_TERM =
 `!(ff:real^3->bool) BB CC b1 b2 c1 c2 k11 k12 k21 k22 f3 f4 a2.
     ff = BB UNION CC /\ BB INTER CC = k11 UNION k12 UNION k21 UNION k22 /\
     BB = b1 UNION b2 /\ DISJOINT b1 b2 /\ CC = c1 UNION c2 /\ DISJOINT c1 c2 /\
     ((f3 = k21 /\ f4 = k22) \/ (f3 = k22 /\ f4 = k21)) /\
     pl_annulus_with_ends b1 k11 f3 /\ pl_annulus_with_ends b2 k12 f4 /\
     pl_annulus_with_ends c1 k11 k12 /\ pl_annulus_with_ends c2 k21 k22 /\
     pl_annulus_with_ends a2 k21 k22 /\
     DISJOINT k11 k12 /\ DISJOINT k11 k21 /\ DISJOINT k11 k22 /\
     DISJOINT k12 k21 /\ DISJOINT k12 k22 /\ DISJOINT k21 k22
     ==> ?b1' b2' c1' c2' k21' k22'.
           ((k21' = k21 /\ k22' = k22) \/ (k21' = k22 /\ k22' = k21)) /\
           pl_annulus_with_ends a2 k21' k22' /\
           ff = b1' UNION b2' UNION c1' UNION c2' /\
           pl_annulus_with_ends b1' k11 k21' /\ pl_annulus_with_ends b2' k12 k22' /\
           pl_annulus_with_ends c1' k11 k12 /\ pl_annulus_with_ends c2' k21' k22' /\
           DISJOINT b1' b2' /\ DISJOINT c1' c2' /\
           b1' INTER c1' = k11 /\ b1' INTER c2' = k21' /\
           b2' INTER c1' = k12 /\ b2' INTER c2' = k22'`;;

let moi_fan_iface3_ok =
  type_of MOI_FAN_FINAL_TERM = bool_ty && frees MOI_FAN_FINAL_TERM = [];;

if not moi_fan_iface3_ok then failwith "moi_fan_iface3_ok";;

(* ========================================================================= *)
(* MOI_FAN_FINAL, the final labelling.                                       *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* MOI_FAN_FINAL proves MOI_FAN_FINAL_TERM.  Uses MOI_S5C_ANN_ENDS_SUBSET    *)
(* and MOI_S5C_ANN_SWAP (pc_moi_s35_minc).  Route: the witnesses are b1, b2, *)
(* c1, c2 with k21' = f3 and k22' = f4; the ends of a2 and c2 are swapped by *)
(* MOI_S5C_ANN_SWAP when f3 = k22.  Each end lies in its annulus, b1 misses  *)
(* k12 and f4 (they lie in b2), c1 misses k21 and k22 (they lie in c2), and  *)
(* every b INTER c lies in BB INTER CC, the four end circles; this gives the *)
(* four intersections.                                                       *)
(* ------------------------------------------------------------------------- *)

let MOI_FAN_FINAL = prove
 (MOI_FAN_FINAL_TERM,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  (* a2 and c2 with the ends f3, f4 *)
  SUBGOAL_THEN `pl_annulus_with_ends (a2:real^3->bool) f3 f4 /\
                pl_annulus_with_ends (c2:real^3->bool) f3 f4 /\
                f3 UNION f4 = k21 UNION (k22:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (is_disj o concl)) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(MATCH_MP_TAC MOI_S5C_ANN_SWAP THEN ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the ends lie in their annuli *)
  MP_TAC(MATCH_MP MOI_S5C_ANN_ENDS_SUBSET
    (ASSUME `pl_annulus_with_ends (b1:real^3->bool) k11 f3`)) THEN
  MP_TAC(MATCH_MP MOI_S5C_ANN_ENDS_SUBSET
    (ASSUME `pl_annulus_with_ends (b2:real^3->bool) k12 f4`)) THEN
  MP_TAC(MATCH_MP MOI_S5C_ANN_ENDS_SUBSET
    (ASSUME `pl_annulus_with_ends (c1:real^3->bool) k11 k12`)) THEN
  MP_TAC(MATCH_MP MOI_S5C_ANN_ENDS_SUBSET
    (ASSUME `pl_annulus_with_ends (c2:real^3->bool) k21 k22`)) THEN
  REPEAT DISCH_TAC THEN
  MAP_EVERY EXISTS_TAC [`b1:real^3->bool`; `b2:real^3->bool`; `c1:real^3->bool`;
                        `c2:real^3->bool`; `f3:real^3->bool`; `f4:real^3->bool`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  MAP_EVERY UNDISCH_TAC
   [`ff = BB UNION (CC:real^3->bool)`;
    `BB INTER CC = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)`;
    `BB = b1 UNION (b2:real^3->bool)`; `CC = c1 UNION (c2:real^3->bool)`;
    `DISJOINT (b1:real^3->bool) b2`; `DISJOINT (c1:real^3->bool) c2`;
    `f3 UNION f4 = k21 UNION (k22:real^3->bool)`;
    `(k11:real^3->bool) SUBSET b1 /\ (f3:real^3->bool) SUBSET b1`;
    `(k12:real^3->bool) SUBSET b2 /\ (f4:real^3->bool) SUBSET b2`;
    `(k11:real^3->bool) SUBSET c1 /\ (k12:real^3->bool) SUBSET c1`;
    `(k21:real^3->bool) SUBSET c2 /\ (k22:real^3->bool) SUBSET c2`] THEN
  SET_TAC[]);;

(* ========================================================================= *)
(* Step E and ANNULUS_NBHD.  The Euler sum of the side surfaces (they cover  *)
(* K and meet in L, the complex of the end circles, of Euler number 0), the  *)
(* four end circles, the side surfaces as two pairs of annuli                *)
(* (MOI_FAN_COUNT), the frontier as the union of the closed sides, and       *)
(* ANNULUS_NBHD : |- MOI_FSN_ANNULUS_NBHD (labelling by MOI_FAN_FINAL).      *)
(* ========================================================================= *)

(* Step E, the Euler sum: the side surfaces KB and KC cover K and meet in   *)
(* L, the complex of the four end circles, whose Euler number is 0.         *)

(* A finite one-dimensional complex in which every vertex lies in exactly   *)
(* two edges has Euler number 0.                                            *)

let MOI_FAN_DEG2_EULER = prove
 (`!L:(real^N->bool)->bool.
     simplicial_complex L /\ (!s. s IN L ==> aff_dim s <= &1) /\
     (!v. {v} IN L ==> CARD {e | e IN L /\ aff_dim e = &1 /\ v IN e} = 2)
     ==> complex_euler L = &0`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_FSB_EULER_1DIM] THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN L}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `L:(real^N->bool)->bool` MOI_FSA_LK_HANDSHAKE) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `nsum {u:real^N | {u} IN L} (\u. CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e}) =
    nsum {u:real^N | {u} IN L} (\u. 2)` SUBST1_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN ASM_SIMP_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ASM_SIMP_TAC[NSUM_CONST] THEN
  REWRITE_TAC[REAL_ARITH `&a - &b = &0 <=> &a:real = &b`; REAL_OF_NUM_EQ] THEN ARITH_TAC);;

(* A closed convex set lies in the closure of its complement of a proper    *)
(* face.                                                                     *)

let MOI_FAN_FACE_DENSE = prove
 (`!(q:real^N->bool) f.
     convex q /\ closed q /\ f face_of q /\ ~(f = q) ==> q SUBSET closure(q DIFF f)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `closure(relative_interior q:real^N->bool)` THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED; SUBSET_REFL];
    MATCH_MP_TAC SUBSET_CLOSURE THEN
    MP_TAC(ISPEC `q:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPECL [`f:real^N->bool`; `q:real^N->bool`] FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* The closures of the sides add exactly the end circles.                    *)

let MOI_FAN_CLOSURE_SIDES = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> closure(moi_fan_bside t la lm j1 j2) SUBSET
           moi_fan_bside t la lm j1 j2 UNION (k11 UNION k12 UNION k21 UNION k22) /\
         closure(moi_fan_cside t la lm j1 j2) SUBSET
           moi_fan_cside t la lm j1 j2 UNION (k11 UNION k12 UNION k21 UNION k22) /\
         k11 UNION k12 UNION k21 UNION k22 SUBSET closure(moi_fan_bside t la lm j1 j2) /\
         k11 UNION k12 UNION k21 UNION k22 SUBSET closure(moi_fan_cside t la lm j1 j2)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_T) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_SIDE_SURFACES) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fan_ctx]) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_fan_bside t la lm j1 j2 UNION moi_fan_cside t la lm j1 j2 UNION
      (k11 UNION k12 UNION k21 UNION k22) = derived_frontier t la /\
    DISJOINT (moi_fan_bside t la lm j1 j2) (moi_fan_cside t la lm j1 j2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_fan_cside; moi_fan_bside] THEN
    UNDISCH_TAC `derived_frontier t la INTER UNIONS lm =
                 k11 UNION k12 UNION k21 UNION (k22:real^3->bool)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `ub:real^3->bool` (X_CHOOSE_THEN `uc:real^3->bool`
    STRIP_ASSUME_TAC) o MATCH_MP MOI_FAN_SIDES_OPEN_REP) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th =
    `moi_fan_bside t la lm j1 j2 = derived_frontier t la INTER (ub:real^3->bool)`)) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th =
    `moi_fan_cside t la lm j1 j2 = derived_frontier t la INTER (uc:real^3->bool)`)) THEN
  ABBREV_TAC `ff = derived_frontier t (la:(real^3->bool)->bool)` THEN
  ABBREV_TAC `ee = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)` THEN
  SUBGOAL_THEN `closed (ff:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `closure (ff INTER ub) SUBSET (ff:real^3->bool) /\
                closure (ff INTER uc) SUBSET (ff:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `uc INTER closure (ff INTER ub) = {}:real^3->bool /\
                ub INTER closure (ff INTER uc) = {}:real^3->bool` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY] THEN
    UNDISCH_TAC `DISJOINT (ff INTER ub) (ff INTER uc:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{q | q IN boundary_complex (derived_nbhd_complex t la) /\
                     q SUBSET closure (ff INTER (ub:real^3->bool))}` MOI_FSP_SB_SUBSET) THEN
  MP_TAC(ISPEC `{q | q IN boundary_complex (derived_nbhd_complex t la) /\
                     q SUBSET closure (ff INTER (uc:real^3->bool))}` MOI_FSP_SB_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`closure (ff INTER ub) SUBSET (ff:real^3->bool)`;
    `closure (ff INTER uc) SUBSET (ff:real^3->bool)`;
    `uc INTER closure (ff INTER ub) = {}:real^3->bool`;
    `ub INTER closure (ff INTER uc) = {}:real^3->bool`;
    `(ff INTER ub) UNION (ff INTER uc) UNION ee = (ff:real^3->bool)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[]);;

(* KB and KC cover K and meet in L.                                          *)

let MOI_FAN_K_SPLIT = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> {q | q IN boundary_complex (derived_nbhd_complex t la) /\
              q SUBSET closure (moi_fan_bside t la lm j1 j2)} UNION
         {q | q IN boundary_complex (derived_nbhd_complex t la) /\
              q SUBSET closure (moi_fan_cside t la lm j1 j2)} =
         boundary_complex (derived_nbhd_complex t la) /\
         {q | q IN boundary_complex (derived_nbhd_complex t la) /\
              q SUBSET closure (moi_fan_bside t la lm j1 j2)} INTER
         {q | q IN boundary_complex (derived_nbhd_complex t la) /\
              q SUBSET closure (moi_fan_cside t la lm j1 j2)} =
         {q | q IN boundary_complex (derived_nbhd_complex t la) /\ q SUBSET UNIONS lm}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_T) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CLOSURE_SIDES) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fan_ctx]) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `lm:(real^3->bool)->bool`] MOI_FRN_SETUP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `moi_fan_bside t la lm j1 j2 UNION moi_fan_cside t la lm j1 j2 =
      derived_frontier t la DIFF UNIONS lm /\
    DISJOINT (moi_fan_bside t la lm j1 j2) (moi_fan_cside t la lm j1 j2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_fan_cside; moi_fan_bside] THEN POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `kk = boundary_complex (derived_nbhd_complex t (la:(real^3->bool)->bool))` THEN
  ABBREV_TAC `bb = moi_fan_bside t la lm j1 j2` THEN
  ABBREV_TAC `cc = moi_fan_cside t la lm j1 j2` THEN
  ABBREV_TAC `ff = derived_frontier t (la:(real^3->bool)->bool)` THEN
  ABBREV_TAC `ee = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)` THEN
  SUBGOAL_THEN
   `!q. q IN kk ==> q IN barycentric_subdivision (barycentric_subdivision t) /\
                    q SUBSET (ff:real^3->bool)` (LABEL_TAC "kq") THENL
   [X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`simplicial_subcomplex kk (barycentric_subdivision (barycentric_subdivision
         (t:(real^3->bool)->bool)))`;
      `UNIONS kk = (ff:real^3->bool)`; `(q:real^3->bool) IN kk`] THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `q:real^3->bool` THEN
    ASM_CASES_TAC `(q:real^3->bool) IN kk` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "kq" (MP_TAC o C MATCH_MP (ASSUME `(q:real^3->bool) IN kk`) o
      SPEC `q:real^3->bool`) THEN
    STRIP_TAC THEN
    ASM_CASES_TAC `q SUBSET UNIONS (lm:(real^3->bool)->bool)` THENL
     [DISJ1_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`q SUBSET UNIONS (lm:(real^3->bool)->bool)`; `(q:real^3->bool) SUBSET ff`;
        `ff INTER UNIONS lm = (ee:real^3->bool)`; `ee SUBSET closure (bb:real^3->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(q INTER UNIONS lm:real^3->bool) face_of q` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^3->bool)->bool)`;
                     `barycentric_subdivision (lm:(real^3->bool)->bool)`; `q:real^3->bool`]
        MOI_FRN_FULL) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex (q:real^3->bool) /\ closed q` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `?n. n simplex (q:real^3->bool)` (CHOOSE_THEN (fun th ->
        MP_TAC(MATCH_MP SIMPLEX_IMP_CONVEX th) THEN
        MP_TAC(MATCH_MP SIMPLEX_IMP_COMPACT th))) THENL
       [UNDISCH_TAC `lf_simplicial_complex (barycentric_subdivision
                       (barycentric_subdivision (t:(real^3->bool)->bool)))` THEN
        REWRITE_TAC[lf_simplicial_complex] THEN
        DISCH_THEN(MP_TAC o SPEC `q:real^3->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[];
        SIMP_TAC[COMPACT_IMP_CLOSED]];
      ALL_TAC] THEN
    SUBGOAL_THEN `q SUBSET closure (q DIFF UNIONS lm:real^3->bool)` ASSUME_TAC THENL
     [SUBGOAL_THEN `q DIFF UNIONS lm = q DIFF (q INTER UNIONS lm:real^3->bool)` SUBST1_TAC
      THENL [SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_FAN_FACE_DENSE THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(q SUBSET UNIONS (lm:(real^3->bool)->bool))` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `connected (q DIFF UNIONS lm:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN
      SUBGOAL_THEN `q DIFF UNIONS lm = q DIFF (q INTER UNIONS lm:real^3->bool)` SUBST1_TAC
      THENL [SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`q:real^3->bool`; `q INTER UNIONS lm:real^3->bool`] FACE_OF_STILLCONVEX) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `q DIFF UNIONS lm SUBSET ff DIFF UNIONS (lm:(real^3->bool)->bool)`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(q:real^3->bool) SUBSET ff` THEN SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(q DIFF UNIONS lm) INTER (bb:real^3->bool) = {}` THENL
     [DISJ2_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure(q DIFF UNIONS lm:real^3->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
      MAP_EVERY UNDISCH_TAC
       [`(q DIFF UNIONS lm) INTER (bb:real^3->bool) = {}`;
        `q DIFF UNIONS lm SUBSET ff DIFF UNIONS (lm:(real^3->bool)->bool)`;
        `bb UNION cc = ff DIFF UNIONS (lm:(real^3->bool)->bool)`] THEN
      SPEC_TAC(`UNIONS lm:real^3->bool`,`m:real^3->bool`) THEN SET_TAC[];
      DISJ1_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure(q DIFF UNIONS lm:real^3->bool)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_CLOSURE THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                     `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`;
                     `a1:real^3->bool`; `a2:real^3->bool`; `k11:real^3->bool`;
                     `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`;
                     `q DIFF UNIONS lm:real^3->bool`] MOI_FAN_B_CLOPEN) THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `q:real^3->bool` THEN
    ASM_CASES_TAC `(q:real^3->bool) IN kk` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "kq" (MP_TAC o C MATCH_MP (ASSUME `(q:real^3->bool) IN kk`) o
      SPEC `q:real^3->bool`) THEN
    STRIP_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(q:real^3->bool) SUBSET ff`; `ff INTER UNIONS lm = (ee:real^3->bool)`;
      `closure bb SUBSET bb UNION (ee:real^3->bool)`;
      `closure cc SUBSET cc UNION (ee:real^3->bool)`;
      `ee SUBSET closure (bb:real^3->bool)`; `ee SUBSET closure (cc:real^3->bool)`;
      `DISJOINT (bb:real^3->bool) cc`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    SPEC_TAC(`UNIONS lm:real^3->bool`,`m:real^3->bool`) THEN SET_TAC[]]);;

(* The Euler sum of the two side surfaces.                                   *)

let MOI_FAN_EULER_SUM = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> complex_euler {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                            q SUBSET closure (moi_fan_bside t la lm j1 j2)} +
         complex_euler {q | q IN boundary_complex (derived_nbhd_complex t la) /\
                            q SUBSET closure (moi_fan_cside t la lm j1 j2)} = &0`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_T) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_L) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_K_SPLIT) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_SIDE_SURFACES) THEN
  ABBREV_TAC `kk = boundary_complex (derived_nbhd_complex t (la:(real^3->bool)->bool))` THEN
  ABBREV_TAC `kb = {q | q IN kk /\ q SUBSET closure (moi_fan_bside t la lm j1 j2)}` THEN
  ABBREV_TAC `kc = {q | q IN kk /\ q SUBSET closure (moi_fan_cside t la lm j1 j2)}` THEN
  ABBREV_TAC `ll = {q | q IN kk /\ q SUBSET UNIONS (lm:(real^3->bool)->bool)}` THEN
  SUBGOAL_THEN `complex_euler (ll:(real^3->bool)->bool) = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FAN_DEG2_EULER THEN ASM_REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "ll" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `kk:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `combinatorial_manifold 2 (kk:(real^3->bool)->bool)` THEN
      SIMP_TAC[combinatorial_manifold]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`kb:(real^3->bool)->bool`; `kc:(real^3->bool)->bool`] COMPLEX_EULER_UNION) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* The four end circles: connected, compact, nonempty, pairwise disjoint.   *)

let MOI_FAN_ENDS_FACTS = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> connected k11 /\ connected k12 /\ connected k21 /\ connected k22 /\
         compact k11 /\ compact k12 /\ compact k21 /\ compact k22 /\
         ~(k11 = {}) /\ ~(k12 = {}) /\ ~(k21 = {}) /\ ~(k22 = {}) /\
         DISJOINT k11 k12 /\ DISJOINT k11 k21 /\ DISJOINT k11 k22 /\
         DISJOINT k12 k21 /\ DISJOINT k12 k22 /\ DISJOINT k21 k22`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_M) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fan_ctx]) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a1:real^3->bool`; `k11:real^3->bool`; `k12:real^3->bool`]
    MOI_FCB_ANN_ENDS_FACTS) THEN
  MP_TAC(ISPECL [`a2:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`]
    MOI_FCB_ANN_ENDS_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`k11 UNION k12 SUBSET (a1:real^3->bool)`; `k21 UNION k22 SUBSET (a2:real^3->bool)`;
    `DISJOINT (a1:real^3->bool) a2`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

(* Step E: the side surfaces are two pairs of disjoint annuli               *)
(* (MOI_FAN_COUNT).                                                          *)

let MOI_FAN_SIDE_ANNULI = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> ?b1 b2 c1 c2 f3 f4.
           ((f3 = k21 /\ f4 = k22) \/ (f3 = k22 /\ f4 = k21)) /\
           closure(moi_fan_bside t la lm j1 j2) = b1 UNION b2 /\ DISJOINT b1 b2 /\
           pl_annulus_with_ends b1 k11 f3 /\ pl_annulus_with_ends b2 k12 f4 /\
           closure(moi_fan_cside t la lm j1 j2) = c1 UNION c2 /\ DISJOINT c1 c2 /\
           pl_annulus_with_ends c1 k11 k12 /\ pl_annulus_with_ends c2 k21 k22`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CTX_SIDE_SURFACES) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_ENDS_FACTS) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_FAN_EULER_SUM) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_PIECES_MEET_ENDS) THEN
  FIRST_ASSUM(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS(MATCH_MP MOI_FAN_B_REACH th))) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FAN_B_REACH o MATCH_MP MOI_FAN_CTX_SYM) THEN
  REWRITE_TAC[ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                      `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
                MOI_FAN_BSIDE_SYM] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `tau1:real^3->bool` (X_CHOOSE_THEN `w1:real^3`
    (X_CHOOSE_THEN `w2:real^3` (X_CHOOSE_THEN `z1:real^3->bool` (X_CHOOSE_THEN `z2:real^3->bool`
    (X_CHOOSE_THEN `z0:real^3->bool` STRIP_ASSUME_TAC))))) o MATCH_MP MOI_FAN_RIM_WIT) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FAN_RIM_WIT o MATCH_MP MOI_FAN_CTX_SYM) THEN
  REWRITE_TAC[ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                      `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
                MOI_FAN_BSIDE_SYM;
              ISPECL [`t:(real^3->bool)->bool`; `la:(real^3->bool)->bool`;
                      `lm:(real^3->bool)->bool`; `j1:real^3->bool`; `j2:real^3->bool`]
                MOI_FAN_CSIDE_SYM] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau2:real^3->bool` (X_CHOOSE_THEN `u1:real^3`
    (X_CHOOSE_THEN `u2:real^3` (X_CHOOSE_THEN `y1:real^3->bool` (X_CHOOSE_THEN `y2:real^3->bool`
    (X_CHOOSE_THEN `zz0:real^3->bool` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN
   `(?g. connected g /\ g SUBSET closure(moi_fan_cside t la lm j1 j2) /\
         ~(g INTER k11 = {}) /\ ~(g INTER k12 = {})) /\
    (?g. connected g /\ g SUBSET closure(moi_fan_cside t la lm j1 j2) /\
         ~(g INTER k21 = {}) /\ ~(g INTER k22 = {}))`
  (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `closure z0:real^3->bool`; EXISTS_TAC `closure zz0:real^3->bool`] THEN
    ASM_SIMP_TAC[CONNECTED_CLOSURE; SUBSET_CLOSURE];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{q | q IN boundary_complex (derived_nbhd_complex t la) /\
          q SUBSET closure (moi_fan_bside t la lm j1 j2)}`;
    `{q | q IN boundary_complex (derived_nbhd_complex t la) /\
          q SUBSET closure (moi_fan_cside t la lm j1 j2)}`;
    `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`; `k22:real^3->bool`]
   MOI_FAN_COUNT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]);;

(* The frontier is the union of the two closed sides, which meet in the     *)
(* four end circles.                                                         *)

let MOI_FAN_FRONTIER_SIDES = prove
 (`!(t:(real^3->bool)->bool) la lm j1 j2 a1 a2 k11 k12 k21 k22.
     moi_fan_ctx t la lm j1 j2 a1 a2 k11 k12 k21 k22
     ==> derived_frontier t la =
           closure(moi_fan_bside t la lm j1 j2) UNION closure(moi_fan_cside t la lm j1 j2) /\
         closure(moi_fan_bside t la lm j1 j2) INTER closure(moi_fan_cside t la lm j1 j2) =
           k11 UNION k12 UNION k21 UNION k22`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_CLOSURE_SIDES) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fan_ctx]) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_fan_bside t la lm j1 j2 UNION moi_fan_cside t la lm j1 j2 =
      derived_frontier t la DIFF UNIONS lm /\
    DISJOINT (moi_fan_bside t la lm j1 j2) (moi_fan_cside t la lm j1 j2)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[moi_fan_cside; moi_fan_bside] THEN POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `moi_fan_bside t la lm j1 j2` CLOSURE_SUBSET) THEN
  MP_TAC(ISPEC `moi_fan_cside t la lm j1 j2` CLOSURE_SUBSET) THEN
  ABBREV_TAC `bb = moi_fan_bside t la lm j1 j2` THEN
  ABBREV_TAC `cc = moi_fan_cside t la lm j1 j2` THEN
  ABBREV_TAC `ff = derived_frontier t (la:(real^3->bool)->bool)` THEN
  ABBREV_TAC `ee = k11 UNION k12 UNION k21 UNION (k22:real^3->bool)` THEN
  MAP_EVERY UNDISCH_TAC
   [`bb UNION cc = ff DIFF UNIONS (lm:(real^3->bool)->bool)`; `DISJOINT (bb:real^3->bool) cc`;
    `ff INTER UNIONS lm = (ee:real^3->bool)`;
    `closure bb SUBSET bb UNION (ee:real^3->bool)`;
    `closure cc SUBSET cc UNION (ee:real^3->bool)`;
    `ee SUBSET closure (bb:real^3->bool)`; `ee SUBSET closure (cc:real^3->bool)`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  SPEC_TAC(`UNIONS lm:real^3->bool`,`m:real^3->bool`) THEN SET_TAC[]);;

(* ANNULUS_NBHD : |- MOI_FSN_ANNULUS_NBHD.                                  *)

let ANNULUS_NBHD = prove
 (MOI_FSN_ANNULUS_NBHD,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(X_CHOOSE_THEN `a1:real^3->bool` (X_CHOOSE_THEN `a2:real^3->bool`
    (X_CHOOSE_THEN `k11:real^3->bool` (X_CHOOSE_THEN `k12:real^3->bool`
    (X_CHOOSE_THEN `k21:real^3->bool` (X_CHOOSE_THEN `k22:real^3->bool` ASSUME_TAC))))) o
    MATCH_MP MOI_FAN_CTX_EXISTS) THEN
  FIRST_ASSUM(X_CHOOSE_THEN `b1:real^3->bool` (X_CHOOSE_THEN `b2:real^3->bool`
    (X_CHOOSE_THEN `c1:real^3->bool` (X_CHOOSE_THEN `c2:real^3->bool`
    (X_CHOOSE_THEN `f3:real^3->bool` (X_CHOOSE_THEN `f4:real^3->bool`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th))))))) o
    MATCH_MP MOI_FAN_SIDE_ANNULI) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FAN_ENDS_FACTS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FAN_FRONTIER_SIDES) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (ASSUME_TAC o SYM) ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fan_ctx]) THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`derived_frontier t (la:(real^3->bool)->bool)`;
                 `closure(moi_fan_bside t la lm j1 j2)`;
                 `closure(moi_fan_cside t la lm j1 j2)`;
                 `b1:real^3->bool`; `b2:real^3->bool`; `c1:real^3->bool`; `c2:real^3->bool`;
                 `k11:real^3->bool`; `k12:real^3->bool`; `k21:real^3->bool`;
                 `k22:real^3->bool`; `f3:real^3->bool`; `f4:real^3->bool`;
                 `a2:real^3->bool`] MOI_FAN_FINAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b1':real^3->bool` (X_CHOOSE_THEN `b2':real^3->bool`
    (X_CHOOSE_THEN `c1':real^3->bool` (X_CHOOSE_THEN `c2':real^3->bool`
    (X_CHOOSE_THEN `k21':real^3->bool` (X_CHOOSE_THEN `k22':real^3->bool`
      (fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)))))))) THEN
  SUBGOAL_THEN `k21' UNION k22' = k21 UNION (k22:real^3->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th ->
      is_disj(concl th) && can (find_term ((=) `k21':real^3->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a1:real^3->bool`; `a2:real^3->bool`; `b1':real^3->bool`;
                        `b2':real^3->bool`; `c1':real^3->bool`; `c2':real^3->bool`;
                        `k11:real^3->bool`; `k12:real^3->bool`; `k21':real^3->bool`;
                        `k22':real^3->bool`] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
  REWRITE_TAC[ASSUME `k21' UNION k22' = k21 UNION (k22:real^3->bool)`] THEN
  FIRST_ASSUM ACCEPT_TAC);;


