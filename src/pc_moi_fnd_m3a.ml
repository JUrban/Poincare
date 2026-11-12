(* ========================================================================= *)
(* pc_moi_fnd_m3a: foundations of the Moise PL core (Moise, Geometric        *)
(* Topology in Dimensions 2 and 3, Sec 23, pp.165-170): combinatorial        *)
(* 3-manifolds with boundary. Main theorems (proving the statement terms of  *)
(* pc_moi_fnd_stmt.ml):                                                      *)
(*   CM_WB_DIM                       = MOI_FND_CM_WB_DIM                     *)
(*   COMPLEX_BOUNDARY_FRONTIER_3     = MOI_FND_COMPLEX_BOUNDARY_3            *)
(*   BOUNDARY_COMPLEX_SURFACE        = MOI_FND_BOUNDARY_COMPLEX              *)
(*   ORIENTABLE_COMPLEX_3            = MOI_FND_ORIENTABLE_R3                 *)
(* The fifth statement term, MOI_FND_LINEAR_IMAGE_COMPLEX, is not provable   *)
(* as stated: its complex_boundary clause has no local finiteness hypothesis *)
(* (see the last two sections); MOI_FM3_LINEAR_IMAGE_COMPLEX_LF proves it    *)
(* for locally finite c, and MOI_FM3_LINEAR_IMAGE_COMPLEX_GEN the other      *)
(* clauses in general.                                                       *)
(* The first section: closed stars and links of vertices in locally finite   *)
(* complexes (finite simplicial complexes, so that pc_moi_smo_cf applies),   *)
(* the cone correspondence between the simplices at a vertex v and the       *)
(* simplices of the link of v, and the dimension bound CM_WB_DIM.            *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_comb.ml";;
needs "src/pc_moi_star.ml";;
needs "src/pc_moi_smo_cf.ml";;
needs "src/pc_moi_fnd1.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Basic facts on locally finite complexes.                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_FM3_LF_FACE = prove
 (`!c s f:real^N->bool.
        lf_simplicial_complex c /\ s IN c /\ f face_of s ==> f IN c`,
  REWRITE_TAC[lf_simplicial_complex] THEN MESON_TAC[]);;

let MOI_FM3_LF_SIMPLEX = prove
 (`!c s:real^N->bool.
        lf_simplicial_complex c /\ s IN c ==> aff_dim s simplex s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o REWRITE_RULE[lf_simplicial_complex]) THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FM3_LF_CONVEX = prove
 (`!c s:real^N->bool. lf_simplicial_complex c /\ s IN c ==> convex s`,
  MESON_TAC[MOI_FM3_LF_SIMPLEX; SIMPLEX_IMP_CONVEX]);;

let MOI_FM3_LF_COMPACT = prove
 (`!c s:real^N->bool. lf_simplicial_complex c /\ s IN c ==> compact s`,
  MESON_TAC[MOI_FM3_LF_SIMPLEX; SIMPLEX_IMP_COMPACT]);;

let MOI_FM3_LF_POLYTOPE = prove
 (`!c s:real^N->bool. lf_simplicial_complex c /\ s IN c ==> polytope s`,
  MESON_TAC[MOI_FM3_LF_SIMPLEX; SIMPLEX_IMP_POLYTOPE]);;

let MOI_FM3_LF_INTER = prove
 (`!c s t:real^N->bool.
        lf_simplicial_complex c /\ s IN c /\ t IN c
        ==> (s INTER t) face_of s /\ (s INTER t) face_of t`,
  REWRITE_TAC[lf_simplicial_complex] THEN MESON_TAC[]);;

(* A simplex whose relative interior meets t lies in t.                     *)

let MOI_FM3_LF_RELINT_SUBSET = prove
 (`!c s t (x:real^N).
        lf_simplicial_complex c /\ s IN c /\ t IN c /\
        x IN relative_interior s /\ x IN t
        ==> s SUBSET t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`;
                 `t:real^N->bool`] MOI_FM3_LF_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s INTER t:real^N->bool = s` THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s INTER t:real^N->bool`; `s:real^N->bool`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  ASM SET_TAC[]);;

let MOI_FM3_LF_SUBSET_FACE = prove
 (`!c s t:real^N->bool.
        lf_simplicial_complex c /\ s IN c /\ t IN c /\ s SUBSET t
        ==> s face_of t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`;
                 `t:real^N->bool`] MOI_FM3_LF_INTER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `s INTER t:real^N->bool = s` (fun th -> SIMP_TAC[th]) THEN
  ASM SET_TAC[]);;

(* Two simplices of the same dimension, one inside the other, are equal.   *)

let MOI_FM3_LF_SUBSET_DIM_EQ = prove
 (`!c s t:real^N->bool.
        lf_simplicial_complex c /\ s IN c /\ t IN c /\ s SUBSET t /\
        aff_dim s = aff_dim t
        ==> s = t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`;
                 `t:real^N->bool`] MOI_FM3_LF_SUBSET_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex(t:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ASM_REWRITE_TAC[INT_LT_REFL]);;

let MOI_FM3_LF_VERTEX = prove
 (`!c s:real^N->bool.
        lf_simplicial_complex c /\ s IN c /\ ~(s = {})
        ==> ?v. {v} IN c /\ v IN s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_FN1_SIMPLEX_EXTREME_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[FACE_OF_SING];
    ASM_MESON_TAC[extreme_point_of]]);;

(* Subsets of a locally finite complex closed under faces are complexes.   *)

let MOI_FM3_LF_SUBCOMPLEX = prove
 (`!c k:(real^N->bool)->bool.
        lf_simplicial_complex c /\ k SUBSET c /\
        (!s f. s IN k /\ f face_of s ==> f IN k)
        ==> lf_simplicial_complex k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[lf_simplicial_complex] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[SUBSET];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{s:real^N->bool | s IN c /\ ~(s INTER u = {})}` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MOI_FM3_LINK_IN = prove
 (`!c (v:real^N) s.
        s IN simplicial_link c v
        ==> s IN c /\ ~(v IN s) /\ ?t. t IN c /\ v IN t /\ s face_of t`,
  REWRITE_TAC[simplicial_link; IN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* The closed star of a vertex: a finite simplicial complex with the same   *)
(* link and the same simplices at v.                                         *)
(* ------------------------------------------------------------------------- *)

let moi_fm3_cstar = new_definition
 `moi_fm3_cstar (c:(real^N->bool)->bool) (v:real^N) =
    {f | ?t. t IN c /\ v IN t /\ f face_of t}`;;

let MOI_FM3_STAR_FINITE = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ v IN UNIONS c
        ==> FINITE {t | t IN c /\ v IN t}`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{s:real^N->bool | s IN c /\ ~(s INTER u = {})}` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FM3_CSTAR = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c
        ==> simplicial_complex (moi_fm3_cstar c v) /\
            moi_fm3_cstar c v SUBSET c /\
            (!t. t IN c /\ v IN t ==> t IN moi_fm3_cstar c v) /\
            {v} IN moi_fm3_cstar c v /\
            simplicial_link (moi_fm3_cstar c v) v = simplicial_link c v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_fm3_cstar c (v:real^N) SUBSET c` ASSUME_TAC THENL
   [REWRITE_TAC[moi_fm3_cstar; SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `f:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^N->bool. t IN c /\ v IN t ==> t IN moi_fm3_cstar c v`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_fm3_cstar; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FACE_OF_REFL THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `moi_fm3_cstar c (v:real^N) =
        UNIONS (IMAGE (\t. {f:real^N->bool | f face_of t})
                      {t | t IN c /\ v IN t})`
      SUBST1_TAC THENL
       [REWRITE_TAC[moi_fm3_cstar; EXTENSION; IN_UNIONS; EXISTS_IN_IMAGE;
                    IN_ELIM_THM; CONJ_ASSOC];
        ALL_TAC] THEN
      REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC MOI_FM3_STAR_FINITE THEN
        ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
        ASM_REWRITE_TAC[IN_SING];
        REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN
        ASM_MESON_TAC[MOI_FM3_LF_POLYTOPE]];
      MATCH_MP_TAC MOI_FM3_LF_SUBCOMPLEX THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[moi_fm3_cstar; IN_ELIM_THM] THEN MESON_TAC[FACE_OF_TRANS]];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SING];
    REWRITE_TAC[simplicial_link; EXTENSION; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^N->bool` THEN
    EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(s:real^N->bool) IN moi_fm3_cstar c v` THEN
        UNDISCH_TAC `moi_fm3_cstar c (v:real^N) SUBSET c` THEN SET_TAC[];
        EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `(t:real^N->bool) IN moi_fm3_cstar c v` THEN
        UNDISCH_TAC `moi_fm3_cstar c (v:real^N) SUBSET c` THEN SET_TAC[]];
      CONJ_TAC THENL
       [REWRITE_TAC[moi_fm3_cstar; IN_ELIM_THM] THEN
        EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]]);;

let MOI_FM3_LINK_SC = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c
        ==> simplicial_complex (simplicial_link c v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_CSTAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC MOI_SCF_LINK_SC THEN ASM_REWRITE_TAC[]);;

let MOI_FM3_LINK_FINITE = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c
        ==> FINITE (simplicial_link c v)`,
  MESON_TAC[MOI_FM3_LINK_SC; MOI_SCF_SC_FINITE]);;

(* ------------------------------------------------------------------------- *)
(* The cone correspondence at a vertex (from the finite combinatorial        *)
(* 3-manifolds of pc_moi_smo_cf, transferred to locally finite complexes     *)
(* through the closed star).                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_FM3_LINK_JOIN = prove
 (`!c (v:real^N) s.
        lf_simplicial_complex c /\ {v} IN c /\ s IN simplicial_link c v
        ==> convex hull (v INSERT s) IN c /\
            v IN convex hull (v INSERT s) /\
            s SUBSET convex hull (v INSERT s) /\
            aff_dim (convex hull (v INSERT s)) = aff_dim s + &1 /\
            ~(v IN s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_CSTAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_fm3_cstar c (v:real^N)`; `v:real^N`; `s:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBSET]);;

let MOI_FM3_LINK_OPP = prove
 (`!c (v:real^N) t.
        lf_simplicial_complex c /\ {v} IN c /\ t IN c /\ v IN t
        ==> ?s. s IN simplicial_link c v /\ t = convex hull (v INSERT s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_CSTAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`moi_fm3_cstar c (v:real^N)`; `v:real^N`; `t:real^N->bool`]
    MOI_SCF_LINK_OPP) THEN
  ASM_SIMP_TAC[]);;

let MOI_FM3_LINK_JOIN_SUBSET = prove
 (`!c (v:real^N) s s'.
        lf_simplicial_complex c /\ {v} IN c /\
        s IN simplicial_link c v /\ s' IN simplicial_link c v
        ==> (convex hull (v INSERT s) SUBSET convex hull (v INSERT s') <=>
             s SUBSET s')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_CSTAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_SCF_LINK_JOIN_SUBSET THEN
  EXISTS_TAC `moi_fm3_cstar c (v:real^N)` THEN ASM_REWRITE_TAC[]);;

let MOI_FM3_LINK_JOIN_INJ = prove
 (`!c (v:real^N) s s'.
        lf_simplicial_complex c /\ {v} IN c /\
        s IN simplicial_link c v /\ s' IN simplicial_link c v /\
        convex hull (v INSERT s) = convex hull (v INSERT s')
        ==> s = s'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_CSTAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_SCF_LINK_JOIN_INJ THEN
  MAP_EVERY EXISTS_TAC [`moi_fm3_cstar c (v:real^N)`; `v:real^N`] THEN
  ASM_REWRITE_TAC[]);;

(* Cofaces of a cone convex hull (v INSERT e) in c correspond to cofaces of *)
(* e in the link of v, one dimension lower.                                  *)

let MOI_FM3_LINK_CARD = prove
 (`!c (v:real^N) e n m.
        lf_simplicial_complex c /\ {v} IN c /\ e IN simplicial_link c v /\
        m = n + &1
        ==> CARD {r | r IN c /\ aff_dim r = m /\
                      convex hull (v INSERT e) SUBSET r} =
            CARD {t | t IN simplicial_link c v /\ aff_dim t = n /\
                      e SUBSET t}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{r | r IN c /\ aff_dim r = m /\
         convex hull ((v:real^N) INSERT e) SUBSET r} =
    IMAGE (\t. convex hull (v INSERT t))
          {t | t IN simplicial_link c v /\ aff_dim t = n /\ e SUBSET t}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `r:real^N->bool`]
        MOI_FM3_LINK_OPP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_FM3_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `aff_dim(r:real^N->bool) = m` THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
        SUBGOAL_THEN
         `convex hull ((v:real^N) INSERT e) SUBSET convex hull (v INSERT s)`
        MP_TAC THENL
         [UNDISCH_TAC
           `convex hull ((v:real^N) INSERT e) SUBSET r` THEN
          ASM_REWRITE_TAC[];
          MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`;
                         `e:real^N->bool`; `s:real^N->bool`]
            MOI_FM3_LINK_JOIN_SUBSET) THEN
          ASM_REWRITE_TAC[] THEN MESON_TAC[]]];
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_FM3_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`;
                     `e:real^N->bool`; `s:real^N->bool`]
        MOI_FM3_LINK_JOIN_SUBSET) THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
      STRIP_TAC THEN MATCH_MP_TAC MOI_FM3_LINK_JOIN_INJ THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `v:real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_RESTRICT THEN
      MATCH_MP_TAC MOI_FM3_LINK_FINITE THEN ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* CM_WB_DIM: simplices of a combinatorial 3-manifold with boundary have    *)
(* dimension at most 3 (vertex links are PL 2-spheres or PL 2-balls, which  *)
(* contain no convex set of dimension 3 by invariance of dimension).        *)
(* ------------------------------------------------------------------------- *)

let MOI_FM3_LINK_DIM_LE_2 = prove
 (`!c (v:real^N) s.
        lf_simplicial_complex c /\ {v} IN c /\
        (pl_sphere 2 (UNIONS (simplicial_link c v)) \/
         pl_ball 2 (UNIONS (simplicial_link c v))) /\
        s IN simplicial_link c v
        ==> aff_dim s <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  (SUBGOAL_THEN `convex(s:real^N->bool) /\
                 s SUBSET UNIONS (simplicial_link c v)`
   STRIP_ASSUME_TAC THENL
    [CONJ_TAC THENL
      [MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
       EXISTS_TAC `c:(real^N->bool)->bool` THEN
       ASM_MESON_TAC[MOI_FM3_LINK_IN];
       REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]];
     ALL_TAC]) THENL
   [MATCH_MP_TAC MOI_SCF_CONVEX_DIM_LE THEN
    EXISTS_TAC `UNIONS (simplicial_link c (v:real^N))` THEN
    ASM_SIMP_TAC[MOI_SCF_LINK_SPHERE];
    UNDISCH_TAC `pl_ball 2 (UNIONS (simplicial_link c (v:real^N)))` THEN
    REWRITE_TAC[pl_ball; pl_homeomorphism; homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `aff_dim(k:real^N->bool) = &2` (SUBST1_TAC o SYM) THENL
     [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
    MATCH_MP_TAC INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN THEN
    EXISTS_TAC `g:real^N->real^N` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `k:real^N->bool`]
        HULL_SUBSET) THEN
      ASM SET_TAC[];
      ASM_MESON_TAC[SUBSET]]]);;

let CM_WB_DIM = prove
 (`!c:(real^N->bool)->bool.
     combinatorial_manifold_with_boundary 3 c ==> !s. s IN c ==> aff_dim s <= &3`,
  GEN_TAC THEN REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_FM3_LF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
    MOI_FM3_LINK_DIM_LE_2) THEN
  ASM_SIMP_TAC[] THEN INT_ARITH_TAC);;

(* ========================================================================= *)
(* Finite complexes L whose polyhedron is homeomorphic to a 2-simplex k (the *)
(* vertex links at the boundary of a combinatorial 3-manifold). The analogue *)
(* for disks of the S^2 case in pc_moi_smo_cf: L has dimension at most 2 and *)
(* is pure; relative interiors of triangles and of edges in two triangles go *)
(* to the interior of k (invariance of domain in the plane of k); edges in   *)
(* exactly one triangle go to the boundary of k; hence the union moi_fm3_bd2 *)
(* L of the edges in exactly one triangle is the preimage of the relative    *)
(* frontier of k (MOI_FM3_DISK_BOUNDARY), a PL 1-sphere when the             *)
(* homeomorphism is PL.                                                      *)
(* ========================================================================= *)

let moi_fm3_bd2 = new_definition
 `moi_fm3_bd2 (L:(real^N->bool)->bool) =
    UNIONS {e | e IN L /\ aff_dim e = &1 /\
                CARD {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = 1}`;;

let MOI_FM3_CARD_EQ_1 = prove
 (`!s:A->bool. FINITE s /\ CARD s = 1 <=> ?a. s = {a}`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[GSYM HAS_SIZE; HAS_SIZE_1_EXISTS; EXISTS_UNIQUE_THM] THEN
    STRIP_TAC THEN EXISTS_TAC `x:A` THEN ASM SET_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[FINITE_SING; CARD_SING]]);;

(* Two distinct elements in a finite nonempty set whose size is not 1.     *)

let MOI_FM3_CARD_NOT_1 = prove
 (`!s:A->bool a. FINITE s /\ a IN s /\ ~(CARD s = 1)
                 ==> ?x y. x IN s /\ y IN s /\ ~(x = y)`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `s = {a:A}` SUBST_ALL_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[CARD_SING]]);;

(* The relative frontier of a 2-simplex has no isolated points.             *)

let MOI_FM3_RF_NOT_ISOLATED = prove
 (`!k:real^N->bool z d.
        &2 simplex k /\ z IN relative_frontier k /\ &0 < d
        ==> ?w. w IN relative_frontier k /\ ~(w = z) /\ dist(w,z) < d`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o
    REWRITE_RULE[NOT_EXISTS_THM; DE_MORGAN_THM; REAL_NOT_LT]) THEN
  SUBGOAL_THEN `connected(relative_frontier k:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED;
                  AFF_DIM_SIMPLEX; INT_ARITH `~(&2:int = &1)`];
    ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `{z:real^N}`) THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[OPEN_IN_CONTAINS_BALL; IN_SING] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `d:real` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL; IN_SING] THEN
    X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N`) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_SIMP_TAC[REAL_ARITH `x < d ==> ~(d <= x)`];
    SUBGOAL_THEN `{z:real^N} = relative_frontier k INTER {z}` SUBST1_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN REWRITE_TAC[CLOSED_SING]];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`k:real^N->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `k = segment[simplex_barycentre k,z:real^N]` ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; IN_SING] THEN
      MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`simplex_barycentre k:real^N`; `z:real^N`]
      (CONJUNCT1 AFF_DIM_SEGMENT)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
    COND_CASES_TAC THEN INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Dimension and purity.                                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_FM3_DISK_DIM_LE = prove
 (`!L k (h:real^N->real^N) g s.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (UNIONS L,k) (h,g) /\ s IN L
        ==> aff_dim s <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(k:real^N->bool) = &2` (SUBST1_TAC o SYM) THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  MATCH_MP_TAC INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN THEN
  EXISTS_TAC `h:real^N->real^N` THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS L` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `homeomorphism (UNIONS L,k) (h:real^N->real^N,g)` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_CON_SC_CONVEX];
    ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `k:real^N->bool`]
      HULL_SUBSET) THEN
    ASM SET_TAC[];
    ASM_MESON_TAC[SUBSET]]);;

(* A nonempty open subset of the polyhedron inside s forces dim s >= 2.     *)

let MOI_FM3_DISK_OPEN_DIM_GE = prove
 (`!L k (h:real^N->real^N) g V s.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (UNIONS L,k) (h,g) /\
        open_in (subtopology euclidean (UNIONS L)) V /\ ~(V = {}) /\
        V SUBSET s
        ==> &2 <= aff_dim s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean k) (IMAGE (h:real^N->real^N) V)`
  MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^N->real^N`; `UNIONS L:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^N` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^N) x` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `homeomorphism (UNIONS L,k) (h:real^N->real^N,g)` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS L` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^N) x IN k` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `aff_dim(ball((h:real^N->real^N) x,r) INTER k) = &2`
  (SUBST1_TAC o SYM) THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN
    MP_TAC(ISPECL [`k:real^N->bool`; `ball((h:real^N->real^N) x,r)`]
      AFF_DIM_CONVEX_INTER_OPEN) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        EXISTS_TAC `(h:real^N->real^N) x` THEN
        ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL]];
      DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[AFF_DIM_SIMPLEX]];
    ALL_TAC] THEN
  MATCH_MP_TAC INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN THEN
  EXISTS_TAC `g:real^N->real^N` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_BALL] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET];
    MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `s:real^N->bool`]
      HULL_SUBSET) THEN
    MATCH_MP_TAC(SET_RULE
     `IMAGE (g:real^N->real^N) t SUBSET V /\ V SUBSET s
      ==> s SUBSET a ==> IMAGE g t SUBSET a`) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN IMAGE (h:real^N->real^N) V` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^N) IN UNIONS L` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[]]);;

let MOI_FM3_DISK_MAXIMAL = prove
 (`!L k (h:real^N->real^N) g t.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (UNIONS L,k) (h,g) /\
        t IN L /\ ~(t = {}) /\ (!u. u IN L /\ t SUBSET u ==> u = t)
        ==> &2 <= aff_dim t`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_FM3_DISK_OPEN_DIM_GE THEN
  MAP_EVERY EXISTS_TAC
   [`L:(real^N->bool)->bool`; `k:real^N->bool`; `h:real^N->real^N`;
    `g:real^N->real^N`;
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

(* Purity: every nonempty simplex lies in a triangle (as MOI_SCF_SURF_PURE). *)

let MOI_FM3_DISK_PURE = prove
 (`!L k (h:real^N->real^N) g s.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (UNIONS L,k) (h,g) /\
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
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `h:real^N->real^N`; `g:real^N->real^N`; `u:real^N->bool`]
      MOI_FM3_DISK_DIM_LE) THEN
    MP_TAC(ISPEC `u:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
    MP_TAC(ISPEC `u:real^N->bool` AFF_DIM_GE) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
    SUBGOAL_THEN `~(u:real^N->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `?t:real^N->bool. t IN L /\ aff_dim t = &1 /\ s SUBSET t` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `h:real^N->real^N`; `g:real^N->real^N`; `t:real^N->bool`]
      MOI_FM3_DISK_MAXIMAL) THEN
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
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `h:real^N->real^N`; `g:real^N->real^N`; `s:real^N->bool`]
      MOI_FM3_DISK_MAXIMAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->bool`] AFF_DIM_SUBSET) THEN
      FIRST_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
      UNDISCH_TAC
       `~(?t:real^N->bool. t IN L /\ aff_dim t = &1 /\ s SUBSET t)` THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN INT_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN INT_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Invariance of domain in the plane of k.                                   *)
(* ------------------------------------------------------------------------- *)

(* Injective continuous images of open subsets of R^2 are open in the       *)
(* polyhedron and go to the interior of k.                                   *)

let MOI_FM3_INJ_COMPOSE = prove
 (`!(f:A->B) (h:B->C) g s t.
        (!x y. x IN s /\ y IN s /\ f x = f y ==> x = y) /\
        (!z. z IN t ==> g (h z) = z) /\ IMAGE f s SUBSET t
        ==> !x y. x IN s /\ y IN s /\ (h o f) x = (h o f) y ==> x = y`,
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; o_THM] THEN MESON_TAC[]);;

let MOI_FM3_DISK_OPEN_IMAGE = prove
 (`!L k (h:real^N->real^N) g (f:real^2->real^N) W.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (UNIONS L,k) (h,g) /\
        open W /\ f continuous_on W /\ IMAGE f W SUBSET UNIONS L /\
        (!x y. x IN W /\ y IN W /\ f x = f y ==> x = y)
        ==> open_in (subtopology euclidean (UNIONS L)) (IMAGE f W) /\
            IMAGE h (IMAGE f W) SUBSET relative_interior k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  UNDISCH_TAC `homeomorphism (UNIONS L,k) (h:real^N->real^N,g)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism] th)) THEN
  SUBGOAL_THEN
   `!x y. x IN W /\ y IN W /\
          ((h:real^N->real^N) o (f:real^2->real^N)) x = (h o f) y ==> x = y`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_INJ_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`g:real^N->real^N`; `UNIONS L:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (affine hull k))
            (IMAGE ((h:real^N->real^N) o (f:real^2->real^N)) W)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN_AFFINE_SETS THEN
    EXISTS_TAC `(:real^2)` THEN
    REWRITE_TAC[AFFINE_UNIV; AFFINE_AFFINE_HULL; AFF_DIM_UNIV; DIMINDEX_2;
                AFF_DIM_AFFINE_HULL; SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN
    ASM_REWRITE_TAC[INT_LE_REFL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `UNIONS L:real^N->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `k:real^N->bool`]
        HULL_SUBSET) THEN
      REWRITE_TAC[IMAGE_o] THEN
      UNDISCH_TAC `IMAGE (f:real^2->real^N) W SUBSET UNIONS L` THEN
      UNDISCH_TAC `IMAGE (h:real^N->real^N) (UNIONS L) = k` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((h:real^N->real^N) o (f:real^2->real^N)) W SUBSET k`
  ASSUME_TAC THENL
   [REWRITE_TAC[IMAGE_o] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^N) W SUBSET UNIONS L` THEN
    UNDISCH_TAC `IMAGE (h:real^N->real^N) (UNIONS L) = k` THEN
    SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN
     `IMAGE (f:real^2->real^N) W =
      IMAGE (g:real^N->real^N) (IMAGE ((h:real^N->real^N) o f) W)`
    SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN CONV_TAC SYM_CONV THEN
      MATCH_MP_TAC(SET_RULE
       `(!x. x IN UNIONS (L:(real^N->bool)->bool)
             ==> (g:real^N->real^N) (h x) = x) /\ s SUBSET UNIONS L
        ==> IMAGE g (IMAGE h s) = s`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^N`; `k:real^N->bool`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
    EXISTS_TAC `affine hull k:real^N->bool` THEN
    ASM_REWRITE_TAC[HULL_SUBSET];
    REWRITE_TAC[GSYM IMAGE_o] THEN
    MP_TAC(ISPECL [`IMAGE ((h:real^N->real^N) o (f:real^2->real^N)) W`;
                   `k:real^N->bool`] OPEN_IN_SUBSET_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[]]);;

(* Relative interiors of triangles go into the relative interior of k.     *)

let MOI_FM3_DISK_TRIANGLE = prove
 (`!L k (h:real^N->real^N) g t.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (UNIONS L,k) (h,g) /\ t IN L /\ aff_dim t = &2
        ==> IMAGE h (relative_interior t) SUBSET relative_interior k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^N->bool) SUBSET UNIONS L` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN DISCH_TAC THEN
  UNDISCH_TAC `homeomorphism (UNIONS L,k) (h:real^N->real^N,g)` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (affine hull k))
            (IMAGE (h:real^N->real^N) (relative_interior t))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN_AFFINE_SETS THEN
    EXISTS_TAC `affine hull t:real^N->bool` THEN
    REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL;
                OPEN_IN_RELATIVE_INTERIOR] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_SIMPLEX; INT_LE_REFL];
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_TRANS];
      MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `k:real^N->bool`]
        HULL_SUBSET) THEN
      ASM SET_TAC[];
      ASM_MESON_TAC[SUBSET]];
    ASM_SIMP_TAC[OPEN_IN_SUBSET_RELATIVE_INTERIOR] THEN ASM SET_TAC[]]);;

(* Unfolding two triangles on a common edge at a prescribed point of the   *)
(* edge (a variant of MOI_SCF_UNFOLD, which hits the midpoint).             *)

let MOI_FM3_UNFOLD_AT = prove
 (`!a b c1 c2:real^N t.
        ~affine_dependent {a,b,c1} /\ ~affine_dependent {a,b,c2} /\
        ~(a = b) /\ ~(c1 = a) /\ ~(c1 = b) /\ ~(c2 = a) /\ ~(c2 = b) /\
        convex hull {a,b,c1} INTER convex hull {a,b,c2} = convex hull {a,b} /\
        &0 < t /\ t < &1
        ==> ?(f:real^2->real^N) W.
                open W /\ f continuous_on W /\
                IMAGE f W SUBSET
                  convex hull {a,b,c1} UNION convex hull {a,b,c2} /\
                (!x y. x IN W /\ y IN W /\ f x = f y ==> x = y) /\
                ?x. x IN W /\ f x = a + t % (b - a)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `\p:real^2. a + p$1 % (b - a) + max (p$2) (&0) % (c1 - a) +
                         max (--(p$2)) (&0) % (c2 - a:real^N)` THEN
  EXISTS_TAC `ball(vector[t; &0]:real^2,min t (&1 - t) / &2)` THEN
  REWRITE_TAC[OPEN_BALL; MOI_SCF_UNFOLD_CONT] THEN
  SUBGOAL_THEN `&0 < min t (&1 - t) /\ min t (&1 - t) <= t /\
                min t (&1 - t) <= &1 - t`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_MIN; REAL_MIN_LE; REAL_LE_REFL] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^2. p IN ball(vector[t; &0],min t (&1 - t) / &2)
               ==> &0 <= p$1 /\ abs(p$2) <= &1 - p$1`
  ASSUME_TAC THENL
   [X_GEN_TAC `p:real^2` THEN REWRITE_TAC[IN_BALL; dist] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`vector[t; &0] - p:real^2`; `1`] COMPONENT_LE_NORM) THEN
    MP_TAC(ISPECL [`vector[t; &0] - p:real^2`; `2`] COMPONENT_LE_NORM) THEN
    REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_2] THEN
    ASM_REAL_ARITH_TAC;
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
    EXISTS_TAC `vector[t; &0]:real^2` THEN BETA_TAC THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL; VECTOR_2] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[REAL_NEG_0; REAL_ARITH `max (&0) (&0) = &0`] THEN
    VECTOR_ARITH_TAC]);;

(* Relative interiors of edges in two triangles go into the relative        *)
(* interior of k.                                                            *)

let MOI_FM3_DISK_EDGE2 = prove
 (`!L k (h:real^N->real^N) g e t1 t2.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (UNIONS L,k) (h,g) /\
        e IN L /\ aff_dim e = &1 /\
        t1 IN L /\ aff_dim t1 = &2 /\ e SUBSET t1 /\
        t2 IN L /\ aff_dim t2 = &2 /\ e SUBSET t2 /\ ~(t1 = t2)
        ==> IMAGE h (relative_interior e) SUBSET relative_interior k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
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
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; RELATIVE_INTERIOR_SEGMENT;
                  IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c1:real^N`; `c2:real^N`; `u:real`]
    MOI_FM3_UNFOLD_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `W:real^2->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `h:real^N->real^N`; `g:real^N->real^N`;
                 `f:real^2->real^N`; `W:real^2->bool`]
    MOI_FM3_DISK_OPEN_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^N) W SUBSET
                 convex hull {a,b,c1} UNION convex hull {a,b,c2}` THEN
    UNDISCH_TAC `(t1:real^N->bool) IN L` THEN
    UNDISCH_TAC `(t2:real^N->bool) IN L` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `(&1 - u) % a + u % b = (f:real^2->real^N) x` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The boundary of a disk complex.  Edges in exactly one triangle           *)
(* go to the relative frontier of k; points that are neither vertices nor   *)
(* on such edges go to the relative interior (the open star of their        *)
(* carrier is a flat disk); vertices off moi_fm3_bd2 L also go to the       *)
(* interior (the relative frontier of k has no isolated points).  Hence     *)
(* moi_fm3_bd2 L is exactly the preimage of the relative frontier of k.     *)
(* ========================================================================= *)

let MOI_FM3_DISK_EDGE1 = prove
 (`!L k (h:real^N->real^N) g e t1.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (UNIONS L,k) (h,g) /\
        e IN L /\ aff_dim e = &1 /\
        {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = {t1}
        ==> IMAGE h e SUBSET relative_frontier k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `t1 IN L /\ aff_dim t1 = &2 /\ (e:real^N->bool) SUBSET t1`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) SUBSET UNIONS L` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
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
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `h:real^N->real^N`; `g:real^N->real^N`; `u:real^N->bool`]
      MOI_FM3_DISK_PURE) THEN
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
  UNDISCH_TAC `homeomorphism (UNIONS L,k) (h:real^N->real^N,g)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism] th)) THEN
  SUBGOAL_THEN `closed(k:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (relative_interior e) SUBSET relative_frontier k`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN e` ASSUME_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN UNIONS L` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN st` ASSUME_TAC THENL
     [EXPAND_TAC "st" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; ASM_MESON_TAC[MOI_SCF_RELINT_SUBSET]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^N) y IN k` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; IN_DIFF] THEN
    DISCH_TAC THEN
    SUBGOAL_THEN
     `open_in (subtopology euclidean k) (IMAGE (h:real^N->real^N) st)`
    MP_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`g:real^N->real^N`; `UNIONS L:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `o1:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `open_in (subtopology euclidean (affine hull k))
              (relative_interior k INTER (o1:real^N->bool))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN
      ASM_REWRITE_TAC[OPEN_IN_RELATIVE_INTERIOR];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `relative_interior k INTER (o1:real^N->bool) SUBSET
      IMAGE (h:real^N->real^N) st`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(h:real^N->real^N) y IN relative_interior k INTER (o1:real^N->bool)`
    ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN
      SUBGOAL_THEN `(h:real^N->real^N) y IN IMAGE h st` MP_TAC THENL
       [ASM SET_TAC[]; ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(st:real^N->bool) SUBSET UNIONS L` ASSUME_TAC THENL
     [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (g:real^N->real^N) (relative_interior k INTER o1) SUBSET t1`
    ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `st:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `relative_interior k INTER (o1:real^N->bool) SUBSET
        IMAGE (h:real^N->real^N) st` THEN
      UNDISCH_TAC `(st:real^N->bool) SUBSET UNIONS L` THEN
      UNDISCH_TAC `!x. x IN UNIONS L ==> (g:real^N->real^N) (h x) = x` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `open_in (subtopology euclidean (affine hull t1))
              (IMAGE (g:real^N->real^N) (relative_interior k INTER o1))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC INVARIANCE_OF_DOMAIN_AFFINE_SETS THEN
      EXISTS_TAC `affine hull k:real^N->bool` THEN
      ASM_REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL] THEN
      SUBGOAL_THEN `relative_interior k INTER (o1:real^N->bool) SUBSET k`
      ASSUME_TAC THENL
       [MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
        ASM_REWRITE_TAC[INT_LE_REFL];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `t1:real^N->bool`]
          HULL_SUBSET) THEN
        UNDISCH_TAC
         `IMAGE (g:real^N->real^N) (relative_interior k INTER o1) SUBSET t1` THEN
        SET_TAC[];
        UNDISCH_TAC `relative_interior k INTER (o1:real^N->bool) SUBSET k` THEN
        UNDISCH_TAC `!y. y IN k ==> (h:real^N->real^N) (g y) = y` THEN
        REWRITE_TAC[SUBSET] THEN MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (g:real^N->real^N) (relative_interior k INTER o1) SUBSET
      relative_interior t1`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL
       [`IMAGE (g:real^N->real^N) (relative_interior k INTER o1)`;
        `t1:real^N->bool`] OPEN_IN_SUBSET_RELATIVE_INTERIOR) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^N) IN relative_interior t1` ASSUME_TAC THENL
     [SUBGOAL_THEN `(g:real^N->real^N) (h y) = y` (SUBST1_TAC o SYM) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC
       `IMAGE (g:real^N->real^N) (relative_interior k INTER o1) SUBSET
        relative_interior t1` THEN
      UNDISCH_TAC
       `(h:real^N->real^N) y IN relative_interior k INTER (o1:real^N->bool)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`e:real^N->bool`; `t1:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_SCF_SUBSET_FACE];
        DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
      UNDISCH_TAC `(y:real^N) IN e` THEN
      UNDISCH_TAC `(y:real^N) IN relative_interior t1` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(relative_interior e) = (e:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED;
                  MOI_CON_SC_CONVEX; MOI_SCF_SC_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (h:real^N->real^N) (closure(relative_interior e)) SUBSET
    relative_frontier k`
  MP_TAC THENL
   [MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN
    ASM_REWRITE_TAC[CLOSED_RELATIVE_FRONTIER] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `UNIONS L:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]]);;

(* Points which are neither vertices nor on edges in exactly one triangle  *)
(* go into the relative interior of k.                                       *)

let MOI_FM3_DISK_NONVERTEX = prove
 (`!L k (h:real^N->real^N) g y.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (UNIONS L,k) (h,g) /\
        y IN UNIONS L /\ ~({y} IN L) /\ ~(y IN moi_fm3_bd2 L)
        ==> h y IN relative_interior k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?t:real^N->bool. t IN L /\ y IN relative_interior t`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^N) IN UNIONS L` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `y:real^N`]
      IN_RELATIVE_INTERIOR_OF_FACE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_CON_SC_CONVEX]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_MESON_TAC[MOI_CON_SC_FACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `h:real^N->real^N`; `g:real^N->real^N`; `t:real^N->bool`]
    MOI_FM3_DISK_DIM_LE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(aff_dim(t:real^N->bool) = &0)` ASSUME_TAC THENL
   [REWRITE_TAC[AFF_DIM_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `(y:real^N) IN relative_interior {z}` THEN
    REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t:real^N->bool) = &1 \/ aff_dim t = &2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
    MP_TAC(ISPEC `t:real^N->bool` AFF_DIM_GE) THEN
    UNDISCH_TAC `aff_dim(t:real^N->bool) <= &2` THEN
    UNDISCH_TAC `~(aff_dim(t:real^N->bool) = &0)` THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC;
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `h:real^N->real^N`; `g:real^N->real^N`; `t:real^N->bool`]
      MOI_FM3_DISK_TRIANGLE) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `h:real^N->real^N`; `g:real^N->real^N`; `t:real^N->bool`]
    MOI_FM3_DISK_PURE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`{u:real^N->bool | u IN L /\ aff_dim u = &2 /\ t SUBSET u}`;
                 `t0:real^N->bool`] MOI_FM3_CARD_NOT_1) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[MOI_SCF_SC_FINITE];
      ASM_REWRITE_TAC[IN_ELIM_THM];
      DISCH_TAC THEN UNDISCH_TAC `~((y:real^N) IN moi_fm3_bd2 L)` THEN
      REWRITE_TAC[moi_fm3_bd2; IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `h:real^N->real^N`; `g:real^N->real^N`; `t:real^N->bool`;
                 `t1:real^N->bool`; `t2:real^N->bool`] MOI_FM3_DISK_EDGE2) THEN
  ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* Vertices off moi_fm3_bd2 L go into the relative interior of k.          *)

let MOI_FM3_DISK_VERTEX = prove
 (`!L k (h:real^N->real^N) g u.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (UNIONS L,k) (h,g) /\
        {u} IN L /\ ~(u IN moi_fm3_bd2 L)
        ==> h u IN relative_interior k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `homeomorphism (UNIONS L,k) (h:real^N->real^N,g)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism] th)) THEN
  SUBGOAL_THEN `(u:real^N) IN UNIONS L` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^N) u IN k` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `closed(k:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(h:real^N->real^N) u IN relative_frontier k` ASSUME_TAC THENL
   [ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; IN_DIFF]; ALL_TAC] THEN
  ABBREV_TAC `F0 = moi_fm3_bd2 L UNION {z:real^N | {z} IN L /\ ~(z = u)}` THEN
  SUBGOAL_THEN `closed(F0:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "F0" THEN MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_fm3_bd2] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[MOI_SCF_SC_FINITE];
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_SCF_SC_CLOSED]];
      MATCH_MP_TAC FINITE_IMP_CLOSED THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{z:real^N | {z} IN L}` THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`\z:real^N. {z}`; `L:(real^N->bool)->bool`]
          FINITE_IMAGE_INJ) THEN
        REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_SIMP_TAC[MOI_SCF_SC_FINITE] THEN SET_TAC[];
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((u:real^N) IN F0)` ASSUME_TAC THENL
   [EXPAND_TAC "F0" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`F0:real^N->bool`; `u:real^N`] SEPARATE_POINT_CLOSED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(g:real^N->real^N) continuous_on k` THEN
  REWRITE_TAC[continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^N) u`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `d:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d':real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(h:real^N->real^N) u`; `d':real`]
    MOI_FM3_RF_NOT_ISOLATED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N) IN k` ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^N) IN relative_frontier k` THEN
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^N) ((h:real^N->real^N) u) = u` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `dist((g:real^N->real^N) w,u) < d` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV)
      [SYM th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->real^N) w IN UNIONS L` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((g:real^N->real^N) w IN F0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(g:real^N->real^N) w` o
      check (fun th -> is_forall(concl th) &&
                       can (find_term ((=) `F0:real^N->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((g:real^N->real^N) w = u)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(w:real^N = (h:real^N->real^N) u)` THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `(h:real^N->real^N) ((g:real^N->real^N) w) = w`
      (SUBST1_TAC o SYM) THENL [ASM_MESON_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `h:real^N->real^N`; `g:real^N->real^N`;
                 `(g:real^N->real^N) w`] MOI_FM3_DISK_NONVERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((g:real^N->real^N) w IN F0)` THEN
    EXPAND_TAC "F0" THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^N) ((g:real^N->real^N) w) = w` SUBST1_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(w:real^N) IN relative_frontier k` THEN
  REWRITE_TAC[relative_frontier; IN_DIFF] THEN MESON_TAC[]);;

(* The boundary of a disk complex: moi_fm3_bd2 L is the preimage of the     *)
(* relative frontier of k.                                                   *)

let MOI_FM3_DISK_BOUNDARY = prove
 (`!L k (h:real^N->real^N) g.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (UNIONS L,k) (h,g)
        ==> moi_fm3_bd2 L = {y | y IN UNIONS L /\ h y IN relative_frontier k}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y:real^N. y IN relative_interior k ==> ~(y IN relative_frontier k)`
  ASSUME_TAC THENL
   [REWRITE_TAC[relative_frontier; IN_DIFF] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N` THEN
  EQ_TAC THENL
   [REWRITE_TAC[moi_fm3_bd2; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL
     [EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `FINITE {t:real^N->bool | t IN L /\ aff_dim t = &2 /\ e SUBSET t}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[MOI_SCF_SC_FINITE];
      ALL_TAC] THEN
    MP_TAC(ISPEC `{t:real^N->bool | t IN L /\ aff_dim t = &2 /\ e SUBSET t}`
      MOI_FM3_CARD_EQ_1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `t1:real^N->bool`) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `h:real^N->real^N`; `g:real^N->real^N`; `e:real^N->bool`;
                   `t1:real^N->bool`] MOI_FM3_DISK_EDGE1) THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    ASM_CASES_TAC `{y:real^N} IN L` THENL
     [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                     `h:real^N->real^N`; `g:real^N->real^N`; `y:real^N`]
        MOI_FM3_DISK_VERTEX);
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                     `h:real^N->real^N`; `g:real^N->real^N`; `y:real^N`]
        MOI_FM3_DISK_NONVERTEX)] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MOI_FM3_BD2_POLYHEDRON = prove
 (`!L:(real^N->bool)->bool.
        simplicial_complex L
        ==> pl_polyhedron (moi_fm3_bd2 L) /\ moi_fm3_bd2 L SUBSET UNIONS L`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[pl_polyhedron; moi_fm3_bd2] THEN
    EXISTS_TAC `{e:real^N->bool | e IN L /\ aff_dim e = &1 /\
                   CARD {t | t IN L /\ aff_dim t = &2 /\ e SUBSET t} = 1}` THEN
    REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[MOI_SCF_SC_FINITE];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_CON_SC_POLYTOPE]];
    REWRITE_TAC[moi_fm3_bd2] THEN MATCH_MP_TAC SUBSET_UNIONS THEN SET_TAC[]]);;

(* With a PL homeomorphism: moi_fm3_bd2 L is a nonempty PL 1-sphere.       *)

let MOI_FM3_DISK_PL = prove
 (`!L:(real^N->bool)->bool.
        simplicial_complex L /\ pl_ball 2 (UNIONS L)
        ==> ?k (f:real^N->real^N) g.
                    &2 simplex k /\ pl_homeomorphism (k,UNIONS L) (f,g) /\
                    moi_fm3_bd2 L = IMAGE f (relative_frontier k) /\
                    pl_sphere 1 (moi_fm3_bd2 L) /\
                    ~(moi_fm3_bd2 L = {})`,
  GEN_TAC THEN REWRITE_TAC[pl_ball] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_homeomorphism (k,UNIONS L) (f:real^N->real^N,g)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[pl_homeomorphism] th)) THEN
  SUBGOAL_THEN `closed(k:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_fm3_bd2 L = IMAGE (f:real^N->real^N) (relative_frontier k)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `g:real^N->real^N`; `f:real^N->real^N`]
      MOI_FM3_DISK_BOUNDARY) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `homeomorphism (k,UNIONS L) (f:real^N->real^N,g)` THEN
    REWRITE_TAC[homeomorphism] THEN
    UNDISCH_TAC `relative_frontier k SUBSET (k:real^N->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ALL_TAC;
    MP_TAC(ISPECL [`k:real^N->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
    SIMP_TAC[IMAGE_EQ_EMPTY]] THEN
  REWRITE_TAC[pl_sphere] THEN
  MAP_EVERY EXISTS_TAC
   [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[pl_homeomorphism] THEN
  MP_TAC(ISPEC `L:(real^N->bool)->bool` MOI_FM3_BD2_POLYHEDRON) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `UNIONS L:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `UNIONS L:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Boundary vertices and the boundary complex (Moise 23.3, p.168). A vertex  *)
(* v lies on complex_boundary c exactly when its link L has an edge in       *)
(* exactly one triangle (the boundary triangles at v are the cones over such *)
(* edges); a PL 2-sphere link has none (every edge of a 2-sphere complex is  *)
(* in two triangles, pc_moi_smo_cf), a PL 2-ball link has some (the boundary *)
(* of a disk complex, above). The link of a boundary vertex in               *)
(* boundary_complex c is the boundary circle moi_fm3_bd2 L of the disk L, a  *)
(* PL 1-sphere. This gives BOUNDARY_COMPLEX_SURFACE.                         *)
(* ========================================================================= *)

(* The boundary triangles of c through a vertex v are the cones over the   *)
(* edges of the link of v that lie in exactly one triangle of the link.    *)

let MOI_FM3_BT_AT_VERTEX = prove
 (`!c (v:real^N) s.
        lf_simplicial_complex c /\ {v} IN c /\ s IN c /\ v IN s /\
        aff_dim s = &2 /\
        CARD {r | r IN c /\ aff_dim r = &3 /\ s SUBSET r} = 1
        ==> ?e. e IN simplicial_link c v /\ aff_dim e = &1 /\
                CARD {t | t IN simplicial_link c v /\ aff_dim t = &2 /\
                          e SUBSET t} = 1 /\
                s = convex hull (v INSERT e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(e:real^N->bool) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`;
                 `&2:int`; `&3:int`] MOI_FM3_LINK_CARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  UNDISCH_TAC `CARD {r | r IN c /\ aff_dim r = &3 /\
                         (s:real^N->bool) SUBSET r} = 1` THEN
  ASM_REWRITE_TAC[]);;

let MOI_FM3_BT_FROM_LINK = prove
 (`!c (v:real^N) e.
        lf_simplicial_complex c /\ {v} IN c /\ e IN simplicial_link c v /\
        aff_dim e = &1 /\
        CARD {t | t IN simplicial_link c v /\ aff_dim t = &2 /\ e SUBSET t} = 1
        ==> convex hull (v INSERT e) IN c /\
            aff_dim (convex hull (v INSERT e)) = &2 /\
            CARD {r | r IN c /\ aff_dim r = &3 /\
                      convex hull (v INSERT e) SUBSET r} = 1 /\
            convex hull (v INSERT e) SUBSET complex_boundary c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`;
                 `&2:int`; `&3:int`] MOI_FM3_LINK_CARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[];
    REWRITE_TAC[complex_boundary] THEN
    MATCH_MP_TAC(SET_RULE `!a:real^N->bool s. a IN s ==> a SUBSET UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

(* v is on the boundary iff the link of v has an edge in one triangle.     *)

let MOI_FM3_CB_VERTEX_BD2 = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c
        ==> (v IN complex_boundary c <=>
             ~(moi_fm3_bd2 (simplicial_link c v) = {}))`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
      MOI_FM3_BT_AT_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[moi_fm3_bd2; GSYM MEMBER_NOT_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
    SUBGOAL_THEN `~(e:real^N->bool = {})` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
    EXISTS_TAC `x:real^N` THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_fm3_bd2; GSYM MEMBER_NOT_EMPTY; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `e:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
      MOI_FM3_BT_FROM_LINK) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
      MOI_FM3_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM SET_TAC[]]);;

(* A PL 2-sphere link has no edge in exactly one triangle.                  *)

let MOI_FM3_LINK_SPHERE_BD2 = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c /\
        pl_sphere 2 (UNIONS (simplicial_link c v))
        ==> moi_fm3_bd2 (simplicial_link c v) = {}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (simplicial_link c (v:real^N)) /\
                UNIONS (simplicial_link c v) homeomorphic
                sphere(vec 0:real^3,&1)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FM3_LINK_SC; MOI_SCF_LINK_SPHERE]; ALL_TAC] THEN
  REWRITE_TAC[moi_fm3_bd2; EMPTY_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `e:real^N->bool`]
    MOI_SCF_SURF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN ARITH_TAC);;

(* Classification of the vertices of a combinatorial 3-manifold with       *)
(* boundary.                                                                 *)

let MOI_FM3_CB_VERTEX_CLASSIFY = prove
 (`!c (v:real^N).
        combinatorial_manifold_with_boundary 3 c /\ {v} IN c
        ==> (v IN complex_boundary c <=>
             pl_ball 2 (UNIONS (simplicial_link c v))) /\
            (~(v IN complex_boundary c) <=>
             pl_sphere 2 (UNIONS (simplicial_link c v)))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FM3_CB_VERTEX_BD2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `pl_ball 2 (UNIONS (simplicial_link c (v:real^N)))
    ==> ~(moi_fm3_bd2 (simplicial_link c v) = {})`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPEC `simplicial_link c (v:real^N)` MOI_FM3_DISK_PL) THEN
    ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_sphere 2 (UNIONS (simplicial_link c (v:real^N)))
    ==> moi_fm3_bd2 (simplicial_link c v) = {}`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LINK_SPHERE_BD2]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* The link of a boundary vertex in the boundary complex is the boundary   *)
(* circle of its link in c.                                                  *)

let MOI_FM3_BC_LINK = prove
 (`!c (w:real^N).
        lf_simplicial_complex c /\ {w} IN c
        ==> UNIONS (simplicial_link (boundary_complex c) w) =
            moi_fm3_bd2 (simplicial_link c w)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(s:real^N->bool) IN simplicial_link (boundary_complex c) w` THEN
    DISCH_THEN(MP_TAC o
      REWRITE_RULE[simplicial_link; boundary_complex; IN_ELIM_THM]) THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `convex(t:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
    SUBGOAL_THEN `~(relative_interior t:real^N->bool = {})` MP_TAC THENL
     [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN
      UNDISCH_TAC `(w:real^N) IN t` THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    SUBGOAL_THEN `(y:real^N) IN complex_boundary c` MP_TAC THENL
     [MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(y:real^N) IN relative_interior t` THEN
      UNDISCH_TAC `(t:real^N->bool) SUBSET complex_boundary c` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `tau:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(t:real^N->bool) SUBSET tau` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `y:real^N`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^N) IN tau` ASSUME_TAC THENL
     [UNDISCH_TAC `(w:real^N) IN t` THEN
      UNDISCH_TAC `(t:real^N->bool) SUBSET tau` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`; `tau:real^N->bool`]
      MOI_FM3_BT_AT_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(s:real^N->bool) IN simplicial_link c w` ASSUME_TAC THENL
     [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET e` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`; `s:real^N->bool`;
                     `e:real^N->bool`] MOI_FM3_LINK_JOIN_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `tau = convex hull ((w:real^N) INSERT e)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC HULL_MINIMAL THEN
      CONJ_TAC THENL
       [REWRITE_TAC[INSERT_SUBSET] THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^N->bool` THEN
        ASM_SIMP_TAC[FACE_OF_IMP_SUBSET];
        MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
        EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[moi_fm3_bd2; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET e` THEN SET_TAC[];
    REWRITE_TAC[moi_fm3_bd2; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`; `e:real^N->bool`]
      MOI_FM3_BT_FROM_LINK) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`; `e:real^N->bool`]
      MOI_FM3_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[simplicial_link; boundary_complex; IN_ELIM_THM] THEN
    SUBGOAL_THEN `(e:real^N->bool) IN c` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LINK_IN]; ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^N->bool) SUBSET complex_boundary c` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `convex hull ((w:real^N) INSERT e)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `convex hull ((w:real^N) INSERT e)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

(* The boundary complex: a subcomplex covering complex_boundary c.          *)

let MOI_FM3_BC_SUBCOMPLEX = prove
 (`!c:(real^N->bool)->bool.
        lf_simplicial_complex c
        ==> simplicial_subcomplex (boundary_complex c) c /\
            UNIONS (boundary_complex c) = complex_boundary c /\
            lf_simplicial_complex (boundary_complex c)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `simplicial_subcomplex (boundary_complex c) (c:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_subcomplex; boundary_complex; SUBSET; IN_ELIM_THM] THEN
    SIMP_TAC[] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_FACE];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[boundary_complex] THEN
    GEN_REWRITE_TAC (RAND_CONV) [complex_boundary] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM complex_boundary] THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_UNIONS THEN GEN_REWRITE_TAC I [SUBSET] THEN
      X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[complex_boundary] THEN
      MATCH_MP_TAC(SET_RULE `!a:real^N->bool s. a IN s ==> a SUBSET UNIONS s`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    MATCH_MP_TAC MOI_FM3_LF_SUBCOMPLEX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex]]);;

(* Simplices of c inside a component b of the boundary.                     *)

let MOI_FM3_BC_COMPONENT = prove
 (`!c (b:real^N->bool) w.
        lf_simplicial_complex c /\ b IN components (complex_boundary c) /\
        {w} IN c /\ w IN b
        ==> simplicial_link {s | s IN c /\ s SUBSET b} w =
            simplicial_link (boundary_complex c) w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `b SUBSET complex_boundary (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^N->bool. t IN c /\ t SUBSET complex_boundary c /\ w IN t
                     ==> t SUBSET b`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `complex_boundary c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN
      MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[simplicial_link; boundary_complex; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `b:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `b:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(t:real^N->bool) SUBSET b` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_SIMP_TAC[FACE_OF_IMP_SUBSET];
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]]]);;

let BOUNDARY_COMPLEX_SURFACE = prove
 (`!c:(real^N->bool)->bool.
     combinatorial_manifold_with_boundary 3 c
     ==> (!v. {v} IN c
              ==> (v IN complex_boundary c <=>
                   pl_ball 2 (UNIONS (simplicial_link c v))) /\
                  (~(v IN complex_boundary c) <=>
                   pl_sphere 2 (UNIONS (simplicial_link c v)))) /\
         simplicial_subcomplex (boundary_complex c) c /\
         UNIONS (boundary_complex c) = complex_boundary c /\
         combinatorial_manifold 2 (boundary_complex c) /\
         (!b. b IN components (complex_boundary c)
              ==> combinatorial_manifold 2 {s | s IN c /\ s SUBSET b} /\
                  UNIONS {s | s IN c /\ s SUBSET b} = b)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FM3_BC_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v:real^N. {v} IN c
               ==> (v IN complex_boundary c <=>
                    pl_ball 2 (UNIONS (simplicial_link c v))) /\
                   (~(v IN complex_boundary c) <=>
                    pl_sphere 2 (UNIONS (simplicial_link c v)))`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FM3_CB_VERTEX_CLASSIFY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^N. {w} IN c /\ w IN complex_boundary c
               ==> pl_sphere 1 (UNIONS (simplicial_link (boundary_complex c) w))`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[MOI_FM3_BC_LINK] THEN
    MP_TAC(ISPEC `simplicial_link c (w:real^N)` MOI_FM3_DISK_PL) THEN
    ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
    X_GEN_TAC `w:real^N` THEN
    DISCH_THEN(STRIP_ASSUME_TAC o
      REWRITE_RULE[boundary_complex; IN_ELIM_THM; SING_SUBSET]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `b:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `b SUBSET complex_boundary (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_SUBCOMPLEX THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
        ASM_SIMP_TAC[FACE_OF_IMP_SUBSET]];
      ALL_TAC] THEN
    X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_ELIM_THM; SING_SUBSET] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `b:real^N->bool`; `w:real^N`]
      MOI_FM3_BC_COMPONENT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(w:real^N) IN b` THEN
    UNDISCH_TAC `b SUBSET complex_boundary (c:(real^N->bool)->bool)` THEN
    SET_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN complex_boundary c` MP_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN b` THEN
      UNDISCH_TAC `b SUBSET complex_boundary (c:(real^N->bool)->bool)` THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `tau:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `tau:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `complex_boundary c:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN
      MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[complex_boundary] THEN
      MATCH_MP_TAC(SET_RULE `!a:real^N->bool s. a IN s ==> a SUBSET UNIONS s`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* Moise 23.7-23.8 (p.168) in real^3: complex_boundary c is the             *)
(* topological boundary of the polyhedron.  A point x off the boundary lies *)
(* in the open star of a vertex v of its carrier; the star of v is PL      *)
(* homeomorphic to a 3-simplex S (cone over the link: a 2-sphere, or a     *)
(* 2-disk whose boundary circle carries the boundary triangles at v), with *)
(* x going to the interior of S, so x is interior by invariance of domain. *)
(* A point in the relative interior of a boundary triangle sees only that  *)
(* triangle and its unique tetrahedron nearby, so it is not interior; by   *)
(* closure no point of a boundary triangle is.  This gives                  *)
(* COMPLEX_BOUNDARY_FRONTIER_3.                                              *)
(* ========================================================================= *)

(* The star of a vertex with a PL 2-sphere link is PL homeomorphic to a     *)
(* 3-simplex with the link going to its relative frontier.  The proof is    *)
(* that of MOI_STA_STAR_PLH (pc_moi_star.ml), which uses only the link of   *)
(* the one vertex v.                                                         *)

let MOI_FM3_STAR_SPHERE = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c /\
        pl_sphere 2 (UNIONS (simplicial_link c v))
        ==> ?S:real^3->bool p q.
                &3 simplex S /\
                pl_homeomorphism
                  (UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)},
                   S)
                  (p,q) /\
                IMAGE p (UNIONS (simplicial_link c v)) = relative_frontier S /\
                ~(UNIONS (simplicial_link c v) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_sphere 2 (UNIONS (simplicial_link c (v:real^N)))` THEN
  REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f0:real^N->real^N`
    (X_CHOOSE_THEN `g0:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_STA_SIMPLEX_RF_R3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `f1:real^3->real^N`
    (X_CHOOSE_THEN `g1:real^N->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier S,UNIONS (simplicial_link c (v:real^N)))
      ((f0:real^N->real^N) o (f1:real^3->real^N),
       (g1:real^N->real^3) o (g0:real^N->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((g1:real^N->real^3) o (g0:real^N->real^N))
          (UNIONS (simplicial_link c (v:real^N))) = relative_frontier S /\
    IMAGE ((f0:real^N->real^N) o (f1:real^3->real^N)) (relative_frontier S) =
          UNIONS (simplicial_link c v)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `pl_homeomorphism (relative_frontier S,UNIONS (simplicial_link c (v:real^N)))
        ((f0:real^N->real^N) o (f1:real^3->real^N),
         (g1:real^N->real^3) o (g0:real^N->real^N))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^3->bool`; `&3:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`relative_frontier S:real^3->bool`; `UNIONS (simplicial_link c (v:real^N))`;
    `simplex_barycentre (S:real^3->bool)`; `v:real^N`;
    `(f0:real^N->real^N) o (f1:real^3->real^N)`;
    `(g1:real^N->real^3) o (g0:real^N->real^N)`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `S:real^3->bool` THEN
  EXISTS_TAC `moi_con_conemap (UNIONS (simplicial_link c v)) (v:real^N)
               (simplex_barycentre (S:real^3->bool))
               ((g1:real^N->real^3) o (g0:real^N->real^N))` THEN
  EXISTS_TAC `moi_con_conemap (relative_frontier S)
               (simplex_barycentre (S:real^3->bool)) (v:real^N)
               ((f0:real^N->real^N) o (f1:real^3->real^N))` THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE ((g1:real^N->real^3) o (g0:real^N->real^N))
                      (UNIONS (simplicial_link c (v:real^N)))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^N. x IN s ==> (f:real^N->real^3) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_CONEMAP_ON_BASE THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `~(relative_frontier S:real^3->bool = {})` THEN
    UNDISCH_TAC
     `IMAGE ((f0:real^N->real^N) o (f1:real^3->real^N)) (relative_frontier S) =
      UNIONS (simplicial_link c (v:real^N))` THEN
    SET_TAC[]]);;

(* A point off the affine hull of k sees each point of k along a segment    *)
(* meeting k only at its end.                                                *)

let MOI_FM3_SEGMENT_OFF_AFFINE = prove
 (`!w k (x:real^N) y.
        ~(w IN affine hull k) /\ x IN k /\ y IN k /\ y IN segment[w,x]
        ==> y = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN segment[w,x]` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `u = &1` THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN affine hull k` (fun th -> ASM_MESON_TAC[th]) THEN
  SUBGOAL_THEN `inv(&1 - u) * (&1 - u) = &1` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `(w:real^N) = inv(&1 - u) % y + (&1 - inv(&1 - u)) % x`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `inv(&1 - u) * u = inv(&1 - u) - &1` SUBST1_TAC THENL
     [UNDISCH_TAC `inv(&1 - u) * (&1 - u) = &1` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[HULL_INC];
    ASM_MESON_TAC[HULL_INC];
    REAL_ARITH_TAC]);;

(* The relative interior of a cone over a simplex.                          *)

let MOI_FM3_RELINT_CONE = prove
 (`!w V (z:real^N) r.
        ~affine_dependent (w INSERT V) /\ ~(w IN V) /\
        z IN relative_interior (convex hull V) /\ &0 < r /\ r < &1
        ==> w + r % (z - w) IN relative_interior (convex hull (w INSERT V))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent(V:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `(w:real^N) INSERT V` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  UNDISCH_TAC `(z:real^N) IN relative_interior (convex hull V)` THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `\x:real^N. if x = w then &1 - r else r * u x` THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FORALL_IN_INSERT] THEN
  SUBGOAL_THEN
   `sum V (\x:real^N. if x = w then &1 - r else r * u x) = r * sum V u /\
    vsum V (\x:real^N. (if x = w then &1 - r else r * u x) % x) =
    r % vsum V (\x. u x % x)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM SUM_LMUL; GSYM VSUM_LMUL; VECTOR_MUL_ASSOC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC SUM_EQ; MATCH_MP_TAC VSUM_EQ] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(x:real^N = w)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(x:real^N = w)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[];
    REAL_ARITH_TAC;
    VECTOR_ARITH_TAC]);;

(* The star of a vertex with a PL 2-ball link (in real^3) is PL            *)
(* homeomorphic to a 3-simplex; points on open segments from v to link      *)
(* points off the boundary circle go to the interior.                        *)

let MOI_FM3_STAR_BALL = prove
 (`!c (v:real^3).
        lf_simplicial_complex c /\ {v} IN c /\
        pl_ball 2 (UNIONS (simplicial_link c v))
        ==> ?S:real^3->bool p q.
                &3 simplex S /\
                pl_homeomorphism
                  (UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)},
                   S)
                  (p,q) /\
                (!y r. y IN UNIONS (simplicial_link c v) /\
                       ~(y IN moi_fm3_bd2 (simplicial_link c v)) /\
                       &0 < r /\ r < &1
                       ==> p (v + r % (y - v)) IN interior S)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `simplicial_link c (v:real^3)` MOI_FM3_DISK_PL) THEN
  ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?w:real^3. ~(w IN affine hull k)` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_FORALL_THM] THEN DISCH_TAC THEN
    SUBGOAL_THEN `affine hull k = (:real^3)` MP_TAC THENL
     [ASM_REWRITE_TAC[EXTENSION; IN_UNIV]; ALL_TAC] THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(k:real^3->bool) /\ closed k /\ ~(k = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX o check (fun th ->
        can (term_match [] `&2 simplex (k:real^3->bool)`) (concl th))) THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((w:real^3) IN k)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^3. x IN k /\ y IN k /\ y IN segment[w,x] ==> y = x`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_SEGMENT_OFF_AFFINE]; ALL_TAC] THEN
  SUBGOAL_THEN `&3 simplex (convex hull ((w:real^3) INSERT k))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:real^3->bool`; `w:real^3`; `&2:int`]
      MOI_CON_CONE_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull k = (k:real^3->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS {segment[w,z] | z | z IN k} = convex hull ((w:real^3) INSERT k)`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_INSERT_SEGMENTS] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_homeomorphism (k,UNIONS (simplicial_link c v))
                 (f:real^3->real^3,g)` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[pl_homeomorphism; homeomorphism] th)) THEN
  SUBGOAL_THEN `pl_polyhedron (UNIONS (simplicial_link c (v:real^3)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `simplicial_link c (v:real^3)` THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_FM3_LINK_SC; MOI_SCF_SC_FINITE; MOI_CON_SC_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(UNIONS (simplicial_link c (v:real^3)) = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^3->real^3) k = UNIONS (simplicial_link c v)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`UNIONS (simplicial_link c (v:real^3))`; `k:real^3->bool`;
    `v:real^3`; `w:real^3`; `g:real^3->real^3`; `f:real^3->real^3`]
    MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `convex hull ((w:real^3) INSERT k)` THEN
  EXISTS_TAC `moi_con_conemap (UNIONS (simplicial_link c v)) (v:real^3) w
                (g:real^3->real^3)` THEN
  EXISTS_TAC `moi_con_conemap k (w:real^3) v (f:real^3->real^3)` THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `r:real`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS (simplicial_link c (v:real^3))`; `v:real^3`;
                 `w:real^3`; `g:real^3->real^3`; `y:real^3`; `r:real`]
    MOI_CON_CONEMAP_EQ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN MATCH_MP_TAC REAL_LT_IMP_LE THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN `(g:real^3->real^3) y IN relative_interior k` ASSUME_TAC THENL
   [SUBGOAL_THEN `(g:real^3->real^3) y IN k` ASSUME_TAC THENL
     [UNDISCH_TAC
       `IMAGE (g:real^3->real^3) (UNIONS (simplicial_link c v)) = k` THEN
      UNDISCH_TAC `(y:real^3) IN UNIONS (simplicial_link c v)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(f:real^3->real^3) ((g:real^3->real^3) y) = y`
    ASSUME_TAC THENL
     [UNDISCH_TAC `!y. y IN UNIONS (simplicial_link c v)
                       ==> (f:real^3->real^3) ((g:real^3->real^3) y) = y` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `closure k = (k:real^3->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC CLOSURE_CLOSED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((g:real^3->real^3) y IN relative_frontier k)` MP_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC
       `~((y:real^3) IN IMAGE (f:real^3->real^3) (relative_frontier k))` THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(g:real^3->real^3) y` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[relative_frontier; IN_DIFF]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `interior(convex hull ((w:real^3) INSERT k)) =
    relative_interior(convex hull (w INSERT k))`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC RELATIVE_INTERIOR_INTERIOR THEN
    REWRITE_TAC[GSYM AFF_DIM_EQ_FULL; DIMINDEX_3] THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  UNDISCH_TAC `&2 simplex (k:real^3->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^3->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(g:real^3->real^3) y IN relative_interior k` THEN
  UNDISCH_TAC `~((w:real^3) IN affine hull k)` THEN
  ASM_REWRITE_TAC[MOI_SCF_HULL_INSERT_HULL; AFFINE_HULL_CONVEX_HULL] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FM3_RELINT_CONE THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN ASM_REWRITE_TAC[];
    DISCH_TAC THEN UNDISCH_TAC `~((w:real^3) IN affine hull V)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]]);;

(* Carriers: every point of the polyhedron is in the relative interior of  *)
(* a simplex of c, and off the link of each vertex of that simplex.         *)

let MOI_FM3_CARRIER_VERTEX = prove
 (`!c (x:real^N).
        lf_simplicial_complex c /\ x IN UNIONS c
        ==> ?t v. t IN c /\ x IN relative_interior t /\ {v} IN c /\ v IN t /\
                  ~(x IN UNIONS (simplicial_link c v))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?t:real^N->bool. t IN c /\ x IN relative_interior t`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN UNIONS c` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
      IN_RELATIVE_INTERIOR_OF_FACE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_CONVEX]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_FM3_LF_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior t` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `v:real^N`] THEN
  ASM_REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_FM3_LINK_IN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^N->bool) SUBSET s` MP_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(v:real^N) IN t` THEN UNDISCH_TAC `~((v:real^N) IN s)` THEN
    SET_TAC[]]);;

(* The star of v lies in the polyhedron.                                    *)

let MOI_FM3_STAR_SUBSET = prove
 (`!c (v:real^N).
        lf_simplicial_complex c
        ==> UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)}
            SUBSET UNIONS c`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2
      (X_CHOOSE_TAC `s:real^N->bool`) ASSUME_TAC)) ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`]
    MOI_CMB_LINK_IN_STAR) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex(t:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(x:real^N) IN sg` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* Points of a simplex at v lie in the star of v.                            *)

let MOI_FM3_IN_STAR = prove
 (`!c (v:real^N) t x.
        lf_simplicial_complex c /\ {v} IN c /\ t IN c /\ v IN t /\ x IN t /\
        ~(UNIONS (simplicial_link c v) = {})
        ==> x IN UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_CON_IN_CONE] THEN
  ASM_CASES_TAC `x:real^N = v` THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `y0:real^N` o
      GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MAP_EVERY EXISTS_TAC [`y0:real^N`; `&0`] THEN
    ASM_REWRITE_TAC[REAL_POS] THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    VECTOR_ARITH_TAC;
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                   `x:real^N`] MOI_CMB_STAR_CONE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `r:real`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`y:real^N`; `r:real`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* Interior points through a PL homeomorphism of the star onto a 3-simplex. *)

let MOI_FM3_INTERIOR_VIA_STAR = prove
 (`!c (v:real^3) (S:real^3->bool) p q x.
        lf_simplicial_complex c /\ &3 simplex S /\
        pl_homeomorphism
          (UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)},S)
          (p,q) /\
        x IN UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)} /\
        p x IN interior S
        ==> x IN interior (UNIONS c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`S:real^3->bool`;
                 `UNIONS {segment[v:real^3,y] | y |
                          y IN UNIONS(simplicial_link c v)}`;
                 `q:real^3->real^3`; `p:real^3->real^3`]
    MOI_FN1_HOMEOMORPHISM_INTERIOR) THEN
  ANTS_TAC THENL [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
                  ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(q:real^3->real^3) (p x) = x` ASSUME_TAC THENL
   [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `interior (UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)})
    SUBSET interior (UNIONS (c:(real^3->bool)->bool))`
  MP_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN ASM_SIMP_TAC[MOI_FM3_STAR_SUBSET];
    ALL_TAC] THEN
  UNDISCH_TAC
   `IMAGE (q:real^3->real^3) (interior S) SUBSET
    interior (UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)})` THEN
  UNDISCH_TAC `(q:real^3->real^3) (p x) = x` THEN
  UNDISCH_TAC `(p:real^3->real^3) x IN interior S` THEN
  SET_TAC[]);;

(* Points off the boundary are interior (Moise 23.8).                        *)

let MOI_FM3_NOT_CB_INTERIOR = prove
 (`!c (x:real^3).
        combinatorial_manifold_with_boundary 3 c /\ x IN UNIONS c /\
        ~(x IN complex_boundary c)
        ==> x IN interior (UNIONS c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `x:real^3`] MOI_FM3_CARRIER_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (X_CHOOSE_THEN `v:real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^3) IN t` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(x:real^3) IN relative_interior t` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`]
    MOI_FM3_CB_VERTEX_CLASSIFY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `pl_sphere 2 (UNIONS (simplicial_link c (v:real^3)))` THENL
   [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`] MOI_FM3_STAR_SPHERE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^3`
      (X_CHOOSE_THEN `q:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC MOI_FM3_INTERIOR_VIA_STAR THEN
    MAP_EVERY EXISTS_TAC [`v:real^3`; `S:real^3->bool`; `p:real^3->real^3`;
                          `q:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `(x:real^3) IN UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FM3_IN_STAR THEN EXISTS_TAC `t:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]] THEN
    UNDISCH_TAC
     `pl_homeomorphism
        (UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)},S)
        (p:real^3->real^3,q)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(p:real^3->real^3) x IN S` ASSUME_TAC THENL
     [UNDISCH_TAC
       `IMAGE (p:real^3->real^3)
          (UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)}) = S` THEN
      UNDISCH_TAC
       `(x:real^3) IN UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)}` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((p:real^3->real^3) x IN relative_frontier S)` MP_TAC THENL
     [UNDISCH_TAC
       `IMAGE (p:real^3->real^3) (UNIONS (simplicial_link c v)) =
        relative_frontier S` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(y:real^3) IN
         UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)}`
      ASSUME_TAC THENL
       [REWRITE_TAC[MOI_CON_IN_CONE] THEN
        MAP_EVERY EXISTS_TAC [`y:real^3`; `&1`] THEN
        ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN VECTOR_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `x:real^3 = y` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `S:real^3->bool` MOI_STA_SIMPLEX_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[IN_DIFF];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_ball 2 (UNIONS (simplicial_link c (v:real^3)))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold_with_boundary 3
                   (c:(real^3->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(x:real^3 = v)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `t:real^3->bool`;
                 `x:real^3`] MOI_CMB_STAR_CONE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` (X_CHOOSE_THEN `r:real`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `r < &1` ASSUME_TAC THENL
   [MATCH_MP_TAC(REAL_ARITH `r <= &1 /\ ~(r = &1) ==> r < &1`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((x:real^3) IN UNIONS (simplicial_link c v))` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `v + &1 % (y - v):real^3 = y`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^3) IN moi_fm3_bd2 (simplicial_link c v))`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_fm3_bd2; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `e:real^3->bool`]
      MOI_FM3_BT_FROM_LINK) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`; `e:real^3->bool`]
      MOI_FM3_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `~((x:real^3) IN complex_boundary c)` THEN REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x:real^3) IN convex hull (v INSERT e)` MP_TAC THENL
     [SUBGOAL_THEN `segment[v:real^3,y] SUBSET convex hull (v INSERT e)`
      MP_TAC THENL
       [MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] CONVEX_CONVEX_HULL) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `x IN s ==> s SUBSET t ==> (x:real^3) IN t`) THEN
      ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `r:real` THEN
      REPEAT CONJ_TAC THENL
       [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
      UNDISCH_TAC `convex hull ((v:real^3) INSERT e) SUBSET
                   complex_boundary c` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `v:real^3`] MOI_FM3_STAR_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^3`
    (X_CHOOSE_THEN `q:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC MOI_FM3_INTERIOR_VIA_STAR THEN
  MAP_EVERY EXISTS_TAC [`v:real^3`; `S:real^3->bool`; `p:real^3->real^3`;
                        `q:real^3->real^3`] THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[MOI_CON_IN_CONE] THEN
  MAP_EVERY EXISTS_TAC [`y:real^3`; `r:real`] THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

(* Points of boundary triangles are not interior (Moise 23.7).              *)

let MOI_FM3_CB_NOT_INTERIOR = prove
 (`!c (x:real^3).
        lf_simplicial_complex c /\ x IN complex_boundary c
        ==> ~(x IN interior (UNIONS c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^3) IN complex_boundary c` THEN
  REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `FINITE {r:real^3->bool | r IN c /\ aff_dim r = &3 /\ tau SUBSET r}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t:real^3->bool | t IN c /\ x IN t}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_STAR_FINITE THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `tau:real^3->bool` THEN ASM_REWRITE_TAC[];
      GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^3->bool` THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN tau` THEN
      UNDISCH_TAC `(tau:real^3->bool) SUBSET r` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{r:real^3->bool | r IN c /\ aff_dim r = &3 /\ tau SUBSET r}`
    MOI_FM3_CARD_EQ_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `r0:real^3->bool`) THEN
  SUBGOAL_THEN `r0 IN c /\ aff_dim r0 = &3 /\ (tau:real^3->bool) SUBSET r0`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o SPEC `r0:real^3->bool` o REWRITE_RULE[EXTENSION]) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(tau:real^3->bool) /\ closed tau` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
      EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
      EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTERIOR] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^3) IN closure(relative_interior tau)` MP_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `e / &2`) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN tau` ASSUME_TAC THENL
   [MP_TAC(ISPEC `tau:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior tau` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `tau:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `y:real^3`] MOI_CMB_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `ball(y:real^3,min d (e / &2)) SUBSET r0` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN UNIONS c` ASSUME_TAC THENL
     [UNDISCH_TAC `ball(x:real^3,e) SUBSET UNIONS c` THEN
      REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
      UNDISCH_TAC `dist(y:real^3,x) < e / &2` THEN
      UNDISCH_TAC `dist(y:real^3,z) < min d (e / &2)` THEN
      CONV_TAC NORM_ARITH;
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
      is_forall(concl th) &&
      can (find_term ((=) `d:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
     [UNDISCH_TAC `dist(y:real^3,z) < min d (e / &2)` THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(tau:real^3->bool) SUBSET t` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
      MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `y:real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `t:real^3->bool = tau` THENL
     [UNDISCH_TAC `(z:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(tau:real^3->bool) SUBSET r0` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(t:real^3->bool) = &3` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tau:real^3->bool`; `t:real^3->bool`]
        FACE_OF_AFF_DIM_LT) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
          EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
          EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPEC `t:real^3->bool` AFF_DIM_LE_UNIV) THEN
      ASM_REWRITE_TAC[DIMINDEX_3] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `t:real^3->bool = r0` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_ASSUM(MP_TAC o SPEC `t:real^3->bool` o REWRITE_RULE[EXTENSION] o
      check (fun th -> is_eq(concl th) && rand(concl th) = `{r0:real^3->bool}`)) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN interior r0` ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `min d (e / &2)` THEN
    ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tau:real^3->bool`; `r0:real^3->bool`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
      EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(tau:real^3->bool) = &2` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `r0:real^3->bool` INTERIOR_SUBSET_RELATIVE_INTERIOR) THEN
  UNDISCH_TAC `(y:real^3) IN interior r0` THEN
  UNDISCH_TAC `(y:real^3) IN tau` THEN SET_TAC[]);;

let COMPLEX_BOUNDARY_FRONTIER_3 = prove
 (`!c:(real^3->bool)->bool.
     combinatorial_manifold_with_boundary 3 c
     ==> complex_boundary c = UNIONS c DIFF interior (UNIONS c) /\
         (FINITE c ==> complex_boundary c = frontier (UNIONS c))`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN
   `complex_boundary c = UNIONS c DIFF interior (UNIONS (c:(real^3->bool)->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN
    EQ_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `c:(real^3->bool)->bool` MOI_FM3_BC_SUBCOMPLEX) THEN
        ASM_REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
        UNDISCH_TAC `UNIONS (boundary_complex c) =
                     complex_boundary (c:(real^3->bool)->bool)` THEN
        DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
        UNDISCH_TAC `(x:real^3) IN UNIONS (boundary_complex c)` THEN
        UNDISCH_TAC `boundary_complex c SUBSET (c:(real^3->bool)->bool)` THEN
        SET_TAC[];
        MATCH_MP_TAC MOI_FM3_CB_NOT_INTERIOR THEN ASM_REWRITE_TAC[]];
      STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~((x:real^3) IN interior (UNIONS c))` THEN
      REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FM3_NOT_CB_INTERIOR THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN REWRITE_TAC[frontier] THEN
  SUBGOAL_THEN `closure(UNIONS c) = UNIONS (c:(real^3->bool)->bool)`
    (fun th -> REWRITE_TAC[th]) THEN
  MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC CLOSED_UNIONS THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
  EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Every locally finite complex in real^3 is orientable (Moise              *)
(* p.170): orient the tetrahedron with vertices a, b, d, e by the sign of  *)
(* det(b - a, d - a, e - a).  The sign alternates under transpositions, and *)
(* two tetrahedra of the complex on a common triangle lie on opposite sides *)
(* of its plane: otherwise the point (1 - t) m + t e (m the barycentre of   *)
(* the triangle, t small) lies in both tetrahedra but off the triangle,     *)
(* while the two tetrahedra meet exactly in the triangle.  This gives       *)
(* ORIENTABLE_COMPLEX_3.                                                     *)
(* ========================================================================= *)

(* Cramer's rule in real^3.                                                  *)

let MOI_FM3_CRAMER_3 = prove
 (`!x y z w:real^3.
        det(vector[x;y;z]) % w =
        det(vector[w;y;z]) % x + det(vector[x;w;z]) % y +
        det(vector[x;y;w]) % z`,
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; DET_3; VECTOR_3;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_RING);;

(* The orientation determinant of four points.                              *)

let MOI_FM3_DET_SWAPS = prove
 (`!a b d e:real^3.
        det(vector[a - b; d - b; e - b]) = --det(vector[b - a; d - a; e - a]) /\
        det(vector[d - a; b - a; e - a]) = --det(vector[b - a; d - a; e - a]) /\
        det(vector[b - a; e - a; d - a]) = --det(vector[b - a; d - a; e - a])`,
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT] THEN CONV_TAC REAL_RING);;

(* The determinant is affine in the last point.                              *)

let MOI_FM3_DET_AFFINE = prove
 (`!a b d (p:real^3) q r s u1 u2 u3 u4.
        u1 + u2 + u3 + u4 = &1
        ==> det(vector[b - a; d - a; (u1 % p + u2 % q + u3 % r + u4 % s) - a]) =
            u1 * det(vector[b - a; d - a; p - a]) +
            u2 * det(vector[b - a; d - a; q - a]) +
            u3 * det(vector[b - a; d - a; r - a]) +
            u4 * det(vector[b - a; d - a; s - a])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_RING);;

let MOI_FM3_DET_TRIVIAL = prove
 (`!a b d:real^3.
        det(vector[b - a; d - a; a - a]) = &0 /\
        det(vector[b - a; d - a; b - a]) = &0 /\
        det(vector[b - a; d - a; d - a]) = &0`,
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT] THEN CONV_TAC REAL_RING);;

(* A tetrahedron in real^3 has nonzero orientation determinant.              *)

let MOI_FM3_DET_NZ = prove
 (`!a b d e:real^3.
        aff_dim(convex hull {a,b,d,e}) = &3
        ==> ~(det(vector[b - a; d - a; e - a]) = &0)`,
  REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN REPEAT GEN_TAC THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM HOMOGENEOUS_LINEAR_EQUATIONS_DET] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{a,b,d,e} SUBSET {y:real^3 | n dot y = n dot a}` MP_TAC THENL
   [UNDISCH_TAC `(vector [b - a; d - a; e - a]:real^3^3) ** (n:real^3) = vec 0` THEN
    SIMP_TAC[CART_EQ; MATRIX_VECTOR_MUL_COMPONENT; DIMINDEX_3; FORALL_3;
             VEC_COMPONENT; ARITH; VECTOR_3] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
    REWRITE_TAC[DOT_LSUB; DOT_SYM] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP AFF_DIM_SUBSET) THEN
  ASM_SIMP_TAC[AFF_DIM_HYPERPLANE; DIMINDEX_3] THEN INT_ARITH_TAC);;

(* Distinctness and affine independence of the vertices of a tetrahedron. *)

let MOI_FM3_TET_FACTS = prove
 (`!a b d e:real^3.
        aff_dim(convex hull {a,b,d,e}) = &3
        ==> ~(det(vector[b - a; d - a; e - a]) = &0) /\
            ~(a = b) /\ ~(a = d) /\ ~(a = e) /\ ~(b = d) /\ ~(b = e) /\
            ~(d = e) /\ ~affine_dependent {a,b,d,e}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_FM3_DET_NZ) THEN
  SUBGOAL_THEN
   `~(a:real^3 = b) /\ ~(a = d) /\ ~(a = e) /\ ~(b = d) /\ ~(b = e) /\
    ~(d = e)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `~(det(vector[b - a; d - a; e - a]:real^3^3) = &0)` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT] THEN
    CONV_TAC REAL_RING;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[AFFINE_INDEPENDENT_IFF_CARD] THEN
  UNDISCH_TAC `aff_dim(convex hull {a,b,d,e:real^3}) = &3` THEN
  REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
  INT_ARITH_TAC);;

(* Affine coordinates with respect to a tetrahedron.                        *)

let MOI_FM3_AFFINE_COORDS_4 = prove
 (`!a b d e y:real^3.
        ~(det(vector[b - a; d - a; e - a]) = &0)
        ==> ?u1 u2 u3 u4. u1 + u2 + u3 + u4 = &1 /\
                          y = u1 % a + u2 % b + u3 % d + u4 % e`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `D = det(vector[b - a; d - a; e - a]:real^3^3)` THEN
  MAP_EVERY EXISTS_TAC
   [`&1 - det(vector[y - a; d - a; e - a]:real^3^3) / D -
           det(vector[b - a; y - a; e - a]:real^3^3) / D -
           det(vector[b - a; d - a; y - a]:real^3^3) / D`;
    `det(vector[y - a; d - a; e - a]:real^3^3) / D`;
    `det(vector[b - a; y - a; e - a]:real^3^3) / D`;
    `det(vector[b - a; d - a; y - a]:real^3^3) / D`] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC `D:real` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`b - a:real^3`; `d - a:real^3`; `e - a:real^3`; `y - a:real^3`]
    MOI_FM3_CRAMER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC; REAL_SUB_LDISTRIB] THEN
  ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_MUL_RID] THEN
  UNDISCH_TAC
   `D % (y - a) =
    det(vector[y - a; d - a; e - a]) % (b - a) +
    det(vector[b - a; y - a; e - a]) % (d - a) +
    det(vector[b - a; d - a; y - a]) % (e - a:real^3)` THEN
  VECTOR_ARITH_TAC);;

(* Convex combinations of four points.                                      *)

let MOI_FM3_IN_CONVEX_HULL_4 = prove
 (`!a b c d:real^N u1 u2 u3 u4.
        &0 <= u1 /\ &0 <= u2 /\ &0 <= u3 /\ &0 <= u4 /\
        u1 + u2 + u3 + u4 = &1
        ==> u1 % a + u2 % b + u3 % c + u4 % d IN convex hull {a,b,c,d}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`convex hull {a,b,c,d:real^N}`; `1..4`;
    `\i. if i = 1 then u1 else if i = 2 then u2 else if i = 3 then u3
         else u4:real`;
    `\i. if i = 1 then a else if i = 2 then b else if i = 3 then c
         else d:real^N`] CONVEX_VSUM) THEN
  REWRITE_TAC[FINITE_NUMSEG; CONVEX_CONVEX_HULL; SUM_4; VSUM_4; IN_NUMSEG] THEN
  CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN MATCH_MP_TAC THEN
  X_GEN_TAC `i:num` THEN
  REWRITE_TAC[ARITH_RULE `1 <= i /\ i <= 4 <=> i = 1 \/ i = 2 \/ i = 3 \/ i = 4`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]);;

(* A small step along a direction keeps three coordinates nonnegative.      *)

let MOI_FM3_SMALL_STEP = prove
 (`!u1 u2 u3. ?t. &0 < t /\ t < &1 /\
                  &0 <= (&1 - t) / &3 + t * u1 /\
                  &0 <= (&1 - t) / &3 + t * u2 /\
                  &0 <= (&1 - t) / &3 + t * u3`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `&0 < &2 + &3 * (abs u1 + abs u2 + abs u3)` ASSUME_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `inv(&2 + &3 * (abs u1 + abs u2 + abs u3))` THEN
  ABBREV_TAC `t = inv(&2 + &3 * (abs u1 + abs u2 + abs u3))` THEN
  SUBGOAL_THEN `&0 < t /\ t * (&2 + &3 * (abs u1 + abs u2 + abs u3)) = &1`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_MUL_LINV;
                                     REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `--(t * abs u1) <= t * u1 /\ --(t * abs u2) <= t * u2 /\
    --(t * abs u3) <= t * u3 /\
    &0 <= t * abs u1 /\ &0 <= t * abs u2 /\ &0 <= t * abs u3`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_MUL_RNEG] THEN
    REPEAT CONJ_TAC THEN
    (MATCH_MP_TAC REAL_LE_LMUL ORELSE MATCH_MP_TAC REAL_LE_MUL) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE; REAL_ABS_POS] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `t * (&2 + &3 * (abs u1 + abs u2 + abs u3)) = &1` THEN
  REWRITE_TAC[REAL_ADD_LDISTRIB] THEN
  REWRITE_TAC[REAL_ARITH `t * &3 * x = &3 * (t * x)`; REAL_ADD_LDISTRIB] THEN
  REPEAT(POP_ASSUM MP_TAC) THEN REAL_ARITH_TAC);;

(* Two real numbers with negative product have opposite signs.              *)

let MOI_FM3_SGN_OPP = prove
 (`!x y. x * y < &0 ==> real_sgn y = --(real_sgn x)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `real_sgn x * real_sgn y = -- &1` MP_TAC THENL
   [REWRITE_TAC[GSYM REAL_SGN_MUL; REAL_SGN_EQ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPEC `x:real` REAL_SGN_CASES) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

let MOI_FM3_DET_AFFINE_3 = prove
 (`!a b d (p:real^3) q r u1 u2 u3.
        u1 + u2 + u3 = &1
        ==> det(vector[b - a; d - a; (u1 % p + u2 % q + u3 % r) - a]) =
            u1 * det(vector[b - a; d - a; p - a]) +
            u2 * det(vector[b - a; d - a; q - a]) +
            u3 * det(vector[b - a; d - a; r - a])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[DET_3; VECTOR_3; VECTOR_SUB_COMPONENT; VECTOR_ADD_COMPONENT;
              VECTOR_MUL_COMPONENT] THEN
  CONV_TAC REAL_RING);;

(* Two tetrahedra of a complex in real^3 on a common triangle lie on        *)
(* opposite sides of its plane.                                              *)

let MOI_FM3_OPPOSITE_SIDES = prove
 (`!c a b d e e':real^3.
        lf_simplicial_complex c /\ ~(e = e') /\
        convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3 /\
        convex hull {a,b,d,e'} IN c /\ aff_dim(convex hull {a,b,d,e'}) = &3
        ==> det(vector[b - a; d - a; e - a]) *
            det(vector[b - a; d - a; e' - a]) < &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `e:real^3`]
    MOI_FM3_TET_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `e':real^3`]
    MOI_FM3_TET_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `convex hull {a,b,d,e} INTER convex hull {a,b,d,e'} =
    convex hull {a:real^3,b,d}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `a:real^3`] MOI_FM3_CSTAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FM3_LF_FACE THEN
      EXISTS_TAC `convex hull {a:real^3,b,d,e}` THEN
      ASM_SIMP_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
                   IN_INSERT];
      ALL_TAC] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`moi_fm3_cstar c (a:real^3)`; `{a:real^3,b,d,e}`;
                   `{a:real^3,b,d,e'}`] MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^3` THEN
    ASM_CASES_TAC `z:real^3 = e` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(e:real^3 = e')` THEN UNDISCH_TAC `~(a:real^3 = e)` THEN
    UNDISCH_TAC `~(b:real^3 = e)` THEN UNDISCH_TAC `~(d:real^3 = e)` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `e':real^3`; `e:real^3`]
    MOI_FM3_AFFINE_COORDS_4) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real` (X_CHOOSE_THEN `u2:real`
    (X_CHOOSE_THEN `u3:real` (X_CHOOSE_THEN `u4:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `det(vector[b - a; d - a; e - a]:real^3^3) =
    u4 * det(vector[b - a; d - a; e' - a])`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `a:real^3`; `b:real^3`;
                   `d:real^3`; `e':real^3`; `u1:real`; `u2:real`; `u3:real`;
                   `u4:real`] MOI_FM3_DET_AFFINE) THEN
    ASM_REWRITE_TAC[MOI_FM3_DET_TRIVIAL] THEN
    UNDISCH_TAC `e:real^3 = u1 % a + u2 % b + u3 % d + u4 % e'` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM REAL_NOT_LE] THEN DISCH_TAC THEN
  SUBGOAL_THEN `&0 < u4` ASSUME_TAC THENL
   [SUBGOAL_THEN
     `&0 < det(vector[b - a; d - a; e' - a]:real^3^3) *
           det(vector[b - a; d - a; e' - a])`
    ASSUME_TAC THENL [ASM_REWRITE_TAC[REAL_LT_SQUARE]; ALL_TAC] THEN
    SUBGOAL_THEN `~(u4 = &0)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~(det(vector[b - a; d - a; e - a]:real^3^3) = &0)` THEN
      ASM_REWRITE_TAC[REAL_MUL_LZERO];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= u4` MP_TAC THENL
     [MP_TAC(ISPECL
       [`&0`; `u4:real`;
        `det(vector[b - a; d - a; e' - a]:real^3^3) *
         det(vector[b - a; d - a; e' - a])`]
        REAL_LE_LMUL_EQ) THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC
       `&0 <= det(vector[b - a; d - a; e - a]:real^3^3) *
              det(vector[b - a; d - a; e' - a])` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      UNDISCH_TAC `~(u4 = &0)` THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u1:real`; `u2:real`; `u3:real`] MOI_FM3_SMALL_STEP) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `((&1 - t) / &3) % a + ((&1 - t) / &3) % b + ((&1 - t) / &3) % d + t % e
    IN convex hull {a,b,d,e:real^3}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_IN_CONVEX_HULL_4 THEN
    UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `t < &1` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `((&1 - t) / &3) % a + ((&1 - t) / &3) % b + ((&1 - t) / &3) % d + t % e
    IN convex hull {a,b,d,e':real^3}`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `((&1 - t) / &3) % a + ((&1 - t) / &3) % b + ((&1 - t) / &3) % d +
      t % e =
      ((&1 - t) / &3 + t * u1) % a + ((&1 - t) / &3 + t * u2) % b +
      ((&1 - t) / &3 + t * u3) % d + (t * u4) % e':real^3`
    SUBST1_TAC THENL
     [UNDISCH_TAC `e:real^3 = u1 % a + u2 % b + u3 % d + u4 % e'` THEN
      DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FM3_IN_CONVEX_HULL_4 THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `t * u1 + t * u2 + t * u3 + t * u4 = t` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN ASM_REWRITE_TAC[REAL_MUL_RID];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL THEN
      UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `&0 < u4` THEN REAL_ARITH_TAC;
      UNDISCH_TAC `t * u1 + t * u2 + t * u3 + t * u4 = t` THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(((&1 - t) / &3) % a + ((&1 - t) / &3) % b + ((&1 - t) / &3) % d +
      t % e IN convex hull {a,b,d:real^3})`
  ASSUME_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real`
      (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `t * det(vector[b - a; d - a; e - a]:real^3^3) = &0` MP_TAC THENL
     [MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `a:real^3`; `b:real^3`;
                     `d:real^3`; `e:real^3`; `(&1 - t) / &3`; `(&1 - t) / &3`;
                     `(&1 - t) / &3`; `t:real`] MOI_FM3_DET_AFFINE) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[MOI_FM3_DET_TRIVIAL; REAL_MUL_RZERO; REAL_ADD_LID] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC
       `((&1 - t) / &3) % a + ((&1 - t) / &3) % b + ((&1 - t) / &3) % d +
        t % e = p % a + q % b + r % d:real^3` THEN
      DISCH_THEN SUBST1_TAC THEN
      MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `a:real^3`;
                     `b:real^3`; `d:real^3`; `p:real`; `q:real`; `r:real`]
        MOI_FM3_DET_AFFINE_3) THEN
      ASM_REWRITE_TAC[MOI_FM3_DET_TRIVIAL] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o REWRITE_RULE[REAL_ENTIRE]) THEN
    UNDISCH_TAC `~(det(vector[b - a; d - a; e - a]:real^3^3) = &0)` THEN
    UNDISCH_TAC `&0 < t` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC
   `convex hull {a,b,d,e} INTER convex hull {a,b,d,e'} =
    convex hull {a:real^3,b,d}` THEN
  REWRITE_TAC[EXTENSION; IN_INTER] THEN
  DISCH_THEN(MP_TAC o SPEC
   `((&1 - t) / &3) % a + ((&1 - t) / &3) % b + ((&1 - t) / &3) % d +
    t % e:real^3`) THEN
  ASM_REWRITE_TAC[]);;

let ORIENTABLE_COMPLEX_3 = prove
 (`!c:(real^3->bool)->bool. lf_simplicial_complex c ==> orientable_complex c`,
  GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[orientable_complex] THEN
  EXISTS_TAC `\a b d e:real^3. real_sgn(det(vector[b - a; d - a; e - a]))` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `e:real^3`]
      MOI_FM3_DET_SWAPS) THEN
    DISCH_THEN(fun th -> SUBST1_TAC(CONJUNCT1 th) THEN
      SUBST1_TAC(CONJUNCT1(CONJUNCT2 th)) THEN
      SUBST1_TAC(CONJUNCT2(CONJUNCT2 th))) THEN
    REWRITE_TAC[REAL_SGN_NEG] THEN
    MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `d:real^3`; `e:real^3`]
      MOI_FM3_DET_NZ) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[REAL_SGN_EQ] THEN REAL_ARITH_TAC;
    REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_FM3_SGN_OPP THEN
    MATCH_MP_TAC MOI_FM3_OPPOSITE_SIDES THEN
    EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* PL balls and PL spheres across ambient spaces.  A homeomorphism          *)
(* between closed convex sets of the same dimension maps relative frontier  *)
(* onto relative frontier (invariance of domain in affine hulls); simplices *)
(* of the same dimension, in any two spaces, are PL homeomorphic by an      *)
(* affine map, also on their relative frontiers; hence pl_ball m and        *)
(* pl_sphere m transfer along PL homeomorphisms into spaces of dimension at *)
(* least m, respectively m + 1 (the latter bound is forced: an m-sphere does *)
(* not embed in a space of dimension m), and along injective linear maps.  *)
(* ========================================================================= *)

let MOI_FM3_HOMEO_RELINT_SUBSET = prove
 (`!(k1:real^M->bool) (k2:real^N->bool) p q.
        homeomorphism (k1,k2) (p,q) /\ aff_dim k2 <= aff_dim k1
        ==> IMAGE p (relative_interior k1) SUBSET relative_interior k2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `k1:real^M->bool` RELATIVE_INTERIOR_SUBSET) THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `open_in (subtopology euclidean (affine hull k2))
            (IMAGE (p:real^M->real^N) (relative_interior k1))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN_AFFINE_SETS THEN
    EXISTS_TAC `affine hull k1:real^M->bool` THEN
    ASM_REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL;
                    OPEN_IN_RELATIVE_INTERIOR] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `k1:real^M->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `k2:real^N->bool`]
        HULL_SUBSET) THEN
      UNDISCH_TAC `IMAGE (p:real^M->real^N) k1 = k2` THEN
      UNDISCH_TAC `relative_interior k1 SUBSET (k1:real^M->bool)` THEN
      SET_TAC[];
      UNDISCH_TAC `!x. x IN k1 ==> (q:real^N->real^M) (p x) = x` THEN
      UNDISCH_TAC `relative_interior k1 SUBSET (k1:real^M->bool)` THEN
      REWRITE_TAC[SUBSET] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (p:real^M->real^N) (relative_interior k1)`;
                 `k2:real^N->bool`] OPEN_IN_SUBSET_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `IMAGE (p:real^M->real^N) k1 = k2` THEN
  UNDISCH_TAC `relative_interior k1 SUBSET (k1:real^M->bool)` THEN
  SET_TAC[]);;

let MOI_FM3_HOMEO_RELATIVE_FRONTIER = prove
 (`!(k1:real^M->bool) (k2:real^N->bool) p q.
        homeomorphism (k1,k2) (p,q) /\ closed k1 /\ closed k2 /\
        aff_dim k1 = aff_dim k2
        ==> IMAGE p (relative_frontier k1) = relative_frontier k2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k1:real^M->bool`; `k2:real^N->bool`; `p:real^M->real^N`;
                 `q:real^N->real^M`] MOI_FM3_HOMEO_RELINT_SUBSET) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[INT_LE_REFL]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`k2:real^N->bool`; `k1:real^M->bool`; `q:real^N->real^M`;
                 `p:real^M->real^N`] MOI_FM3_HOMEO_RELINT_SUBSET) THEN
  ANTS_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[INT_LE_REFL];
    DISCH_TAC] THEN
  ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN
  MP_TAC(ISPEC `k1:real^M->bool` RELATIVE_INTERIOR_SUBSET) THEN
  MP_TAC(ISPEC `k2:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC `homeomorphism (k1,k2) (p:real^M->real^N,q)` THEN
  REWRITE_TAC[homeomorphism] THEN
  UNDISCH_TAC
   `IMAGE (p:real^M->real^N) (relative_interior k1) SUBSET relative_interior k2` THEN
  UNDISCH_TAC
   `IMAGE (q:real^N->real^M) (relative_interior k2) SUBSET relative_interior k1` THEN
  SET_TAC[]);;

(* Simplices of the same dimension are PL homeomorphic by an affine map,    *)
(* which also matches their relative frontiers.                              *)

let MOI_FM3_SIMPLEX_PLH = prove
 (`!(k1:real^M->bool) (k2:real^N->bool) n.
        n simplex k1 /\ n simplex k2
        ==> ?p q. pl_homeomorphism (k1,k2) (p,q) /\
                  pl_homeomorphism (relative_frontier k1,relative_frontier k2)
                                   (p,q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed(k1:real^M->bool) /\ closed(k2:real^N->bool) /\
                polytope k1 /\ polytope k2 /\ aff_dim k1 = aff_dim k2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_POLYTOPE; AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  UNDISCH_TAC `n simplex (k1:real^M->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V1:real^M->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  UNDISCH_TAC `n simplex (k2:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V2:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `FINITE(V1:real^M->bool) /\ FINITE(V2:real^N->bool) /\
                CARD V1 = CARD V2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_EQ] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V1:real^M->bool`; `V2:real^N->bool`] CARD_EQ_BIJECTIONS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^M->real^N` (X_CHOOSE_THEN `b':real^N->real^M`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V1:real^M->bool`; `b:real^M->real^N`]
    MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`V2:real^N->bool`; `b':real^N->real^M`]
    MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M` (X_CHOOSE_THEN `y':real^M`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `IMAGE (b:real^M->real^N) V1 = V2 /\
                IMAGE (b':real^N->real^M) V2 = V1`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphism (convex hull V1,convex hull V2)
      ((\x:real^M. (l:real^M->real^N) x + y),
       (\x:real^N. (l':real^N->real^M) x + y'))`
  ASSUME_TAC THENL
   [REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\x:real^M. x`; `b:real^M->real^N`;
                     `\x:real^M. (l:real^M->real^N) x + y`;
                     `\x:real^N. (l':real^N->real^M) x + y'`;
                     `l:real^M->real^N`; `y:real^N`; `l':real^N->real^M`;
                     `y':real^M`; `V1:real^M->bool`]
        MOI_REAL_AFFINE_INVERSE_ON_SIMPLEX) THEN
      ASM_SIMP_TAC[IMAGE_ID];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\x:real^M. x`; `b:real^M->real^N`;
                     `\x:real^M. (l:real^M->real^N) x + y`;
                     `l:real^M->real^N`; `y:real^N`; `V1:real^M->bool`]
        MOI_REAL_IMAGE_SIMPLEX) THEN
      ASM_SIMP_TAC[IMAGE_ID];
      MATCH_MP_TAC MOI_PLM_AFFINE_CONTINUOUS_ON THEN
      MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\x:real^N. x`; `b':real^N->real^M`;
                     `\x:real^N. (l':real^N->real^M) x + y'`;
                     `\x:real^M. (l:real^M->real^N) x + y`;
                     `l':real^N->real^M`; `y':real^M`; `l:real^M->real^N`;
                     `y:real^N`; `V2:real^N->bool`]
        MOI_REAL_AFFINE_INVERSE_ON_SIMPLEX) THEN
      ASM_SIMP_TAC[IMAGE_ID];
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`\x:real^N. x`; `b':real^N->real^M`;
                     `\x:real^N. (l':real^N->real^M) x + y'`;
                     `l':real^N->real^M`; `y':real^M`; `V2:real^N->bool`]
        MOI_REAL_IMAGE_SIMPLEX) THEN
      ASM_SIMP_TAC[IMAGE_ID];
      MATCH_MP_TAC MOI_PLM_AFFINE_CONTINUOUS_ON THEN
      MAP_EVERY EXISTS_TAC [`l':real^N->real^M`; `y':real^M`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`\x:real^M. (l:real^M->real^N) x + y`;
                        `\x:real^N. (l':real^N->real^M) x + y'`] THEN
  SUBGOAL_THEN
   `pl_homeomorphism (convex hull V1,convex hull V2)
      ((\x:real^M. (l:real^M->real^N) x + y),
       (\x:real^N. (l':real^N->real^M) x + y'))`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[pl_homeomorphism] THEN CONJ_TAC THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `IMAGE (\x:real^M. (l:real^M->real^N) x + y) (relative_frontier (convex hull V1)) =
    relative_frontier (convex hull V2)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_HOMEO_RELATIVE_FRONTIER THEN
    EXISTS_TAC `\x:real^N. (l':real^N->real^M) x + y'` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier (convex hull V1) SUBSET (convex hull V1:real^M->bool) /\
                relative_frontier (convex hull V2) SUBSET (convex hull V2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED] THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `pl_homeomorphism (convex hull V1,convex hull V2)
      ((\x:real^M. (l:real^M->real^N) x + y),
       (\x:real^N. (l':real^N->real^M) x + y'))` THEN
  REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`convex hull V1:real^M->bool`; `convex hull V2:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `convex hull V1:real^M->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON;
                 MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `convex hull V2:real^N->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON;
                 MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER]]);;

(* Transfer of PL balls and PL spheres along PL homeomorphisms between     *)
(* spaces of possibly different dimensions.                                  *)

let MOI_FM3_PL_BALL_TRANSFER = prove
 (`!(s:real^M->bool) (t:real^N->bool) p q m.
        pl_ball m s /\ pl_homeomorphism (s,t) (p,q) /\ m <= dimindex(:N)
        ==> pl_ball m t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k1:real^M->bool` (X_CHOOSE_THEN `p1:real^M->real^M`
      (X_CHOOSE_THEN `q1:real^M->real^M` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `&m:int` (INST_TYPE [`:N`,`:N`] CHOOSE_SIMPLEX)) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN
  ANTS_TAC THENL [MP_TAC(SPEC `m:num` INT_POS) THEN INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k2:real^N->bool`) THEN
  MP_TAC(ISPECL [`k2:real^N->bool`; `k1:real^M->bool`; `&m:int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^N->real^M` (X_CHOOSE_THEN `q2:real^M->real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`k2:real^N->bool`;
    `(p:real^M->real^N) o (p1:real^M->real^M) o (p2:real^N->real^M)`;
    `((q2:real^M->real^N) o (q1:real^M->real^M)) o (q:real^N->real^M)`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `k1:real^M->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_FM3_PL_SPHERE_TRANSFER = prove
 (`!(s:real^M->bool) (t:real^N->bool) p q m.
        pl_sphere m s /\ pl_homeomorphism (s,t) (p,q) /\ m + 1 <= dimindex(:N)
        ==> pl_sphere m t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k1:real^M->bool` (X_CHOOSE_THEN `p1:real^M->real^M`
      (X_CHOOSE_THEN `q1:real^M->real^M` STRIP_ASSUME_TAC)))
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `&(m + 1):int` (INST_TYPE [`:N`,`:N`] CHOOSE_SIMPLEX)) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN
  ANTS_TAC THENL
   [MP_TAC(SPEC `m + 1` INT_POS) THEN INT_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `k2:real^N->bool`) THEN
  MP_TAC(ISPECL [`k2:real^N->bool`; `k1:real^M->bool`; `&(m + 1):int`]
    MOI_FM3_SIMPLEX_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p2:real^N->real^M` (X_CHOOSE_THEN `q2:real^M->real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`k2:real^N->bool`;
    `(p:real^M->real^N) o (p1:real^M->real^M) o (p2:real^N->real^M)`;
    `((q2:real^M->real^N) o (q1:real^M->real^M)) o (q:real^N->real^M)`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_frontier k1:real^M->bool` THEN ASM_REWRITE_TAC[]);;

(* Dimension bounds for spaces containing a ball or a sphere.               *)

let MOI_FM3_BALL_DIM = prove
 (`!(t:real^N->bool) (s:real^M->bool) p q m.
        pl_ball m t /\ homeomorphism (t,s) (p,q) ==> m <= dimindex(:M)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_ball; pl_homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `p1:real^N->real^N`
      (X_CHOOSE_THEN `q1:real^N->real^N` STRIP_ASSUME_TAC)))
    ASSUME_TAC) THEN
  MP_TAC(ISPECL
   [`k:real^N->bool`; `s:real^M->bool`;
    `(p:real^N->real^M) o (p1:real^N->real^N)`;
    `(q1:real^N->real^N) o (q:real^M->real^N)`; `k:real^N->bool`;
    `(:real^M)`; `&m:int`] MOI_FN1_HOMEO_SIMPLEX_DIM) THEN
  REWRITE_TAC[AFF_DIM_UNIV; INT_OF_NUM_LE] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[SUBSET_REFL; AFFINE_HULL_UNIV; SUBSET_UNIV] THEN
  MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_FM3_SPHERE_DIM = prove
 (`!(t:real^N->bool) (s:real^M->bool) p q m.
        pl_sphere m t /\ homeomorphism (t,s) (p,q) ==> m + 1 <= dimindex(:M)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `p1:real^N->real^N`
      (X_CHOOSE_THEN `q1:real^N->real^N` STRIP_ASSUME_TAC)))
    ASSUME_TAC) THEN
  SUBGOAL_THEN
   `homeomorphism (relative_frontier k,s)
      ((p:real^N->real^M) o (p1:real^N->real^N),
       (q1:real^N->real^N) o (q:real^M->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `~(d < m + 1) ==> m + 1 <= d`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&(m + 1):int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `bounded(k:real^N->bool) /\ convex k` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED;
                  SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  UNDISCH_TAC
   `homeomorphism (relative_frontier k,s)
      ((p:real^N->real^M) o (p1:real^N->real^N),
       (q1:real^N->real^N) o (q:real^M->real^N))` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`(p:real^N->real^M) o (p1:real^N->real^N)`;
                 `k:real^N->bool`; `relative_frontier k:real^N->bool`;
                 `(:real^M)`] INVARIANCE_OF_DOMAIN_SPHERE_AFFINE_SET_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_UNIV; AFFINE_UNIV; OPEN_IN_REFL; AFF_DIM_UNIV] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[];
      FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
      ASM_REWRITE_TAC[INT_OF_NUM_LT]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `IMAGE ((p:real^N->real^M) o (p1:real^N->real^N))
                      (relative_frontier k)` COMPACT_OPEN) THEN
  ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
  UNDISCH_TAC
   `IMAGE ((p:real^N->real^M) o (p1:real^N->real^N)) (relative_frontier k) =
    s` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  ASM_SIMP_TAC[COMPACT_RELATIVE_FRONTIER_BOUNDED]);;

(* PL homeomorphisms along an injective linear map.                          *)

let MOI_FM3_LINEAR_PLH = prove
 (`!(f:real^M->real^N) X.
        linear f /\ (!x y. f x = f y ==> x = y) /\ pl_polyhedron X
        ==> ?g. linear g /\ (!x. g (f x) = x) /\
                pl_homeomorphism (X,IMAGE f X) (f,g)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `f:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^M. (g:real^N->real^M) ((f:real^M->real^N) x) = x`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[o_THM; I_THM];
    ALL_TAC] THEN
  EXISTS_TAC `g:real^N->real^M` THEN ASM_REWRITE_TAC[pl_homeomorphism] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID] THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^M. (f:real^M->real^N) x + vec 0` THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_RID];
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^N. (g:real^N->real^M) x + vec 0` THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_RID];
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC PL_POLYHEDRON_LINEAR_IMAGE THEN ASM_REWRITE_TAC[]]]);;

let MOI_FM3_PL_LINEAR_IMAGE_EQ = prove
 (`!(f:real^M->real^N) X m.
        linear f /\ (!x y. f x = f y ==> x = y) /\ pl_polyhedron X
        ==> (pl_sphere m (IMAGE f X) <=> pl_sphere m X) /\
            (pl_ball m (IMAGE f X) <=> pl_ball m X)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `X:real^M->bool`] MOI_FM3_LINEAR_PLH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `pl_homeomorphism (IMAGE f X,X)
                  ((g:real^N->real^M),(f:real^M->real^N))`
  ASSUME_TAC THENL [ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `dimindex(:M) <= dimindex(:N)` ASSUME_TAC THENL
   [MATCH_MP_TAC LINEAR_INJECTIVE_DIMINDEX_LE THEN
    EXISTS_TAC `f:real^M->real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `homeomorphism (X,IMAGE f X)
                  ((f:real^M->real^N),(g:real^N->real^M)) /\
                homeomorphism (IMAGE f X,X)
                  ((g:real^N->real^M),(f:real^M->real^N))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  CONJ_TAC THEN EQ_TAC THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`IMAGE (f:real^M->real^N) X`; `X:real^M->bool`;
                   `g:real^N->real^M`; `f:real^M->real^N`; `m:num`]
      MOI_FM3_PL_SPHERE_TRANSFER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (f:real^M->real^N) X`; `X:real^M->bool`;
                   `g:real^N->real^M`; `f:real^M->real^N`; `m:num`]
      MOI_FM3_SPHERE_DIM) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`m:num`; `X:real^M->bool`; `IMAGE (f:real^M->real^N) X`;
                   `f:real^M->real^N`; `g:real^N->real^M`]
      MOI_CMB_PL_SPHERE_TRANSFER) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`IMAGE (f:real^M->real^N) X`; `X:real^M->bool`;
                   `g:real^N->real^M`; `f:real^M->real^N`; `m:num`]
      MOI_FM3_PL_BALL_TRANSFER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`IMAGE (f:real^M->real^N) X`; `X:real^M->bool`;
                   `g:real^N->real^M`; `f:real^M->real^N`; `m:num`]
      MOI_FM3_BALL_DIM) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`X:real^M->bool`; `IMAGE (f:real^M->real^N) X`;
                   `f:real^M->real^N`; `g:real^N->real^M`; `m:num`]
      MOI_FM3_PL_BALL_TRANSFER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MP_TAC(ISPECL [`X:real^M->bool`; `IMAGE (f:real^M->real^N) X`;
                   `f:real^M->real^N`; `g:real^N->real^M`; `m:num`]
      MOI_FM3_BALL_DIM) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Transport of complexes along injective linear maps (used to             *)
(* move complexes between real^3 and real^7 in the loop theorem glue).     *)
(* Local finiteness, finiteness, vertex links, combinatorial manifolds      *)
(* (with boundary), orientability and, for locally finite complexes, the   *)
(* combinatorial boundary all transport.  The boundary clause needs local  *)
(* finiteness: complex_boundary counts tetrahedra on a triangle with CARD, *)
(* which is unspecified on infinite sets.                                   *)
(* ========================================================================= *)

let MOI_FM3_INJ_IN_IMAGE = prove
 (`!(h:A->B) s x. (!x y. h x = h y ==> x = y) ==> (h x IN IMAGE h s <=> x IN s)`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

let MOI_FM3_INJ_IMAGE_SUBSET = prove
 (`!(h:A->B) s t.
        (!x y. h x = h y ==> x = y)
        ==> (IMAGE h s SUBSET IMAGE h t <=> s SUBSET t)`,
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_IMAGE] THEN MESON_TAC[]);;

let MOI_FM3_INJ_IMAGE_EQ = prove
 (`!(h:A->B) s t.
        (!x y. h x = h y ==> x = y) ==> (IMAGE h s = IMAGE h t <=> s = t)`,
  MESON_TAC[INJECTIVE_IMAGE]);;

let MOI_FM3_IMAGE_SING = prove
 (`!(h:A->B) s w.
        (!x y. h x = h y ==> x = y)
        ==> (IMAGE h s = {w} <=> ?v. s = {v} /\ w = h v)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(w:B) IN IMAGE (h:A->B) s` MP_TAC THENL
     [ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:A` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:A` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_SING] THEN X_GEN_TAC `z:A` THEN EQ_TAC THENL
     [DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      SUBGOAL_THEN `(h:A->B) z IN {w}` MP_TAC THENL
       [UNDISCH_TAC `IMAGE (h:A->B) s = {w}` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[IN_SING]];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES]]);;

(* Local finiteness.                                                         *)

let MOI_FM3_LINEAR_IMAGE_RULES = prove
 (`!h:real^M->real^N.
        linear h /\ (!x y. h x = h y ==> x = y)
        ==> (!s n. n simplex IMAGE h s <=> n simplex s) /\
            (!t s. IMAGE h t face_of IMAGE h s <=> t face_of s) /\
            (!s t. IMAGE h s INTER IMAGE h t = IMAGE h (s INTER t)) /\
            (!s t. IMAGE h s = IMAGE h t <=> s = t) /\
            (!s t. IMAGE h s SUBSET IMAGE h t <=> s SUBSET t) /\
            (!s x. h x IN IMAGE h s <=> x IN s) /\
            (!s. aff_dim (IMAGE h s) = aff_dim s) /\
            (!s. convex hull (IMAGE h s) = IMAGE h (convex hull s))`,
  GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN REPEAT GEN_TAC THENL
   [MATCH_MP_TAC SIMPLEX_LINEAR_IMAGE_EQ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FACE_OF_LINEAR_IMAGE THEN ASM_REWRITE_TAC[];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC IMAGE_INTER_INJ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FM3_INJ_IMAGE_EQ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FM3_INJ_IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FM3_INJ_IN_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC AFF_DIM_INJECTIVE_LINEAR_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONVEX_HULL_LINEAR_IMAGE THEN ASM_REWRITE_TAC[]]);;

let MOI_FM3_LF_LINEAR_IMAGE = prove
 (`!(h:real^M->real^N) c.
        linear h /\ (!x y. h x = h y ==> x = y)
        ==> (lf_simplicial_complex (IMAGE (IMAGE h) c) <=>
             lf_simplicial_complex c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `h:real^M->real^N` MOI_FM3_LINEAR_IMAGE_RULES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `h:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^M. (g:real^N->real^M) ((h:real^M->real^N) x) = x`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[o_THM; I_THM];
    ALL_TAC] THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  MATCH_MP_TAC(TAUT `(a <=> a') /\ (b <=> b') /\ (c <=> c') /\ (d <=> d')
                     ==> (a /\ b /\ c /\ d <=> a' /\ b' /\ c' /\ d')`) THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
    EQ_TAC THEN DISCH_TAC THENL
     [MAP_EVERY X_GEN_TAC [`t:real^M->bool`; `s:real^M->bool`] THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`IMAGE (h:real^M->real^N) t`;
                                    `IMAGE (h:real^M->real^N) s`]) THEN
      ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
       [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `IMAGE (h:real^M->real^N) t = IMAGE h u` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t':real^N->bool`; `s':real^N->bool`] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      SUBGOAL_THEN `(t':real^N->bool) SUBSET IMAGE (h:real^M->real^N) s`
      MP_TAC THENL
       [UNDISCH_TAC `(t':real^N->bool) face_of s'` THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[FACE_OF_IMP_SUBSET];
        ALL_TAC] THEN
      REWRITE_TAC[SUBSET_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `u:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `s:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(t':real^N->bool) face_of s'` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM IMAGE_UNIONS; FORALL_IN_IMAGE] THEN
    EQ_TAC THEN DISCH_TAC THEN X_GEN_TAC `x:real^M` THEN DISCH_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `{z:real^M | (h:real^M->real^N) z IN v}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT];
        ALL_TAC] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{s:real^M->bool | s IN c /\
                     ~(IMAGE (h:real^M->real^N) s INTER v = {})}` THEN
      CONJ_TAC THENL
       [MP_TAC(ISPECL [`IMAGE (h:real^M->real^N)`;
                       `{s:real^M->bool | s IN c /\
                           ~(IMAGE (h:real^M->real^N) s INTER v = {})}`]
          FINITE_IMAGE_INJ_EQ) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN MESON_TAC[]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{s':real^N->bool | s' IN IMAGE (IMAGE (h:real^M->real^N)) c /\
                                       ~(s' INTER v = {})}` THEN
        ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        MESON_TAC[FUN_IN_IMAGE];
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SET_TAC[]];
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `{y:real^N | (g:real^N->real^M) y IN u}` THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN
        ASM_SIMP_TAC[LINEAR_CONTINUOUS_AT];
        ALL_TAC] THEN
      MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (IMAGE (h:real^M->real^N))
                    {s:real^M->bool | s IN c /\ ~(s INTER u = {})}` THEN
      ASM_SIMP_TAC[FINITE_IMAGE] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `s':real^N->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(s' INTER {y:real^N | (g:real^N->real^M) y IN u} = {})` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_ELIM_THM; IN_IMAGE] THEN
      ASM_MESON_TAC[]]]);;

(* Vertices and vertex links.                                                *)

let MOI_FM3_VERTEX_LINEAR_IMAGE = prove
 (`!(h:real^M->real^N) c w.
        (!x y. h x = h y ==> x = y)
        ==> ({w} IN IMAGE (IMAGE h) c <=> ?v. {v} IN c /\ w = h v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`h:real^M->real^N`; `s:real^M->bool`; `w:real^N`]
      MOI_FM3_IMAGE_SING) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^M` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^M` THEN
    UNDISCH_TAC `(s:real^M->bool) IN c` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `v:real^M` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{v:real^M}` THEN ASM_REWRITE_TAC[IMAGE_CLAUSES]]);;

let MOI_FM3_LINK_LINEAR_IMAGE = prove
 (`!(h:real^M->real^N) c v.
        linear h /\ (!x y. h x = h y ==> x = y)
        ==> simplicial_link (IMAGE (IMAGE h) c) (h v) =
            IMAGE (IMAGE h) (simplicial_link c v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `h:real^M->real^N` MOI_FM3_LINEAR_IMAGE_RULES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `s':real^N->bool` THEN
  REWRITE_TAC[simplicial_link; IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t':real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC)
          STRIP_ASSUME_TAC)))) THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `~((h:real^M->real^N) v IN s')` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `t:real^M->bool` THEN
      UNDISCH_TAC `(h:real^M->real^N) v IN t'` THEN
      UNDISCH_TAC `(s':real^N->bool) face_of t'` THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` (CONJUNCTS_THEN2 SUBST1_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC))))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `IMAGE (h:real^M->real^N) t` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[]]]);;

let MOI_FM3_LINK_POLYHEDRON = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ {v} IN c
        ==> pl_polyhedron (UNIONS (simplicial_link c v))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `simplicial_link c (v:real^N)` THEN REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LINK_FINITE THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FM3_LF_POLYTOPE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[MOI_FM3_LINK_IN]]);;

(* Combinatorial manifolds, with or without boundary.                       *)

let MOI_FM3_CM_LINEAR_IMAGE = prove
 (`!(h:real^M->real^N) c.
        linear h /\ (!x y. h x = h y ==> x = y)
        ==> (!n. combinatorial_manifold n (IMAGE (IMAGE h) c) <=>
                 combinatorial_manifold n c) /\
            (!n. combinatorial_manifold_with_boundary n (IMAGE (IMAGE h) c) <=>
                 combinatorial_manifold_with_boundary n c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[combinatorial_manifold; combinatorial_manifold_with_boundary] THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `c:(real^M->bool)->bool`]
    MOI_FM3_LF_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `!P. (!w. {w} IN IMAGE (IMAGE (h:real^M->real^N)) c
             ==> P (UNIONS (simplicial_link (IMAGE (IMAGE h) c) w))) <=>
        (!v. {v} IN c ==> P (IMAGE h (UNIONS (simplicial_link c v))))`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN
    MP_TAC(ISPECL [`h:real^M->real^N`; `c:(real^M->bool)->bool`]
      MOI_FM3_VERTEX_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
    ONCE_REWRITE_TAC[SWAP_FORALL_THM] THEN
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_UNWIND_THM2] THEN
    MP_TAC(ISPECL [`h:real^M->real^N`; `c:(real^M->bool)->bool`]
      MOI_FM3_LINK_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[GSYM IMAGE_UNIONS];
    ALL_TAC] THEN
  CONJ_TAC THEN GEN_TAC THEN
  ASM_CASES_TAC `lf_simplicial_complex (c:(real^M->bool)->bool)` THEN
  ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [FUN_EQ_THM] THEN X_GEN_TAC `v:real^M` THEN
  ASM_CASES_TAC `{v:real^M} IN c` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`h:real^M->real^N`;
                 `UNIONS (simplicial_link c (v:real^M))`; `n - 1`]
    MOI_FM3_PL_LINEAR_IMAGE_EQ) THEN
  (ANTS_TAC THENL
    [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FM3_LINK_POLYHEDRON THEN
     ASM_REWRITE_TAC[];
     SIMP_TAC[]]));;

(* The combinatorial boundary, for locally finite complexes.                *)

let MOI_FM3_COFACES_LINEAR_IMAGE = prove
 (`!(h:real^M->real^N) c s n.
        linear h /\ (!x y. h x = h y ==> x = y)
        ==> {r' | r' IN IMAGE (IMAGE h) c /\ aff_dim r' = n /\
                  IMAGE h s SUBSET r'} =
            IMAGE (IMAGE h) {r | r IN c /\ aff_dim r = n /\ s SUBSET r}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `h:real^M->real^N` MOI_FM3_LINEAR_IMAGE_RULES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `r':real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `r:real^M->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real^M->bool` THEN
    UNDISCH_TAC `aff_dim(r':real^N->bool) = n` THEN
    UNDISCH_TAC `IMAGE (h:real^M->real^N) s SUBSET r'` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `r:real^M->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_FM3_CARD_COFACES_LINEAR_IMAGE = prove
 (`!(h:real^M->real^N) c s n.
        linear h /\ (!x y. h x = h y ==> x = y) /\ lf_simplicial_complex c /\
        s IN c /\ ~(s = {})
        ==> CARD {r' | r' IN IMAGE (IMAGE h) c /\ aff_dim r' = n /\
                       IMAGE h s SUBSET r'} =
            CARD {r | r IN c /\ aff_dim r = n /\ s SUBSET r}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `h:real^M->real^N` MOI_FM3_LINEAR_IMAGE_RULES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `c:(real^M->bool)->bool`;
                 `s:real^M->bool`; `n:int`] MOI_FM3_COFACES_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^M` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{t:real^M->bool | t IN c /\ x IN t}` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FM3_STAR_FINITE THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[];
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `r:real^M->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^M) IN s` THEN UNDISCH_TAC `(s:real^M->bool) SUBSET r` THEN
    SET_TAC[]]);;

let MOI_FM3_IMAGE_RESTRICT = prove
 (`!(f:A->B) c P Q.
        (!s. s IN c ==> (Q (f s) <=> P s))
        ==> {y | y IN IMAGE f c /\ Q y} = IMAGE f {x | x IN c /\ P x}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
  ASM_MESON_TAC[]);;

let MOI_FM3_CB_LINEAR_IMAGE = prove
 (`!(h:real^M->real^N) c.
        linear h /\ (!x y. h x = h y ==> x = y) /\ lf_simplicial_complex c
        ==> complex_boundary (IMAGE (IMAGE h) c) =
            IMAGE h (complex_boundary c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `h:real^M->real^N` MOI_FM3_LINEAR_IMAGE_RULES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[complex_boundary; IMAGE_UNIONS] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC MOI_FM3_IMAGE_RESTRICT THEN
  X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `aff_dim(s:real^M->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(s:real^M->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^M->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^M->real^N`; `c:(real^M->bool)->bool`;
                 `s:real^M->bool`; `&3:int`]
    MOI_FM3_CARD_COFACES_LINEAR_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

(* Orientability.                                                            *)

let MOI_FM3_TET_PUSH = prove
 (`!(h:real^M->real^N) c a b d e.
        linear h /\ (!x y. h x = h y ==> x = y) /\
        convex hull {a,b,d,e} IN c /\ aff_dim(convex hull {a,b,d,e}) = &3
        ==> convex hull {h a,h b,h d,h e} IN IMAGE (IMAGE h) c /\
            aff_dim(convex hull {h a,h b,h d,h e}) = &3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `h:real^M->real^N` MOI_FM3_LINEAR_IMAGE_RULES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{(h:real^M->real^N) a,h b,h d,h e} = IMAGE h {a,b,d,e}`
  SUBST1_TAC THENL [REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]);;

let MOI_FM3_TET_PULL = prove
 (`!(h:real^M->real^N) g c a b d e.
        linear h /\ (!x y. h x = h y ==> x = y) /\ (!x. g (h x) = x) /\
        convex hull {a,b,d,e} IN IMAGE (IMAGE h) c /\
        aff_dim(convex hull {a,b,d,e}) = &3
        ==> convex hull {g a,g b,g d,g e} IN c /\
            aff_dim(convex hull {g a,g b,g d,g e}) = &3 /\
            h (g a) = a /\ h (g b) = b /\ h (g d) = d /\ h (g e) = e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `h:real^M->real^N` MOI_FM3_LINEAR_IMAGE_RULES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `convex hull {a,b,d,e} IN IMAGE (IMAGE (h:real^M->real^N)) c` THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `(h:real^M->real^N) ((g:real^N->real^M) a) = a /\ h (g b) = b /\
    h (g d) = d /\ h (g e) = e`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `{a,b,d,e} SUBSET IMAGE (h:real^M->real^N) t` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && is_comb(rand(concl th)) &&
        rator(rand(concl th)) = `IMAGE (h:real^M->real^N)`)) THEN
      REWRITE_TAC[HULL_SUBSET];
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_IMAGE] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {a,b,d,e} =
    IMAGE (h:real^M->real^N)
          (convex hull {(g:real^N->real^M) a,g b,g d,g e})`
  ASSUME_TAC THENL
   [UNDISCH_THEN `(!s. convex hull IMAGE (h:real^M->real^N) s =
                       IMAGE h (convex hull s))`
      (fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {(g:real^N->real^M) a,g b,g d,g e} =
                (t:real^M->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `convex hull {a,b,d,e} = IMAGE (h:real^M->real^N) t` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(convex hull {a,b,d,e:real^N}) = &3` THEN
  UNDISCH_TAC `convex hull {a,b,d,e} = IMAGE (h:real^M->real^N) t` THEN
  DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_FM3_ORIENT_LINEAR_IMAGE = prove
 (`!(h:real^M->real^N) c.
        linear h /\ (!x y. h x = h y ==> x = y)
        ==> (orientable_complex (IMAGE (IMAGE h) c) <=> orientable_complex c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `h:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^M. (g:real^N->real^M) ((h:real^M->real^N) x) = x`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[o_THM; I_THM];
    ALL_TAC] THEN
  REWRITE_TAC[orientable_complex] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `sg:real^N->real^N->real^N->real^N->real`
      (CONJUNCTS_THEN2 (LABEL_TAC "p1") (LABEL_TAC "p2"))) THEN
    EXISTS_TAC `\a b d e:real^M. (sg:real^N->real^N->real^N->real^N->real)
                                  (h a) (h b) (h d) (h e)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`h:real^M->real^N`; `c:(real^M->bool)->bool`;
                     `a:real^M`; `b:real^M`; `d:real^M`; `e:real^M`]
        MOI_FM3_TET_PUSH) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "p1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`h:real^M->real^N`; `c:(real^M->bool)->bool`;
                     `a:real^M`; `b:real^M`; `d:real^M`; `e:real^M`]
        MOI_FM3_TET_PUSH) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`h:real^M->real^N`; `c:(real^M->bool)->bool`;
                     `a:real^M`; `b:real^M`; `d:real^M`; `e':real^M`]
        MOI_FM3_TET_PUSH) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((h:real^M->real^N) e = h e')` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(e:real^M = e')` THEN REWRITE_TAC[] THEN
        UNDISCH_TAC `(h:real^M->real^N) e = h e'` THEN
        UNDISCH_TAC `!x y. (h:real^M->real^N) x = h y ==> x = y` THEN
        MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "p2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `sg:real^M->real^M->real^M->real^M->real`
      (CONJUNCTS_THEN2 (LABEL_TAC "p1") (LABEL_TAC "p2"))) THEN
    EXISTS_TAC `\a b d e:real^N. (sg:real^M->real^M->real^M->real^M->real)
                                  (g a) (g b) (g d) (g e)` THEN
    REWRITE_TAC[] THEN CONJ_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
     [MP_TAC(ISPECL [`h:real^M->real^N`; `g:real^N->real^M`;
                     `c:(real^M->bool)->bool`; `a:real^N`; `b:real^N`;
                     `d:real^N`; `e:real^N`] MOI_FM3_TET_PULL) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "p1" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`h:real^M->real^N`; `g:real^N->real^M`;
                     `c:(real^M->bool)->bool`; `a:real^N`; `b:real^N`;
                     `d:real^N`; `e:real^N`] MOI_FM3_TET_PULL) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`h:real^M->real^N`; `g:real^N->real^M`;
                     `c:(real^M->bool)->bool`; `a:real^N`; `b:real^N`;
                     `d:real^N`; `e':real^N`] MOI_FM3_TET_PULL) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((g:real^N->real^M) e = g e')` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(e:real^N = e')` THEN REWRITE_TAC[] THEN
        UNDISCH_TAC `(h:real^M->real^N) ((g:real^N->real^M) e) = e` THEN
        UNDISCH_TAC `(h:real^M->real^N) ((g:real^N->real^M) e') = e'` THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "p2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

(* Assembly.  The statement of COMPLEX_INJECTIVE_LINEAR_IMAGE (term         *)
(* MOI_FND_LINEAR_IMAGE_COMPLEX) has no local finiteness hypothesis; its    *)
(* complex_boundary clause compares CARD of sets of tetrahedra on a         *)
(* triangle, which may be infinite when c is not locally finite, and CARD  *)
(* is unspecified on infinite sets.  We prove the full statement for        *)
(* locally finite c, and every clause but the boundary one in general.     *)

let MOI_FM3_LINEAR_IMAGE_COMPLEX_LF = prove
 (`!(f:real^M->real^N) (c:(real^M->bool)->bool).
     linear f /\ (!x y. f x = f y ==> x = y) /\ lf_simplicial_complex c
     ==> (lf_simplicial_complex (IMAGE (IMAGE f) c) <=>
          lf_simplicial_complex c) /\
         (FINITE (IMAGE (IMAGE f) c) <=> FINITE c) /\
         (!n. combinatorial_manifold n (IMAGE (IMAGE f) c) <=>
              combinatorial_manifold n c) /\
         (!n. combinatorial_manifold_with_boundary n (IMAGE (IMAGE f) c) <=>
              combinatorial_manifold_with_boundary n c) /\
         complex_boundary (IMAGE (IMAGE f) c) = IMAGE f (complex_boundary c) /\
         (orientable_complex (IMAGE (IMAGE f) c) <=> orientable_complex c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_LINEAR_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
    ASM_MESON_TAC[MOI_FM3_INJ_IMAGE_EQ];
    MP_TAC(ISPECL [`f:real^M->real^N`; `c:(real^M->bool)->bool`]
      MOI_FM3_CM_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`f:real^M->real^N`; `c:(real^M->bool)->bool`]
      MOI_FM3_CM_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MATCH_MP_TAC MOI_FM3_CB_LINEAR_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FM3_ORIENT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[]]);;

let MOI_FM3_LINEAR_IMAGE_COMPLEX_GEN = prove
 (`!(f:real^M->real^N) (c:(real^M->bool)->bool).
     linear f /\ (!x y. f x = f y ==> x = y)
     ==> (lf_simplicial_complex (IMAGE (IMAGE f) c) <=>
          lf_simplicial_complex c) /\
         (FINITE (IMAGE (IMAGE f) c) <=> FINITE c) /\
         (!n. combinatorial_manifold n (IMAGE (IMAGE f) c) <=>
              combinatorial_manifold n c) /\
         (!n. combinatorial_manifold_with_boundary n (IMAGE (IMAGE f) c) <=>
              combinatorial_manifold_with_boundary n c) /\
         (lf_simplicial_complex c
          ==> complex_boundary (IMAGE (IMAGE f) c) =
              IMAGE f (complex_boundary c)) /\
         (orientable_complex (IMAGE (IMAGE f) c) <=> orientable_complex c)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_LINEAR_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC FINITE_IMAGE_INJ_EQ THEN
    ASM_MESON_TAC[MOI_FM3_INJ_IMAGE_EQ];
    MP_TAC(ISPECL [`f:real^M->real^N`; `c:(real^M->bool)->bool`]
      MOI_FM3_CM_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    MP_TAC(ISPECL [`f:real^M->real^N`; `c:(real^M->bool)->bool`]
      MOI_FM3_CM_LINEAR_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    DISCH_TAC THEN MATCH_MP_TAC MOI_FM3_CB_LINEAR_IMAGE THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FM3_ORIENT_LINEAR_IMAGE THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Why the statement term MOI_FND_LINEAR_IMAGE_COMPLEX is not provable as    *)
(* stated. Its complex_boundary clause, for M = N = 3, already implies that  *)
(* for any family tt of tetrahedra on a common triangle s0, CARD of the      *)
(* image of tt under the scaling by 2 is 1 exactly when CARD tt = 1. For an  *)
(* infinite tt this compares CARD of two infinite sets, and CARD is defined  *)
(* through ITSET, which is specified only on finite sets; so the statement   *)
(* is not provable without a local finiteness hypothesis (which              *)
(* MOI_FM3_LINEAR_IMAGE_COMPLEX_LF adds).                                    *)
(* ========================================================================= *)

let MOI_FM3_CB_INSERT = prove
 (`!(c:(real^N->bool)->bool) t.
        aff_dim t = &2 /\ (!r. r IN c ==> aff_dim r = &3 /\ t SUBSET r)
        ==> complex_boundary (t INSERT c) = if CARD c = 1 then t else {}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN c ==> ~(r = t)` ASSUME_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `!r:real^N->bool. r IN c ==> aff_dim r = &3 /\ t SUBSET r` THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{r | r IN t INSERT c /\ aff_dim r = &3 /\ t SUBSET r} =
    (c:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN
    ASM_CASES_TAC `(r:real^N->bool) IN c` THEN ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[];
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      UNDISCH_TAC `aff_dim(r:real^N->bool) = &3` THEN
      UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
      UNDISCH_TAC `r:real^N->bool = t` THEN
      DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{s | s IN t INSERT c /\ aff_dim s = &2 /\
         CARD {r | r IN t INSERT c /\ aff_dim r = &3 /\ s SUBSET r} = 1} =
    if CARD (c:(real^N->bool)->bool) = 1 then {t} else {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    GEN_REWRITE_TAC (LAND_CONV o LAND_CONV) [IN_INSERT] THEN
    ASM_CASES_TAC `s:real^N->bool = t` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY];
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `~((s:real^N->bool) IN c /\ aff_dim s = &2)` ASSUME_TAC THENL
       [STRIP_TAC THEN
        UNDISCH_TAC `!r:real^N->bool. r IN c ==> aff_dim r = &3 /\ t SUBSET r` THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      COND_CASES_TAC THEN ASM_REWRITE_TAC[IN_SING; NOT_IN_EMPTY] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[complex_boundary] THEN
  COND_CASES_TAC THEN REWRITE_TAC[UNIONS_1; UNIONS_0]);;

let MOI_FM3_TARGET5_CARD = prove
 (mk_imp(inst [`:3`,`:M`; `:3`,`:N`] MOI_FND_LINEAR_IMAGE_COMPLEX,
   `!s0 (tt:(real^3->bool)->bool).
        aff_dim s0 = &2 /\ (!r. r IN tt ==> aff_dim r = &3 /\ s0 SUBSET r)
        ==> (CARD (IMAGE (IMAGE (\x:real^3. &2 % x)) tt) = 1 <=> CARD tt = 1)`),
  DISCH_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `linear (\x:real^3. &2 % x) /\
    (!x y. (\x:real^3. &2 % x) x = (\x:real^3. &2 % x) y ==> x = y)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[linear] THEN VECTOR_ARITH_TAC;
      REPEAT GEN_TAC THEN REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN REWRITE_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`\x:real^3. &2 % x`;
                                `(s0:real^3->bool) INSERT tt`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
             CONJUNCT2) THEN
  MP_TAC(ISPEC `\x:real^3. &2 % x` MOI_FM3_LINEAR_IMAGE_RULES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(s0:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(s0:real^3->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN
  MP_TAC(ISPECL [`tt:(real^3->bool)->bool`; `s0:real^3->bool`]
    MOI_FM3_CB_INSERT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`IMAGE (IMAGE (\x:real^3. &2 % x)) tt`;
                 `IMAGE (\x:real^3. &2 % x) s0`] MOI_FM3_CB_INSERT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[FORALL_IN_IMAGE]; DISCH_THEN SUBST1_TAC] THEN
  REPEAT COND_CASES_TAC THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; IMAGE_EQ_EMPTY] THEN
  ASM_MESON_TAC[IMAGE_EQ_EMPTY]);;

