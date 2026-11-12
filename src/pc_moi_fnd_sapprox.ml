needs "src/pc_moi_fnd_stmt5.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_fnd_sapprox: SIMPLICIAL_APPROX, the simplicial approximation       *)
(* theorem relative to a full subcomplex (the statement term                 *)
(* MOI_FND_SIMPLICIAL_APPROX of pc_moi_fnd_stmt5). Route:                    *)
(*   1. carriers in a simplicial complex: every point of the polyhedron     *)
(*      lies in the relative interior of a simplex, contained in every      *)
(*      simplex through the point;                                          *)
(*   2. affine extensions of vertex values on affinely independent sets;    *)
(*   3. the simplicial map of a vertex map, glued by the pasting lemma;     *)
(*   4. the star condition: phi v lies in every simplex of l through f x,   *)
(*      for every x all of whose simplices contain v;                       *)
(*   5. vertex choices from a Lebesgue number of the cover of the compact  *)
(*      image by the open vertex stars of l (stars of vertices outside the *)
(*      full subcomplex near the compact set), uniform continuity and fine *)
(*      iterated barycentric subdivisions;                                  *)
(*   6. the relative clause, and the straight-line homotopy in carriers.    *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* 1. Simplicial complex facts: iterated subdivisions, carriers, vertices.   *)
(* ------------------------------------------------------------------------- *)

let MOI_FSAP_ITER = prove
 (`!(k:(real^N->bool)->bool) n.
     simplicial_complex k
     ==> simplicial_complex (ITER n barycentric_subdivision k) /\
         UNIONS (ITER n barycentric_subdivision k) = UNIONS k`,
  GEN_TAC THEN REWRITE_TAC[RIGHT_FORALL_IMP_THM] THEN DISCH_TAC THEN
  INDUCT_TAC THEN ASM_REWRITE_TAC[ITER] THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC (SUBST1_TAC o SYM)) THEN
  MATCH_MP_TAC MOI_BAR_UNIONS_SUBDIVISION THEN
  ASM_MESON_TAC[MOI_BAR_SIMPLICIAL_COMPLEX]);;

let MOI_FSAP_CARRIER = prove
 (`!(k:(real^N->bool)->bool) x.
     simplicial_complex k /\ x IN UNIONS k
     ==> ?s. s IN k /\ x IN relative_interior s`,
  REWRITE_TAC[IN_UNIONS] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `x:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  ASM_MESON_TAC[simplicial_complex]);;

let MOI_FSAP_RELINT_SUBSET = prove
 (`!(k:(real^N->bool)->bool) s t x.
     simplicial_complex k /\ s IN k /\ t IN k /\
     x IN relative_interior s /\ x IN t
     ==> s SUBSET t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t INTER s:real^N->bool) face_of s` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_CASES_TAC `t INTER s:real^N->bool = s` THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t INTER s:real^N->bool`; `s:real^N->bool`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  ASM SET_TAC[]);;

let MOI_FSAP_CARRIER_MIN = prove
 (`!(l:(real^N->bool)->bool) y.
     simplicial_complex l /\ y IN UNIONS l
     ==> ?s. s IN l /\ y IN relative_interior s /\ y IN s /\
             !t. t IN l /\ y IN t ==> s SUBSET t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `y:real^N`] MOI_FSAP_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ASM_MESON_TAC[MOI_FSAP_RELINT_SUBSET]]);;

let MOI_FSAP_VERTEX_EXTREME = prove
 (`!(l:(real^N->bool)->bool) s w.
     simplicial_complex l /\ {w} IN l /\ s IN l /\ w IN s
     ==> w extreme_point_of s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
  SUBGOAL_THEN `{w:real^N} = {w} INTER s` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[simplicial_complex]]);;

let MOI_FSAP_SIMPLEX_VERTICES = prove
 (`!(k:(real^N->bool)->bool) s.
     simplicial_complex k /\ s IN k
     ==> ?V. ~affine_dependent V /\ FINITE V /\ s = convex hull V /\
             {v | v extreme_point_of s} = V /\
             (!v. v extreme_point_of s <=> v IN V) /\
             (!v. v IN V ==> {v} IN k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int`
    (X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `V:real^N->bool` THEN
  SUBGOAL_THEN `!v:real^N. v extreme_point_of s <=> v IN V` ASSUME_TAC THENL
   [ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]; ALL_TAC] THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `{v:real^N} face_of s` ASSUME_TAC THENL
     [ASM_MESON_TAC[FACE_OF_SING]; ASM_MESON_TAC[simplicial_complex]]]);;

let MOI_FSAP_HULL_IN = prove
 (`!(l:(real^N->bool)->bool) s w.
     simplicial_complex l /\ s IN l /\ w SUBSET s /\ (!v. v IN w ==> {v} IN l)
     ==> convex hull w IN l /\ ~affine_dependent w /\ FINITE w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_FSAP_SIMPLEX_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N->bool) SUBSET V` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^N) extreme_point_of s` MP_TAC THENL
     [MATCH_MP_TAC MOI_FSAP_VERTEX_EXTREME THEN
      EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_SIMP_TAC[] THEN
      ASM SET_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(convex hull w:real^N->bool) face_of s` MP_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[simplicial_complex]] THEN
    UNDISCH_TAC `s:real^N->bool = convex hull V` THEN
    DISCH_THEN SUBST1_TAC THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `w:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET];
    ASM_MESON_TAC[FINITE_SUBSET]]);;

let MOI_FSAP_EMPTY_IN = prove
 (`!(l:(real^N->bool)->bool). simplicial_complex l /\ ~(l = {}) ==> {} IN l`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `s:real^N->bool` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  ASM_MESON_TAC[simplicial_complex; EMPTY_FACE_OF]);;

(* ------------------------------------------------------------------------- *)
(* 2. Affine maps x -> L x + y: extension from affinely independent vertex   *)
(* sets, agreement on convex hulls, images of hulls and relative interiors.  *)
(* ------------------------------------------------------------------------- *)

let MOI_FSAP_AFFINE_EXTEND = prove
 (`!(V:real^M->bool) (phi:real^M->real^N).
     ~affine_dependent V
     ==> ?L y. linear L /\ !v. v IN V ==> L v + y = phi v`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `V:real^M->bool = {}` THENL
   [MAP_EVERY EXISTS_TAC [`\x:real^M. vec 0:real^N`; `vec 0:real^N`] THEN
    ASM_REWRITE_TAC[NOT_IN_EMPTY; LINEAR_ZERO];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `a:real^M` o
    GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `independent (IMAGE (\x:real^M. x - a) (V DELETE a))`
  ASSUME_TAC THENL
   [REWRITE_TAC[independent] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`a:real^M`; `(V:real^M->bool) DELETE a`]
      DEPENDENT_IMP_AFFINE_DEPENDENT) THEN
    ASM_REWRITE_TAC[IN_DELETE; SIMPLE_IMAGE] THEN
    SUBGOAL_THEN `(a:real^M) INSERT (V DELETE a) = V`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\z:real^M. (phi:real^M->real^N)(z + a) - phi a`;
                 `IMAGE (\x:real^M. x - a) (V DELETE a)`]
    LINEAR_INDEPENDENT_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^M->real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`L:real^M->real^N`; `(phi:real^M->real^N) a - L a`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN
  ASM_CASES_TAC `v:real^M = a` THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v - a:real^M`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE; IN_DELETE] THEN EXISTS_TAC `v:real^M` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[LINEAR_SUB; VECTOR_SUB_ADD] THEN VECTOR_ARITH_TAC);;

let MOI_FSAP_AFFINE_VSUM = prove
 (`!(L:real^M->real^N) y w u.
     linear L /\ FINITE w /\ sum w u = &1
     ==> L (vsum w (\v. u v % v)) + y = vsum w (\v. u v % (L v + y))`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[LINEAR_VSUM; o_DEF; LINEAR_CMUL; VECTOR_ADD_LDISTRIB;
               VSUM_ADD; VSUM_RMUL; VECTOR_MUL_LID]);;

let MOI_FSAP_AFFINE_AGREE = prove
 (`!(L1:real^M->real^N) L2 y1 y2 w x.
     linear L1 /\ linear L2 /\ FINITE w /\
     (!v. v IN w ==> L1 v + y1 = L2 v + y2) /\ x IN convex hull w
     ==> L1 x + y1 = L2 x + y2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^M) IN convex hull w` THEN
  ASM_SIMP_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^M->real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  ASM_SIMP_TAC[MOI_FSAP_AFFINE_VSUM] THEN
  MATCH_MP_TAC VSUM_EQ THEN ASM_SIMP_TAC[]);;

let MOI_FSAP_AFFINE_IMAGE_SPLIT = prove
 (`!(L:real^M->real^N) y t.
     IMAGE (\x. L x + y) t = IMAGE (\x. y + x) (IMAGE L t)`,
  REWRITE_TAC[EXTENSION; IN_IMAGE] THEN MESON_TAC[VECTOR_ADD_SYM]);;

let MOI_FSAP_AFFINE_HULL_IMAGE = prove
 (`!(L:real^M->real^N) y s.
     linear L
     ==> IMAGE (\x. L x + y) (convex hull s) =
         convex hull (IMAGE (\x. L x + y) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_FSAP_AFFINE_IMAGE_SPLIT] THEN
  ASM_SIMP_TAC[CONVEX_HULL_TRANSLATION; CONVEX_HULL_LINEAR_IMAGE]);;

let MOI_FSAP_AFFINE_RELINT_IMAGE = prove
 (`!(L:real^M->real^N) y s.
     linear L /\ convex s
     ==> IMAGE (\x. L x + y) (relative_interior s) =
         relative_interior (IMAGE (\x. L x + y) s)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[MOI_FSAP_AFFINE_IMAGE_SPLIT] THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_TRANSLATION;
               RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX]);;

let MOI_FSAP_AGREE_INTER = prove
 (`!(k:(real^M->bool)->bool) s t (L1:real^M->real^N) L2 y1 y2 x.
     simplicial_complex k /\ s IN k /\ t IN k /\ linear L1 /\ linear L2 /\
     (!v. v extreme_point_of s /\ v extreme_point_of t
          ==> L1 v + y1 = L2 v + y2) /\
     x IN s /\ x IN t
     ==> L1 x + y1 = L2 x + y2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s INTER t:real^M->bool) face_of s /\ (s INTER t) face_of t`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (s:real^M->bool) /\ compact s /\ convex (t:real^M->bool) /\
                compact t`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {v:real^M | v extreme_point_of s}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `s:real^M->bool`]
      MOI_FSAP_SIMPLEX_VERTICES) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^M. v extreme_point_of (s INTER t)
               ==> v extreme_point_of s /\ v extreme_point_of t`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`s INTER t:real^M->bool`; `s:real^M->bool`; `v:real^M`]
        EXTREME_POINT_OF_FACE);
      MP_TAC(ISPECL [`s INTER t:real^M->bool`; `t:real^M->bool`; `v:real^M`]
        EXTREME_POINT_OF_FACE)] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FSAP_AFFINE_AGREE THEN
  EXISTS_TAC `{v:real^M | v extreme_point_of (s INTER t)}` THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{v:real^M | v extreme_point_of s}` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[];
    SUBGOAL_THEN
     `s INTER t = convex hull {v:real^M | v extreme_point_of (s INTER t)}`
      (fun th -> REWRITE_TAC[GSYM th] THEN ASM SET_TAC[]) THEN
    MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
    ASM_SIMP_TAC[CONVEX_INTER; COMPACT_INTER]]);;

(* ------------------------------------------------------------------------- *)
(* 3. The simplicial map of a vertex map: affine extensions on the simplices *)
(* glued by the pasting lemma.  The hypothesis on the vertex map is that the *)
(* images of the vertices of each simplex of k are vertices of l lying in a  *)
(* common simplex of l.                                                      *)
(* ------------------------------------------------------------------------- *)

let MOI_FSAP_AFFINE_PIECES = prove
 (`!(k:(real^M->bool)->bool) (phi:real^M->real^N).
     simplicial_complex k
     ==> ?LL:(real^M->bool)->real^M->real^N. ?YY:(real^M->bool)->real^N.
           !s. s IN k ==> linear (LL s) /\
                          !v. v extreme_point_of s ==> LL s v + YY s = phi v`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM SKOLEM_THM] THEN
  X_GEN_TAC `s:real^M->bool` THEN REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `s:real^M->bool`]
    MOI_FSAP_SIMPLEX_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^M->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:real^M->bool`; `phi:real^M->real^N`]
    MOI_FSAP_AFFINE_EXTEND) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN ASM_SIMP_TAC[]);;

let MOI_FSAP_GLUE = prove
 (`!(k:(real^M->bool)->bool) (LL:(real^M->bool)->real^M->real^N) YY.
     simplicial_complex k /\
     (!s. s IN k ==> linear (LL s)) /\
     (!s t v. s IN k /\ t IN k /\ v extreme_point_of s /\ v extreme_point_of t
              ==> LL s v + YY s = LL t v + YY t)
     ==> ?g. g continuous_on UNIONS k /\
             !s x. s IN k /\ x IN s ==> g x = LL s x + YY s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(BETA_RULE(ISPECL
   [`subtopology euclidean (UNIONS k:real^M->bool)`; `euclidean:(real^N)topology`;
    `\s:real^M->bool. \x. (LL:(real^M->bool)->real^M->real^N) s x + YY s`;
    `\s:real^M->bool. s`; `k:(real^M->bool)->bool`]
   PASTING_LEMMA_EXISTS_CLOSED)) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; SUBTOPOLOGY_SUBTOPOLOGY;
              CONTINUOUS_MAP_EUCLIDEAN] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_SUBSET THEN CONJ_TAC THENL
         [ASM SET_TAC[];
          ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT;
                        COMPACT_IMP_CLOSED]];
        MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
        MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN ASM_SIMP_TAC[ETA_AX]];
      MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `t:real^M->bool`; `x:real^M`] THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_FSAP_AGREE_INTER THEN
      MAP_EVERY EXISTS_TAC [`k:(real^M->bool)->bool`; `s:real^M->bool`;
                            `t:real^M->bool`] THEN
      ASM_SIMP_TAC[ETA_AX] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`s:real^M->bool`; `x:real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
  ASM SET_TAC[]);;

let MOI_FSAP_EXTEND = prove
 (`!(k:(real^M->bool)->bool) (l:(real^N->bool)->bool) (phi:real^M->real^N).
     simplicial_complex k /\ simplicial_complex l /\
     (!v. {v} IN k ==> {phi v} IN l) /\
     (!s. s IN k ==> ?t. t IN l /\ !v. v extreme_point_of s ==> phi v IN t)
     ==> ?g. g continuous_on UNIONS k /\ simplicial_map_on k l g /\
             (!v. {v} IN k ==> g v = phi v) /\
             (!s. s IN k
                  ==> IMAGE g s =
                      convex hull (IMAGE phi {v | v extreme_point_of s}) /\
                      IMAGE g (relative_interior s) =
                      relative_interior
                       (convex hull (IMAGE phi {v | v extreme_point_of s})))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `phi:real^M->real^N`]
    MOI_FSAP_AFFINE_PIECES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `LL:(real^M->bool)->real^M->real^N`
    (X_CHOOSE_TAC `YY:(real^M->bool)->real^N`)) THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `LL:(real^M->bool)->real^M->real^N`;
                 `YY:(real^M->bool)->real^N`] MOI_FSAP_GLUE) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!s. s IN k
        ==> IMAGE (g:real^M->real^N) s =
            convex hull (IMAGE phi {v | v extreme_point_of s}) /\
            IMAGE g (relative_interior s) =
            relative_interior (convex hull (IMAGE phi {v | v extreme_point_of s}))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `s:real^M->bool`]
      MOI_FSAP_SIMPLEX_VERTICES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^M->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `s:real^M->bool`)) THEN
    SUBGOAL_THEN
     `linear ((LL:(real^M->bool)->real^M->real^N) (convex hull V)) /\
      (!v. v IN V
           ==> LL (convex hull V) v + YY (convex hull V) = (phi:real^M->real^N) v)`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `convex hull V:real^M->bool` o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `YY:(real^M->bool)->real^N`)) (concl th) &&
        not (can (find_term ((=) `g:real^M->real^N`)) (concl th)))) THEN
      REWRITE_TAC[ASSUME `convex hull V:real^M->bool IN k`;
                  ASSUME `!v:real^M. v extreme_point_of convex hull V <=> v IN V`];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!t. t SUBSET convex hull V
          ==> IMAGE (g:real^M->real^N) t =
              IMAGE (\x. LL (convex hull V:real^M->bool) x + YY (convex hull V)) t`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC IMAGE_EQ THEN
      X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN BETA_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) &&
        can (find_term ((=) `g:real^M->real^N`)) (concl th))) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `{v:real^M | v extreme_point_of convex hull V} = V` THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `IMAGE (phi:real^M->real^N) V =
                  IMAGE (\x. LL (convex hull V:real^M->bool) x + YY (convex hull V)) V`
    SUBST1_TAC THENL
     [MATCH_MP_TAC IMAGE_EQ THEN BETA_TAC THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM(MATCH_MP MOI_FSAP_AFFINE_HULL_IMAGE
      (ASSUME `linear ((LL:(real^M->bool)->real^M->real^N) (convex hull V))`))] THEN
    ASM_SIMP_TAC[SUBSET_REFL; RELATIVE_INTERIOR_SUBSET] THEN
    MATCH_MP_TAC MOI_FSAP_AFFINE_RELINT_IMAGE THEN
    ASM_REWRITE_TAC[CONVEX_CONVEX_HULL; ETA_AX];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[simplicial_map_on] THEN X_GEN_TAC `s:real^M->bool` THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^M->bool` o check (fun th ->
        can (find_term ((=) `l:(real^N->bool)->bool`)) (concl th) &&
        is_forall (concl th) &&
        not (can (find_term ((=) `g:real^M->real^N`)) (concl th)))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`;
                     `IMAGE (phi:real^M->real^N) {v | v extreme_point_of s}`]
        MOI_FSAP_HULL_IN) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ASSUME `!v:real^M. {v} IN k ==> {(phi:real^M->real^N) v} IN l`) THEN
      MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `s:real^M->bool`]
        MOI_FSAP_SIMPLEX_VERTICES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `V:real^M->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(v:real^M) extreme_point_of s` THEN ASM_REWRITE_TAC[];
      MAP_EVERY EXISTS_TAC [`(LL:(real^M->bool)->real^M->real^N) s`;
                            `(YY:(real^M->bool)->real^N) s`] THEN
      ASM_SIMP_TAC[]];
    X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`{v:real^M}`; `v:real^M`] o check (fun th ->
      can (find_term ((=) `g:real^M->real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
    ASM_MESON_TAC[EXTREME_POINT_OF_SING]]);;

(* ------------------------------------------------------------------------- *)
(* 4. The star condition.  A vertex map phi satisfies it for f when phi v is *)
(* a vertex of l lying in every simplex of l through f x, for every x all   *)
(* of whose simplices in k contain v (x in the open star of v).  Then the   *)
(* simplicial map of phi maps x into every simplex of l through f x, and    *)
(* into the relative interior of the image of the carrier of x.              *)
(* ------------------------------------------------------------------------- *)

let MOI_FSAP_RELINT_STAR = prove
 (`!(k:(real^N->bool)->bool) r x v.
     simplicial_complex k /\ r IN k /\ x IN relative_interior r /\
     v extreme_point_of r
     ==> x IN UNIONS k /\ (!t. t IN k /\ x IN t ==> v IN t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN r /\ (v:real^N) IN r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; extreme_point_of];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) SUBSET t` MP_TAC THENL
   [MATCH_MP_TAC MOI_FSAP_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`k:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let MOI_FSAP_STAR_MAP = prove
 (`!(k:(real^M->bool)->bool) (l:(real^N->bool)->bool) (f:real^M->real^N)
    (phi:real^M->real^N).
     simplicial_complex k /\ simplicial_complex l /\ ~(l = {}) /\
     IMAGE f (UNIONS k) SUBSET UNIONS l /\
     (!v. {v} IN k
          ==> {phi v} IN l /\
              !x. x IN UNIONS k /\ (!t. t IN k /\ x IN t ==> v IN t)
                  ==> !s. s IN l /\ f x IN s ==> phi v IN s)
     ==> ?g. g continuous_on UNIONS k /\ simplicial_map_on k l g /\
             (!x s. x IN UNIONS k /\ s IN l /\ f x IN s ==> g x IN s) /\
             (!x. x IN UNIONS k
                  ==> ?r. r IN k /\ x IN relative_interior r /\
                          g x IN relative_interior
                                  (convex hull
                                    (IMAGE phi {v | v extreme_point_of r})))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!r x s v. r IN k /\ x IN relative_interior r /\
              s IN l /\ (f:real^M->real^N) x IN s /\ v extreme_point_of r
              ==> (phi:real^M->real^N) v IN s`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `r:real^M->bool`; `x:real^M`;
                   `v:real^M`] MOI_FSAP_RELINT_STAR) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `{v:real^M} IN k` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `r:real^M->bool`]
        MOI_FSAP_SIMPLEX_VERTICES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `V:real^M->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(v:real^M) extreme_point_of r` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^M` o check (fun th ->
      can (find_term ((=) `phi:real^M->real^N`)) (concl th) &&
      can (find_term ((=) `f:real^M->real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `l:(real^N->bool)->bool`;
                 `phi:real^M->real^N`] MOI_FSAP_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN X_GEN_TAC `r:real^M->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `r:real^M->bool = {}` THENL
     [EXISTS_TAC `{}:real^N->bool` THEN
      ASM_SIMP_TAC[MOI_FSAP_EMPTY_IN; extreme_point_of; NOT_IN_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `?x:real^M. x IN relative_interior r` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
      SUBGOAL_THEN `convex (r:real^M->bool)` MP_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
        ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^M) IN UNIONS k` ASSUME_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; IN_UNIONS];
      ALL_TAC] THEN
    SUBGOAL_THEN `?s:real^N->bool. s IN l /\ (f:real^M->real^N) x IN s`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `r:real^M->bool` THEN EXISTS_TAC `x:real^M` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^M->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`x:real^M`; `s:real^N->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `x:real^M`] MOI_FSAP_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `IMAGE (g:real^M->real^N) r SUBSET s` MP_TAC THENL
     [ASM_SIMP_TAC[] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
        REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        EXISTS_TAC `r:real^M->bool` THEN EXISTS_TAC `x:real^M` THEN
        ASM_REWRITE_TAC[];
        ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]];
      MP_TAC(ISPEC `r:real^M->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[]];
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `x:real^M`] MOI_FSAP_CARRIER) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^M->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `IMAGE (g:real^M->real^N) (relative_interior r) =
      relative_interior (convex hull (IMAGE phi {v | v extreme_point_of r}))`
     (fun th -> REWRITE_TAC[GSYM th]) THENL
     [ASM_SIMP_TAC[]; ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 5. Vertex choices.  The open star of a vertex w of l is the trace on |l|  *)
(* of the open set of points lying in no simplex of l that misses w.  These *)
(* open sets cover |l| (carriers), and the ones of vertices outside a full   *)
(* subcomplex l0 cover the complement of |l0|.  Lebesgue numbers on compact *)
(* sets, uniform continuity of f and a small mesh of k' give phi.           *)
(* ------------------------------------------------------------------------- *)

let MOI_FSAP_STAR_OPEN = prove
 (`!(l:(real^N->bool)->bool) w.
     simplicial_complex l
     ==> open ((:real^N) DIFF UNIONS {t | t IN l /\ ~(w IN t)})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_UNIV] THEN
  MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED]]);;

let MOI_FSAP_STAR_COVER = prove
 (`!(l:(real^N->bool)->bool) y.
     simplicial_complex l /\ y IN UNIONS l
     ==> ?w. {w} IN l /\ !t. t IN l /\ y IN t ==> w IN t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `y:real^N`] MOI_FSAP_CARRIER_MIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?w:real^N. w extreme_point_of s` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
    CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `w:real^N` THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_FSAP_SIMPLEX_VERTICES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    UNDISCH_TAC `(w:real^N) extreme_point_of s` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET t` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(w:real^N) IN s` MP_TAC THENL
     [ASM_MESON_TAC[extreme_point_of]; SET_TAC[]]]);;

let MOI_FSAP_STAR_COVER_FULL = prove
 (`!(l:(real^N->bool)->bool) l0 y.
     simplicial_complex l /\ simplicial_subcomplex l0 l /\
     (!s. s IN l /\ ~(s = {}) /\ (!v. {v} IN l /\ v IN s ==> {v} IN l0) ==> s IN l0) /\
     y IN UNIONS l /\ ~(y IN UNIONS l0)
     ==> ?w. {w} IN l /\ ~({w} IN l0) /\ !t. t IN l /\ y IN t ==> w IN t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `y:real^N`] MOI_FSAP_CARRIER_MIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((s:real^N->bool) IN l0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((y:real^N) IN UNIONS l0)` THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^N. {w} IN l /\ w IN s /\ ~({w} IN l0)`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `?w:real^N. {w} IN l /\ w IN s /\ ~({w} IN l0)` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((s:real^N->bool) IN l0)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `l0:(real^N->bool)->bool`)) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET t` MP_TAC THENL
   [ASM_MESON_TAC[]; ASM SET_TAC[]]);;

let MOI_FSAP_LEBESGUE = prove
 (`!(l:(real^N->bool)->bool) (W:real^N->bool) S.
     simplicial_complex l /\ compact S /\
     (!y. y IN S ==> ?w. w IN W /\ !t. t IN l /\ y IN t ==> w IN t)
     ==> ?d. &0 < d /\
             !y. y IN S
                 ==> ?w. w IN W /\
                         !z t. dist(y,z) < d /\ t IN l /\ z IN t ==> w IN t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `S:real^N->bool` HEINE_BOREL_LEMMA) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE (\w. (:real^N) DIFF UNIONS {t | t IN l /\ ~(w IN t)}) W`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[MOI_FSAP_STAR_OPEN] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[EXISTS_IN_IMAGE] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`z:real^N`; `t:real^N->bool`] THEN STRIP_TAC THEN
  UNDISCH_TAC
   `ball(y:real^N,d) SUBSET (:real^N) DIFF UNIONS {t | t IN l /\ ~(w IN t)}` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let MOI_FSAP_VERTEX_CHOICE = prove
 (`!(k:(real^M->bool)->bool) (l:(real^N->bool)->bool) (l0:(real^N->bool)->bool)
    (f:real^M->real^N) (c:real^M->bool).
     simplicial_complex k /\ simplicial_complex l /\ simplicial_subcomplex l0 l /\
     (!s. s IN l /\ ~(s = {}) /\ (!v. {v} IN l /\ v IN s ==> {v} IN l0)
          ==> s IN l0) /\
     f continuous_on UNIONS k /\ IMAGE f (UNIONS k) SUBSET UNIONS l /\
     compact c /\ c SUBSET UNIONS k /\ DISJOINT (IMAGE f c) (UNIONS l0)
     ==> ?e. &0 < e /\
             !k'. simplicial_complex k' /\ UNIONS k' = UNIONS k /\
                  (!s. s IN k' ==> diameter s < e)
                  ==> ?phi:real^M->real^N.
                        !v. {v} IN k'
                            ==> {phi v} IN l /\
                                (!x. x IN UNIONS k' /\
                                     (!t. t IN k' /\ x IN t ==> v IN t)
                                     ==> !s. s IN l /\ f x IN s ==> phi v IN s) /\
                                ((?x. x IN c /\ (!t. t IN k' /\ x IN t ==> v IN t))
                                 ==> ~({phi v} IN l0))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact (UNIONS k:real^M->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `{w:real^N | {w} IN l}`;
                 `IMAGE (f:real^M->real^N) (UNIONS k)`] MOI_FSAP_LEBESGUE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_CONTINUOUS_IMAGE; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_FSAP_STAR_COVER THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `{w:real^N | {w} IN l /\ ~({w} IN l0)}`;
                 `IMAGE (f:real^M->real^N) c`] MOI_FSAP_LEBESGUE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC MOI_FSAP_STAR_COVER_FULL THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^M->real^N`; `UNIONS k:real^M->bool`]
    COMPACT_UNIFORMLY_CONTINUOUS) THEN
  ASM_REWRITE_TAC[uniformly_continuous_on] THEN
  DISCH_THEN(MP_TAC o SPEC `min d1 d2:real`) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `eta:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `eta / &2` THEN ASM_REWRITE_TAC[REAL_HALF] THEN
  X_GEN_TAC `k':(real^M->bool)->bool` THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM SKOLEM_THM] THEN X_GEN_TAC `v:real^M` THEN
  REWRITE_TAC[RIGHT_EXISTS_IMP_THM] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(v:real^M) IN UNIONS k` ASSUME_TAC THENL
   [SUBGOAL_THEN `(v:real^M) IN UNIONS k'` MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^M}` THEN
      ASM_REWRITE_TAC[IN_SING];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^M. x IN UNIONS k' /\ (!t. t IN k' /\ x IN t ==> v IN t)
               ==> dist(v,x) < eta / &2`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?t:real^M->bool. t IN k' /\ x IN t` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `diameter(t:real^M->bool)` THEN
    ASM_SIMP_TAC[] THEN REWRITE_TAC[dist] THEN
    MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  ASM_CASES_TAC `?x0:real^M. x0 IN c /\ (!t. t IN k' /\ x0 IN t ==> v IN t)` THENL
   [FIRST_ASSUM(X_CHOOSE_THEN `x0:real^M` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x0:real^M) IN UNIONS k` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(x0:real^M) IN UNIONS k'` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dist(v:real^M,x0) < eta / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME
       `!x:real^M. x IN UNIONS k' /\ (!t. t IN k' /\ x IN t ==> v IN t)
                   ==> dist(v,x) < eta / &2`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `!y. y IN IMAGE (f:real^M->real^N) c
          ==> ?w. ({w} IN l /\ ~({w} IN l0)) /\
                  !z t. dist(y,z) < d2 /\ t IN l /\ z IN t ==> w IN t` THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) x0`) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN UNIONS k'` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dist(v:real^M,x) < eta / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME
       `!x:real^M. x IN UNIONS k' /\ (!t. t IN k' /\ x IN t ==> v IN t)
                   ==> dist(v,x) < eta / &2`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(ASSUME
     `!z t. dist((f:real^M->real^N) x0,z) < d2 /\ t IN l /\ z IN t
            ==> (w:real^N) IN t`) THEN
    EXISTS_TAC `(f:real^M->real^N) x` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    MP_TAC(SPECL [`x0:real^M`; `x:real^M`] (ASSUME
     `!x x'. x IN UNIONS k /\ x' IN UNIONS k /\ dist(x',x) < eta
             ==> dist((f:real^M->real^N) x',f x) < d1 /\ dist(f x',f x) < d2`)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`x:real^M`; `v:real^M`; `x0:real^M`] DIST_TRIANGLE) THEN
      MP_TAC(ISPECL [`x:real^M`; `v:real^M`] DIST_SYM) THEN
      UNDISCH_TAC `dist(v:real^M,x) < eta / &2` THEN
      UNDISCH_TAC `dist(v:real^M,x0) < eta / &2` THEN
      REAL_ARITH_TAC;
      SIMP_TAC[]];
    UNDISCH_TAC
     `!y. y IN IMAGE (f:real^M->real^N) (UNIONS k)
          ==> ?w. {w} IN l /\
                  !z t. dist(y,z) < d1 /\ t IN l /\ z IN t ==> w IN t` THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^M->real^N) v`) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN UNIONS k'` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `dist(v:real^M,x) < eta / &2` ASSUME_TAC THENL
     [MATCH_MP_TAC(ASSUME
       `!x:real^M. x IN UNIONS k' /\ (!t. t IN k' /\ x IN t ==> v IN t)
                   ==> dist(v,x) < eta / &2`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(ASSUME
     `!z t. dist((f:real^M->real^N) v,z) < d1 /\ t IN l /\ z IN t
            ==> (w:real^N) IN t`) THEN
    EXISTS_TAC `(f:real^M->real^N) x` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN
    MP_TAC(SPECL [`v:real^M`; `x:real^M`] (ASSUME
     `!x x'. x IN UNIONS k /\ x' IN UNIONS k /\ dist(x',x) < eta
             ==> dist((f:real^M->real^N) x',f x) < d1 /\ dist(f x',f x) < d2`)) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN
      UNDISCH_TAC `dist(v:real^M,x) < eta / &2` THEN
      UNDISCH_TAC `&0 < eta` THEN REAL_ARITH_TAC;
      SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* 6. The relative clause and the theorem.  If x lies in c, every vertex v   *)
(* of the carrier r of x has x in its open star, so phi v is not a vertex  *)
(* of l0.  A point of the relative interior of the image hull of r lying in *)
(* a simplex t of l0 would force the whole hull into t, hence phi v into    *)
(* l0.  The homotopy is the straight line inside a simplex through f x.     *)
(* ------------------------------------------------------------------------- *)

let MOI_FSAP_REL_AVOID = prove
 (`!(k':(real^M->bool)->bool) (l:(real^N->bool)->bool) (l0:(real^N->bool)->bool)
    (f:real^M->real^N) (phi:real^M->real^N) (c:real^M->bool) r x y.
     simplicial_complex k' /\ simplicial_complex l /\ simplicial_subcomplex l0 l /\
     IMAGE f (UNIONS k') SUBSET UNIONS l /\
     (!v. {v} IN k'
          ==> {phi v} IN l /\
              (!x. x IN UNIONS k' /\ (!t. t IN k' /\ x IN t ==> v IN t)
                   ==> !s. s IN l /\ f x IN s ==> phi v IN s) /\
              ((?x. x IN c /\ (!t. t IN k' /\ x IN t ==> v IN t))
               ==> ~({phi v} IN l0))) /\
     r IN k' /\ x IN c /\ x IN relative_interior r /\
     y IN relative_interior (convex hull (IMAGE phi {v | v extreme_point_of r}))
     ==> ~(y IN UNIONS l0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IN_UNIONS; NOT_EXISTS_THM] THEN
  X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^M) IN r` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^M) IN UNIONS k'` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_UNIONS]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->bool) IN l` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN l /\ (f:real^M->real^N) x IN s`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real^M->real^N) x IN UNIONS l` MP_TAC THENL
     [ASM_MESON_TAC[SUBSET; FUN_IN_IMAGE]; REWRITE_TAC[IN_UNIONS]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^M. v extreme_point_of r
               ==> {v} IN k' /\ (!t. t IN k' /\ x IN t ==> v IN t)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`k':(real^M->bool)->bool`; `r:real^M->bool`]
        MOI_FSAP_SIMPLEX_VERTICES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `V:real^M->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `(v:real^M) extreme_point_of r` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`k':(real^M->bool)->bool`; `r:real^M->bool`; `x:real^M`;
                     `v:real^M`] MOI_FSAP_RELINT_STAR) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^M. v extreme_point_of r
               ==> {(phi:real^M->real^N) v} IN l /\ phi v IN s /\
                   ~({phi v} IN l0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `{v:real^M} IN k' /\ (!t. t IN k' /\ x IN t ==> v IN t)`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^M` o check (fun th ->
      can (find_term ((=) `l0:(real^N->bool)->bool`)) (concl th) &&
      can (find_term ((=) `phi:real^M->real^N`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC MP_TAC)) THEN
    ANTS_TAC THENL [EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE (phi:real^M->real^N) {v | v extreme_point_of r}) IN l`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `s:real^N->bool`;
                   `IMAGE (phi:real^M->real^N) {v | v extreme_point_of r}`]
      MOI_FSAP_HULL_IN) THEN
    ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
    ASM_REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE (phi:real^M->real^N) {v | v extreme_point_of r}) SUBSET t`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSAP_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`l:(real^N->bool)->bool`; `y:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v:real^M. v extreme_point_of r` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN
    CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(phi:real^M->real^N) v IN t` ASSUME_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[SUBSET] (ASSUME
     `convex hull (IMAGE (phi:real^M->real^N) {v | v extreme_point_of r})
      SUBSET t`)) THEN
    MATCH_MP_TAC HULL_INC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `{(phi:real^M->real^N) v} IN l /\ ~({phi v} IN l0)`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~({(phi:real^M->real^N) v} IN l0)` THEN REWRITE_TAC[] THEN
  UNDISCH_TAC `simplicial_subcomplex (l0:(real^N->bool)->bool) l` THEN
  REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{(phi:real^M->real^N) v} = {phi v} INTER t` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[simplicial_complex]]);;

let SIMPLICIAL_APPROX = prove
 (MOI_FND_SIMPLICIAL_APPROX,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `l:(real^N->bool)->bool`;
                 `l0:(real^N->bool)->bool`; `f:real^M->real^N`; `c:real^M->bool`]
    MOI_FSAP_VERTEX_CHOICE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `e:real`]
    ITERATED_BARYCENTRIC_SUBDIVISION_FINE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  MP_TAC(ISPECL [`k:(real^M->bool)->bool`; `n:num`] MOI_FSAP_ITER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `ITER n barycentric_subdivision (k:(real^M->bool)->bool)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `phi:real^M->real^N`) THEN
  MP_TAC(ISPECL [`ITER n barycentric_subdivision (k:(real^M->bool)->bool)`;
                 `l:(real^N->bool)->bool`; `f:real^M->real^N`; `phi:real^M->real^N`]
    MOI_FSAP_STAR_MAP) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^M->real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `g:real^M->real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^M) IN UNIONS k` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o check (fun th ->
      can (find_term ((=) `relative_interior:(real^N->bool)->real^N->bool`))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FSAP_REL_AVOID THEN
    MAP_EVERY EXISTS_TAC
     [`ITER n barycentric_subdivision (k:(real^M->bool)->bool)`;
      `l:(real^N->bool)->bool`; `f:real^M->real^N`; `phi:real^M->real^N`;
      `c:real^M->bool`; `r:real^M->bool`; `x:real^M`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HOMOTOPIC_WITH_LINEAR THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?s:real^N->bool. s IN l /\ (f:real^M->real^N) x IN s`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(f:real^M->real^N) x IN UNIONS l` MP_TAC THENL
       [ASM_MESON_TAC[SUBSET; FUN_IN_IMAGE]; REWRITE_TAC[IN_UNIONS]];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `convex (s:real^N->bool)` MP_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_SIMP_TAC[];
      ASM SET_TAC[]]]);;

