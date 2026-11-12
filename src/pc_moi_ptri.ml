needs "src/pc_moi_tridef.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_real.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_ptri: PL triangulations of compact parts of PL 3-manifolds        *)
(* (Moise, Geometric Topology in Dimensions 2 and 3, Sec 7 and the proof of *)
(* Thm 8.3), and three reusable PL tools: max and min of PL real-valued     *)
(* maps, and the extension of a PL map from a subpolyhedron.                *)
(* First, the empty triangulation, restriction to the topspace, and         *)
(* max and min of PL maps into real^1.                                      *)
(* ========================================================================= *)

let PL_TRIANGULATION_EMPTY = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^M))->bool) (t:real^N->A).
     pl_triangulation top atlas {} t {}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_triangulation; UNIONS_0; NOT_IN_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[lf_simplicial_complex; NOT_IN_EMPTY; UNIONS_0];
    REWRITE_TAC[HOMEOMORPHIC_MAP_MAPS; homeomorphic_maps] THEN
    EXISTS_TAC `\x:A. vec 0:real^N` THEN
    SIMP_TAC[CONTINUOUS_MAP_ON_EMPTY; TOPSPACE_SUBTOPOLOGY;
             TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; INTER_EMPTY; NOT_IN_EMPTY];
    REPEAT STRIP_TAC THEN EXISTS_TAC `\x:real^N. vec 0:real^M` THEN
    REWRITE_TAC[pl_map_on; EMPTY_GSPEC; NOT_IN_EMPTY]]);;

let MOI_PTR_PL_TRIANGULATION_RESTRICT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^M))->bool)
    (c:(real^N->bool)->bool) t s.
     pl_triangulation top atlas c t s <=>
     pl_triangulation top atlas c t (topspace top INTER s)`,
  REWRITE_TAC[pl_triangulation; GSYM SUBTOPOLOGY_RESTRICT]);;

(* The part of a polytope where one affine real-valued map is below another *)
(* is a polytope.                                                           *)

let MOI_PTR_POLYTOPE_AFFINE_LE = prove
 (`!(k:real^M->bool) (f:real^M->real^1) g lf yf lg yg.
     polytope k /\ linear lf /\ linear lg /\
     (!z. z IN k ==> f z = lf z + yf) /\ (!z. z IN k ==> g z = lg z + yg)
     ==> polytope {z | z IN k /\ drop(f z) <= drop(g z)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{z | z IN k /\ drop((f:real^M->real^1) z) <= drop(g z)} =
    k INTER {z | (\z. (lf:real^M->real^1) z - lg z) z + (yf - yg) IN
                 {w:real^1 | basis 1 dot w <= &0}}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^M` THEN
    SIMP_TAC[DOT_BASIS; DIMINDEX_1; LE_REFL] THEN
    ASM_CASES_TAC `(z:real^M) IN k` THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM drop; DROP_ADD; DROP_SUB] THEN REAL_ARITH_TAC;
    MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PLM_POLYHEDRON_AFFINE_PREIMAGE THEN
    REWRITE_TAC[POLYHEDRON_HALFSPACE_LE] THEN
    MATCH_MP_TAC LINEAR_COMPOSE_SUB THEN ASM_REWRITE_TAC[ETA_AX]]);;

let PL_MAP_ON_LIFT_MAX = prove
 (`!(s:real^M->bool) (f:real^M->real^1) g.
     pl_map_on s f /\ pl_map_on s g
     ==> pl_map_on s (\x. lift(max (drop(f x)) (drop(g x))))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_PLM_PL_MAP_ON_PAIR) THEN
  DISCH_TAC THEN REWRITE_TAC[pl_map_on] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool`
   (X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC
   `IMAGE (\k:real^M->bool.
             {z | z IN k /\ drop((f:real^M->real^1) z) <=
                            drop((g:real^M->real^1) z)}) c UNION
    IMAGE (\k:real^M->bool.
             {z | z IN k /\ drop((g:real^M->real^1) z) <=
                            drop((f:real^M->real^1) z)}) c` THEN
  EXISTS_TAC `u:real^M->bool` THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE] THEN CONJ_TAC THENL
   [UNDISCH_TAC `s INTER u SUBSET UNIONS (c:(real^M->bool)->bool)` THEN
    REWRITE_TAC[UNIONS_UNION; UNIONS_IMAGE] THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM; IN_UNIONS; IN_INTER] THEN
    MESON_TAC[REAL_LE_TOTAL];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNION; TAUT `(a \/ b ==> c) <=> (a ==> c) /\ (b ==> c)`;
              FORALL_AND_THM; FORALL_IN_IMAGE] THEN
  CONJ_TAC THEN X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `lf:real^M->real^1` (X_CHOOSE_THEN `yf:real^1`
        STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `lg:real^M->real^1` (X_CHOOSE_THEN `yg:real^1`
        STRIP_ASSUME_TAC))))) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PTR_POLYTOPE_AFFINE_LE THEN
    MAP_EVERY EXISTS_TAC
     [`lf:real^M->real^1`; `yf:real^1`; `lg:real^M->real^1`; `yg:real^1`] THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    MAP_EVERY EXISTS_TAC [`lg:real^M->real^1`; `yg:real^1`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `a <= b ==> max a b = b`; LIFT_DROP];
    MATCH_MP_TAC MOI_PTR_POLYTOPE_AFFINE_LE THEN
    MAP_EVERY EXISTS_TAC
     [`lg:real^M->real^1`; `yg:real^1`; `lf:real^M->real^1`; `yf:real^1`] THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[];
    MAP_EVERY EXISTS_TAC [`lf:real^M->real^1`; `yf:real^1`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_SIMP_TAC[REAL_ARITH `b <= a ==> max a b = a`; LIFT_DROP]]);;

let PL_MAP_ON_LIFT_MIN = prove
 (`!(s:real^M->bool) (f:real^M->real^1) g.
     pl_map_on s f /\ pl_map_on s g
     ==> pl_map_on s (\x. lift(min (drop(f x)) (drop(g x))))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `\x. --(&1) % (f:real^M->real^1) x`;
                 `\x. --(&1) % (g:real^M->real^1) x`] PL_MAP_ON_LIFT_MAX) THEN
  ASM_SIMP_TAC[PL_MAP_ON_CMUL] THEN
  DISCH_THEN(MP_TAC o SPEC `--(&1)` o MATCH_MP PL_MAP_ON_CMUL) THEN
  MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] PL_MAP_ON_EQ) THEN
  REWRITE_TAC[GSYM DROP_EQ; DROP_CMUL; LIFT_DROP] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Extension of a PL map from a compact subpolyhedron (Moise               *)
(* uses it implicitly when PL complexes are combined, Sec 7).  Triangulate *)
(* the big polyhedron so that the small one is a union of simplices on     *)
(* which the map is affine, then extend simplexwise affinely from the      *)
(* vertex values.                                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_PTR_SIMPLICIAL_COMPLEX_POLYTOPE = prove
 (`!(c:(real^N->bool)->bool) s. simplicial_complex c /\ s IN c ==> polytope s`,
  REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_POLYTOPE]);;

let MOI_PTR_SIMPLEXWISE_AFFINE = prove
 (`!(t:(real^M->bool)->bool) (vals:real^M->real^N).
     simplicial_complex t
     ==> ?h. (!s. s IN t
                  ==> ?l y. linear l /\ !x. x IN s ==> h x = l x + y) /\
             (!vs v. vs IN moi_real_vertex_sets t /\ v IN vs ==> h v = vals v)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\x:real^M. x`; `vals:real^M->real^N`;
                 `moi_real_vertex_sets (t:(real^M->bool)->bool)`]
    MOI_REAL_SIMPLEXWISE_AFFINE) THEN
  ASM_SIMP_TAC[MOI_REAL_VERTEX_SETS_REALIZES; IMAGE_ID] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N` (LABEL_TAC "h")) THEN
  EXISTS_TAC `h:real^M->real^N` THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `s:real^M->bool = {}` THENL
     [MAP_EVERY EXISTS_TAC [`\x:real^M. vec 0:real^N`; `vec 0:real^N`] THEN
      ASM_REWRITE_TAC[NOT_IN_EMPTY; LINEAR_ZERO];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^M->bool)->bool`; `s:real^M->bool`]
      MOI_REAL_SIMPLEX_VERTICES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `vs:real^M->bool` STRIP_ASSUME_TAC) THEN
    REMOVE_THEN "h" (MP_TAC o SPEC `vs:real^M->bool`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`vs:real^M->bool`; `v:real^M`] THEN STRIP_TAC THEN
    REMOVE_THEN "h" (MP_TAC o SPEC `vs:real^M->bool`) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(v:real^M) IN convex hull vs` ASSUME_TAC THENL
     [ASM_MESON_TAC[HULL_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

let PL_MAP_EXTENSION = prove
 (`!(p:real^M->bool) a (f:real^M->real^N).
     pl_polyhedron p /\ pl_polyhedron a /\ a SUBSET p /\ pl_map_on a f
     ==> ?g. pl_map_on p g /\ !x. x IN a ==> g x = f x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?ta:(real^M->bool)->bool. simplicial_complex ta /\ UNIONS ta = a`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ta:(real^M->bool)->bool`; `f:real^M->real^N`]
    SIMPLICIAL_SUBDIVISION_PL_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tb:(real^M->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "faff"))))) THEN
  UNDISCH_TAC `pl_polyhedron (p:real^M->bool)` THEN
  REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `cp:(real^M->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))) THEN
  MP_TAC(ISPEC `cp UNION tb:(real^M->bool)->bool`
    POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FINITE_UNION; IN_UNION] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      ASM_MESON_TAC[MOI_PTR_SIMPLICIAL_COMPLEX_POLYTOPE]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^M->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "ref")))) THEN
  MP_TAC(ISPECL [`t:(real^M->bool)->bool`;
                 `\v:real^M. if v IN a then (f:real^M->real^N) v else vec 0`]
    MOI_PTR_SIMPLEXWISE_AFFINE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^M->real^N`
    (CONJUNCTS_THEN2 (LABEL_TAC "haff") (LABEL_TAC "hvert"))) THEN
  EXISTS_TAC `h:real^M->real^N` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `UNIONS cp:real^M->bool = UNIONS t` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[UNIONS_UNION] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real^M->real^N`; `t:(real^M->bool)->bool`]
      MOI_REAL_PIECEWISE_AFFINE_UNIONS) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
      X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_PTR_SIMPLICIAL_COMPLEX_POLYTOPE];
        REMOVE_THEN "haff" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?k:real^M->bool. k IN tb /\ (x:real^M) IN k`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?s:real^M->bool. s IN t /\ (x:real^M) IN s /\ s SUBSET k`
  STRIP_ASSUME_TAC THENL
   [REMOVE_THEN "ref" (MP_TAC o SPEC `k:real^M->bool`) THEN
    ASM_REWRITE_TAC[IN_UNION] THEN
    DISCH_THEN(X_CHOOSE_THEN `fk:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(x:real^M) IN k` THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^M->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?vs:real^M->bool. vs IN moi_real_vertex_sets t /\
                                  s = convex hull vs`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_REAL_SIMPLEX_VERTICES THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "haff" (MP_TAC o SPEC `s:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lh:real^M->real^N` (X_CHOOSE_THEN `yh:real^N`
    STRIP_ASSUME_TAC)) THEN
  REMOVE_THEN "faff" (MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `lf:real^M->real^N` (X_CHOOSE_THEN `yf:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`lh:real^M->real^N`; `lf:real^M->real^N`; `yh:real^N`;
                 `yf:real^N`; `vs:real^M->bool`]
    MOI_REAL_AFFINE_EQ_ON_CONVEX_HULL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(v:real^M) IN s` ASSUME_TAC THENL
     [ASM_MESON_TAC[HULL_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^M) IN a` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "hvert" (MP_TAC o SPECL [`vs:real^M->bool`; `v:real^M`]) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(v:real^M) IN k` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN
  SUBGOAL_THEN `(x:real^M) IN convex hull vs` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(x:real^M) IN k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Compact polyhedra that are finite unions of polytopes of                *)
(* dimension at most d.  They are closed under finite unions and PL images, *)
(* they can be triangulated by simplices of dimension at most d, and for   *)
(* 2 d + 1 <= dimindex(:N) they are PL homeomorphic to a Euclidean complex *)
(* in real^N (Moise 7.1 via SIMPLICIAL_COMPLEX_REREALIZATION).             *)
(* ------------------------------------------------------------------------- *)

let moi_ptr_dim_polyhedron = new_definition
 `moi_ptr_dim_polyhedron d (s:real^N->bool) <=>
    ?u. FINITE u /\ (!k. k IN u ==> polytope k /\ aff_dim k <= &d) /\
        s = UNIONS u`;;

let MOI_PTR_DIM_POLYHEDRON_IMP_PL_POLYHEDRON = prove
 (`!d (s:real^N->bool). moi_ptr_dim_polyhedron d s ==> pl_polyhedron s`,
  REWRITE_TAC[moi_ptr_dim_polyhedron; pl_polyhedron] THEN MESON_TAC[]);;

let MOI_PTR_DIM_POLYHEDRON_POLYTOPE = prove
 (`!d (k:real^N->bool).
     polytope k /\ aff_dim k <= &d ==> moi_ptr_dim_polyhedron d k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_ptr_dim_polyhedron] THEN
  EXISTS_TAC `{k:real^N->bool}` THEN
  ASM_REWRITE_TAC[FINITE_SING; IN_SING; UNIONS_1] THEN ASM_MESON_TAC[]);;

let MOI_PTR_DIM_POLYHEDRON_EMPTY = prove
 (`!d. moi_ptr_dim_polyhedron d ({}:real^N->bool)`,
  GEN_TAC THEN REWRITE_TAC[moi_ptr_dim_polyhedron] THEN
  EXISTS_TAC `{}:(real^N->bool)->bool` THEN
  REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY; UNIONS_0]);;

let MOI_PTR_DIM_POLYHEDRON_UNION = prove
 (`!d (s:real^N->bool) t.
     moi_ptr_dim_polyhedron d s /\ moi_ptr_dim_polyhedron d t
     ==> moi_ptr_dim_polyhedron d (s UNION t)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ptr_dim_polyhedron] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `u:(real^N->bool)->bool` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `v:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `u UNION v:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[FINITE_UNION; IN_UNION; UNIONS_UNION] THEN
  ASM_MESON_TAC[]);;

let MOI_PTR_DIM_POLYHEDRON_UNIONS = prove
 (`!d (v:(real^N->bool)->bool).
     FINITE v /\ (!s. s IN v ==> moi_ptr_dim_polyhedron d s)
     ==> moi_ptr_dim_polyhedron d (UNIONS v)`,
  GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; MOI_PTR_DIM_POLYHEDRON_EMPTY; UNIONS_INSERT;
              FORALL_IN_INSERT] THEN
  MESON_TAC[MOI_PTR_DIM_POLYHEDRON_UNION]);;

let MOI_PTR_AFF_DIM_AFFINE_IMAGE_LE = prove
 (`!(l:real^M->real^N) y s.
     linear l ==> aff_dim (IMAGE (\z. l z + y) s) <= aff_dim s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\z. (l:real^M->real^N) z + y) s =
                IMAGE (\x. y + x) (IMAGE l s)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[VECTOR_ADD_SYM];
    REWRITE_TAC[AFF_DIM_TRANSLATION_EQ] THEN
    ASM_SIMP_TAC[AFF_DIM_LINEAR_IMAGE_LE]]);;

let MOI_PTR_DIM_POLYHEDRON_PL_IMAGE_POLYTOPE = prove
 (`!d (k:real^M->bool) (f:real^M->real^N).
     polytope k /\ aff_dim k <= &d /\ pl_map_on k f
     ==> moi_ptr_dim_polyhedron d (IMAGE f k)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^M->bool`; `f:real^M->real^N`]
    MOI_PLM_PL_MAP_ON_COMPACT_FINITE) THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[moi_ptr_dim_polyhedron] THEN
  EXISTS_TAC `IMAGE (IMAGE (f:real^M->real^N)) c` THEN
  REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `j:real^M->bool` THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
        STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `IMAGE (f:real^M->real^N) j = IMAGE (\z. l z + y) j`
    SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x:A. x IN s ==> (f:A->B) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_PLM_POLYTOPE_AFFINE_IMAGE THEN ASM_REWRITE_TAC[ETA_AX];
      MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `aff_dim(j:real^M->bool)` THEN
      ASM_SIMP_TAC[MOI_PTR_AFF_DIM_AFFINE_IMAGE_LE] THEN
      MATCH_MP_TAC INT_LE_TRANS THEN
      EXISTS_TAC `aff_dim(k:real^M->bool)` THEN
      ASM_SIMP_TAC[AFF_DIM_SUBSET]];
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [ASSUME `k:real^M->bool = UNIONS c`] THEN
    REWRITE_TAC[IMAGE_UNIONS]]);;

let MOI_PTR_DIM_POLYHEDRON_PL_IMAGE = prove
 (`!d (s:real^M->bool) (f:real^M->real^N).
     moi_ptr_dim_polyhedron d s /\ pl_map_on s f
     ==> moi_ptr_dim_polyhedron d (IMAGE f s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[moi_ptr_dim_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[IMAGE_UNIONS; GSYM moi_ptr_dim_polyhedron] THEN
  MATCH_MP_TAC MOI_PTR_DIM_POLYHEDRON_UNIONS THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_PTR_DIM_POLYHEDRON_PL_IMAGE_POLYTOPE THEN
  ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
  EXISTS_TAC `UNIONS u:real^M->bool` THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE] THEN ASM SET_TAC[]);;

let MOI_PTR_COMPACT_LOCAL_COVER = prove
 (`!(P:(real^M->bool)->bool) s.
     compact s /\
     (!x. x IN s
          ==> ?c u. FINITE c /\ open u /\ x IN u /\
                    s INTER u SUBSET UNIONS c /\ !k. k IN c ==> P k)
     ==> ?c. FINITE c /\ s SUBSET UNIONS c /\ !k. k IN c ==> P k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])) THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`C:real^M->(real^M->bool)->bool`;
                       `U:real^M->real^M->bool`] THEN
  DISCH_THEN(LABEL_TAC "cov") THEN
  MP_TAC(ISPEC `s:real^M->bool` COMPACT_IMP_HEINE_BOREL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (U:real^M->real^M->bool) s`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[EXISTS_FINITE_SUBSET_IMAGE] o
    ONCE_REWRITE_RULE[TAUT `a /\ b /\ c <=> b /\ a /\ c`]) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `UNIONS (IMAGE (C:real^M->(real^M->bool)->bool) p)` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN ASM_MESON_TAC[SUBSET];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?x:real^M. x IN p /\ z IN (U:real^M->real^M->bool) x`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `s SUBSET UNIONS (IMAGE (U:real^M->real^M->bool) p)` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^M) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "cov" (MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `?k:real^M->bool. k IN (C:real^M->(real^M->bool)->bool) x /\ z IN k`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `s INTER (U:real^M->real^M->bool) x SUBSET
                   UNIONS ((C:real^M->(real^M->bool)->bool) x)` THEN
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE] THEN
    EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `k:real^M->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^M) IN s` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "cov" (MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

let MOI_PTR_DIM_POLYHEDRON_LOCAL = prove
 (`!d (s:real^M->bool).
     compact s /\
     (!x. x IN s
          ==> ?c u. FINITE c /\ open u /\ x IN u /\
                    s INTER u SUBSET UNIONS c /\
                    !k. k IN c ==> polytope k /\ k SUBSET s /\ aff_dim k <= &d)
     ==> moi_ptr_dim_polyhedron d s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\k:real^M->bool. polytope k /\ k SUBSET s /\ aff_dim k <= &d`;
                 `s:real^M->bool`] MOI_PTR_COMPACT_LOCAL_COVER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[moi_ptr_dim_polyhedron] THEN
  EXISTS_TAC `c:(real^M->bool)->bool` THEN ASM_SIMP_TAC[] THEN
  REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[UNIONS_SUBSET] THEN ASM_MESON_TAC[]);;

let MOI_PTR_DIM_POLYHEDRON_TRIANGULATE = prove
 (`!d (s:real^N->bool).
     moi_ptr_dim_polyhedron d s
     ==> ?t. simplicial_complex t /\ UNIONS t = s /\
             !k. k IN t ==> aff_dim k <= &d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_ptr_dim_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `u:(real^N->bool)->bool` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ASM_SIMP_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
  ASM_CASES_TAC `k:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `k:real^N->bool`;
                 `u:(real^N->bool)->bool`] MOI_PLT_SIMPLEX_IN_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{j:real^N->bool | j IN u /\ ?f. f SUBSET t /\ j = UNIONS f} = u`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o
      check (fun th -> is_eq(concl th) && is_comb(lhs(concl th)) &&
                       fst(dest_const(rator(lhs(concl th)))) = "UNIONS" &&
                       rand(lhs(concl th)) = `t:(real^N->bool)->bool`)) THEN
    ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `j:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(j:real^N->bool)` THEN
    ASM_SIMP_TAC[AFF_DIM_SUBSET]]);;

let MOI_PTR_DIM_POLYHEDRON_REALIZE = prove
 (`!d (s:real^M->bool).
     moi_ptr_dim_polyhedron d s /\ 2 * d + 1 <= dimindex(:N)
     ==> ?(c:(real^N->bool)->bool) h h'.
           simplicial_complex c /\ pl_homeomorphism (s,UNIONS c) (h,h')`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP MOI_PTR_DIM_POLYHEDRON_TRIANGULATE) THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^M->bool)->bool`; `d:num`]
    (INST_TYPE [`:N`,`:N`] SIMPLICIAL_COMPLEX_REREALIZATION)) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Charts and their inverses, PL maps composed with charts, and the passage  *)
(* from a homeomorphism of a dimension-3 compact polyhedron onto a subset of *)
(* the manifold (PL in every chart) to a PL triangulation realized in        *)
(* real^N.  First application: a single chart cube                           *)
(* (PL_TRIANGULATION_CHART_CUBE).                                            *)
(* ------------------------------------------------------------------------- *)

let MOI_PTR_LOCALLY_POLYHEDRAL_PREIMAGE_OPEN = prove
 (`!(s:real^M->bool) (top:A topology) (f:real^M->A) v.
     locally_polyhedral s /\ continuous_map (subtopology euclidean s,top) f /\
     open_in top v
     ==> locally_polyhedral {x | x IN s /\ f x IN v}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:real^M->A`; `subtopology euclidean (s:real^M->bool)`;
                 `top:A topology`; `v:A->bool`]
    OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^M->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[]);;

let MOI_PTR_CHART_MAPS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U phi.
     pl_manifold_atlas top atlas /\ (U,phi) IN atlas
     ==> open_in top U /\ open (IMAGE phi U) /\
         ?psi. homeomorphic_maps (subtopology top U,
                                  subtopology euclidean (IMAGE phi U))
                                 (phi,psi)`,
  REWRITE_TAC[pl_manifold_atlas; HOMEOMORPHIC_MAP_MAPS] THEN MESON_TAC[]);;

let MOI_PTR_CHART_FACTS = prove
 (`!(top:A topology) U (phi:A->real^N) psi.
     open_in top U /\
     homeomorphic_maps (subtopology top U,subtopology euclidean (IMAGE phi U))
                       (phi,psi)
     ==> U SUBSET topspace top /\
         (!x. x IN U ==> psi(phi x) = x) /\
         (!y. y IN IMAGE phi U ==> psi y IN U /\ phi(psi y) = y) /\
         continuous_map (subtopology euclidean (IMAGE phi U),top) psi /\
         continuous_map (subtopology top U,euclidean) phi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP OPEN_IN_SUBSET) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [homeomorphic_maps]) THEN
  REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY;
              TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[SET_RULE `(u:A->bool) SUBSET t ==> t INTER u = u`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
  ASM SET_TAC[]);;

let MOI_PTR_CHART_INVERSE_HOMEO = prove
 (`!(top:A topology) U (phi:A->real^N) psi k.
     open_in top U /\
     homeomorphic_maps (subtopology top U,subtopology euclidean (IMAGE phi U))
                       (phi,psi) /\
     k SUBSET IMAGE phi U
     ==> homeomorphic_map (subtopology euclidean k,
                           subtopology top {x | x IN U /\ phi x IN k}) psi`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `U:A->bool`; `phi:A->real^N`;
                 `psi:real^N->A`] MOI_PTR_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `homeomorphic_map
      (subtopology (subtopology euclidean (IMAGE (phi:A->real^N) U)) k,
       subtopology (subtopology top U) {x | x IN U /\ phi x IN k}) psi`
  MP_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_MAP_SUBTOPOLOGIES THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHIC_MAPS_IMP_MAP THEN
      EXISTS_TAC `phi:A->real^N` THEN
      ONCE_REWRITE_TAC[HOMEOMORPHIC_MAPS_SYM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
      REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INTER; IN_ELIM_THM] THEN
      X_GEN_TAC `z:A` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
        ASM_MESON_TAC[SUBSET];
        STRIP_TAC THEN EXISTS_TAC `(phi:A->real^N) z` THEN
        ASM_MESON_TAC[SUBSET; IN_IMAGE]]];
    REWRITE_TAC[SUBTOPOLOGY_SUBTOPOLOGY] THEN
    ASM_SIMP_TAC[SET_RULE `(k:real^N->bool) SUBSET s ==> s INTER k = k`;
                 SET_RULE `(U:A->bool) INTER {x | x IN U /\ P x} =
                           {x | x IN U /\ P x}`]]);;

let MOI_PTR_PL_CHART_COMPOSE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^N))->bool) U phi psi V chi
    (s:real^M->bool) (f:real^M->real^N).
     pl_manifold_atlas top atlas /\ (U,phi) IN atlas /\ (V,chi) IN atlas /\
     (!y. y IN IMAGE phi U ==> psi y IN U /\ phi(psi y) = y) /\
     pl_map_on s f /\ (!x. x IN s ==> f x IN IMAGE phi U /\ psi(f x) IN V)
     ==> pl_map_on s (\x. chi(psi(f x)))`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC
   `pl_manifold_atlas (top:A topology)
                      (atlas:((A->bool)#(A->real^N))->bool)` THEN
  REWRITE_TAC[pl_manifold_atlas] THEN
  DISCH_THEN(MP_TAC o SPECL [`U:A->bool`; `phi:A->real^N`; `V:A->bool`;
                             `chi:A->real^N`] o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `(g:real^N->real^N) o (f:real^M->real^N)` THEN CONJ_TAC THENL
   [X_GEN_TAC `x:real^M` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    SUBGOAL_THEN `(f:real^M->real^N) x = phi((psi:real^N->A)(f x))`
     (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `IMAGE (phi:A->real^N) (U INTER V)` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^M` THEN
    DISCH_TAC THEN REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    EXISTS_TAC `(psi:real^N->A)(f(x:real^M))` THEN ASM_MESON_TAC[]]);;

let MOI_PTR_PL_TRI_COMPOSE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^P))->bool)
    (c:(real^N->bool)->bool) t s V chi (r:real^M->bool) (f:real^M->real^N).
     pl_triangulation top atlas c t s /\ (V,chi) IN atlas /\ pl_map_on r f /\
     (!x. x IN r ==> f x IN UNIONS c /\ t(f x) IN V)
     ==> pl_map_on r (\x. chi(t(f x)))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_triangulation] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ch")))
    STRIP_ASSUME_TAC) THEN
  REMOVE_THEN "ch" (MP_TAC o SPECL [`V:A->bool`; `chi:A->real^P`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^P` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN
  EXISTS_TAC `(g:real^N->real^P) o (f:real^M->real^N)` THEN CONJ_TAC THENL
   [REWRITE_TAC[o_THM] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
    EXISTS_TAC `{y | y IN UNIONS c /\ (t:real^N->A) y IN V}` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let MOI_PTR_TRIANGULATION_FROM_POLYHEDRON = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^P))->bool) (x:real^M->bool)
    (theta:real^M->A) s.
     pl_manifold_atlas top atlas /\ moi_ptr_dim_polyhedron 3 x /\
     7 <= dimindex(:N) /\
     homeomorphic_map (subtopology euclidean x,subtopology top s) theta /\
     (!V chi. (V,chi) IN atlas
              ==> pl_map_on {p | p IN x /\ theta p IN V} (\p. chi(theta p)))
     ==> ?(c:(real^N->bool)->bool) t. FINITE c /\ pl_triangulation top atlas c t s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`3`; `x:real^M->bool`] MOI_PTR_DIM_POLYHEDRON_REALIZE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool`
   (X_CHOOSE_THEN `h:real^M->real^N` (X_CHOOSE_THEN `h':real^N->real^M`
     STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN
  EXISTS_TAC `(theta:real^M->A) o (h':real^N->real^M)` THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  SUBGOAL_THEN `FINITE (c:(real^N->bool)->bool) /\ lf_simplicial_complex c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphic_map (subtopology euclidean (UNIONS c),subtopology top s)
                     ((theta:real^M->A) o (h':real^N->real^M))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHIC_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (x:real^M->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHIC_MAPS_IMP_MAP THEN
    EXISTS_TAC `h:real^M->real^N` THEN
    REWRITE_TAC[HOMEOMORPHIC_MAPS_EUCLIDEAN_SUBTOPOLOGY] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[pl_triangulation] THEN
  MAP_EVERY X_GEN_TAC [`V:A->bool`; `chi:A->real^P`] THEN DISCH_TAC THEN
  EXISTS_TAC `(\p. (chi:A->real^P)((theta:real^M->A) p)) o (h':real^N->real^M)` THEN
  REWRITE_TAC[o_THM] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN
  EXISTS_TAC `{p | p IN x /\ (theta:real^M->A) p IN V}` THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `UNIONS c:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`UNIONS c:real^N->bool`; `top:A topology`;
                   `(theta:real^M->A) o (h':real^N->real^M)`; `V:A->bool`]
      MOI_PTR_LOCALLY_POLYHEDRAL_PREIMAGE_OPEN) THEN
    REWRITE_TAC[o_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[LOCALLY_POLYHEDRAL_LF_COMPLEX];
      FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP o
        check (fun th -> can (find_term ((=) `UNIONS (c:(real^N->bool)->bool)`))
                             (concl th) &&
                         is_comb(concl th) &&
                         fst(dest_const(fst(strip_comb(concl th)))) =
                           "homeomorphic_map")) THEN
      MESON_TAC[CONTINUOUS_MAP_INTO_FULLTOPOLOGY];
      ASM_MESON_TAC[MOI_PTR_CHART_MAPS]];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    UNDISCH_TAC
     `homeomorphism (x:real^M->bool,UNIONS c) (h:real^M->real^N,h')` THEN
    REWRITE_TAC[homeomorphism] THEN SET_TAC[]]);;

let PL_TRIANGULATION_CHART_CUBE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) U phi (a:real^3) b.
     pl_manifold_atlas top atlas /\ (U,phi) IN atlas /\
     interval[a,b] SUBSET IMAGE phi U /\ 7 <= dimindex(:N)
     ==> ?(c:(real^N->bool)->bool) t.
           FINITE c /\
           pl_triangulation top atlas c t {x | x IN U /\ phi x IN interval[a,b]}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] MOI_PTR_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `psi:real^3->A`))) THEN
  MP_TAC(ISPECL [`top:A topology`; `U:A->bool`; `phi:A->real^3`;
                 `psi:real^3->A`] MOI_PTR_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(INST_TYPE [`:3`,`:M`] MOI_PTR_TRIANGULATION_FROM_POLYHEDRON) THEN
  MAP_EVERY EXISTS_TAC [`interval[a:real^3,b]`; `psi:real^3->A`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PTR_DIM_POLYHEDRON_POLYTOPE THEN
    REWRITE_TAC[POLYTOPE_INTERVAL] THEN
    MP_TAC(ISPEC `interval[a:real^3,b]` AFF_DIM_LE_UNIV) THEN
    REWRITE_TAC[DIMINDEX_3];
    MATCH_MP_TAC MOI_PTR_CHART_INVERSE_HOMEO THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`V:A->bool`; `chi:A->real^3`] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `U:A->bool`; `phi:A->real^3`; `psi:real^3->A`;
                   `V:A->bool`; `chi:A->real^3`;
                   `{p | p IN interval[a:real^3,b] /\ (psi:real^3->A) p IN V}`;
                   `\p:real^3. p`] MOI_PTR_PL_CHART_COMPOSE) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
    MATCH_MP_TAC MOI_PTR_LOCALLY_POLYHEDRAL_PREIMAGE_OPEN THEN
    EXISTS_TAC `top:A topology` THEN
    REPEAT CONJ_TAC THENL
     [SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL];
      MATCH_MP_TAC CONTINUOUS_MAP_FROM_SUBTOPOLOGY_MONO THEN
      EXISTS_TAC `IMAGE (phi:A->real^3) U` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[MOI_PTR_CHART_MAPS]]]);;

(* ------------------------------------------------------------------------- *)
(* Basic facts about a PL triangulation, local polyhedrality                *)
(* of PL preimages, the dimension bound coming from injective PL charts,   *)
(* and gluing two compact polyhedra mapped injectively into the manifold   *)
(* (a continuous bijection of a compact space onto a Hausdorff space is a  *)
(* homeomorphism), the key to Moise's growing of PL complexes (Sec 8).     *)
(* ------------------------------------------------------------------------- *)

let MOI_PTR_PL_TRI_FACTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^P))->bool)
    (c:(real^N->bool)->bool) t s.
     pl_triangulation top atlas c t s
     ==> continuous_map (subtopology euclidean (UNIONS c),top) t /\
         IMAGE t (UNIONS c) = topspace top INTER s /\
         (!x y. x IN UNIONS c /\ y IN UNIONS c /\ t x = t y ==> x = y) /\
         locally_polyhedral (UNIONS c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_triangulation] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_LF_COMPLEX] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_INJECTIVE_MAP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_SURJECTIVE_MAP) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  MESON_TAC[CONTINUOUS_MAP_INTO_FULLTOPOLOGY]);;

let MOI_PTR_PL_TRI_CHART = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^P))->bool)
    (c:(real^N->bool)->bool) t s V chi.
     pl_triangulation top atlas c t s /\ (V,chi) IN atlas
     ==> pl_map_on {y | y IN UNIONS c /\ t y IN V} (\y. chi(t y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_triangulation] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`V:A->bool`; `chi:A->real^P`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->real^P` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `g:real^N->real^P` THEN
  ASM_SIMP_TAC[IN_ELIM_THM]);;

let MOI_PTR_PL_TRI_POLYHEDRON = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^P))->bool)
    (c:(real^N->bool)->bool) t s.
     FINITE c /\ pl_triangulation top atlas c t s
     ==> simplicial_complex c /\ pl_polyhedron (UNIONS c) /\ compact (UNIONS c)`,
  REWRITE_TAC[pl_triangulation] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF; PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX;
                PL_POLYHEDRON_IMP_COMPACT]);;

let MOI_PTR_LOCALLY_POLYHEDRAL_PL_PREIMAGE = prove
 (`!(s:real^M->bool) (f:real^M->real^N) m.
     pl_map_on s f /\ polyhedron m ==> locally_polyhedral {x | x IN s /\ f x IN m}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[locally_polyhedral; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^M` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M` o REWRITE_RULE[pl_map_on]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^M->bool)->bool`
    (X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC
   `IMAGE (\k:real^M->bool. {z | z IN k /\ (f:real^M->real^N) z IN m}) c` THEN
  EXISTS_TAC `u:real^M->bool` THEN ASM_SIMP_TAC[FINITE_IMAGE] THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_IMAGE] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN
    UNDISCH_TAC `s INTER u SUBSET UNIONS (c:(real^M->bool)->bool)` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN MESON_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `k:real^M->bool` THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `l:real^M->real^N` (X_CHOOSE_THEN `y:real^N`
        STRIP_ASSUME_TAC)))) THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `{z | z IN k /\ (f:real^M->real^N) z IN m} =
                    k INTER {z | l z + y IN m}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
      ASM_SIMP_TAC[MOI_PLM_POLYHEDRON_AFFINE_PREIMAGE];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[]]]);;

let MOI_PTR_COMPACT_LOCALLY_POLYHEDRAL = prove
 (`!s:real^N->bool. compact s /\ locally_polyhedral s ==> pl_polyhedron s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. x`]
    MOI_PLM_PL_MAP_ON_COMPACT_FINITE) THEN
  ASM_REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID] THEN
  REWRITE_TAC[pl_polyhedron] THEN MESON_TAC[]);;

let MOI_PTR_CHART_COMPACT = prove
 (`!(top:A topology) U (phi:A->real^N) psi k.
     open_in top U /\
     homeomorphic_maps (subtopology top U,subtopology euclidean (IMAGE phi U))
                       (phi,psi) /\
     compact k /\ k SUBSET IMAGE phi U
     ==> IMAGE psi k = {x | x IN U /\ phi x IN k} /\
         compact_in top {x | x IN U /\ phi x IN k}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `U:A->bool`; `phi:A->real^N`;
                 `psi:real^N->A`] MOI_PTR_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (psi:real^N->A) k = {x | x IN U /\ phi x IN k}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `z:A` THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
      ASM_MESON_TAC[SUBSET];
      STRIP_TAC THEN EXISTS_TAC `(phi:A->real^N) z` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC IMAGE_COMPACT_IN THEN
  EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^N) U)` THEN
  ASM_REWRITE_TAC[COMPACT_IN_SUBTOPOLOGY; COMPACT_IN_EUCLIDEAN]);;

let MOI_PTR_INJECTIVE_AFFINE_DIM = prove
 (`!(l:real^M->real^N) y k.
     linear l /\ convex k /\
     (!x x'. x IN k /\ x' IN k /\ l x + y = l x' + y ==> x = x')
     ==> aff_dim k <= &(dimindex(:N))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `y:real^N`; `k:real^M->bool`]
    MOI_PLM_AFFINE_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M` (X_CHOOSE_THEN `y':real^M`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `k = IMAGE (\w. (l':real^N->real^M) w + y')
              (IMAGE (\x. (l:real^M->real^N) x + y) k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^M. x IN k ==> f x = x) ==> k = IMAGE f k`) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN
  EXISTS_TAC `aff_dim (IMAGE (\x. (l:real^M->real^N) x + y) k)` THEN
  ASM_SIMP_TAC[MOI_PTR_AFF_DIM_AFFINE_IMAGE_LE; AFF_DIM_LE_UNIV]);;

let MOI_PTR_TRIANGULATION_DIM3 = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
    (c:(real^N->bool)->bool) t s.
     pl_manifold_atlas top atlas /\ FINITE c /\ pl_triangulation top atlas c t s
     ==> moi_ptr_dim_polyhedron 3 (UNIONS c)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(real^N->bool)->bool`; `t:real^N->A`; `s:A->bool`]
    MOI_PTR_PL_TRI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(real^N->bool)->bool`; `t:real^N->A`; `s:A->bool`]
    MOI_PTR_PL_TRI_POLYHEDRON) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_PTR_DIM_POLYHEDRON_LOCAL THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?V (chi:A->real^3).
                 (V,chi) IN (atlas:((A->bool)#(A->real^3))->bool) /\
                 (t:real^N->A) x IN V`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_manifold_atlas (top:A topology)
                   (atlas:((A->bool)#(A->real^3))->bool)` THEN
    REWRITE_TAC[pl_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPEC `(t:real^N->A) x` o CONJUNCT1 o CONJUNCT2) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `V:A->bool`; `chi:A->real^3`] MOI_PTR_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `om:real^3->A`))) THEN
  MP_TAC(ISPECL [`top:A topology`; `V:A->bool`; `chi:A->real^3`;
                 `om:real^3->A`] MOI_PTR_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c:(real^N->bool)->bool`; `t:real^N->A`; `s:A->bool`;
                 `V:A->bool`; `chi:A->real^3`] MOI_PTR_PL_TRI_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o REWRITE_RULE[pl_map_on]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^N->bool)->bool`
    (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:real^N->A`; `subtopology euclidean (UNIONS c:real^N->bool)`;
                 `top:A topology`; `V:A->bool`]
    OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `u INTER w:real^N->bool`] THEN
  ASM_SIMP_TAC[OPEN_INTER] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    X_GEN_TAC `k:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `l:real^N->real^3` (X_CHOOSE_THEN `y:real^3`
        STRIP_ASSUME_TAC)))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM DIMINDEX_3] THEN
    MATCH_MP_TAC MOI_PTR_INJECTIVE_AFFINE_DIM THEN
    MAP_EVERY EXISTS_TAC [`l:real^N->real^3`; `y:real^3`] THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN
    MAP_EVERY X_GEN_TAC [`z1:real^N`; `z2:real^N`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z1:real^N) IN UNIONS (c:(real^N->bool)->bool) /\
                  (t:real^N->A) z1 IN V /\
                  (z2:real^N) IN UNIONS c /\ t z2 IN V`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(chi:A->real^3)(t(z1:real^N)) = chi(t z2)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `om:real^3->A`) THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[]]);;

let MOI_PTR_CONTINUOUS_MAP_CLOSED_UNION = prove
 (`!(top:A topology) (top':B topology) f s t.
     closed_in top s /\ closed_in top t /\
     continuous_map (subtopology top s,top') f /\
     continuous_map (subtopology top t,top') f
     ==> continuous_map (subtopology top (s UNION t),top') f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`subtopology top (s UNION t):A topology`;
                       `top':B topology`; `\i:A->bool. (f:A->B)`; `f:A->B`;
                       `\i:A->bool. i`; `{s,t}:(A->bool)->bool`]
    PASTING_LEMMA_CLOSED) THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; FORALL_IN_INSERT; NOT_IN_EMPTY;
              EXISTS_IN_INSERT; SUBTOPOLOGY_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY;
              IN_INTER; IN_UNION;
              SET_RULE `((s:A->bool) UNION t) INTER s = s /\
                        (s UNION t) INTER t = t`] THEN
  ASM_SIMP_TAC[CLOSED_IN_SUBSET_TOPSPACE; SUBSET_UNION] THEN MESON_TAC[]);;

let MOI_PTR_GLUE_HOMEOMORPHIC = prove
 (`!(top:A topology) (x1:real^M->bool) x2 (theta:real^M->A) s1 s2.
     hausdorff_space top /\ compact x1 /\ compact x2 /\
     continuous_map (subtopology euclidean x1,top) theta /\
     continuous_map (subtopology euclidean x2,top) theta /\
     IMAGE theta x1 = topspace top INTER s1 /\
     IMAGE theta x2 = topspace top INTER s2 /\
     (!p q. p IN x1 UNION x2 /\ q IN x1 UNION x2 /\ theta p = theta q ==> p = q)
     ==> homeomorphic_map (subtopology euclidean (x1 UNION x2),
                           subtopology top (s1 UNION s2)) theta`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `continuous_map (subtopology euclidean (x1 UNION x2),top) (theta:real^M->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_PTR_CONTINUOUS_MAP_CLOSED_UNION THEN
    ASM_SIMP_TAC[CLOSED_IN_EUCLIDEAN; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (theta:real^M->A) (x1 UNION x2) =
                topspace top INTER (s1 UNION s2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IMAGE_UNION] THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC BIJECTIVE_CLOSED_IMP_HOMEOMORPHIC_MAP THEN
  REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  REPEAT CONJ_TAC THENL
   [SET_TAC[];
    MATCH_MP_TAC CONTINUOUS_IMP_CLOSED_MAP THEN
    ASM_SIMP_TAC[HAUSDORFF_SPACE_SUBTOPOLOGY; COMPACT_SPACE_SUBTOPOLOGY;
                 COMPACT_IN_EUCLIDEAN; COMPACT_UNION] THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_IN_SUBTOPOLOGY;
                    TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    SET_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_PTR_GLUE_PL_CHART = prove
 (`!(x1:real^M->bool) x2 (theta:real^M->A) V (chi:A->real^P).
     closed x1 /\ closed x2 /\
     pl_map_on {p | p IN x1 /\ theta p IN V} (\p. chi(theta p)) /\
     pl_map_on {p | p IN x2 /\ theta p IN V} (\p. chi(theta p))
     ==> pl_map_on {p | p IN x1 UNION x2 /\ theta p IN V} (\p. chi(theta p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{p | p IN x1 UNION x2 /\ (theta:real^M->A) p IN V} =
    {p | p IN x1 /\ theta p IN V} UNION {p | p IN x2 /\ theta p IN V}`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_UNION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `{p | p IN x1 /\ (theta:real^M->A) p IN V} =
      ({p | p IN x1 /\ theta p IN V} UNION {p | p IN x2 /\ theta p IN V})
      INTER x1`
     (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `{p | p IN x2 /\ (theta:real^M->A) p IN V} =
      ({p | p IN x1 /\ theta p IN V} UNION {p | p IN x2 /\ theta p IN V})
      INTER x2`
     (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN ASM_REWRITE_TAC[]]);;

let MOI_PTR_GLUE_TRIANGULATION = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^P))->bool) (x1:real^M->bool)
    x2 (theta:real^M->A) s1 s2.
     hausdorff_space top /\ pl_manifold_atlas top atlas /\ 7 <= dimindex(:N) /\
     moi_ptr_dim_polyhedron 3 x1 /\ moi_ptr_dim_polyhedron 3 x2 /\
     continuous_map (subtopology euclidean x1,top) theta /\
     continuous_map (subtopology euclidean x2,top) theta /\
     IMAGE theta x1 = topspace top INTER s1 /\
     IMAGE theta x2 = topspace top INTER s2 /\
     (!p q. p IN x1 UNION x2 /\ q IN x1 UNION x2 /\ theta p = theta q
            ==> p = q) /\
     (!V chi. (V,chi) IN atlas
              ==> pl_map_on {p | p IN x1 /\ theta p IN V} (\p. chi(theta p))) /\
     (!V chi. (V,chi) IN atlas
              ==> pl_map_on {p | p IN x2 /\ theta p IN V} (\p. chi(theta p)))
     ==> ?(c:(real^N->bool)->bool) t.
           FINITE c /\ pl_triangulation top atlas c t (s1 UNION s2)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `compact (x1:real^M->bool) /\ compact (x2:real^M->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_PTR_DIM_POLYHEDRON_IMP_PL_POLYHEDRON;
                  PL_POLYHEDRON_IMP_COMPACT];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PTR_TRIANGULATION_FROM_POLYHEDRON THEN
  MAP_EVERY EXISTS_TAC [`x1 UNION x2:real^M->bool`; `theta:real^M->A`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_PTR_DIM_POLYHEDRON_UNION THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_PTR_GLUE_HOMEOMORPHIC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PTR_GLUE_PL_CHART THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED]]);;

(* ------------------------------------------------------------------------- *)
(* Real-valued PL combinators, a PL bump on real^3 vanishing                *)
(* exactly on a cube and equal to 1 outside an enlarged cube, and for the  *)
(* main step (Rado's growing, Moise Thm 8.3): the part A of an old complex *)
(* mapped into the new cube is a compact polyhedron, a PL cut-off alpha    *)
(* vanishing exactly on A, and PL maps G (extending phi o t1 from A) and H *)
(* (extending its inverse from the image of A to the cube).                *)
(* ------------------------------------------------------------------------- *)

let MOI_PTR_PL_LIFT_MAX = prove
 (`!(s:real^M->bool) f g.
     pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
     ==> pl_map_on s (\x. lift(max (f x) (g x)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP PL_MAP_ON_LIFT_MAX) THEN
  REWRITE_TAC[LIFT_DROP]);;

let MOI_PTR_PL_LIFT_MIN = prove
 (`!(s:real^M->bool) f g.
     pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
     ==> pl_map_on s (\x. lift(min (f x) (g x)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o MATCH_MP PL_MAP_ON_LIFT_MIN) THEN
  REWRITE_TAC[LIFT_DROP]);;

let MOI_PTR_PL_LIFT_CMUL = prove
 (`!(s:real^M->bool) f c.
     pl_map_on s (\x. lift(f x)) ==> pl_map_on s (\x. lift(c * f x))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(MP_TAC o SPEC `c:real` o MATCH_MP PL_MAP_ON_CMUL) THEN
  REWRITE_TAC[LIFT_CMUL]);;

let MOI_PTR_PL_LIFT_CONST = prove
 (`!(s:real^M->bool) c. locally_polyhedral s ==> pl_map_on s (\x. lift c)`,
  SIMP_TAC[PL_MAP_ON_CONST]);;

let MOI_PTR_PL_LIFT_COORD = prove
 (`!(s:real^M->bool) i d.
     locally_polyhedral s
     ==> pl_map_on s (\x. lift(d - x$i)) /\ pl_map_on s (\x. lift(x$i - d))`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. --(lift(x$i))`; `lift d`]
      PL_MAP_ON_AFFINE) THEN
    ASM_SIMP_TAC[LINEAR_COMPOSE_NEG; LINEAR_LIFT_COMPONENT] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] PL_MAP_ON_EQ) THEN
    REWRITE_TAC[LIFT_SUB] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    MP_TAC(ISPECL [`s:real^M->bool`; `\x:real^M. lift(x$i)`; `--(lift d)`]
      PL_MAP_ON_AFFINE) THEN
    ASM_SIMP_TAC[LINEAR_LIFT_COMPONENT] THEN
    MATCH_MP_TAC(REWRITE_RULE[IMP_CONJ] PL_MAP_ON_EQ) THEN
    REWRITE_TAC[LIFT_SUB] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC]);;

let MOI_PTR_CUBE_BUMP = prove
 (`!(a:real^3) b e.
     &0 < e
     ==> ?beta:real^3->real^1.
           pl_map_on (:real^3) beta /\
           (!w. beta w = vec 0 <=> w IN interval[a,b]) /\
           (!w. ~(w IN interval[a - e % vec 1,b + e % vec 1])
                ==> beta w = lift(&1))`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC
   `\w:real^3. lift(min (&1) (max (&0) (inv e *
       max (max ((a:real^3)$1 - w$1) (w$1 - (b:real^3)$1))
           (max (max (a$2 - w$2) (w$2 - b$2))
                (max (a$3 - w$3) (w$3 - b$3))))))` THEN
  SUBGOAL_THEN `&0 < inv e` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `locally_polyhedral (:real^3)` ASSUME_TAC THENL
     [SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!i. pl_map_on (:real^3)
            (\w:real^3. lift(max ((a:real^3)$i - w$i) (w$i - (b:real^3)$i)))`
    ASSUME_TAC THENL
     [GEN_TAC THEN MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN
      ASM_SIMP_TAC[MOI_PTR_PL_LIFT_COORD];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_PTR_PL_LIFT_MIN THEN
    ASM_SIMP_TAC[MOI_PTR_PL_LIFT_CONST] THEN
    MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN
    ASM_SIMP_TAC[MOI_PTR_PL_LIFT_CONST] THEN
    MATCH_MP_TAC MOI_PTR_PL_LIFT_CMUL THEN
    MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PTR_PL_LIFT_MAX THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `w:real^3` THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ; IN_INTERVAL; DIMINDEX_3; FORALL_3] THEN
    SUBGOAL_THEN `!x. inv e * x <= &0 <=> x <= &0`
     (fun th -> REWRITE_TAC[REAL_ARITH
        `min (&1) (max (&0) x) = &0 <=> x <= &0`; th]) THENL
     [GEN_TAC THEN MP_TAC(SPECL [`x:real`; `&0`; `inv e`] REAL_LE_LMUL_EQ) THEN
      ASM_REWRITE_TAC[REAL_MUL_RZERO];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_MAX_LE] THEN REAL_ARITH_TAC;
    X_GEN_TAC `w:real^3` THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3; VECTOR_SUB_COMPONENT;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    DISCH_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&1 < x ==> min (&1) (max (&0) x) = &1`) THEN
    SUBGOAL_THEN `inv e * e = &1` ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ]; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv e * e` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LT_LMUL_EQ] THEN
    REWRITE_TAC[REAL_LT_MAX] THEN
    FIRST_X_ASSUM(MP_TAC o check (is_neg o concl)) THEN REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* For an old finite triangulation (c1,t1) of s1 and a chart                *)
(* cube k (a polytope inside the chart image): the part A of UNIONS c1     *)
(* mapped into the cube is a compact polyhedron; phi o t1 extends from A   *)
(* to a PL map G on UNIONS c1; its inverse extends from phi(t1(A)) to a PL *)
(* map H on k; and a PL cut-off alpha on UNIONS c1 equal to lift(1) where  *)
(* t1 leaves a compact chart region (PL_MAP_ON_LOCAL).                      *)
(* ------------------------------------------------------------------------- *)

let MOI_PTR_UNION_CUBE_A = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
    (c1:(real^N->bool)->bool) t1 s1 U phi (k:real^3->bool).
     hausdorff_space top /\ pl_manifold_atlas top atlas /\ FINITE c1 /\
     pl_triangulation top atlas c1 t1 s1 /\ (U,phi) IN atlas /\
     polytope k /\ k SUBSET IMAGE phi U
     ==> pl_polyhedron {y | y IN UNIONS c1 /\ t1 y IN U /\ phi(t1 y) IN k}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`]
    MOI_PTR_PL_TRI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`]
    MOI_PTR_PL_TRI_POLYHEDRON) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] MOI_PTR_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `psi:real^3->A`))) THEN
  MATCH_MP_TAC MOI_PTR_COMPACT_LOCALLY_POLYHEDRAL THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`top:A topology`; `U:A->bool`; `phi:A->real^3`;
                   `psi:real^3->A`; `k:real^3->bool`] MOI_PTR_CHART_COMPACT) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT] THEN STRIP_TAC THEN
    MATCH_MP_TAC CLOSED_IN_COMPACT THEN
    EXISTS_TAC `UNIONS c1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t1:real^N->A`;
                   `subtopology euclidean (UNIONS c1:real^N->bool)`;
                   `top:A topology`; `{x:A | x IN U /\ (phi:A->real^3) x IN k}`]
      CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY;
                 IN_ELIM_THM];
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`;
                   `U:A->bool`; `phi:A->real^3`] MOI_PTR_PL_TRI_CHART) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`{y | y IN UNIONS c1 /\ (t1:real^N->A) y IN U}`;
                   `\y. (phi:A->real^3)((t1:real^N->A) y)`; `k:real^3->bool`]
      MOI_PTR_LOCALLY_POLYHEDRAL_PL_PREIMAGE) THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_POLYHEDRON] THEN
    MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONJ_ASSOC]]);;

let MOI_PTR_UNION_CUBE_G = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
    (c1:(real^N->bool)->bool) t1 s1 U phi (k:real^3->bool).
     hausdorff_space top /\ pl_manifold_atlas top atlas /\ FINITE c1 /\
     pl_triangulation top atlas c1 t1 s1 /\ (U,phi) IN atlas /\
     polytope k /\ k SUBSET IMAGE phi U
     ==> ?G. pl_map_on (UNIONS c1) G /\
             !y. y IN UNIONS c1 /\ t1 y IN U /\ phi(t1 y) IN k
                 ==> G y = phi(t1 y)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`;
                 `U:A->bool`; `phi:A->real^3`; `k:real^3->bool`]
    MOI_PTR_UNION_CUBE_A) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`UNIONS c1:real^N->bool`;
                 `{y | y IN UNIONS c1 /\ (t1:real^N->A) y IN U /\
                       (phi:A->real^3)(t1 y) IN k}`;
                 `\y. (phi:A->real^3)((t1:real^N->A) y)`] PL_MAP_EXTENSION) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_PTR_PL_TRI_POLYHEDRON];
    SET_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `{y | y IN UNIONS c1 /\ (t1:real^N->A) y IN U}` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_PTR_PL_TRI_CHART]; SET_TAC[]]]);;

let MOI_PTR_UNION_CUBE_H = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
    (c1:(real^N->bool)->bool) t1 s1 U phi (k:real^3->bool).
     hausdorff_space top /\ pl_manifold_atlas top atlas /\ FINITE c1 /\
     pl_triangulation top atlas c1 t1 s1 /\ (U,phi) IN atlas /\
     polytope k /\ k SUBSET IMAGE phi U
     ==> ?H. pl_map_on k H /\
             !y. y IN UNIONS c1 /\ t1 y IN U /\ phi(t1 y) IN k
                 ==> H(phi(t1 y)) = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`;
                 `U:A->bool`; `phi:A->real^3`; `k:real^3->bool`]
    MOI_PTR_UNION_CUBE_A) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`]
    MOI_PTR_PL_TRI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] MOI_PTR_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `psi:real^3->A`))) THEN
  MP_TAC(ISPECL [`top:A topology`; `U:A->bool`; `phi:A->real^3`;
                 `psi:real^3->A`] MOI_PTR_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `pl_map_on {y | y IN UNIONS c1 /\ (t1:real^N->A) y IN U /\
                   (phi:A->real^3)(t1 y) IN k} (\y. phi(t1 y))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `{y | y IN UNIONS c1 /\ (t1:real^N->A) y IN U}` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_PTR_PL_TRI_CHART]; SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`{y | y IN UNIONS c1 /\ (t1:real^N->A) y IN U /\ (phi:A->real^3)(t1 y) IN k}`;
    `\y. (phi:A->real^3)((t1:real^N->A) y)`;
    `IMAGE (\y. (phi:A->real^3)((t1:real^N->A) y))
           {y | y IN UNIONS c1 /\ t1 y IN U /\ phi(t1 y) IN k}`]
   HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT; PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`y1:real^N`; `y2:real^N`] THEN STRIP_TAC THEN
    UNDISCH_TAC `(phi:A->real^3)((t1:real^N->A) y1) = phi(t1 y2)` THEN
    DISCH_THEN(MP_TAC o AP_TERM `psi:real^3->A`) THEN ASM_SIMP_TAC[] THEN
    ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_TAC `g:real^3->real^N`)] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [homeomorphism]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
  MP_TAC(ISPECL
   [`k:real^3->bool`;
    `IMAGE (\y. (phi:A->real^3)((t1:real^N->A) y))
           {y | y IN UNIONS c1 /\ t1 y IN U /\ phi(t1 y) IN k}`;
    `g:real^3->real^N`] PL_MAP_EXTENSION) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON];
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
      MATCH_MP_TAC PL_MAP_ON_HOMEOMORPHISM_INVERSE THEN
      MAP_EVERY EXISTS_TAC
       [`{y | y IN UNIONS c1 /\ (t1:real^N->A) y IN U /\
              (phi:A->real^3)(t1 y) IN k}`;
        `\y. (phi:A->real^3)((t1:real^N->A) y)`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `H:real^3->real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `(H:real^3->real^N)((phi:A->real^3)((t1:real^N->A) y)) = g(phi(t1 y))`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[]]);;

let MOI_PTR_UNION_CUBE_ALPHA = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
    (c1:(real^N->bool)->bool) t1 s1 U phi (beta:real^3->real^1) k.
     hausdorff_space top /\ pl_manifold_atlas top atlas /\ FINITE c1 /\
     pl_triangulation top atlas c1 t1 s1 /\ (U,phi) IN atlas /\
     compact k /\ k SUBSET IMAGE phi U /\ pl_map_on (:real^3) beta /\
     (!w. ~(w IN k) ==> beta w = lift(&1))
     ==> pl_map_on (UNIONS c1)
           (\y. if t1 y IN U then beta(phi(t1 y)) else lift(&1))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`]
    MOI_PTR_PL_TRI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] MOI_PTR_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `psi:real^3->A`))) THEN
  MP_TAC(ISPECL [`top:A topology`; `U:A->bool`; `phi:A->real^3`;
                 `psi:real^3->A`; `k:real^3->bool`] MOI_PTR_CHART_COMPACT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ONCE_REWRITE_TAC[PL_MAP_ON_LOCAL] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(t1:real^N->A) y IN U` THENL
   [MP_TAC(ISPECL [`t1:real^N->A`;
                   `subtopology euclidean (UNIONS c1:real^N->bool)`;
                   `top:A topology`; `U:A->bool`]
      OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "weq"))) THEN
    EXISTS_TAC `w:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [USE_THEN "weq" MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "weq" (SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC
     `(beta:real^3->real^1) o (\y. (phi:A->real^3)((t1:real^N->A) y))` THEN
    CONJ_TAC THENL [SIMP_TAC[IN_ELIM_THM; o_THM]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN ASM_MESON_TAC[MOI_PTR_PL_TRI_CHART];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t1:real^N->A`;
                 `subtopology euclidean (UNIONS c1:real^N->bool)`;
                 `top:A topology`; `{x:A | x IN U /\ (phi:A->real^3) x IN k}`]
    CLOSED_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_SIMP_TAC[COMPACT_IN_IMP_CLOSED_IN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `subtopology euclidean (UNIONS c1:real^N->bool)`
    OPEN_IN_TOPSPACE) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS c1:real^N->bool)`;
                 `UNIONS c1:real^N->bool`;
                 `{z | z IN UNIONS c1 /\
                       (t1:real^N->A) z IN {x | x IN U /\ (phi:A->real^3) x IN k}}`]
    OPEN_IN_DIFF) THEN
  ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "weq"))) THEN
  EXISTS_TAC `w:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [USE_THEN "weq" MP_TAC THEN REWRITE_TAC[EXTENSION; IN_DIFF; IN_INTER;
                                          IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\z:real^N. lift(&1)` THEN
  CONJ_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "weq" (MP_TAC o SPEC `z:real^N` o
      REWRITE_RULE[EXTENSION; IN_DIFF; IN_INTER; IN_ELIM_THM]) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^N) IN UNIONS c1 INTER w` THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN COND_CASES_TAC THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_CONST THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The combinatorics of the graph trick.  The old polyhedron                *)
(* s0 is embedded by F1 (graph of G and alpha), the cube k by F2 (graph of *)
(* H and vec 0); the two images meet exactly over A (where alpha vanishes) *)
(* and theta (t1 on the first image, the chart inverse psi on the second)  *)
(* is well defined and injective on their union.                           *)
(* ------------------------------------------------------------------------- *)

let MOI_PTR_PASTECART3_EQ = prove
 (`!p q:real^((M,N)finite_sum,P)finite_sum.
     p = q <=> fstcart(fstcart p) = fstcart(fstcart q) /\
               sndcart(fstcart p) = sndcart(fstcart q) /\
               sndcart p = sndcart q`,
  MESON_TAC[PASTECART_EQ]);;

let MOI_PTR_PL_MAP_ON_LINEAR = prove
 (`!(s:real^M->bool) (l:real^M->real^N).
     locally_polyhedral s /\ linear l ==> pl_map_on s l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^M->bool`; `l:real^M->real^N`; `vec 0:real^N`]
    PL_MAP_ON_AFFINE) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_RID; ETA_AX]);;

let MOI_PTR_UNION_CUBE_KEY = prove
 (`!(s0:real^N->bool) (k:real^M->bool) (t1:real^N->A) U (phi:A->real^M) psi
    (G:real^N->real^M) (alpha:real^N->real^P) (H:real^M->real^N)
    (F1:real^N->real^((N,M)finite_sum,P)finite_sum) F2
    (theta:real^((N,M)finite_sum,P)finite_sum->A).
     (!y. y IN s0 ==> fstcart(fstcart(F1 y)) = y /\
                      sndcart(fstcart(F1 y)) = G y /\
                      sndcart(F1 y) = alpha y) /\
     (!z. fstcart(fstcart(F2 z)) = H z /\ sndcart(fstcart(F2 z)) = z /\
          sndcart(F2 z) = vec 0) /\
     (!p. p IN IMAGE F1 s0 ==> theta p = t1(fstcart(fstcart p))) /\
     (!p. ~(p IN IMAGE F1 s0) ==> theta p = psi(sndcart(fstcart p))) /\
     (!y. y IN s0 /\ t1 y IN U /\ phi(t1 y) IN k
          ==> G y = phi(t1 y) /\ H(phi(t1 y)) = y) /\
     (!y. y IN s0 ==> (alpha y = vec 0 <=> t1 y IN U /\ phi(t1 y) IN k)) /\
     (!x. x IN U ==> psi(phi x) = x) /\
     (!w. w IN IMAGE phi U ==> psi w IN U /\ phi(psi w) = w) /\
     k SUBSET IMAGE phi U /\
     (!x y. x IN s0 /\ y IN s0 ==> (t1 x = t1 y <=> x = y))
     ==> (!y. y IN s0 ==> theta(F1 y) = t1 y) /\
         (!z. z IN k ==> theta(F2 z) = psi z) /\
         (!p q. p IN IMAGE F1 s0 UNION IMAGE F2 k /\
                q IN IMAGE F1 s0 UNION IMAGE F2 k /\ theta p = theta q
                ==> p = q)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!y z. y IN s0 /\ z IN k /\
          (F1:real^N->real^((N,M)finite_sum,P)finite_sum) y = F2 z
          ==> ((t1:real^N->A) y IN U /\ (phi:A->real^M)(t1 y) IN k) /\
              z = phi(t1 y)`
  (LABEL_TAC "K3") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    UNDISCH_TAC
     `(F1:real^N->real^((N,M)finite_sum,P)finite_sum) y = F2 (z:real^M)` THEN
    ONCE_REWRITE_TAC[MOI_PTR_PASTECART3_EQ] THEN ASM_SIMP_TAC[] THEN
    STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN s0 /\ (t1:real^N->A) y IN U /\ (phi:A->real^M)(t1 y) IN k
        ==> (F1:real^N->real^((N,M)finite_sum,P)finite_sum) y = F2(phi(t1 y))`
  (LABEL_TAC "K6") THENL
   [REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[MOI_PTR_PASTECART3_EQ] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN s0
        ==> (theta:real^((N,M)finite_sum,P)finite_sum->A)
              ((F1:real^N->real^((N,M)finite_sum,P)finite_sum) y) =
            (t1:real^N->A) y`
  (LABEL_TAC "K5") THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN
     `(F1:real^N->real^((N,M)finite_sum,P)finite_sum) y IN IMAGE F1 s0`
    ASSUME_TAC THENL [ASM_SIMP_TAC[FUN_IN_IMAGE]; ALL_TAC] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!z. z IN k
        ==> (theta:real^((N,M)finite_sum,P)finite_sum->A)
              ((F2:real^M->real^((N,M)finite_sum,P)finite_sum) z) =
            (psi:real^M->A) z`
  (LABEL_TAC "K4") THENL
   [X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    ASM_CASES_TAC
     `(F2:real^M->real^((N,M)finite_sum,P)finite_sum) z IN
      IMAGE (F1:real^N->real^((N,M)finite_sum,P)finite_sum) s0`
    THENL
     [FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC o
        REWRITE_RULE[IN_IMAGE]) THEN
      REMOVE_THEN "K3" (MP_TAC o SPECL [`y:real^N`; `z:real^M`]) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      ASM_SIMP_TAC[];
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y z. y IN s0 /\ (z:real^M) IN k /\
          (theta:real^((N,M)finite_sum,P)finite_sum->A)
            ((F1:real^N->real^((N,M)finite_sum,P)finite_sum) y) =
          theta(F2 z)
          ==> F1 y = F2 z`
  (LABEL_TAC "K7") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(t1:real^N->A) y = (psi:real^M->A) z` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^M) IN IMAGE (phi:A->real^M) U` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(t1:real^N->A) y IN U /\ (phi:A->real^M)(t1 y) = z`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REMOVE_THEN "K6" (MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  REWRITE_TAC[IN_UNION; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THENL
   [ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    SUBGOAL_THEN `(psi:real^M->A) x = psi x'` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `phi:A->real^M`) THEN
    SUBGOAL_THEN `(x:real^M) IN IMAGE (phi:A->real^M) U /\ x' IN IMAGE phi U`
    STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Assembly of the main step (PL_TRIANGULATION_UNION_CUBE).  Given G, alpha, *)
(* H and the graph embeddings F1, F2 into                                    *)
(* real^((N,3)finite_sum,1)finite_sum, the union of the two graphs is a      *)
(* dimension-3 compact polyhedron mapped homeomorphically onto s1 UNION      *)
(* (chart cube) by theta, PL in every chart; MOI_PTR_GLUE_TRIANGULATION      *)
(* realizes it in real^N.                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_PTR_LINEAR_PROJ = prove
 (`linear (\p:real^((M,N)finite_sum,P)finite_sum. fstcart(fstcart p)) /\
   linear (\p:real^((M,N)finite_sum,P)finite_sum. sndcart(fstcart p))`,
  REWRITE_TAC[linear; FSTCART_ADD; FSTCART_CMUL; SNDCART_ADD; SNDCART_CMUL]);;

let MOI_PTR_UNION_CUBE_GLUE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
    (c1:(real^N->bool)->bool) t1 s1 U phi psi (a:real^3) b
    (G:real^N->real^3) (alpha:real^N->real^1) (H:real^3->real^N)
    (F1:real^N->real^((N,3)finite_sum,1)finite_sum)
    (F2:real^3->real^((N,3)finite_sum,1)finite_sum)
    (theta:real^((N,3)finite_sum,1)finite_sum->A).
     hausdorff_space top /\ pl_manifold_atlas top atlas /\ 7 <= dimindex(:N) /\
     FINITE c1 /\ pl_triangulation top atlas c1 t1 s1 /\ (U,phi) IN atlas /\
     homeomorphic_maps (subtopology top U,subtopology euclidean (IMAGE phi U))
                       (phi,psi) /\
     interval[a,b] SUBSET IMAGE phi U /\
     pl_map_on (UNIONS c1) F1 /\ pl_map_on (interval[a,b]) F2 /\
     (!y. y IN UNIONS c1 ==> fstcart(fstcart(F1 y)) = y /\
                             sndcart(fstcart(F1 y)) = G y /\
                             sndcart(F1 y) = alpha y) /\
     (!z. fstcart(fstcart(F2 z)) = H z /\ sndcart(fstcart(F2 z)) = z /\
          sndcart(F2 z) = vec 0) /\
     (!p. p IN IMAGE F1 (UNIONS c1) ==> theta p = t1(fstcart(fstcart p))) /\
     (!p. ~(p IN IMAGE F1 (UNIONS c1))
          ==> theta p = psi(sndcart(fstcart p))) /\
     (!y. y IN UNIONS c1 /\ t1 y IN U /\ phi(t1 y) IN interval[a,b]
          ==> G y = phi(t1 y) /\ H(phi(t1 y)) = y) /\
     (!y. y IN UNIONS c1
          ==> (alpha y = vec 0 <=> t1 y IN U /\ phi(t1 y) IN interval[a,b]))
     ==> ?(c:(real^N->bool)->bool) t.
           FINITE c /\
           pl_triangulation top atlas c t
             (s1 UNION {x | x IN U /\ phi x IN interval[a,b]})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`]
    MOI_PTR_PL_TRI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`]
    MOI_PTR_PL_TRI_POLYHEDRON) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] MOI_PTR_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`top:A topology`; `U:A->bool`; `phi:A->real^3`;
                 `psi:real^3->A`] MOI_PTR_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `U:A->bool`; `phi:A->real^3`;
                 `psi:real^3->A`; `interval[a:real^3,b]`]
    MOI_PTR_CHART_COMPACT) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS c1:real^N->bool`; `interval[a:real^3,b]`;
                 `t1:real^N->A`; `U:A->bool`; `phi:A->real^3`;
                 `psi:real^3->A`; `G:real^N->real^3`; `alpha:real^N->real^1`;
                 `H:real^3->real^N`;
                 `F1:real^N->real^((N,3)finite_sum,1)finite_sum`;
                 `F2:real^3->real^((N,3)finite_sum,1)finite_sum`;
                 `theta:real^((N,3)finite_sum,1)finite_sum->A`]
    MOI_PTR_UNION_CUBE_KEY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `pl_polyhedron (IMAGE (F1:real^N->real^((N,3)finite_sum,1)finite_sum)
                         (UNIONS c1)) /\
    pl_polyhedron (IMAGE (F2:real^3->real^((N,3)finite_sum,1)finite_sum)
                         (interval[a,b]))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map
      (subtopology euclidean
        (IMAGE (F1:real^N->real^((N,3)finite_sum,1)finite_sum) (UNIONS c1)),
       top) (theta:real^((N,3)finite_sum,1)finite_sum->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `(t1:real^N->A) o
                (\p:real^((N,3)finite_sum,1)finite_sum. fstcart(fstcart p))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (UNIONS c1:real^N->bool)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MOI_PTR_LINEAR_PROJ];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `continuous_map
      (subtopology euclidean
        (IMAGE (F2:real^3->real^((N,3)finite_sum,1)finite_sum) (interval[a,b])),
       top) (theta:real^((N,3)finite_sum,1)finite_sum->A)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_MAP_EQ THEN
    EXISTS_TAC `(psi:real^3->A) o
                (\p:real^((N,3)finite_sum,1)finite_sum. sndcart(fstcart p))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; o_THM; FORALL_IN_IMAGE] THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_MAP_COMPOSE THEN
    EXISTS_TAC `subtopology euclidean (IMAGE (phi:A->real^3) U)` THEN
    ASM_REWRITE_TAC[CONTINUOUS_MAP_EUCLIDEAN2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MOI_PTR_LINEAR_PROJ];
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:((N,3)finite_sum,1)finite_sum`,`:M`]
    MOI_PTR_GLUE_TRIANGULATION) THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (F1:real^N->real^((N,3)finite_sum,1)finite_sum) (UNIONS c1)`;
    `IMAGE (F2:real^3->real^((N,3)finite_sum,1)finite_sum) (interval[a,b])`;
    `theta:real^((N,3)finite_sum,1)finite_sum->A`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_PTR_DIM_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PTR_TRIANGULATION_DIM3 THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`;
                          `atlas:((A->bool)#(A->real^3))->bool`;
                          `t1:real^N->A`; `s1:A->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_PTR_DIM_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PTR_DIM_POLYHEDRON_POLYTOPE THEN
    REWRITE_TAC[POLYTOPE_INTERVAL] THEN
    MP_TAC(ISPEC `interval[a:real^3,b]` AFF_DIM_LE_UNIV) THEN
    REWRITE_TAC[DIMINDEX_3];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    SUBGOAL_THEN
     `IMAGE (theta:real^((N,3)finite_sum,1)finite_sum->A)
            (IMAGE (F1:real^N->real^((N,3)finite_sum,1)finite_sum)
                   (UNIONS c1)) =
      IMAGE (t1:real^N->A) (UNIONS c1)`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x:real^N. x IN s ==> (f:real^N->A) x = g x)
        ==> IMAGE f s = IMAGE g s`) THEN
      ASM_SIMP_TAC[o_THM];
      ASM_REWRITE_TAC[]];
    SUBGOAL_THEN
     `IMAGE (theta:real^((N,3)finite_sum,1)finite_sum->A)
            (IMAGE (F2:real^3->real^((N,3)finite_sum,1)finite_sum)
                   (interval[a,b])) =
      IMAGE (psi:real^3->A) (interval[a,b])`
    SUBST1_TAC THENL
     [REWRITE_TAC[GSYM IMAGE_o] THEN
      MATCH_MP_TAC(SET_RULE
       `(!x:real^3. x IN s ==> (f:real^3->A) x = g x)
        ==> IMAGE f s = IMAGE g s`) THEN
      ASM_SIMP_TAC[o_THM];
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    FIRST_ASSUM ACCEPT_TAC;
    MAP_EVERY X_GEN_TAC [`V:A->bool`; `chi:A->real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `open_in top (V:A->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_PTR_CHART_MAPS]; ALL_TAC] THEN
    SUBGOAL_THEN
     `locally_polyhedral
        {p | p IN IMAGE (F1:real^N->real^((N,3)finite_sum,1)finite_sum)
                        (UNIONS c1) /\
             (theta:real^((N,3)finite_sum,1)finite_sum->A) p IN V}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_PTR_LOCALLY_POLYHEDRAL_PREIMAGE_OPEN THEN
      EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
      ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\p:real^((N,3)finite_sum,1)finite_sum.
                  (chi:A->real^3)((t1:real^N->A)(fstcart(fstcart p)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_PTR_PL_TRI_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`;
                          `atlas:((A->bool)#(A->real^3))->bool`;
                          `c1:(real^N->bool)->bool`; `s1:A->bool`;
                          `V:A->bool`] THEN
    ASM_SIMP_TAC[MOI_PTR_PL_MAP_ON_LINEAR; MOI_PTR_LINEAR_PROJ] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`V:A->bool`; `chi:A->real^3`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `open_in top (V:A->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_PTR_CHART_MAPS]; ALL_TAC] THEN
    SUBGOAL_THEN
     `locally_polyhedral
        {p | p IN IMAGE (F2:real^3->real^((N,3)finite_sum,1)finite_sum)
                        (interval[a,b]) /\
             (theta:real^((N,3)finite_sum,1)finite_sum->A) p IN V}`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_PTR_LOCALLY_POLYHEDRAL_PREIMAGE_OPEN THEN
      EXISTS_TAC `top:A topology` THEN
      ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
      ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\p:real^((N,3)finite_sum,1)finite_sum.
                  (chi:A->real^3)((psi:real^3->A)(sndcart(fstcart p)))` THEN
    CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
      REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_PTR_PL_CHART_COMPOSE THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`;
                          `atlas:((A->bool)#(A->real^3))->bool`;
                          `U:A->bool`; `phi:A->real^3`; `V:A->bool`] THEN
    ASM_SIMP_TAC[MOI_PTR_PL_MAP_ON_LINEAR; MOI_PTR_LINEAR_PROJ] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN REPEAT STRIP_TAC THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl))) THEN
    ASM_SIMP_TAC[] THENL [ASM SET_TAC[]; ASM_MESON_TAC[]]]);;

let PL_TRIANGULATION_UNION_CUBE = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
    (c1:(real^N->bool)->bool) t1 s1 U phi (a:real^3) b e.
     hausdorff_space top /\ pl_manifold_atlas top atlas /\ 7 <= dimindex(:N) /\
     FINITE c1 /\ pl_triangulation top atlas c1 t1 s1 /\
     (U,phi) IN atlas /\ &0 < e /\
     interval[a - e % vec 1,b + e % vec 1] SUBSET IMAGE phi U
     ==> ?(c:(real^N->bool)->bool) t.
           FINITE c /\
           pl_triangulation top atlas c t
             (s1 UNION {x | x IN U /\ phi x IN interval[a,b]})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `interval[a:real^3,b] SUBSET IMAGE (phi:A->real^3) U`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interval[a - e % vec 1:real^3,b + e % vec 1]` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_INTERVAL; VECTOR_SUB_COMPONENT;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < e` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`]
    MOI_PTR_PL_TRI_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] MOI_PTR_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `psi:real^3->A`))) THEN
  MP_TAC(ISPECL [`a:real^3`; `b:real^3`; `e:real`] MOI_PTR_CUBE_BUMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `beta:real^3->real^1` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`;
                 `U:A->bool`; `phi:A->real^3`; `beta:real^3->real^1`;
                 `interval[a - e % vec 1:real^3,b + e % vec 1]`]
    MOI_PTR_UNION_CUBE_ALPHA) THEN
  ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`;
                 `U:A->bool`; `phi:A->real^3`; `interval[a:real^3,b]`]
    MOI_PTR_UNION_CUBE_G) THEN
  ASM_REWRITE_TAC[POLYTOPE_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^N->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `c1:(real^N->bool)->bool`; `t1:real^N->A`; `s1:A->bool`;
                 `U:A->bool`; `phi:A->real^3`; `interval[a:real^3,b]`]
    MOI_PTR_UNION_CUBE_H) THEN
  ASM_REWRITE_TAC[POLYTOPE_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `H:real^3->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?alpha:real^N->real^1.
      pl_map_on (UNIONS c1) alpha /\
      !y. y IN UNIONS c1
          ==> (alpha y = vec 0 <=>
               (t1:real^N->A) y IN U /\ (phi:A->real^3)(t1 y) IN interval[a,b])`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\y. if (t1:real^N->A) y IN U
                    then (beta:real^3->real^1)((phi:A->real^3)(t1 y))
                    else lift(&1)` THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM LIFT_NUM; LIFT_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?F1:real^N->real^((N,3)finite_sum,1)finite_sum.
      pl_map_on (UNIONS c1) F1 /\
      !y. y IN UNIONS c1 ==> fstcart(fstcart(F1 y)) = y /\
                             sndcart(fstcart(F1 y)) = (G:real^N->real^3) y /\
                             sndcart(F1 y) = (alpha:real^N->real^1) y`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\y:real^N. pastecart (pastecart y ((G:real^N->real^3) y))
                                     ((alpha:real^N->real^1) y)` THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    MATCH_MP_TAC PL_MAP_ON_PASTECART THEN ASM_REWRITE_TAC[ETA_AX] THEN
    MATCH_MP_TAC PL_MAP_ON_PASTECART THEN ASM_REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?F2:real^3->real^((N,3)finite_sum,1)finite_sum.
      pl_map_on (interval[a,b]) F2 /\
      !z. fstcart(fstcart(F2 z)) = (H:real^3->real^N) z /\
          sndcart(fstcart(F2 z)) = z /\ sndcart(F2 z) = vec 0`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\z:real^3. pastecart (pastecart ((H:real^3->real^N) z) z)
                                     (vec 0:real^1)` THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART] THEN
    SUBGOAL_THEN `locally_polyhedral (interval[a:real^3,b])` ASSUME_TAC THENL
     [SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_INTERVAL]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_PASTECART THEN
    ASM_SIMP_TAC[ETA_AX; PL_MAP_ON_CONST] THEN
    MATCH_MP_TAC PL_MAP_ON_PASTECART THEN ASM_REWRITE_TAC[ETA_AX] THEN
    ASM_REWRITE_TAC[GSYM LOCALLY_POLYHEDRAL_EQ_PL_MAP_ON_ID];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?theta:real^((N,3)finite_sum,1)finite_sum->A.
      (!p. p IN IMAGE (F1:real^N->real^((N,3)finite_sum,1)finite_sum)
                      (UNIONS c1)
           ==> theta p = (t1:real^N->A)(fstcart(fstcart p))) /\
      (!p. ~(p IN IMAGE F1 (UNIONS c1))
           ==> theta p = (psi:real^3->A)(sndcart(fstcart p)))`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `\p. if p IN IMAGE (F1:real^N->real^((N,3)finite_sum,1)finite_sum)
                                  (UNIONS c1)
                    then (t1:real^N->A)(fstcart(fstcart p))
                    else (psi:real^3->A)(sndcart(fstcart p))` THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_PTR_UNION_CUBE_GLUE THEN
  MAP_EVERY EXISTS_TAC
   [`c1:(real^N->bool)->bool`; `t1:real^N->A`; `psi:real^3->A`; `G:real^N->real^3`; `alpha:real^N->real^1`;
    `H:real^3->real^N`; `F1:real^N->real^((N,3)finite_sum,1)finite_sum`;
    `F2:real^3->real^((N,3)finite_sum,1)finite_sum`;
    `theta:real^((N,3)finite_sum,1)finite_sum->A`] THEN
  ASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Compact parts (Moise Thm 8.3, compact case).  Every point lies in the     *)
(* open interior of a chart cube with a margin; finitely many cover a        *)
(* compact set k, and the union of the closed cubes is triangulated one cube *)
(* at a time (PL_TRIANGULATION_UNION_CUBE).  A compact PL 3-manifold is the  *)
(* union.                                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_PTR_OPEN_CONTAINS_CUBE = prove
 (`!s:real^3->bool x.
     open s /\ x IN s
     ==> ?a b e. &0 < e /\ x IN interval(a,b) /\
                 interval[a - e % vec 1,b + e % vec 1] SUBSET s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` OPEN_CONTAINS_INTERVAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:real^3` (X_CHOOSE_THEN `b0:real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `?e. &0 < e /\
        !i. 1 <= i /\ i <= 3
            ==> e < (x:real^3)$i - (a0:real^3)$i /\ e < (b0:real^3)$i - x$i`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN interval(a0,b0)` THEN
    REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; FORALL_3] THEN STRIP_TAC THEN
    EXISTS_TAC
     `min (min (min ((x:real^3)$1 - (a0:real^3)$1) ((b0:real^3)$1 - x$1))
               (min (x$2 - a0$2) (b0$2 - x$2)))
          (min (x$3 - a0$3) (b0$3 - x$3)) / &2` THEN
    REWRITE_TAC[FORALL_3] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`(a0:real^3) + e % vec 1`; `(b0:real^3) - e % vec 1`; `e:real`] THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `((a:real^N) + e % v) - e % v = a`;
                  VECTOR_ARITH `((b:real^N) - e % v) + e % v = b`] THEN
  REWRITE_TAC[IN_INTERVAL; DIMINDEX_3; VECTOR_ADD_COMPONENT;
              VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
  X_GEN_TAC `i:num` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
  REAL_ARITH_TAC);;

let MOI_PTR_CHART_CUBE_AT = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) x.
     pl_manifold_atlas top atlas /\ x IN topspace top
     ==> ?U phi a b e.
           (U,phi) IN atlas /\ &0 < e /\
           interval[a - e % vec 1,b + e % vec 1] SUBSET IMAGE phi U /\
           x IN {y | y IN U /\ phi y IN interval(a,b)} /\
           open_in top {y | y IN U /\ phi y IN interval(a,b)}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?U (phi:A->real^3).
                  (U,phi) IN (atlas:((A->bool)#(A->real^3))->bool) /\ x IN U`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_manifold_atlas (top:A topology)
                   (atlas:((A->bool)#(A->real^3))->bool)` THEN
    REWRITE_TAC[pl_manifold_atlas] THEN
    DISCH_THEN(MP_TAC o SPEC `x:A` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `U:A->bool`; `phi:A->real^3`] MOI_PTR_CHART_MAPS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `psi:real^3->A`))) THEN
  MP_TAC(ISPECL [`top:A topology`; `U:A->bool`; `phi:A->real^3`;
                 `psi:real^3->A`] MOI_PTR_CHART_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE (phi:A->real^3) U`; `(phi:A->real^3) x`]
    MOI_PTR_OPEN_CONTAINS_CUBE) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3`
    (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`U:A->bool`; `phi:A->real^3`; `a:real^3`;
                        `b:real^3`; `e:real`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `U:A->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`phi:A->real^3`; `subtopology top (U:A->bool)`;
                 `euclidean:(real^3)topology`; `interval(a:real^3,b)`]
    OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_REWRITE_TAC[GSYM OPEN_IN; OPEN_INTERVAL; TOPSPACE_SUBTOPOLOGY] THEN
  ASM_SIMP_TAC[SET_RULE `(U:A->bool) SUBSET t ==> t INTER U = U`]);;

let MOI_PTR_FINITE_CUBES = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
    (UU:K->A->bool) (PH:K->A->real^3) AA BB EE.
     hausdorff_space top /\ pl_manifold_atlas top atlas /\ 7 <= dimindex(:N)
     ==> !xs. FINITE xs /\
              (!i. i IN xs
                   ==> (UU i,PH i) IN atlas /\ &0 < EE i /\
                       interval[AA i - EE i % vec 1,BB i + EE i % vec 1] SUBSET
                       IMAGE (PH i) (UU i))
              ==> ?(c:(real^N->bool)->bool) t.
                    FINITE c /\
                    pl_triangulation top atlas c t
                      (UNIONS (IMAGE (\i. {y | y IN UU i /\
                                               PH i y IN interval[AA i,BB i]})
                                     xs))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0] THEN
    EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    EXISTS_TAC `\y:real^N. (@z:A. T)` THEN
    REWRITE_TAC[FINITE_EMPTY; PL_TRIANGULATION_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`j:K`; `xs:K->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[FORALL_IN_INSERT] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:(real^N->bool)->bool`
    (X_CHOOSE_THEN `t1:real^N->A` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[IMAGE_CLAUSES; UNIONS_INSERT] THEN
  ONCE_REWRITE_TAC[UNION_COMM] THEN
  MATCH_MP_TAC PL_TRIANGULATION_UNION_CUBE THEN
  MAP_EVERY EXISTS_TAC [`c1:(real^N->bool)->bool`; `t1:real^N->A`;
                        `(EE:K->real) j`] THEN
  ASM_REWRITE_TAC[ETA_AX]);;

let PL_TRIANGULATION_COMPACT_NBHD = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool) k.
     hausdorff_space top /\ pl_manifold_atlas top atlas /\ compact_in top k /\
     7 <= dimindex(:N)
     ==> ?(c:(real^N->bool)->bool) t s.
           FINITE c /\ pl_triangulation top atlas c t s /\
           compact_in top s /\ k SUBSET top interior_of s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:A. x IN k
          ==> ?U phi a b e.
                (U,phi) IN (atlas:((A->bool)#(A->real^3))->bool) /\ &0 < e /\
                interval[a - e % vec 1,b + e % vec 1] SUBSET IMAGE phi U /\
                x IN {y | y IN U /\ phi y IN interval(a,b)} /\
                open_in top {y | y IN U /\ phi y IN interval(a,b)}`
  (MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_PTR_CHART_CUBE_AT THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[COMPACT_IN_SUBSET_TOPSPACE; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`UU:A->A->bool`; `PH:A->A->real^3`; `AA:A->real^3`;
                       `BB:A->real^3`; `EE:A->real`] THEN
  DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [compact_in] o
    check (fun th -> is_comb(concl th) &&
                     fst(dest_const(fst(strip_comb(concl th)))) = "compact_in")) THEN
  DISCH_THEN(MP_TAC o SPEC
   `IMAGE (\x:A. {y | y IN (UU:A->A->bool) x /\
                      (PH:A->A->real^3) x y IN interval((AA:A->real^3) x,
                                                        (BB:A->real^3) x)}) k`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:A` THEN DISCH_TAC THEN EXISTS_TAC `x:A` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[EXISTS_FINITE_SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `xs:A->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `UU:A->A->bool`; `PH:A->A->real^3`; `AA:A->real^3`;
                 `BB:A->real^3`; `EE:A->real`] MOI_PTR_FINITE_CUBES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `xs:A->bool`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(i:A) IN k` (fun th -> ASM_MESON_TAC[th]) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool`
    (X_CHOOSE_THEN `t:real^N->A` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC
   [`c:(real^N->bool)->bool`; `t:real^N->A`;
    `UNIONS (IMAGE (\i:A. {y | y IN (UU:A->A->bool) i /\
                               (PH:A->A->real^3) i y IN
                               interval[(AA:A->real^3) i,(BB:A->real^3) i]})
                   xs)`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC COMPACT_IN_UNIONS THEN
    ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `i:A` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(i:A) IN k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `i:A` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                   `(UU:A->A->bool) i`; `(PH:A->A->real^3) i`]
      MOI_PTR_CHART_MAPS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_TAC `psi:real^3->A`))) THEN
    MP_TAC(ISPECL [`top:A topology`; `(UU:A->A->bool) i`;
                   `(PH:A->A->real^3) i`; `psi:real^3->A`;
                   `interval[(AA:A->real^3) i,(BB:A->real^3) i]`]
      MOI_PTR_CHART_COMPACT) THEN
    ASM_REWRITE_TAC[COMPACT_INTERVAL] THEN ANTS_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `interval[(AA:A->real^3) i - (EE:A->real) i % vec 1,
                           (BB:A->real^3) i + EE i % vec 1]` THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_INTERVAL; VECTOR_SUB_COMPONENT;
                  VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN X_GEN_TAC `m:num` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `&0 < (EE:A->real) i` THEN
      REAL_ARITH_TAC;
      SIMP_TAC[]];
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC
     `UNIONS (IMAGE (\x:A. {y | y IN (UU:A->A->bool) x /\
                                (PH:A->A->real^3) x y IN
                                interval((AA:A->real^3) x,(BB:A->real^3) x)})
                    xs)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC UNIONS_MONO_IMAGE THEN X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[INTERVAL_OPEN_SUBSET_CLOSED; SUBSET];
      MATCH_MP_TAC OPEN_IN_UNIONS THEN REWRITE_TAC[FORALL_IN_IMAGE] THEN
      X_GEN_TAC `x:A` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(x:A) IN k` (fun th -> ASM_MESON_TAC[th]) THEN
      ASM SET_TAC[]]]);;

let PL_TRIANGULATION_COMPACT_EXISTS = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool).
     hausdorff_space top /\ compact_space top /\ pl_manifold_atlas top atlas /\
     7 <= dimindex(:N)
     ==> ?(c:(real^N->bool)->bool) t.
           FINITE c /\ pl_triangulation top atlas c t (topspace top)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `atlas:((A->bool)#(A->real^3))->bool`;
                 `topspace top:A->bool`] PL_TRIANGULATION_COMPACT_NBHD) THEN
  ASM_REWRITE_TAC[GSYM compact_space] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` (X_CHOOSE_THEN `t:real^N->A`
    (X_CHOOSE_THEN `s:A->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `t:real^N->A`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_triangulation (top:A topology)
                 (atlas:((A->bool)#(A->real^3))->bool)
                 (c:(real^N->bool)->bool) t s` THEN
  ONCE_REWRITE_TAC[MOI_PTR_PL_TRIANGULATION_RESTRICT] THEN
  MATCH_MP_TAC(TAUT `(p <=> q) ==> p ==> q`) THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`top:A topology`; `s:A->bool`] INTERIOR_OF_SUBSET) THEN
  ASM SET_TAC[]);;

