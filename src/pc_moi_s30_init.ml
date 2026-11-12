needs "src/pc_moi_s3032_stmt.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_fnd_m3b.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s30_init: an initial separating surface (Moise, Geometric        *)
(* Topology in Dimensions 2 and 3, GTM 47, p.216, the first paragraphs of  *)
(* 30.4 and 30.6).  Main theorem (statement of pc_moi_s3032_stmt.ml):       *)
(*   INIT_SURFACE = MOI_S30_INIT_SURFACE                                    *)
(* Route.  A compact set a in an open set v of real^3 has a finite           *)
(* combinatorial 3-manifold neighbourhood w inside v: the second derived     *)
(* neighbourhood of the simplices meeting a in a fine barycentric            *)
(* triangulation of a big tetrahedron (only the manifold half of             *)
(* DERIVED_NBHD_MANIFOLD is used).  Its complex boundary c separates a from  *)
(* b (the interior of UNIONS w is UNIONS w minus c, pc_moi_fnd_m3a), c has   *)
(* finitely many components, so by 30.2 (MOISE_302) one component d          *)
(* separates, and the simplices of w inside d form a closed connected        *)
(* combinatorial surface (BOUNDARY_COMPLEX_SURFACE).                         *)
(* ========================================================================= *)

(* ------------------------------------------------------------------------- *)
(* A big tetrahedron around a bounded set, fine combinatorial               *)
(* triangulations of a tetrahedron, finitely many components of a finite    *)
(* union of connected sets.                                                  *)
(* ------------------------------------------------------------------------- *)

(* The standard tetrahedron (copies of MOI_SS2_STD_SB, MOI_SPU_STD_DISTINCT, *)
(* MOI_SPU_STD_SIMPLEX and MOI_SPU_INT_K0 of pc_moi_sch3_s2 and             *)
(* pc_moi_sch3_push, kept here to keep the load closure small).             *)

let MOI_S3IN_STD_SB = prove
 (`{basis i | 1 <= i /\ i <= dimindex(:3)} = {basis 1:real^3,basis 2,basis 3}`,
  REWRITE_TAC[DIMINDEX_3; EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `i = 1 \/ i = 2 \/ i = 3` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THENL
     [EXISTS_TAC `1`; EXISTS_TAC `2`; EXISTS_TAC `3`] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC]);;

let MOI_S3IN_STD_DISTINCT = prove
 (`~(basis 1:real^3 = basis 2) /\ ~(basis 1:real^3 = basis 3) /\
   ~(basis 2:real^3 = basis 3) /\ ~(vec 0:real^3 = basis 1) /\
   ~(vec 0:real^3 = basis 2) /\ ~(vec 0:real^3 = basis 3)`,
  ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN
  SIMP_TAC[BASIS_INJ_EQ; DIMINDEX_3; ARITH; BASIS_NONZERO]);;

let MOI_S3IN_STD_TET = prove
 (`&3 simplex (convex hull {vec 0:real^3,basis 1,basis 2,basis 3}) /\
   interior (convex hull {vec 0:real^3,basis 1,basis 2,basis 3}) =
   {z:real^3 | &0 < z$1 /\ &0 < z$2 /\ &0 < z$3 /\ z$1 + z$2 + z$3 < &1}`,
  SUBGOAL_THEN `{vec 0:real^3,basis 1,basis 2,basis 3} =
                vec 0 INSERT {basis i | 1 <= i /\ i <= dimindex(:3)}`
  SUBST1_TAC THENL [REWRITE_TAC[MOI_S3IN_STD_SB]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[simplex] THEN
    EXISTS_TAC `(vec 0:real^3) INSERT {basis i | 1 <= i /\ i <= dimindex(:3)}` THEN
    REWRITE_TAC[AFFINE_INDEPENDENT_STDBASIS] THEN
    REWRITE_TAC[MOI_S3IN_STD_SB] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; MOI_S3IN_STD_DISTINCT] THEN
    CONV_TAC(NUM_REDUCE_CONV THENC INT_REDUCE_CONV);
    REWRITE_TAC[INTERIOR_STD_SIMPLEX; DIMINDEX_3; FORALL_3; SUM_3; EXTENSION;
                IN_ELIM_THM] THEN
    REWRITE_TAC[CONJ_ASSOC]]);;

(* A bounded set lies in the interior of a tetrahedron. *)

let MOI_S3IN_BIG_TET = prove
 (`!s:real^3->bool. bounded s ==> ?k. &3 simplex k /\ s SUBSET interior k`,
  GEN_TAC THEN REWRITE_TAC[BOUNDED_POS] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(&12 * r = &0) /\ &0 < inv(&12 * r)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\x:real^3. (&12 * r) % x + (--(&2 * r)) % vec 1)
                    (convex hull {vec 0:real^3,basis 1,basis 2,basis 3})` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[AFFINITY_SCALING_TRANSLATION; IMAGE_o; SIMPLEX_TRANSLATION_EQ] THEN
    W(MP_TAC o PART_MATCH (lhand o rand) SIMPLEX_LINEAR_IMAGE_EQ o snd) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[LINEAR_SCALING; VECTOR_MUL_LCANCEL];
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[MOI_S3IN_STD_TET]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[INTERIOR_AFFINITY; MOI_S3IN_STD_TET] THEN
  REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `abs((y:real^3)$1) <= r /\ abs(y$2) <= r /\ abs(y$3) <= r`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[COMPONENT_LE_NORM; REAL_LE_TRANS]; ALL_TAC] THEN
  EXISTS_TAC `inv(&12 * r) % (y + (&2 * r) % vec 1):real^3` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_RINV] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_COMPONENT; VECTOR_ADD_COMPONENT; VEC_COMPONENT; REAL_MUL_RID] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_LT_MUL THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[GSYM REAL_ADD_LDISTRIB] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `inv(&12 * r) * (&9 * r)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_FIELD `&0 < r ==> inv(&12 * r) * (&9 * r) = &3 / &4`] THEN
      REAL_ARITH_TAC]]);;

(* Fine combinatorial triangulations of a tetrahedron: iterated barycentric *)
(* subdivisions of its face complex.                                         *)

let MOI_S3IN_FINE_TRI = prove
 (`!(k:real^3->bool) e.
     &3 simplex k /\ &0 < e
     ==> ?t. FINITE t /\ lf_simplicial_complex t /\
             combinatorial_manifold_with_boundary 3 t /\ UNIONS t = k /\
             (!s. s IN t ==> diameter s < e)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FMB_FACE_COMPLEX) THEN
  MP_TAC(ISPECL [`{f:real^3->bool | f face_of k}`; `e:real`]
    ITERATED_BARYCENTRIC_SUBDIVISION_FINE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:num`) THEN
  EXISTS_TAC `ITER n barycentric_subdivision {f:real^3->bool | f face_of k}` THEN
  SUBGOAL_THEN
   `!m. simplicial_complex (ITER m barycentric_subdivision {f:real^3->bool | f face_of k}) /\
        combinatorial_manifold_with_boundary 3
          (ITER m barycentric_subdivision {f:real^3->bool | f face_of k}) /\
        UNIONS (ITER m barycentric_subdivision {f:real^3->bool | f face_of k}) = k`
  (MP_TAC o SPEC `n:num`) THENL
   [INDUCT_TAC THEN REWRITE_TAC[ITER] THENL
     [ASM_SIMP_TAC[MOI_FMB_FACE_COMPLEX_CMWB];
      ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX; COMBINATORIAL_WB_BARYCENTRIC;
                   UNIONS_BARYCENTRIC_SUBDIVISION; MOI_FMB_SC_LF]];
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[MOI_SIMPLICIAL_COMPLEX_LF]) THEN
    ASM_REWRITE_TAC[]]);;

(* Finitely many components (copy of MOI_S5B_FINITE_COMPONENTS_UNIONS of    *)
(* pc_moi_s35_minb, kept here to keep the load closure small).               *)

let MOI_S3IN_FINITE_COMPONENTS = prove
 (`!f:(real^N->bool)->bool.
     FINITE f /\ (!c. c IN f ==> connected c) ==> FINITE (components (UNIONS f))`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; COMPONENTS_EMPTY; FINITE_EMPTY;
              FORALL_IN_INSERT] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_COMPONENTS_UNION THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  ASM_CASES_TAC `x:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[COMPONENTS_EMPTY; FINITE_EMPTY] THEN
  SUBGOAL_THEN `components(x:real^N->bool) = {x}` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[COMPONENTS_EQ_SING]; REWRITE_TAC[FINITE_SING]]);;

(* ------------------------------------------------------------------------- *)
(* A compact set a in an open set v of real^3 has a finite                  *)
(* combinatorial 3-manifold neighbourhood w with a SUBSET interior (UNIONS  *)
(* w) and UNIONS w SUBSET v (given the manifold half of DERIVED_NBHD_       *)
(* MANIFOLD): the second derived neighbourhood of the simplices meeting a   *)
(* in a triangulation of a big tetrahedron k of mesh below half the        *)
(* distance from a to the complement of v INTER interior k.                  *)
(* ------------------------------------------------------------------------- *)

let MOI_S3IN_NBHD = prove
 (`(!(t:(real^3->bool)->bool) l.
       combinatorial_manifold_with_boundary 3 t /\ simplicial_subcomplex l t
       ==> combinatorial_manifold_with_boundary 3 (derived_nbhd_complex t l))
   ==> !(a:real^3->bool) v.
         compact a /\ open v /\ a SUBSET v
         ==> ?w. FINITE w /\ combinatorial_manifold_with_boundary 3 w /\
                 a SUBSET interior (UNIONS w) /\ UNIONS w SUBSET v`,
  DISCH_THEN(LABEL_TAC "DNM") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  (* the big tetrahedron and the distance d *)
  MP_TAC(ISPEC `a:real^3->bool` MOI_S3IN_BIG_TET) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a:real^3->bool`; `(:real^3) DIFF (v INTER interior k)`]
    SEPARATE_COMPACT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM OPEN_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
      MAP_EVERY UNDISCH_TAC
       [`(a:real^3->bool) SUBSET v`; `(a:real^3->bool) SUBSET interior k`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIV; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "D"))) THEN
  (* the fine triangulation t of k *)
  MP_TAC(ISPECL [`k:real^3->bool`; `d / &2`] MOI_S3IN_FINE_TRI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MESH")))))) THEN
  (* the subcomplex l of the simplices meeting a and their faces *)
  ABBREV_TAC `l = {f:real^3->bool | ?s. s IN t /\ ~(s INTER a = {}) /\ f face_of s}` THEN
  SUBGOAL_THEN `simplicial_subcomplex (l:(real^3->bool)->bool) t` ASSUME_TAC THENL
   [EXPAND_TAC "l" THEN REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `f:real^3->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `s:real^3->bool` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`g:real^3->bool`; `f:real^3->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `g:real^3->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3->bool) SUBSET UNIONS l` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN UNIONS t` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN
      MAP_EVERY UNDISCH_TAC [`(x:real^3) IN a`; `(a:real^3->bool) SUBSET interior k`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `sg:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `sg:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "l" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    EXISTS_TAC `sg:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(x:real^3) IN sg`; `(x:real^3) IN a`] THEN SET_TAC[];
      MATCH_MP_TAC FACE_OF_REFL THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
      EXISTS_TAC `t:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  (* the second derived t2 *)
  ABBREV_TAC
   `t2 = barycentric_subdivision (barycentric_subdivision (t:(real^3->bool)->bool))` THEN
  SUBGOAL_THEN
   `FINITE (t2:(real^3->bool)->bool) /\ lf_simplicial_complex t2 /\ UNIONS t2 = k /\
    (!r. r IN t2 /\ ~(r = {}) ==> ?s. s IN t /\ r SUBSET s)`
  (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "REF")))) THENL
   [EXPAND_TAC "t2" THEN
    ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; BARYCENTRIC_SUBDIVISION_LF;
                 UNIONS_BARYCENTRIC_SUBDIVISION] THEN
    X_GEN_TAC `r:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPEC `barycentric_subdivision (t:(real^3->bool)->bool)`
      BARYCENTRIC_SUBDIVISION_REFINES) THEN
    ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real^3->bool` o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r1:real^3->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `t:(real^3->bool)->bool` BARYCENTRIC_SUBDIVISION_REFINES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `r1:real^3->bool` o CONJUNCT1) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`~(r:real^3->bool = {})`; `(r:real^3->bool) SUBSET r1`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(r:real^3->bool) SUBSET r1`; `(r1:real^3->bool) SUBSET s`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the neighbourhood complex *)
  EXISTS_TAC `derived_nbhd_complex (t:(real^3->bool)->bool) l` THEN
  SUBGOAL_THEN
   `combinatorial_manifold_with_boundary 3 (derived_nbhd_complex (t:(real^3->bool)->bool) l)`
  (fun th -> REWRITE_TAC[th]) THENL
   [USE_THEN "DNM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `derived_nbhd_complex (t:(real^3->bool)->bool) l =
    {s | ?r. r IN t2 /\ ~(r INTER UNIONS l = {}) /\ s face_of r}`
  SUBST1_TAC THENL
   [EXPAND_TAC "t2" THEN REWRITE_TAC[derived_nbhd_complex]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* finite *)
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t2:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:real^3->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_FM3_LF_FACE THEN EXISTS_TAC `r:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    (* a is inside the interior: an open star argument in t2 *)
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `interior k DIFF UNIONS {r | r IN t2 /\ ~((x:real^3) IN r)} SUBSET
      interior (UNIONS {s | ?r. r IN (t2:(real^3->bool)->bool) /\
                                ~(r INTER UNIONS l = {}) /\ s face_of r})`
    MP_TAC THENL
     [MATCH_MP_TAC INTERIOR_MAXIMAL THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
        X_GEN_TAC `p:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `(p:real^3) IN UNIONS t2` MP_TAC THENL
         [ASM_REWRITE_TAC[] THEN MP_TAC(ISPEC `k:real^3->bool` INTERIOR_SUBSET) THEN
          UNDISCH_TAC `(p:real^3) IN interior k` THEN SET_TAC[];
          ALL_TAC] THEN
        REWRITE_TAC[IN_UNIONS] THEN
        DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
        SUBGOAL_THEN `(x:real^3) IN r` ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        EXISTS_TAC `r:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        EXISTS_TAC `r:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `x:real^3` THEN
          ASM_REWRITE_TAC[] THEN
          MAP_EVERY UNDISCH_TAC [`(x:real^3) IN a`; `(a:real^3->bool) SUBSET UNIONS l`] THEN
          SET_TAC[];
          MATCH_MP_TAC FACE_OF_REFL THEN MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
          EXISTS_TAC `t2:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]];
        MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_INTERIOR] THEN
        MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
         [ASM_SIMP_TAC[FINITE_RESTRICT];
          REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `r:real^3->bool` THEN STRIP_TAC THEN
          MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
          EXISTS_TAC `t2:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[]]];
      MATCH_MP_TAC(SET_RULE `!x:real^3 a b. x IN a ==> a SUBSET b ==> x IN b`) THEN
      REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC [`(x:real^3) IN a`; `(a:real^3->bool) SUBSET interior k`] THEN
        SET_TAC[];
        MESON_TAC[]]];
    (* UNIONS w SUBSET v: points of w are within 2 mesh of a *)
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `p:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `(p:real^3) IN r` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`r:real^3->bool`; `s:real^3->bool`] FACE_OF_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(p:real^3) IN s` THEN SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "REF" (MP_TAC o SPEC `r:real^3->bool`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(p:real^3) IN r` THEN SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `tau:real^3->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~((r:real^3->bool) INTER UNIONS l = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^3` (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
    EXPAND_TAC "l" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `sg:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `~((sg:real^3->bool) INTER a = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^3) IN tau /\ (p:real^3) IN tau /\ (y:real^3) IN sg`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`sg:real^3->bool`; `f:real^3->bool`] FACE_OF_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`(y:real^3) IN r`; `(p:real^3) IN r`; `(y:real^3) IN f`;
        `(r:real^3->bool) SUBSET tau`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `bounded (tau:real^3->bool) /\ bounded (sg:real^3->bool)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
      EXISTS_TAC `t:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(y:real^3,p) <= diameter(tau:real^3->bool) /\
                  dist(z:real^3,y) <= diameter(sg:real^3->bool)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN REWRITE_TAC[dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `diameter(tau:real^3->bool) < d / &2 /\ diameter(sg:real^3->bool) < d / &2`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "MESH" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(p:real^3) IN v` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "D" (MP_TAC o SPECL [`z:real^3`; `p:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`z:real^3`; `y:real^3`; `p:real^3`] DIST_TRIANGLE) THEN
    ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* The complex boundary of a finite combinatorial 3-manifold               *)
(* neighbourhood separates (the interior of UNIONS w is UNIONS w minus the *)
(* complex boundary), and the final assembly with 30.2.                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3IN_SEPARATION = prove
 (`!(w:(real^3->bool)->bool) a b v.
     FINITE w /\ combinatorial_manifold_with_boundary 3 w /\
     a SUBSET interior (UNIONS w) /\ UNIONS w SUBSET v /\ DISJOINT v b
     ==> compact (complex_boundary w) /\ complex_boundary w SUBSET v /\
         DISJOINT (complex_boundary w) a /\
         FINITE (components (complex_boundary w)) /\
         euclidean_separates (complex_boundary w) a b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (w:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPEC `w:(real^3->bool)->bool` MOI_FM3_BC_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (boundary_complex (w:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS (w:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
    EXISTS_TAC `w:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `complex_boundary (w:(real^3->bool)->bool) SUBSET UNIONS w /\
    compact (complex_boundary w) /\ FINITE (components (complex_boundary w))`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS (boundary_complex w) = complex_boundary (w:(real^3->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
      EXISTS_TAC `w:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(q:real^3->bool) IN boundary_complex w`;
                             `boundary_complex w SUBSET (w:(real^3->bool)->bool)`] THEN
      SET_TAC[];
      MATCH_MP_TAC MOI_S3IN_FINITE_COMPONENTS THEN ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN MATCH_MP_TAC CONVEX_CONNECTED THEN
      MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN
      EXISTS_TAC `w:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(q:real^3->bool) IN boundary_complex w`;
                             `boundary_complex w SUBSET (w:(real^3->bool)->bool)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (complex_boundary (w:(real^3->bool)->bool)) a` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `x:real^3`] MOI_FM3_CB_NOT_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(x:real^3) IN a`;
                           `(a:real^3->bool) SUBSET interior (UNIONS w)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`complex_boundary (w:(real^3->bool)->bool) SUBSET UNIONS w`;
      `UNIONS (w:(real^3->bool)->bool) SUBSET v`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[euclidean_separates] THEN
  MAP_EVERY EXISTS_TAC [`interior (UNIONS (w:(real^3->bool)->bool))`;
                        `(:real^3) DIFF UNIONS w`] THEN
  REWRITE_TAC[OPEN_INTERIOR] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    MP_TAC(ISPEC `UNIONS (w:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN SET_TAC[];
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    REWRITE_TAC[IN_UNION; IN_DIFF; IN_UNIV] THEN
    ASM_CASES_TAC `(x:real^3) IN UNIONS w` THEN ASM_REWRITE_TAC[] THENL
     [EQ_TAC THEN DISCH_TAC THENL
       [DISCH_TAC THEN
        MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `x:real^3`] MOI_FM3_CB_NOT_INTERIOR) THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_FM3_NOT_CB_INTERIOR THEN ASM_REWRITE_TAC[]];
      UNDISCH_TAC `complex_boundary (w:(real^3->bool)->bool) SUBSET UNIONS w` THEN
      UNDISCH_TAC `~((x:real^3) IN UNIONS w)` THEN SET_TAC[]];
    ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`UNIONS (w:(real^3->bool)->bool) SUBSET v`; `DISJOINT (v:real^3->bool) b`] THEN
    SET_TAC[]]);;

(* The main theorem: an initial separating surface. *)

let INIT_SURFACE = prove
 (MOI_S30_INIT_SURFACE,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "302") ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!(t:(real^3->bool)->bool) l.
       combinatorial_manifold_with_boundary 3 t /\ simplicial_subcomplex l t
       ==> combinatorial_manifold_with_boundary 3 (derived_nbhd_complex t l)`
  (LABEL_TAC "DNM1") THENL
   [FIRST_X_ASSUM(fun th -> MESON_TAC[th]); ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real^3->bool`; `b:real^3->bool`; `v:real^3->bool`] THEN
  STRIP_TAC THEN
  USE_THEN "DNM1" (MP_TAC o SPECL [`a:real^3->bool`; `v:real^3->bool`] o
                   MATCH_MP MOI_S3IN_NBHD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `a:real^3->bool`; `b:real^3->bool`;
                 `v:real^3->bool`] MOI_S3IN_SEPARATION) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  (* 30.2 in real^3 *)
  USE_THEN "302" (MP_TAC o SPECL [`(:real^3)`; `complex_boundary (w:(real^3->bool)->bool)`;
                                  `a:real^3->bool`; `b:real^3->bool`] o
                  REWRITE_RULE[MOISE_302_STATEMENT]) THEN
  REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM CLOSED_IN; separates_in; GSYM OPEN_IN;
              GSYM euclidean_separates] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[OPEN_UNIV; CONVEX_IMP_SIMPLY_CONNECTED; CONVEX_UNIV; COMPACT_IMP_CLOSED] THEN
    MAP_EVERY UNDISCH_TAC
     [`(a:real^3->bool) SUBSET v`; `DISJOINT (v:real^3->bool) b`;
      `complex_boundary (w:(real^3->bool)->bool) SUBSET v`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* the surface of the component d *)
  MP_TAC(MATCH_MP BOUNDARY_COMPLEX_SURFACE
    (ASSUME `combinatorial_manifold_with_boundary 3 (w:(real^3->bool)->bool)`)) THEN
  DISCH_THEN(MP_TAC o SPEC `d:real^3->bool` o last o CONJUNCTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `{s | s IN w /\ s SUBSET (d:real^3->bool)}` THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC IN_COMPONENTS_CONNECTED THEN
    EXISTS_TAC `complex_boundary (w:(real^3->bool)->bool)` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC IN_COMPONENTS_NONEMPTY THEN
    EXISTS_TAC `complex_boundary (w:(real^3->bool)->bool)` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`complex_boundary (w:(real^3->bool)->bool)`; `d:real^3->bool`]
      IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`complex_boundary (w:(real^3->bool)->bool) SUBSET v`;
      `DISJOINT (complex_boundary (w:(real^3->bool)->bool)) a`] THEN
    SET_TAC[]]);;

