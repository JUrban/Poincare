(* ========================================================================= *)
(* pc_moi_comb: every PL triangulation of an open subset of a PL 3-manifold *)
(* is a combinatorial 3-manifold (vertex links are PL 2-spheres).  PL        *)
(* counterpart of Moise, Geometric Topology in Dimensions 2 and 3, Thm 23.1. *)
(* Part 1: a compact polyhedron met exactly once by every ray from a point  *)
(* outside it is a PL sphere (pseudo-radial projection, Rourke-Sanderson,    *)
(* Introduction to PL topology, Lemma 2.19).                                 *)
(* Part 2: the vertex links of a PL triangulation are PL 2-spheres.          *)
(* ========================================================================= *)

needs "src/pc_moi_tridef.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_real.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Central projection onto a hyperplane: the map y |-> y / (a dot y) on  *)
(* a region where a dot y > 0 preserves convex hulls and affine             *)
(* independence of point sets lying in a hyperplane missing the origin.     *)
(* ------------------------------------------------------------------------- *)

let MOI_CMB_HYPERPLANE_FUNCTIONAL = prove
 (`!s:real^N->bool.
        ~(vec 0 IN affine hull s) ==> ?a. !x. x IN s ==> a dot x = &1`,
  GEN_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[NOT_IN_EMPTY] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{vec 0:real^N}`; `affine hull s:real^N->bool`]
    SEPARATING_HYPERPLANE_AFFINE_AFFINE) THEN
  ASM_REWRITE_TAC[AFFINE_SING; AFFINE_AFFINE_HULL; AFFINE_HULL_EQ_EMPTY;
                  NOT_INSERT_EMPTY; SET_RULE `DISJOINT {a:A} s <=> ~(a IN s)`] THEN
  REWRITE_TAC[IN_SING; FORALL_UNWIND_THM2; DOT_RZERO] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real`
    (X_CHOOSE_THEN `c:real` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `inv(c) % a:real^N` THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a:real^N) dot x = c` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
  ASM_REWRITE_TAC[DOT_LMUL] THEN MATCH_MP_TAC REAL_MUL_LINV THEN
  ASM_REAL_ARITH_TAC);;

let MOI_CMB_PROJ_CONVEX_HULL = prove
 (`!(a:real^N) w.
        (!y. y IN convex hull w ==> &0 < a dot y)
        ==> IMAGE (\y. inv(a dot y) % y) (convex hull w) =
            convex hull (IMAGE (\y. inv(a dot y) % y) w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!x:real^N. x IN convex hull (IMAGE (\y:real^N. inv(a dot y) % y) w)
                           ==> (a:real^N) dot x = &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `convex hull (IMAGE (\y:real^N. inv(a dot y) % y) w) SUBSET
                  {x | (a:real^N) dot x = &1}`
      (fun th -> MESON_TAC[th; SUBSET; IN_ELIM_THM]) THEN
    MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_HYPERPLANE] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; DOT_RMUL] THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_MUL_LINV THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x ==> ~(x = &0)`) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[HULL_INC];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [SUBGOAL_THEN `convex hull w SUBSET
       conic hull (convex hull (IMAGE (\y:real^N. inv(a dot y) % y) w))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN
      SIMP_TAC[CONVEX_CONIC_HULL; CONVEX_CONVEX_HULL] THEN
      REWRITE_TAC[SUBSET; CONIC_HULL_EXPLICIT; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < (a:real^N) dot y` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`(a:real^N) dot y`; `inv((a:real^N) dot y) % y`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE; VECTOR_MUL_ASSOC; REAL_MUL_RINV;
                   REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN
       conic hull (convex hull (IMAGE (\y:real^N. inv(a dot y) % y) w))`
    MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CONIC_HULL_EXPLICIT; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `z:real^N`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a:real^N) dot y = c` ASSUME_TAC THENL
     [ASM_SIMP_TAC[DOT_RMUL; REAL_MUL_RID]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                 VECTOR_MUL_LID];
    SUBGOAL_THEN `convex hull (IMAGE (\y:real^N. inv(a dot y) % y) w) SUBSET
                  conic hull (convex hull w)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN
      SIMP_TAC[CONVEX_CONIC_HULL; CONVEX_CONVEX_HULL] THEN
      REWRITE_TAC[SUBSET; CONIC_HULL_EXPLICIT; IN_ELIM_THM; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `&0 < (a:real^N) dot y` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
      MAP_EVERY EXISTS_TAC [`inv((a:real^N) dot y)`; `y:real^N`] THEN
      ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; HULL_INC];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN conic hull (convex hull w)` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[CONIC_HULL_EXPLICIT; IN_ELIM_THM; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `z:real^N`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((a:real^N) dot z) * c = &1` ASSUME_TAC THENL
     [ASM_MESON_TAC[DOT_RMUL; REAL_MUL_SYM]; ALL_TAC] THEN
    SUBGOAL_THEN `inv((a:real^N) dot z) = c` (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC REAL_MUL_RINV_UNIQ THEN ASM_REWRITE_TAC[]]);;

let MOI_CMB_PROJ_AFFINE_INDEPENDENT = prove
 (`!(a:real^N) m w.
        ~affine_dependent w /\
        (!y. y IN w ==> m dot y = &1) /\
        (!y. y IN w ==> &0 < a dot y)
        ==> ~affine_dependent (IMAGE (\y. inv(a dot y) % y) w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (w:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x y:real^N. x IN w /\ y IN w /\ inv(a dot x) % x = inv(a dot y) % y
                 ==> x = y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `inv((a:real^N) dot x) = inv(a dot y)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `\z:real^N. (m:real^N) dot z`) THEN
      ASM_SIMP_TAC[DOT_RMUL; REAL_MUL_RID];
      ALL_TAC] THEN
    UNDISCH_TAC `inv((a:real^N) dot x) % x = inv(a dot y) % y` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL; REAL_INV_EQ_0] THEN
    ASM_MESON_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (IMAGE (\y:real^N. inv(a dot y) % y) w) = CARD w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(vec 0:real^N IN affine hull w)` ASSUME_TAC THENL
   [SUBGOAL_THEN `affine hull w SUBSET {x:real^N | m dot x = &1}` MP_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
      ASM_SIMP_TAC[SUBSET; IN_ELIM_THM];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN
      REWRITE_TAC[DOT_RZERO] THEN MESON_TAC[REAL_ARITH `~(&0 = &1)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(vec 0:real^N IN affine hull (IMAGE (\y:real^N. inv(a dot y) % y) w))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `affine hull (IMAGE (\y:real^N. inv(a dot y) % y) w) SUBSET
                  {x:real^N | a dot x = &1}` MP_TAC THENL
     [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[AFFINE_HYPERPLANE] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM; DOT_RMUL] THEN
      ASM_MESON_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN
      REWRITE_TAC[DOT_RZERO] THEN MESON_TAC[REAL_ARITH `~(&0 = &1)`]];
    ALL_TAC] THEN
  SUBGOAL_THEN `dim (IMAGE (\y:real^N. inv(a dot y) % y) w) = dim w`
  ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM DIM_SPAN] THEN AP_TERM_TAC THEN
    REWRITE_TAC[SPAN_EQ; SUBSET; FORALL_IN_IMAGE] THEN CONJ_TAC THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THENL
     [MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `y:real^N = ((a:real^N) dot y) % inv(a dot y) % y`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_RINV; REAL_LT_IMP_NZ;
                     VECTOR_MUL_LID];
        MATCH_MP_TAC SPAN_MUL THEN MATCH_MP_TAC SPAN_SUPERSET THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `y:real^N` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [AFFINE_INDEPENDENT_IFF_CARD]) THEN
  REWRITE_TAC[AFFINE_INDEPENDENT_IFF_CARD; AFF_DIM_DIM] THEN
  ASM_SIMP_TAC[FINITE_IMAGE]);;

let MOI_CMB_LOCAL_PROJ_HULL = prove
 (`!(R:real^N->real^N) a w w'.
        (!y. y IN convex hull w ==> &0 < a dot y /\ R y = inv(a dot y) % y) /\
        w' SUBSET w
        ==> IMAGE R (convex hull w') = convex hull (IMAGE R w')`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `convex hull w' SUBSET convex hull (w:real^N->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(w':real^N->bool) SUBSET convex hull w` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull w':real^N->bool` THEN
    ASM_REWRITE_TAC[HULL_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (R:real^N->real^N) (convex hull w') =
                IMAGE (\y. inv(a dot y) % y) (convex hull w')`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = g x) ==> IMAGE (f:A->B) s = IMAGE g s`) THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (R:real^N->real^N) w' = IMAGE (\y. inv(a dot y) % y) w'`
  SUBST1_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `(!x. x IN s ==> f x = g x) ==> IMAGE (f:A->B) s = IMAGE g s`) THEN
    X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
    ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_CMB_PROJ_CONVEX_HULL THEN ASM_MESON_TAC[SUBSET]);;

let MOI_CMB_RADIAL_REALIZES = prove
 (`!(L:(real^N->bool)->bool) (R:real^N->real^N).
     simplicial_complex L /\
     (!z1 z2. z1 IN UNIONS L /\ z2 IN UNIONS L /\ R z1 = R z2 ==> z1 = z2) /\
     (!d. d IN L /\ ~(d = {})
          ==> ?a m. !y. y IN d ==> &0 < a dot y /\ R y = inv(a dot y) % y /\
                                   m dot y = &1)
     ==> abstract_realizes R (moi_real_vertex_sets L) /\
         UNIONS (abstract_realization R (moi_real_vertex_sets L)) =
         IMAGE R (UNIONS L)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (LABEL_TAC "inj") (LABEL_TAC "loc"))) THEN
  SUBGOAL_THEN
   `!w:real^N->bool. w IN moi_real_vertex_sets L
        ==> ?a m. !y. y IN convex hull w
                      ==> &0 < a dot y /\ (R:real^N->real^N) y = inv(a dot y) % y /\
                          m dot y = &1`
  (LABEL_TAC "proj") THENL
   [REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN REPEAT STRIP_TAC THEN
    USE_THEN "loc" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w w':real^N->bool. w IN moi_real_vertex_sets L /\ w' SUBSET w
        ==> IMAGE (R:real^N->real^N) (convex hull w') = convex hull (IMAGE R w')`
  (LABEL_TAC "hull") THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "proj" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `w IN moi_real_vertex_sets (L:(real^N->bool)->bool)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_TAC `m:real^N`)) THEN
    MATCH_MP_TAC MOI_CMB_LOCAL_PROJ_HULL THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `w:real^N->bool`] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^N->bool. w IN moi_real_vertex_sets L ==> convex hull w SUBSET UNIONS L`
  (LABEL_TAC "sub") THENL
   [REWRITE_TAC[MOI_REAL_IN_VERTEX_SETS] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) IN c ==> s SUBSET UNIONS c`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (moi_real_vertex_sets (L:(real^N->bool)->bool)) SUBSET UNIONS L`
  ASSUME_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET] THEN X_GEN_TAC `w:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `convex hull w:real^N->bool` THEN
    REWRITE_TAC[HULL_SUBSET] THEN USE_THEN "sub" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[abstract_realizes] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `w:real^N->bool` THEN DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_REAL_IN_VERTEX_SETS]) THEN
      STRIP_TAC THEN
      USE_THEN "proj" (fun th -> MP_TAC(MATCH_MP th (ASSUME
        `w IN moi_real_vertex_sets (L:(real^N->bool)->bool)`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `m:real^N`
        ASSUME_TAC)) THEN
      SUBGOAL_THEN `IMAGE (R:real^N->real^N) w = IMAGE (\y. inv(a dot y) % y) w`
      SUBST1_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `(!x. x IN s ==> f x = g x) ==> IMAGE (f:A->B) s = IMAGE g s`) THEN
        X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN BETA_TAC THEN
        ASM_MESON_TAC[HULL_INC];
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_CMB_PROJ_AFFINE_INDEPENDENT THEN
      EXISTS_TAC `m:real^N` THEN ASM_MESON_TAC[HULL_INC];
      USE_THEN "inj" MP_TAC THEN UNDISCH_TAC
       `UNIONS (moi_real_vertex_sets (L:(real^N->bool)->bool)) SUBSET UNIONS L` THEN
      REWRITE_TAC[SUBSET] THEN MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`w1:real^N->bool`; `w2:real^N->bool`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       `convex hull (IMAGE (R:real^N->real^N) w1) = IMAGE R (convex hull w1) /\
        convex hull (IMAGE (R:real^N->real^N) w2) = IMAGE R (convex hull w2) /\
        convex hull (IMAGE (R:real^N->real^N) (w1 INTER w2)) =
        IMAGE R (convex hull (w1 INTER w2))`
      (fun th -> REWRITE_TAC[th]) THENL
       [REPEAT CONJ_TAC THEN CONV_TAC SYM_CONV THEN
        USE_THEN "hull" MATCH_MP_TAC THENL
         [EXISTS_TAC `w1:real^N->bool`; EXISTS_TAC `w2:real^N->bool`;
          EXISTS_TAC `w1:real^N->bool`] THEN
        ASM_REWRITE_TAC[SUBSET_REFL; INTER_SUBSET];
        ALL_TAC] THEN
      SUBGOAL_THEN `convex hull w1 INTER convex hull w2 =
                    convex hull (w1 INTER w2:real^N->bool)`
      (SUBST1_TAC o SYM) THENL
       [MATCH_MP_TAC MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL THEN
        EXISTS_TAC `L:(real^N->bool)->bool` THEN
        ASM_MESON_TAC[MOI_REAL_IN_VERTEX_SETS];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE
       `!(f:A->B) u a b. (!x y. x IN u /\ y IN u /\ f x = f y ==> x = y) /\
        a SUBSET u /\ b SUBSET u
        ==> IMAGE f a INTER IMAGE f b = IMAGE f (a INTER b)`) THEN
      EXISTS_TAC `UNIONS (L:(real^N->bool)->bool)` THEN
      REPEAT CONJ_TAC THENL
       [USE_THEN "inj" ACCEPT_TAC;
        USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        USE_THEN "sub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
    MP_TAC(ISPEC `L:(real^N->bool)->bool` MOI_REAL_VERTEX_SETS_UNIONS) THEN
    ASM_REWRITE_TAC[abstract_realization; UNIONS_INSERT; UNION_EMPTY; IMAGE_ID] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN CONV_TAC SYM_CONV THEN
    MP_TAC(ISPECL [`R:real^N->real^N`; `\s:real^N->bool. convex hull s`;
                   `\s:real^N->bool. convex hull (IMAGE (R:real^N->real^N) s)`;
                   `moi_real_vertex_sets (L:(real^N->bool)->bool)`]
      MOI_REAL_IMAGE_UNIONS_GSPEC) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    X_GEN_TAC `w:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "hull" MATCH_MP_TAC THEN EXISTS_TAC `w:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* 2. Radial projection onto a polyhedron that meets every ray from the     *)
(* origin exactly once, and the fan of cones over its simplices.             *)
(* ------------------------------------------------------------------------- *)

let moi_cmb_radial = new_definition
 `moi_cmb_radial (s:real^N->bool) (u:real^N) = (@r. &0 < r /\ r % u IN s) % u`;;

let MOI_CMB_RADIAL = prove
 (`!(s:real^N->bool) u.
        (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN s) /\ ~(u = vec 0)
        ==> moi_cmb_radial s u IN s /\
            (?r. &0 < r /\ moi_cmb_radial s u = r % u) /\
            (!r. &0 < r /\ r % u IN s ==> moi_cmb_radial s u = r % u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N`) THEN
  ASM_REWRITE_TAC[EXISTS_UNIQUE_ALT] THEN
  DISCH_THEN(X_CHOOSE_TAC `r0:real`) THEN
  SUBGOAL_THEN `(@r. &0 < r /\ r % (u:real^N) IN s) = r0` ASSUME_TAC THENL
   [MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `y:real` THEN
    BETA_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_cmb_radial] THEN ASM_MESON_TAC[]);;

let MOI_CMB_NEAR_SCALAR = prove
 (`!(x:real^N) e. ~(x = vec 0) /\ &0 < e ==> ?t. &1 < t /\ dist(x,t % x) < e`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(x:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
  EXISTS_TAC `&1 + e / (&2 * norm(x:real^N))` THEN
  SUBGOAL_THEN `&0 < e / (&2 * norm(x:real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[dist; VECTOR_ARITH `x - (&1 + a) % x:real^N = --(a % x)`;
              NORM_NEG; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
  SUBGOAL_THEN `e / (&2 * norm(x:real^N)) * norm x = e / &2` SUBST1_TAC THENL
   [UNDISCH_TAC `&0 < norm(x:real^N)` THEN CONV_TAC REAL_FIELD;
    ASM_REAL_ARITH_TAC]);;

let MOI_CMB_STAR_AFFINE_HULL = prove
 (`!(s:real^N->bool) k.
        (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN s) /\ ~(vec 0 IN s) /\
        convex k /\ k SUBSET s
        ==> ~(vec 0 IN affine hull k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `k:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[AFFINE_HULL_EMPTY; NOT_IN_EMPTY] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?x:real^N. x IN relative_interior k` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEMBER_NOT_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_RELATIVE_INTERIOR]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(x:real^N = vec 0)` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`x:real^N`; `e:real`] MOI_CMB_NEAR_SCALAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:real) % (x:real^N) IN k` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_BALL] THEN
    MP_TAC(REWRITE_RULE[AFFINE_ALT]
      (ISPEC `k:real^N->bool` AFFINE_AFFINE_HULL)) THEN
    DISCH_THEN(MP_TAC o SPECL [`vec 0:real^N`; `x:real^N`; `t:real`]) THEN
    ASM_SIMP_TAC[HULL_INC; VECTOR_MUL_RZERO; VECTOR_ADD_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN s /\ t % x IN s` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `~(x:real^N = vec 0)`)) THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`&1`; `t:real`] o CONJUNCT2) THEN
  ASM_REWRITE_TAC[VECTOR_MUL_LID] THEN ASM_REAL_ARITH_TAC);;

let MOI_CMB_FACE_FUNCTIONAL = prove
 (`!(k:real^N->bool) f.
        convex k /\ vec 0 IN relative_interior k /\ f face_of k /\ ~(f = k)
        ==> ?m. !y. y IN f ==> m dot y = &1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CMB_HYPERPLANE_FUNCTIONAL THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `f:real^N->bool`]
    AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_CMB_RAY_INTERIOR = prove
 (`!(k:real^N->bool) z u.
        convex k /\ vec 0 IN relative_interior k /\ z IN closure k /\
        &0 < u /\ u < &1
        ==> u % z IN relative_interior k`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `z:real^N = vec 0` THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RZERO] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `vec 0:real^N`; `z:real^N`]
    IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[IN_SEGMENT] THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let MOI_CMB_RAY_FRONTIER_UNIQUE = prove
 (`!(k:real^N->bool) z1 z2 u.
        convex k /\ vec 0 IN relative_interior k /\
        z1 IN relative_frontier k /\ z2 IN relative_frontier k /\
        &0 < u /\ z1 = u % z2
        ==> u = &1`,
  REWRITE_TAC[relative_frontier; IN_DIFF] THEN REPEAT STRIP_TAC THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `u < &1 \/ u = &1 \/ &1 < u`) THEN
  ASM_REWRITE_TAC[] THENL
   [MP_TAC(ISPECL [`k:real^N->bool`; `z2:real^N`; `u:real`]
      MOI_CMB_RAY_INTERIOR) THEN
    ASM_MESON_TAC[];
    MP_TAC(ISPECL [`k:real^N->bool`; `z1:real^N`; `inv u:real`]
      MOI_CMB_RAY_INTERIOR) THEN
    SUBGOAL_THEN `inv u % (z1:real^N) = z2` SUBST1_TAC THENL
     [ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
                   VECTOR_MUL_LID];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < inv u /\ inv u < &1` STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_INV_EQ; REAL_INV_LT_1]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

let MOI_CMB_CONE_RADIAL = prove
 (`!(s:real^N->bool) d a y.
        (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN s) /\ d SUBSET s /\
        (!x. x IN d ==> a dot x = &1) /\ y IN conic hull d /\ ~(y = vec 0)
        ==> &0 < a dot y /\ moi_cmb_radial s y = inv(a dot y) % y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN conic hull d` THEN
  REWRITE_TAC[CONIC_HULL_EXPLICIT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real` (X_CHOOSE_THEN `x:real^N`
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC SUBST_ALL_TAC))) THEN
  SUBGOAL_THEN `(a:real^N) dot (c % x) = c` SUBST1_TAC THENL
   [ASM_SIMP_TAC[DOT_RMUL; REAL_MUL_RID]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < c` ASSUME_TAC THENL
   [ASM_CASES_TAC `c = &0` THENL
     [ASM_MESON_TAC[VECTOR_MUL_LZERO]; ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `c % x:real^N`] MOI_CMB_RADIAL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN
  ASM_SIMP_TAC[REAL_LT_INV_EQ; VECTOR_MUL_ASSOC; REAL_MUL_LINV;
               REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
  ASM SET_TAC[]);;

let MOI_CMB_FAN_POLYTOPES = prove
 (`!(s:real^N->bool) K sx.
        simplicial_complex K /\ UNIONS K = s /\
        (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN s) /\
        polytope sx /\ vec 0 IN relative_interior sx
        ==> ?P. FINITE P /\ (!k. k IN P ==> polytope k) /\
                UNIONS P = relative_frontier sx /\
                (!k. k IN P ==> ?d e. d IN K /\ e face_of sx /\ ~(e = sx) /\
                                      k = conic hull d INTER e)`,
  REPEAT STRIP_TAC THEN
  EXISTS_TAC `{conic hull d INTER e | d IN K /\
               e IN {e:real^N->bool | e face_of sx /\ ~(e = sx)}}` THEN
  REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`\d e:real^N->bool. conic hull d INTER e`;
                   `K:(real^N->bool)->bool`;
                   `\d:real^N->bool. {e:real^N->bool | e face_of sx /\ ~(e = sx)}`]
      FINITE_PRODUCT_DEPENDENT) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{e:real^N->bool | e face_of sx}` THEN
    ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[];
    REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[INTER_COMM] THEN
    MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN CONJ_TAC THENL
     [ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE];
      MATCH_MP_TAC POLYHEDRON_CONIC_HULL_POLYTOPE THEN
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE]];
    ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON_ALT; POLYTOPE_IMP_POLYHEDRON] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC; IN_ELIM_THM] THEN
      REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(SET_RULE
       `!c e:A->bool f. e IN f ==> c INTER e SUBSET UNIONS f`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~(z:real^N = vec 0)` ASSUME_TAC THENL
       [DISCH_TAC THEN
        MP_TAC(ISPECL [`sx:real^N->bool`; `e:real^N->bool`]
          AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
        ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `vec 0:real^N`) THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[HULL_INC];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `z:real^N`] MOI_CMB_RADIAL) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) (K ALL_TAC))) THEN
      SUBGOAL_THEN `?d:real^N->bool. d IN K /\ moi_cmb_radial s z IN d`
      STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `conic hull d INTER e:real^N->bool` THEN
      REWRITE_TAC[IN_INTER] THEN REPEAT CONJ_TAC THENL
       [MAP_EVERY EXISTS_TAC [`d:real^N->bool`; `e:real^N->bool`] THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[CONIC_HULL_EXPLICIT; IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`inv r:real`; `moi_cmb_radial s (z:real^N)`] THEN
        ASM_SIMP_TAC[REAL_LE_INV_EQ; REAL_LT_IMP_LE; VECTOR_MUL_ASSOC;
                     REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
        ASM_REWRITE_TAC[]]];
    REWRITE_TAC[FORALL_IN_GSPEC; IN_ELIM_THM] THEN MESON_TAC[]]);;

let MOI_CMB_FAN_TRIANGULATION = prove
 (`!(s:real^N->bool) K sx.
        simplicial_complex K /\ UNIONS K = s /\ ~(vec 0 IN s) /\
        (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN s) /\
        polytope sx /\ vec 0 IN relative_interior sx
        ==> ?L. simplicial_complex L /\ UNIONS L = relative_frontier sx /\
                !d. d IN L /\ ~(d = {})
                    ==> ?a m. !y. y IN d
                                  ==> &0 < a dot y /\
                                      moi_cmb_radial s y = inv(a dot y) % y /\
                                      m dot y = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `K:(real^N->bool)->bool`; `sx:real^N->bool`]
    MOI_CMB_FAN_POLYTOPES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `P:(real^N->bool)->bool` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `del:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `del:real^N->bool`;
                 `P:(real^N->bool)->bool`] MOI_PLT_SIMPLEX_IN_COVER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `{k:real^N->bool | k IN P /\ ?f. f SUBSET L /\ k = UNIONS f} = P`
    SUBST1_TAC THENL
     [UNDISCH_TAC
       `!k:real^N->bool. k IN P ==> ?f. f SUBSET L /\ k = UNIONS f` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `UNIONS L = relative_frontier (sx:real^N->bool)`)) THEN
    MATCH_MP_TAC(SET_RULE `(s:A->bool) IN c ==> s SUBSET UNIONS c`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?d e:real^N->bool. d IN K /\ e face_of sx /\ ~(e = sx) /\
                                   k = conic hull d INTER e`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(d:real^N->bool) SUBSET s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `d:real^N->bool` MOI_CMB_HYPERPLANE_FUNCTIONAL) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC MOI_CMB_STAR_AFFINE_HULL THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`)] THEN
  MP_TAC(ISPECL [`sx:real^N->bool`; `e:real^N->bool`] MOI_CMB_FACE_FUNCTIONAL) THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN
  DISCH_THEN(X_CHOOSE_TAC `m:real^N`) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `m:real^N`] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN conic hull d /\ y IN e` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N) dot y = &1` ASSUME_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^N = vec 0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `(m:real^N) dot y = &1` THEN
    ASM_REWRITE_TAC[DOT_RZERO] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CMB_CONE_RADIAL THEN
  EXISTS_TAC `d:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 3. Pseudo-radial projection: a polyhedron met exactly once by every ray  *)
(* from a point outside it is a PL sphere (Rourke-Sanderson, Lemma 2.19).    *)
(* ------------------------------------------------------------------------- *)

let MOI_CMB_FRONTIER_NONZERO = prove
 (`!(sx:real^N->bool) z.
        vec 0 IN relative_interior sx /\ z IN relative_frontier sx
        ==> ~(z = vec 0)`,
  REWRITE_TAC[relative_frontier; IN_DIFF] THEN MESON_TAC[]);;

let MOI_CMB_RADIAL_INJECTIVE = prove
 (`!(s:real^N->bool) sx z1 z2.
        (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN s) /\
        convex sx /\ vec 0 IN relative_interior sx /\
        z1 IN relative_frontier sx /\ z2 IN relative_frontier sx /\
        moi_cmb_radial s z1 = moi_cmb_radial s z2
        ==> z1 = z2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(z1:real^N = vec 0) /\ ~(z2:real^N = vec 0)` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[MOI_CMB_FRONTIER_NONZERO]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `z1:real^N`] MOI_CMB_RADIAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `z2:real^N`] MOI_CMB_RADIAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) (K ALL_TAC))) THEN
  MP_TAC(ISPECL [`sx:real^N->bool`; `z1:real^N`; `z2:real^N`; `inv r1 * r2`]
    MOI_CMB_RAY_FRONTIER_UNIQUE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < inv r1 * r2` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_INV_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `z1:real^N = (inv r1 * r2) % z2`
   (fun th -> REWRITE_TAC[th] THEN DISCH_TAC THEN
              ASM_REWRITE_TAC[VECTOR_MUL_LID]) THEN
  SUBGOAL_THEN `(r1:real) % (z1:real^N) = r2 % z2` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(%) (inv r1):real^N->real^N`) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; REAL_LT_IMP_NZ;
               VECTOR_MUL_LID]);;

let MOI_CMB_RADIAL_IMAGE = prove
 (`!(s:real^N->bool) sx.
        (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN s) /\ ~(vec 0 IN s) /\
        bounded sx /\ vec 0 IN relative_interior sx /\
        affine hull sx = (:real^N)
        ==> IMAGE (moi_cmb_radial s) (relative_frontier sx) = s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^N` THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `z:real^N`] MOI_CMB_RADIAL) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[MOI_CMB_FRONTIER_NONZERO]; SIMP_TAC[]];
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(x:real^N = vec 0)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`sx:real^N->bool`; `vec 0:real^N`; `x:real^N`]
      RAY_TO_RELATIVE_FRONTIER) THEN
    ASM_REWRITE_TAC[IN_UNIV; VECTOR_ADD_LID] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d % x:real^N` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(d % x:real^N = vec 0)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[VECTOR_MUL_EQ_0] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `d % x:real^N`] MOI_CMB_RADIAL) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `inv d:real` o last o CONJUNCTS) THEN
    ASM_SIMP_TAC[REAL_LT_INV_EQ; VECTOR_MUL_ASSOC; REAL_MUL_LINV;
                 REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

let MOI_CMB_STAR_SHAPED_PL_SPHERE_0 = prove
 (`!s:real^N->bool.
        pl_polyhedron s /\ ~(vec 0 IN s) /\
        (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ r % u IN s)
        ==> pl_sphere (dimindex(:N) - 1) s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX]) THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `vec 0:real^N` CHOOSE_SURROUNDING_SIMPLEX_FULL) THEN
  DISCH_THEN(X_CHOOSE_THEN `sx:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `polytope (sx:real^N->bool) /\ convex sx /\ bounded sx`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_CONVEX;
                  POLYTOPE_IMP_BOUNDED];
    ALL_TAC] THEN
  SUBGOAL_THEN `affine hull (sx:real^N->bool) = (:real^N)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_HULL_NONEMPTY_INTERIOR THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `vec 0 IN relative_interior (sx:real^N->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_INTERIOR]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `K:(real^N->bool)->bool`; `sx:real^N->bool`]
    MOI_CMB_FAN_TRIANGULATION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `moi_cmb_radial (s:real^N->bool)`]
    MOI_CMB_RADIAL_REALIZES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_CMB_RADIAL_INJECTIVE THEN
    MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `sx:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. x`; `moi_cmb_radial (s:real^N->bool)`;
                 `moi_real_vertex_sets (L:(real^N->bool)->bool)`]
    ABSTRACT_REALIZATIONS_PL_HOMEOMORPHIC) THEN
  ASM_SIMP_TAC[MOI_REAL_VERTEX_SETS_FINITE; MOI_REAL_VERTEX_SETS_ABSTRACT_COMPLEX;
               MOI_REAL_VERTEX_SETS_REALIZES; MOI_REAL_VERTEX_SETS_UNIONS] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `sx:real^N->bool`] MOI_CMB_RADIAL_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^N` (X_CHOOSE_THEN `h':real^N->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)))) THEN
  MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
  MAP_EVERY EXISTS_TAC [`relative_frontier sx:real^N->bool`;
                        `h:real^N->real^N`; `h':real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
  ASM_SIMP_TAC[DIMINDEX_GE_1; SUB_ADD]);;

let MOI_CMB_TRANSLATION_PL_HOMEOMORPHISM = prove
 (`!(s:real^N->bool) p.
        pl_polyhedron s
        ==> pl_homeomorphism (IMAGE (\x. --p + x) s,s) ((\x. p + x),(\x. --p + x))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism; FORALL_IN_IMAGE; GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[VECTOR_ARITH `p + --p + x:real^N = x`;
                VECTOR_ARITH `--p + p + x:real^N = x`; IMAGE_ID] THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `\x:real^N. x + p` THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
      VECTOR_ARITH_TAC;
      MP_TAC(ISPECL [`IMAGE (\x:real^N. --p + x) s`; `\x:real^N. x`;
                     `p:real^N`] PL_MAP_ON_AFFINE) THEN
      REWRITE_TAC[LINEAR_ID] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      ASM_SIMP_TAC[PL_POLYHEDRON_TRANSLATION]]]);;

let STAR_SHAPED_PL_SPHERE = prove
 (`!(s:real^3->bool) (p:real^3).
     pl_polyhedron s /\ ~(p IN s) /\
     (!u. ~(u = vec 0) ==> ?!r. &0 < r /\ p + r % u IN s)
     ==> pl_sphere 2 s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!y:real^3. y IN IMAGE (\x. --p + x) s <=> p + y IN s`
  ASSUME_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_ARITH `p + --p + x:real^N = x`];
      DISCH_TAC THEN EXISTS_TAC `p + y:real^3` THEN ASM_REWRITE_TAC[] THEN
      VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPEC `IMAGE (\x:real^3. --p + x) s` MOI_CMB_STAR_SHAPED_PL_SPHERE_0) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_RID; DIMINDEX_3] THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[PL_POLYHEDRON_TRANSLATION]; ALL_TAC] THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN DISCH_TAC THEN
  MATCH_MP_TAC PL_SPHERE_PL_HOMEOMORPHIC THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (\x:real^3. --p + x) s`; `\x:real^3. p + x`;
                        `\x:real^3. --p + x`] THEN
  ASM_SIMP_TAC[MOI_CMB_TRANSLATION_PL_HOMEOMORPHISM]);;

(* ------------------------------------------------------------------------- *)
(* 4. Local structure of a locally finite complex at a vertex: the star is  *)
(* a neighbourhood, and it is the cone from the vertex over the link with   *)
(* unique cone coordinates.  PL maps are conical near a point.              *)
(* ------------------------------------------------------------------------- *)

let MOI_CMB_FINITE_CLOSED_AVOID = prove
 (`!C (v:real^N) u.
        FINITE C /\ (!k. k IN C ==> closed k) /\ open u /\ v IN u
        ==> ?e. &0 < e /\
                !x. dist(v,x) < e ==> x IN u /\ !k. k IN C /\ x IN k ==> v IN k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closed (UNIONS {k:real^N->bool | k IN C /\ ~(v IN k)})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[IN_ELIM_THM; FINITE_RESTRICT];
    ALL_TAC] THEN
  MP_TAC(ISPEC `u DIFF UNIONS {k:real^N->bool | k IN C /\ ~(v IN k)}`
    OPEN_CONTAINS_BALL) THEN
  ASM_SIMP_TAC[OPEN_DIFF] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
  MESON_TAC[]);;

let MOI_CMB_STAR_NBHD = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ v IN UNIONS c
        ==> ?e. &0 < e /\
                !x. x IN UNIONS c /\ dist(v,x) < e
                    ==> ?t. t IN c /\ v IN t /\ x IN t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `v:real^N`)))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`{s:real^N->bool | s IN c /\ ~(s INTER u = {})}`;
                 `v:real^N`; `u:real^N->bool`] MOI_CMB_FINITE_CLOSED_AVOID) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `t:real^N->bool`)) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]);;

let MOI_CMB_LINK_FINITE = prove
 (`!c (v:real^N).
        lf_simplicial_complex c /\ v IN UNIONS c
        ==> FINITE (simplicial_link c v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (K ALL_TAC) (MP_TAC o SPEC `v:real^N`)))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `UNIONS {{f:real^N->bool | f face_of t} |
                      t IN {s:real^N->bool | s IN c /\ ~(s INTER u = {})}}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNIONS; SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_POLYTOPE_FACES THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    REWRITE_TAC[SUBSET; simplicial_link; IN_ELIM_THM; IN_UNIONS] THEN
    X_GEN_TAC `f:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `{f:real^N->bool | f face_of t}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM SET_TAC[]]);;

let MOI_CMB_LINK_IN_STAR = prove
 (`!c (v:real^N) y.
        y IN UNIONS (simplicial_link c v)
        ==> ?t. t IN c /\ v IN t /\ y IN t /\ ~(y = v)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[simplicial_link; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ASM_MESON_TAC[]]);;

let MOI_CMB_SEGMENT_IN = prove
 (`!t (v:real^N) y r.
        convex t /\ v IN t /\ y IN t /\ &0 <= r /\ r <= &1
        ==> v + r % (y - v) IN t`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[VECTOR_ARITH `v + r % (y - v):real^N = (&1 - r) % v + r % y`] THEN
  ASM_MESON_TAC[CONVEX_ALT]);;

let MOI_CMB_STAR_CONE = prove
 (`!c (v:real^N) t x.
        lf_simplicial_complex c /\ {v} IN c /\ t IN c /\ v IN t /\ x IN t /\
        ~(x = v)
        ==> ?y r. y IN UNIONS (simplicial_link c v) /\ &0 < r /\ r <= &1 /\
                  x = v + r % (y - v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  SUBGOAL_THEN `?V:real^N->bool. ~affine_dependent V /\ t = convex hull V`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplex]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN V` ASSUME_TAC THENL
   [SUBGOAL_THEN `{v:real^N} face_of t` MP_TAC THENL
     [SUBGOAL_THEN `{v:real^N} INTER t = {v}` (fun th -> ASM_MESON_TAC[th]) THEN
      ASM SET_TAC[];
      ASM_REWRITE_TAC[FACE_OF_SING] THEN
      ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT]];
    ALL_TAC] THEN
  ASM_CASES_TAC `V DELETE (v:real^N) = {}` THENL
   [SUBGOAL_THEN `V = {v:real^N}` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN t` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `V:real^N->bool = v INSERT (V DELETE v)`
    (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o RAND_CONV) [th]) THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
    (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`y:real^N`; `b:real`] THEN
  SUBGOAL_THEN `~(b = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `a = &1` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `~(x:real^N = v)` THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LZERO; VECTOR_ADD_RID];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `convex hull (V DELETE v):real^N->bool` THEN
    ASM_REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    SUBGOAL_THEN `convex hull (V DELETE v) face_of (t:real^N->bool)`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `V DELETE (v:real^N)` THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      UNDISCH_TAC `~affine_dependent (V:real^N->bool)` THEN
      REWRITE_TAC[affine_dependent] THEN
      MP_TAC(ISPEC `V DELETE (v:real^N)` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      REWRITE_TAC[SUBSET] THEN ASM_MESON_TAC[];
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ASM_REAL_ARITH_TAC;
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `a = &1 - b` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]]);;

let MOI_CMB_LINK_NOT_BETWEEN = prove
 (`!c (v:real^N) y1 y2 l.
        lf_simplicial_complex c /\
        y1 IN UNIONS (simplicial_link c v) /\
        y2 IN UNIONS (simplicial_link c v) /\ &0 < l /\ l < &1
        ==> ~(y2 = v + l % (y1 - v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
  UNDISCH_TAC `(y1:real^N) IN UNIONS (simplicial_link c v)` THEN
  REWRITE_TAC[simplicial_link; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f1:real^N->bool` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t1:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
  UNDISCH_TAC `v + l % (y1 - v) IN UNIONS (simplicial_link c (v:real^N))` THEN
  REWRITE_TAC[simplicial_link; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `f2:real^N->bool` (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `t2:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(y1:real^N) IN t1` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (t1:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `v + l % (y1 - v) IN (t1:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v:real^N = y1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(v + l % (y1 - v):real^N) IN segment(v,y1)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `l:real` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f2 INTER t1:real^N->bool) face_of t1` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[face_of] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `y1:real^N`; `v + l % (y1 - v):real^N`] o
    CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[IN_INTER]);;

let MOI_CMB_SCALE_EQ = prove
 (`!(v:real^N) y1 y2 r1 r2.
        ~(r2 = &0) /\ v + r1 % (y1 - v) = v + r2 % (y2 - v)
        ==> y2 = v + (inv r2 * r1) % (y1 - v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `r2 % (y2 - v):real^N = r1 % (y1 - v)` MP_TAC THENL
   [UNDISCH_TAC `v + r1 % (y1 - v):real^N = v + r2 % (y2 - v)` THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o AP_TERM `(%) (inv r2):real^N->real^N`) THEN
  ASM_SIMP_TAC[VECTOR_MUL_ASSOC; REAL_MUL_LINV; VECTOR_MUL_LID] THEN
  VECTOR_ARITH_TAC);;

let MOI_CMB_CONE_UNIQUE = prove
 (`!c (v:real^N) y1 y2 r1 r2.
        lf_simplicial_complex c /\
        y1 IN UNIONS (simplicial_link c v) /\
        y2 IN UNIONS (simplicial_link c v) /\ &0 < r1 /\ &0 < r2 /\
        v + r1 % (y1 - v) = v + r2 % (y2 - v)
        ==> r1 = r2 /\ y1 = y2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r1:real) = r2` ASSUME_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (REAL_ARITH `(r1:real) < r2 \/ r1 = r2 \/ r2 < r1`) THEN
    ASM_REWRITE_TAC[] THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y1:real^N`;
                     `y2:real^N`; `inv(r2:real) * r1`] MOI_CMB_LINK_NOT_BETWEEN) THEN
      MP_TAC(ISPECL [`v:real^N`; `y1:real^N`; `y2:real^N`; `r1:real`; `r2:real`]
        MOI_CMB_SCALE_EQ);
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y2:real^N`;
                     `y1:real^N`; `inv(r1:real) * r2`] MOI_CMB_LINK_NOT_BETWEEN) THEN
      MP_TAC(ISPECL [`v:real^N`; `y2:real^N`; `y1:real^N`; `r2:real`; `r1:real`]
        MOI_CMB_SCALE_EQ)] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_TAC THEN
    REWRITE_TAC[NOT_IMP] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_INV_EQ] THEN
    ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN REWRITE_TAC[GSYM real_div] THEN
    ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `v + r1 % (y1 - v):real^N = v + r2 % (y2 - v)` THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `v + r % (y1 - v):real^N = v + r % (y2 - v) <=>
                                r % (y1 - v) = r % (y2 - v)`] THEN
  ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ] THEN VECTOR_ARITH_TAC);;

let MOI_CMB_PL_LOCALLY_CONIC = prove
 (`!(W:real^N->bool) (g:real^N->real^M) v.
        pl_map_on W g /\ v IN W
        ==> ?e. &0 < e /\
                !x l. x IN W /\ dist(v,x) < e /\ &0 <= l /\ l <= &1
                      ==> v + l % (x - v) IN W /\
                          g(v + l % (x - v)) = g v + l % (g x - g v)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o GEN_REWRITE_RULE I [pl_map_on]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:(real^N->bool)->bool`
    (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`C:(real^N->bool)->bool`; `v:real^N`; `u:real^N->bool`]
    MOI_CMB_FINITE_CLOSED_AVOID) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[POLYTOPE_IMP_CLOSED]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `l:real`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?k:real^N->bool. k IN C /\ x IN k` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN k` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(k:real^N->bool) IN C`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `L:real^N->real^M` (X_CHOOSE_THEN `y:real^M`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `v + l % (x - v):real^N IN k` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN
  FIRST_ASSUM(fun th -> REWRITE_TAC[MATCH_MP LINEAR_ADD th;
    MATCH_MP LINEAR_CMUL th; MATCH_MP LINEAR_SUB th]) THEN
  VECTOR_ARITH_TAC);;

let MOI_CMB_SMALL_SCALE = prove
 (`!(s:real^N->bool) v e.
        bounded s /\ &0 < e
        ==> ?r. &0 < r /\ r <= &1 /\
                !y. y IN s ==> dist(v,v + r % (y - v)) < e`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [BOUNDED_POS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `B:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?D. &0 < D /\ !y:real^N. y IN s ==> norm(y - v) <= D`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `B + norm(v:real^N) + &1` THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `v:real^N` NORM_POS_LE) THEN ASM_REAL_ARITH_TAC;
      X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
      NORM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\ r <= &1 /\ r * D <= e / &2` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1) (e / (&2 * D))` THEN
    SUBGOAL_THEN `&0 < e / (&2 * D)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `e / (&2 * D) * D` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
        REAL_ARITH_TAC;
        SUBGOAL_THEN `e / (&2 * D) * D = e / &2`
          (fun th -> REWRITE_TAC[th; REAL_LE_REFL]) THEN
        UNDISCH_TAC `&0 < D` THEN CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[dist; VECTOR_ARITH `v - (v + r % (y - v)):real^N = --(r % (y - v))`;
              NORM_NEG; NORM_MUL] THEN
  ASM_SIMP_TAC[REAL_ARITH `&0 < r ==> abs r = r`] THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `r * D` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN ASM_SIMP_TAC[REAL_LT_IMP_LE];
    ASM_REAL_ARITH_TAC]);;

let MOI_CMB_PL_POLYHEDRON_SCALE = prove
 (`!(s:real^N->bool) v r.
        pl_polyhedron s ==> pl_polyhedron (IMAGE (\y. v + r % (y - v)) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\y:real^N. v + r % (y - v)) s =
                IMAGE (\x. (&1 - r) % v + x) (IMAGE (\y. r % y) s)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PL_POLYHEDRON_TRANSLATION THEN
  MATCH_MP_TAC PL_POLYHEDRON_LINEAR_IMAGE THEN
  ASM_REWRITE_TAC[LINEAR_SCALING]);;

let MOI_CMB_SCALE_PL_HOMEOMORPHISM = prove
 (`!(s:real^N->bool) v r.
        pl_polyhedron s /\ &0 < r
        ==> pl_homeomorphism (s,IMAGE (\y. v + r % (y - v)) s)
                             ((\y. v + r % (y - v)),(\z. v + inv r % (z - v)))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `!x:real^N. v + inv r % ((v + r % (x - v)) - v) = x`
    ASSUME_TAC THENL
     [GEN_TAC THEN
      REWRITE_TAC[VECTOR_ARITH `(v + r % (x - v)) - v:real^N = r % (x - v)`;
                  VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[homeomorphism; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID] THEN
    SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_CMUL; CONTINUOUS_ON_SUB;
             CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\y:real^N. r % y + (&1 - r) % v` THEN CONJ_TAC THENL
     [REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
      MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. r % y`;
                     `(&1 - r) % v:real^N`] PL_MAP_ON_AFFINE) THEN
      ASM_SIMP_TAC[LINEAR_SCALING; LOCALLY_POLYHEDRAL_PL_POLYHEDRON]]]);;

let MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER = prove
 (`!k:real^N->bool. polytope k ==> pl_polyhedron (relative_frontier k)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `{f:real^N->bool | f facet_of k}` THEN
  ASM_SIMP_TAC[FINITE_POLYTOPE_FACETS; IN_ELIM_THM;
               RELATIVE_FRONTIER_OF_POLYHEDRON; POLYTOPE_IMP_POLYHEDRON] THEN
  ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; facet_of]);;

let MOI_CMB_PL_SPHERE_TRANSFER = prove
 (`!n (s:real^M->bool) (t:real^N->bool) f g.
        dimindex(:M) <= dimindex(:N) /\ pl_sphere n s /\
        pl_homeomorphism (s,t) (f,g)
        ==> pl_sphere n t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `k:real^M->bool` (X_CHOOSE_THEN `f0:real^M->real^M`
      (X_CHOOSE_THEN `g0:real^M->real^M` STRIP_ASSUME_TAC)))
    ASSUME_TAC)) THEN
  MP_TAC ISOMETRY_UNIV_UNIV THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:real^M->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x y:real^M. (j:real^M->real^N) x = j y ==> x = y`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_INJECTIVE_0] THEN
    ONCE_REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `j:real^M->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `j':real^N->real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^M. (j':real^N->real^M) ((j:real^M->real^N) x) = x`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[o_THM; I_THM];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (j:real^M->real^N) k` THEN
  EXISTS_TAC `(f:real^M->real^N) o ((f0:real^M->real^M) o (j':real^N->real^M))` THEN
  EXISTS_TAC `((j:real^M->real^N) o (g0:real^M->real^M)) o (g:real^N->real^M)` THEN
  SUBGOAL_THEN `linear (j:real^M->real^N) /\ (!x y:real^M. j x = j y ==> x = y)`
   (fun th -> REWRITE_TAC[MATCH_MP SIMPLEX_LINEAR_IMAGE_EQ th;
                          MATCH_MP RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE th])
  THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `s:real^M->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `relative_frontier k:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [REWRITE_TAC[homeomorphism; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN ASM_REWRITE_TAC[IMAGE_ID] THEN
    ASM_SIMP_TAC[LINEAR_CONTINUOUS_ON];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `\x:real^N. (j':real^N->real^M) x + vec 0` THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_RID];
      MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
      MATCH_MP_TAC PL_POLYHEDRON_LINEAR_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]]]);;

(* ------------------------------------------------------------------------- *)
(* 5. Vertex links of a PL triangulation of an open subset of a PL           *)
(* 3-manifold: near a vertex the chart map is conical, the image of a small *)
(* copy of the link is met exactly once by every ray from the image of the  *)
(* vertex, hence it is a PL 2-sphere, and so is the link.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_CMB_IN_IMAGE_IMAGE = prove
 (`!(g:A->B) (h:C->A) s z.
        z IN IMAGE g (IMAGE h s) <=> ?y. y IN s /\ z = g(h y)`,
  REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

let MOI_CMB_RAY_PROPERTY = prove
 (`!(c:(real^N->bool)->bool) v (W:real^N->bool) (g:real^N->real^M) e r d.
        lf_simplicial_complex c /\ {v} IN c /\ W SUBSET UNIONS c /\
        &0 < r /\ r <= &1 /\ &0 < d /\
        (!x. x IN UNIONS c /\ dist(v,x) < e ==> ?t. t IN c /\ v IN t /\ x IN t) /\
        (!x l. x IN W /\ dist(v,x) < e /\ &0 <= l /\ l <= &1
               ==> v + l % (x - v) IN W /\
                   g(v + l % (x - v)) = g v + l % (g x - g v)) /\
        (!y. y IN UNIONS (simplicial_link c v)
             ==> v + r % (y - v) IN W /\ dist(v,v + r % (y - v)) < e) /\
        (!x y. x IN W /\ y IN W /\ g x = g y ==> x = y) /\
        (!q. dist(g v,q) < d ==> ?x. x IN W /\ dist(v,x) < e /\ g x = q)
        ==> !u. ~(u = vec 0)
                ==> ?!rho. &0 < rho /\
                           g v + rho % u IN
                           IMAGE g (IMAGE (\y. v + r % (y - v))
                                          (UNIONS (simplicial_link c v)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (LABEL_TAC "star") (CONJUNCTS_THEN2 (LABEL_TAC "conic")
   (CONJUNCTS_THEN2 (LABEL_TAC "lr") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
    (LABEL_TAC "open"))))))))))) THEN
  X_GEN_TAC `u:real^M` THEN DISCH_TAC THEN
  REWRITE_TAC[EXISTS_UNIQUE_THM; MOI_CMB_IN_IMAGE_IMAGE] THEN
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 < norm(u:real^M)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < d / (&2 * norm(u:real^M))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "open" (MP_TAC o SPEC
      `(g:real^N->real^M) v + (d / (&2 * norm(u:real^M))) % u`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[dist; VECTOR_ARITH `a - (a + b):real^N = --b`;
                  NORM_NEG; NORM_MUL] THEN
      ASM_SIMP_TAC[REAL_ARITH `&0 < a ==> abs a = a`] THEN
      SUBGOAL_THEN `d / (&2 * norm(u:real^M)) * norm u = d / &2`
      SUBST1_TAC THENL
       [UNDISCH_TAC `&0 < norm(u:real^M)` THEN CONV_TAC REAL_FIELD;
        ASM_REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC)] THEN
    SUBGOAL_THEN `~(x:real^N = v)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC
       `(g:real^N->real^M) x = g v + (d / (&2 * norm(u:real^M))) % u` THEN
      ASM_REWRITE_TAC[VECTOR_ARITH `a = a + b <=> b = vec 0:real^N`;
                      VECTOR_MUL_EQ_0] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `?t:real^N->bool. t IN c /\ v IN t /\ x IN t`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "star" MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                   `x:real^N`] MOI_CMB_STAR_CONE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `s:real`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))))) THEN
    USE_THEN "lr" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `y IN UNIONS (simplicial_link c (v:real^N))`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `(g:real^N->real^M)(v + r % (y - v)) =
      g v + (r / s) % (g(v + s % (y - v)) - g v)`
    ASSUME_TAC THENL
     [DISJ_CASES_TAC(REAL_ARITH `(s:real) <= r \/ r < s`) THENL
       [USE_THEN "conic" (MP_TAC o SPECL [`v + r % (y - v):real^N`; `s / r`]) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                       REAL_MUL_LID];
          ALL_TAC] THEN
        REWRITE_TAC[VECTOR_ARITH `(v + r % (y - v)) - v:real^N = r % (y - v)`;
                    VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`;
                        VECTOR_MUL_ASSOC] THEN
        SUBGOAL_THEN `r / s * s / r = &1` SUBST1_TAC THENL
         [MAP_EVERY UNDISCH_TAC [`&0 < r`; `&0 < s`] THEN CONV_TAC REAL_FIELD;
          VECTOR_ARITH_TAC];
        USE_THEN "conic" (MP_TAC o SPECL [`v + s % (y - v):real^N`; `r / s`]) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                       REAL_MUL_LID];
          ALL_TAC] THEN
        REWRITE_TAC[VECTOR_ARITH `(v + r % (y - v)) - v:real^N = r % (y - v)`;
                    VECTOR_MUL_ASSOC] THEN
        ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]];
      ALL_TAC] THEN
    EXISTS_TAC `r / s * d / (&2 * norm(u:real^M))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_DIV]; ALL_TAC] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`; VECTOR_MUL_ASSOC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b y1 y2. &0 < a /\ a < b /\
                y1 IN UNIONS (simplicial_link c v) /\
                y2 IN UNIONS (simplicial_link c v) /\
                (g:real^N->real^M) v + a % u = g(v + r % (y1 - v)) /\
                g v + b % u = g(v + r % (y2 - v))
                ==> F`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    USE_THEN "lr" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `y2 IN UNIONS (simplicial_link c (v:real^N))`))) THEN
    STRIP_TAC THEN
    USE_THEN "lr" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `y1 IN UNIONS (simplicial_link c (v:real^N))`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "conic" (MP_TAC o SPECL [`v + r % (y2 - v):real^N`; `a / b`]) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ;
                   REAL_MUL_LID];
      ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH `(v + r % (y - v)) - v:real^N = r % (y - v)`;
                VECTOR_MUL_ASSOC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `v + (a / b * r) % (y2 - v):real^N = v + r % (y1 - v)`
    ASSUME_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(g:real^N->real^M) v + a % u = g(v + r % (y1 - v))`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(g:real^N->real^M) v + b % u = g(v + r % (y2 - v))`)) THEN
      REWRITE_TAC[VECTOR_ARITH `(a + b) - a:real^N = b`; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y2:real^N`;
                   `y1:real^N`; `a / b * r`; `r:real`] MOI_CMB_CONE_UNIQUE) THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_DIV] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    SUBGOAL_THEN `a / b * r < &1 * r` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN
      ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:real`; `b:real`] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y2:real^N` STRIP_ASSUME_TAC))) THEN
  REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
   (REAL_ARITH `(a:real) < b \/ a = b \/ b < a`) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_CMB_LOCAL_LINK_SPHERE = prove
 (`!(c:(real^N->bool)->bool) (v:real^N) (W:real^N->bool) (g:real^N->real^3).
        3 <= dimindex(:N) /\
        lf_simplicial_complex c /\ {v} IN c /\
        W SUBSET UNIONS c /\ v IN W /\
        (?e. &0 < e /\ !x. x IN UNIONS c /\ dist(v,x) < e ==> x IN W) /\
        pl_map_on W g /\
        (!x y. x IN W /\ y IN W /\ g x = g y ==> x = y) /\
        (!e. &0 < e
             ==> ?d. &0 < d /\
                     !q. dist(g v,q) < d
                         ==> ?x. x IN W /\ dist(v,x) < e /\ g x = q)
        ==> pl_sphere 2 (UNIONS (simplicial_link c v))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
     (LABEL_TAC "open"))))))))) THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (UNIONS (simplicial_link c (v:real^N)))`
  ASSUME_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `simplicial_link c (v:real^N)` THEN
    ASM_SIMP_TAC[MOI_CMB_LINK_FINITE] THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [lf_simplicial_complex]) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_CMB_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`W:real^N->bool`; `g:real^N->real^3`; `v:real^N`]
    MOI_CMB_PL_LOCALLY_CONIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e3:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?e. &0 < e /\ e <= e1 /\ e <= e2 /\ e <= e3`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min e1 (min e2 e3)` THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x. x IN UNIONS c /\ dist(v:real^N,x) < e
        ==> ?t. t IN c /\ v IN t /\ x IN t`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LTE_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x l. x IN W /\ dist(v:real^N,x) < e /\ &0 <= l /\ l <= &1
          ==> v + l % (x - v) IN W /\
              (g:real^N->real^3)(v + l % (x - v)) = g v + l % (g x - g v)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[REAL_LTE_TRANS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS (simplicial_link c (v:real^N))`; `v:real^N`; `e:real`]
    MOI_CMB_SMALL_SCALE) THEN
  ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT; COMPACT_IMP_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!y. y IN UNIONS (simplicial_link c v)
        ==> v + r % (y - v) IN W /\ dist(v:real^N,v + r % (y - v)) < e`
  (LABEL_TAC "lr") THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `dist(v:real^N,v + r % (y - v)) < e` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `v + r % (y - v) IN UNIONS (c:(real^N->bool)->bool)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`]
        MOI_CMB_LINK_IN_STAR) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
      ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    ASM_MESON_TAC[REAL_LTE_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\y. v + r % (y - v)) (UNIONS (simplicial_link c (v:real^N))) SUBSET W`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN
    DISCH_TAC THEN USE_THEN "lr" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `y IN UNIONS (simplicial_link c (v:real^N))`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_polyhedron (IMAGE (\y. v + r % (y - v))
                         (UNIONS (simplicial_link c (v:real^N))))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_SCALE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on (IMAGE (\y. v + r % (y - v))
                     (UNIONS (simplicial_link c (v:real^N))))
              (g:real^N->real^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `W:real^N->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    ALL_TAC] THEN
  USE_THEN "open" (fun th -> MP_TAC(MATCH_MP th (ASSUME `&0 < e`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `W:real^N->bool`;
                 `g:real^N->real^3`; `e:real`; `r:real`; `d:real`]
    MOI_CMB_RAY_PROPERTY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (g:real^N->real^3) (IMAGE (\y. v + r % (y - v))
                         (UNIONS (simplicial_link c (v:real^N))))`;
                 `(g:real^N->real^3) v`] STAR_SHAPED_PL_SPHERE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[MOI_CMB_IN_IMAGE_IMAGE; NOT_EXISTS_THM] THEN
      X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      USE_THEN "lr" (fun th -> MP_TAC(MATCH_MP th (ASSUME
        `y IN UNIONS (simplicial_link c (v:real^N))`))) THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `~(y:real^N = v)` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`]
          MOI_CMB_LINK_IN_STAR) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `v:real^N = v + r % (y - v)` MP_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[VECTOR_ARITH
       `(v:real^N) = v + r % (y - v) <=> r % (y - v) = vec 0`;
       VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (\y. v + r % (y - v))
                        (UNIONS (simplicial_link c (v:real^N)))`;
                 `g:real^N->real^3`;
                 `IMAGE (g:real^N->real^3) (IMAGE (\y. v + r % (y - v))
                         (UNIONS (simplicial_link c (v:real^N))))`]
    HOMEOMORPHISM_COMPACT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT];
      ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON];
      REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`] THEN STRIP_TAC THEN
      USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (\y. v + r % (y - v))
                     (UNIONS (simplicial_link c (v:real^N))) SUBSET W` THEN
      MAP_EVERY UNDISCH_TAC
       [`x1 IN IMAGE (\y. v + r % (y - v))
                     (UNIONS (simplicial_link c (v:real^N)))`;
        `x2 IN IMAGE (\y. v + r % (y - v))
                     (UNIONS (simplicial_link c (v:real^N)))`] THEN
      SET_TAC[]];
    DISCH_THEN(X_CHOOSE_TAC `g':real^3->real^N`)] THEN
  MATCH_MP_TAC(ISPECL
   [`2`; `IMAGE (g:real^N->real^3) (IMAGE (\y. v + r % (y - v))
                         (UNIONS (simplicial_link c (v:real^N))))`;
    `UNIONS (simplicial_link c (v:real^N))`;
    `(\z:real^N. v + inv r % (z - v)) o (g':real^3->real^N)`;
    `(g:real^N->real^3) o (\y:real^N. v + r % (y - v))`]
   MOI_CMB_PL_SPHERE_TRANSFER) THEN
  ASM_REWRITE_TAC[DIMINDEX_3] THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN
  MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `IMAGE (\y. v + r % (y - v))
                    (UNIONS (simplicial_link c (v:real^N)))` THEN
  ASM_SIMP_TAC[MOI_CMB_SCALE_PL_HOMEOMORPHISM] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 6. The chart data of a PL triangulation, and the main theorem.            *)
(* ------------------------------------------------------------------------- *)

let MOI_CMB_TRIANG_OPEN = prove
 (`!(top:A topology) (c:(real^N->bool)->bool) t s U.
        homeomorphic_map (subtopology euclidean (UNIONS c),subtopology top s) t /\
        open_in top U
        ==> open_in (subtopology euclidean (UNIONS c))
                    {x | x IN UNIONS c /\ t x IN U}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP) THEN
  MP_TAC(ISPECL [`t:real^N->A`; `subtopology euclidean (UNIONS c:real^N->bool)`;
                 `subtopology top (s:A->bool)`; `s INTER U:A->bool`]
    OPEN_IN_CONTINUOUS_MAP_PREIMAGE) THEN
  ASM_SIMP_TAC[OPEN_IN_SUBTOPOLOGY_INTER_OPEN; TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE) THEN
  REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
  SET_TAC[]);;

let MOI_CMB_OPEN_IN_BALL = prove
 (`!(u:real^N->bool) w v.
        open_in (subtopology euclidean u) w /\ v IN w
        ==> ?e. &0 < e /\ !x. x IN u /\ dist(v,x) < e ==> x IN w`,
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN
  MESON_TAC[]);;

let MOI_CMB_TRIANG_INJ = prove
 (`!(top:A topology) (c:(real^N->bool)->bool) t s U (phi:A->real^M) g.
        homeomorphic_map (subtopology euclidean (UNIONS c),subtopology top s) t /\
        open_in top s /\ open_in top U /\
        homeomorphic_map (subtopology top U,subtopology euclidean (IMAGE phi U))
                         phi /\
        (!x. x IN UNIONS c /\ t x IN U ==> g x = phi(t x))
        ==> !x y. x IN {x | x IN UNIONS c /\ t x IN U} /\
                  y IN {x | x IN UNIONS c /\ t x IN U} /\ g x = g y
                  ==> x = y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^N->A) x IN s /\ t y IN s` STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE
     (MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP (ASSUME
       `homeomorphic_map (subtopology euclidean (UNIONS c),subtopology top s)
                         (t:real^N->A)`))) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    MAP_EVERY UNDISCH_TAC [`(x:real^N) IN UNIONS c`; `(y:real^N) IN UNIONS c`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:A->bool) SUBSET topspace top` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->A) x = t y` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology top (U:A->bool)`;
                   `subtopology euclidean (IMAGE (phi:A->real^M) U)`;
                   `phi:A->real^M`] HOMEOMORPHIC_IMP_INJECTIVE_MAP) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY; IN_INTER] THEN
    DISCH_THEN(MP_TAC o SPECL [`(t:real^N->A) x`; `(t:real^N->A) y`]) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[SUBSET]; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS c:real^N->bool)`;
                 `subtopology top (s:A->bool)`;
                 `t:real^N->A`] HOMEOMORPHIC_IMP_INJECTIVE_MAP) THEN
  ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
  DISCH_THEN(MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
  ASM_REWRITE_TAC[]);;

let MOI_CMB_TRIANG_OPEN_MAP = prove
 (`!(top:A topology) (c:(real^N->bool)->bool) t s U (phi:A->real^M) g v e.
        homeomorphic_map (subtopology euclidean (UNIONS c),subtopology top s) t /\
        open_in top s /\ open_in top U /\ open (IMAGE phi U) /\
        homeomorphic_map (subtopology top U,subtopology euclidean (IMAGE phi U))
                         phi /\
        (!x. x IN UNIONS c /\ t x IN U ==> g x = phi(t x)) /\
        v IN UNIONS c /\ t v IN U /\ &0 < e
        ==> ?d. &0 < d /\
                !q. dist(g v,q) < d
                    ==> ?x. x IN {x | x IN UNIONS c /\ t x IN U} /\
                            dist(v,x) < e /\ g x = q`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `B = {x | x IN UNIONS c /\ (t:real^N->A) x IN U} INTER ball(v,e)` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS c:real^N->bool)) B`
  ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN
    REWRITE_TAC[OPEN_BALL] THEN MATCH_MP_TAC MOI_CMB_TRIANG_OPEN THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `s:A->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(B:real^N->bool) SUBSET UNIONS c /\
                IMAGE (t:real^N->A) B SUBSET U /\ IMAGE t B SUBSET s`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE
     (MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP (ASSUME
       `homeomorphic_map (subtopology euclidean (UNIONS c),subtopology top s)
                         (t:real^N->A)`))) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    EXPAND_TAC "B" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open_in top (IMAGE (t:real^N->A) B)` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_TRANS_FULL THEN EXISTS_TAC `s:A->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:real^N->A`; `subtopology euclidean (UNIONS c:real^N->bool)`;
                   `subtopology top (s:A->bool)`; `B:real^N->bool`]
      HOMEOMORPHIC_MAP_OPENNESS) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (phi:A->real^M) (IMAGE (t:real^N->A) B))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (phi:A->real^M) U` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`phi:A->real^M`; `subtopology top (U:A->bool)`;
                   `subtopology euclidean (IMAGE (phi:A->real^M) U)`;
                   `IMAGE (t:real^N->A) B`] HOMEOMORPHIC_MAP_OPENNESS) THEN
    ASM_REWRITE_TAC[TOPSPACE_SUBTOPOLOGY] THEN
    ANTS_TAC THENL
     [MP_TAC(ISPECL [`top:A topology`; `s:A->bool`] OPEN_IN_SUBSET) THEN
      ASM SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET_TOPSPACE THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN B` ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; CENTRE_IN_BALL];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `(g:real^N->real^M) v`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(t:real^N->A) v` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `q:real^M` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(q:real^M) IN IMAGE (phi:A->real^M) (IMAGE (t:real^N->A) B)`
  MP_TAC THENL
   [UNDISCH_TAC `ball((g:real^N->real^M) v,d) SUBSET
                 IMAGE (phi:A->real^M) (IMAGE (t:real^N->A) B)` THEN
    REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:A` (CONJUNCTS_THEN2 SUBST1_TAC
    (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `x:real^N` THEN
  UNDISCH_TAC `(x:real^N) IN B` THEN EXPAND_TAC "B" THEN
  REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[]);;

let PL_TRIANGULATION_COMBINATORIAL = prove
 (`!(top:A topology) (atlas:((A->bool)#(A->real^3))->bool)
    (c:(real^N->bool)->bool) t s.
     3 <= dimindex(:N) /\ pl_manifold_atlas top atlas /\ open_in top s /\
     pl_triangulation top atlas c t s
     ==> combinatorial_manifold 3 c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_triangulation; combinatorial_manifold] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  CONV_TAC(ONCE_DEPTH_CONV NUM_REDUCE_CONV) THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->A) v IN topspace top` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP CONTINUOUS_MAP_IMAGE_SUBSET_TOPSPACE
     (MATCH_MP HOMEOMORPHIC_IMP_CONTINUOUS_MAP (ASSUME
       `homeomorphic_map (subtopology euclidean (UNIONS c),subtopology top s)
                         (t:real^N->A)`))) THEN
    REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY; TOPSPACE_SUBTOPOLOGY] THEN
    UNDISCH_TAC `(v:real^N) IN UNIONS c` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_manifold_atlas]) THEN
  SUBGOAL_THEN `?U (phi:A->real^3). (U,phi) IN atlas /\ (t:real^N->A) v IN U`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?g:real^N->real^3.
        pl_map_on {x | x IN UNIONS c /\ (t:real^N->A) x IN U} g /\
        !x. x IN UNIONS c /\ t x IN U ==> g x = phi(t x)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `open_in top (U:A->bool) /\ open (IMAGE (phi:A->real^3) U) /\
    homeomorphic_map (subtopology top U,subtopology euclidean (IMAGE phi U)) phi`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_CMB_LOCAL_LINK_SPHERE THEN
  MAP_EVERY EXISTS_TAC [`{x | x IN UNIONS c /\ (t:real^N->A) x IN U}`;
                        `g:real^N->real^3`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    SET_TAC[];
    ASM_REWRITE_TAC[IN_ELIM_THM];
    MATCH_MP_TAC MOI_CMB_OPEN_IN_BALL THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CMB_TRIANG_OPEN THEN
      MAP_EVERY EXISTS_TAC [`top:A topology`; `s:A->bool`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_CMB_TRIANG_INJ THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `s:A->bool`; `phi:A->real^3`] THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `e:real` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_CMB_TRIANG_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`top:A topology`; `s:A->bool`; `phi:A->real^3`] THEN
    ASM_REWRITE_TAC[]]);;

