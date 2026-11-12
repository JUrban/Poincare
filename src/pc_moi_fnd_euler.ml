(* ========================================================================= *)
(* pc_moi_fnd_euler: the Euler characteristic complex_euler of finite       *)
(* complexes (Moise Sec 21, pp.147-150): additivity under unions, PL         *)
(* invariance, the values on the standard pieces, and the holed disk with   *)
(* one hole as an annulus.  Route: Lawrence's valuation (100/polyhedron.ml, *)
(* the Euler characteristic of unions of cells of a hyperplane arrangement, *)
(* independent of the arrangement) instead of Moise's open cell-complexes;  *)
(* it gives subdivision invariance in every dimension at once.               *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_pl2.ml";;

prioritize_real();;
type_invention_error := true;;

(* 100/polyhedron.ml invents type variables while loading, so it is loaded  *)
(* with type_invention_error off, as pc_moi_pl2 does for 100/pick.ml.        *)

type_invention_error := false;;
needs "100/polyhedron.ml";;
type_invention_error := true;;
prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* 1. complex_euler as a sum over the nonempty members; additivity.          *)
(* ------------------------------------------------------------------------- *)

let MOI_FEU_COMPLEX_EULER_SUM = prove
 (`!c:(real^N->bool)->bool.
        FINITE c
        ==> complex_euler c =
            sum {s | s IN c /\ ~(s = {})}
                (\s. (-- &1) pow (num_of_int(aff_dim s)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[complex_euler] THEN
  MP_TAC(ISPECL [`\s:real^N->bool. aff_dim s`;
                 `\s:real^N->bool. (-- &1) pow (num_of_int(aff_dim s))`;
                 `{s:real^N->bool | s IN c /\ ~(s = {})}`;
                 `IMAGE int_of_num (0..dimindex(:N))`]
                SUM_GROUP) THEN
  SIMP_TAC[SUM_IMAGE; INT_OF_NUM_EQ; o_DEF; NUM_OF_INT_OF_NUM] THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_IMAGE; IN_NUMSEG; LE_0] THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; INT_EXISTS_POS] THEN
    EXISTS_TAC `aff_dim(s:real^N->bool)` THEN
    ASM_REWRITE_TAC[AFF_DIM_LE_UNIV; AFF_DIM_POS_LE];
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[IN_ELIM_THM; GSYM CONJ_ASSOC] THEN
    MATCH_MP_TAC SUM_EQ_NUMSEG THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    REWRITE_TAC[] THEN
    SUBGOAL_THEN `{s:real^N->bool | s IN c /\ ~(s = {}) /\ aff_dim s = &k} =
                  {s | s IN c /\ aff_dim s = &k}` SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
      X_GEN_TAC `s:real^N->bool` THEN
      ASM_CASES_TAC `s:real^N->bool = {}` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT; NUM_OF_INT_OF_NUM] THEN
    REWRITE_TAC[REAL_MUL_AC]]);;

let MOI_FEU_COMPLEX_EULER_SUM_ALT = prove
 (`!c:(real^N->bool)->bool.
        FINITE c
        ==> complex_euler c =
            sum c (\s. if s = {} then &0
                       else (-- &1) pow (num_of_int(aff_dim s)))`,
  SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM; SUM_RESTRICT_SET] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUM_EQ THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
  COND_CASES_TAC THEN ASM_REWRITE_TAC[]);;

let COMPLEX_EULER_UNION = prove
 (`!(c:(real^N->bool)->bool) d.
     FINITE c /\ FINITE d
     ==> complex_euler (c UNION d) =
         complex_euler c + complex_euler d - complex_euler (c INTER d)`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM_ALT; FINITE_UNION; FINITE_INTER] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `d:(real^N->bool)->bool`;
                 `\s:real^N->bool. if s = {} then &0
                                   else (-- &1) pow (num_of_int(aff_dim s))`]
                SUM_INCL_EXCL) THEN
  ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* 2. The valuation.  moi_feu_euler s v: s is a union of cells of a finite  *)
(* hyperplane arrangement with Euler characteristic v (Lawrence; by          *)
(* EULER_CHARACTERSTIC_INVARIANT the value does not depend on the            *)
(* arrangement).  Calculus: uniqueness, disjoint unions, differences.        *)
(* ------------------------------------------------------------------------- *)

let moi_feu_euler = new_definition
 `moi_feu_euler (s:real^N->bool) (v:real) <=>
    ?A. FINITE A /\ hyperplane_cellcomplex A s /\
        euler_characteristic A s = v`;;

let MOI_FEU_EULER_INVARIANT = prove
 (`!A B (s:real^N->bool).
        FINITE A /\ FINITE B /\
        hyperplane_cellcomplex A s /\ hyperplane_cellcomplex B s
        ==> euler_characteristic A s = euler_characteristic B s`,
  MESON_TAC[EULER_CHARACTERSTIC_INVARIANT]);;

let MOI_FEU_EULER_UNIQUE = prove
 (`!(s:real^N->bool) v w. moi_feu_euler s v /\ moi_feu_euler s w ==> v = w`,
  REWRITE_TAC[moi_feu_euler] THEN MESON_TAC[MOI_FEU_EULER_INVARIANT]);;

let MOI_FEU_EULER_EMPTY = prove
 (`moi_feu_euler ({}:real^N->bool) (&0)`,
  REWRITE_TAC[moi_feu_euler] THEN EXISTS_TAC `{}:(real^N#real)->bool` THEN
  REWRITE_TAC[FINITE_EMPTY; HYPERPLANE_CELLCOMPLEX_EMPTY;
              EULER_CHARACTERISTIC_EMPTY]);;

let MOI_FEU_EULER_UNION_DISJOINT = prove
 (`!(s:real^N->bool) t v w.
        moi_feu_euler s v /\ moi_feu_euler t w /\ DISJOINT s t
        ==> moi_feu_euler (s UNION t) (v + w)`,
  REWRITE_TAC[moi_feu_euler] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `A:(real^N#real)->bool` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `B:(real^N#real)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `A UNION B:(real^N#real)->bool` THEN
  SUBGOAL_THEN `hyperplane_cellcomplex (A UNION B) (s:real^N->bool) /\
                hyperplane_cellcomplex (A UNION B) (t:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
    ASM_MESON_TAC[SUBSET_UNION];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_UNION; HYPERPLANE_CELLCOMPLEX_UNION;
               EULER_CHARACTERISTIC_CELLCOMPLEX_UNION] THEN
  BINOP_TAC THEN ASM_MESON_TAC[MOI_FEU_EULER_INVARIANT; FINITE_UNION]);;

let MOI_FEU_EULER_DIFF = prove
 (`!(s:real^N->bool) t v w.
        moi_feu_euler s v /\ moi_feu_euler t w /\ t SUBSET s
        ==> moi_feu_euler (s DIFF t) (v - w)`,
  REWRITE_TAC[moi_feu_euler] THEN REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `A:(real^N#real)->bool` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2
     (X_CHOOSE_THEN `B:(real^N#real)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  EXISTS_TAC `A UNION B:(real^N#real)->bool` THEN
  SUBGOAL_THEN `hyperplane_cellcomplex (A UNION B) (s:real^N->bool) /\
                hyperplane_cellcomplex (A UNION B) (t:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HYPERPLANE_CELLCOMPLEX_MONO THEN
    ASM_MESON_TAC[SUBSET_UNION];
    ALL_TAC] THEN
  ASM_SIMP_TAC[FINITE_UNION; HYPERPLANE_CELLCOMPLEX_DIFF] THEN
  MP_TAC(ISPECL [`A UNION B:(real^N#real)->bool`; `s DIFF t:real^N->bool`;
                 `t:real^N->bool`] EULER_CHARACTERISTIC_CELLCOMPLEX_UNION) THEN
  ASM_SIMP_TAC[FINITE_UNION; HYPERPLANE_CELLCOMPLEX_DIFF] THEN
  ANTS_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s DIFF t) UNION t:real^N->bool = s` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `euler_characteristic (A UNION B) (s:real^N->bool) = v /\
                euler_characteristic (A UNION B) (t:real^N->bool) = w`
   (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[MOI_FEU_EULER_INVARIANT; FINITE_UNION]; REAL_ARITH_TAC]);;

let MOI_FEU_EULER_UNION = prove
 (`!(s:real^N->bool) t u v w.
        moi_feu_euler s u /\ moi_feu_euler t v /\
        moi_feu_euler (s INTER t) w
        ==> moi_feu_euler (s UNION t) (u + v - w)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s UNION t:real^N->bool = (s DIFF (s INTER t)) UNION t`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `u + v - w:real = (u - w) + v` SUBST1_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FEU_EULER_UNION_DISJOINT THEN
  ASM_SIMP_TAC[MOI_FEU_EULER_DIFF; INTER_SUBSET] THEN SET_TAC[]);;

let MOI_FEU_EULER_UNIONS = prove
 (`!(ix:A->bool) (x:A->real^N->bool) v.
        FINITE ix /\
        (!i j. i IN ix /\ j IN ix /\ ~(i = j) ==> DISJOINT (x i) (x j)) /\
        (!i. i IN ix ==> moi_feu_euler (x i) (v i))
        ==> moi_feu_euler (UNIONS (IMAGE x ix)) (sum ix v)`,
  GEN_TAC THEN GEN_TAC THEN GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN
  SPEC_TAC(`ix:A->bool`,`ix:A->bool`) THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[IMAGE_CLAUSES; UNIONS_0; SUM_CLAUSES; MOI_FEU_EULER_EMPTY];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:A`; `ix:A->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  DISCH_THEN(LABEL_TAC "dis") THEN DISCH_THEN(LABEL_TAC "val") THEN
  SIMP_TAC[IMAGE_CLAUSES; UNIONS_INSERT; SUM_CLAUSES;
           ASSUME `FINITE(ix:A->bool)`; ASSUME `~((i:A) IN ix)`] THEN
  MATCH_MP_TAC MOI_FEU_EULER_UNION_DISJOINT THEN REPEAT CONJ_TAC THENL
   [USE_THEN "val" MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT];
    REMOVE_THEN "ih" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    CONJ_TAC THEN REPEAT STRIP_TAC THENL
     [USE_THEN "dis" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
      ASM_REWRITE_TAC[IN_INSERT];
      USE_THEN "val" MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT]];
    REWRITE_TAC[DISJOINT; INTER_UNIONS; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `j:A` THEN DISCH_TAC THEN
    REWRITE_TAC[GSYM DISJOINT] THEN
    USE_THEN "dis" (MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. Relative interiors of polyhedra are single cells; values of open      *)
(* cells, of polyhedra (through their faces) and of simplicial complexes.   *)
(* ------------------------------------------------------------------------- *)

let MOI_FEU_SGN_NEG = prove
 (`!x y. x < &0 ==> (real_sgn x = real_sgn y <=> y < &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_sgn] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_FEU_SGN_ZERO = prove
 (`!x y. x = &0 ==> (real_sgn x = real_sgn y <=> y = &0)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[real_sgn] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_FEU_RELATIVE_INTERIOR_HYPERPLANE_CELL = prove
 (`!s:real^N->bool.
        polyhedron s /\ ~(s = {})
        ==> ?A. FINITE A /\ hyperplane_cell A (relative_interior s)`,
  REPEAT STRIP_TAC THEN FIRST_ASSUM
   (MP_TAC o GEN_REWRITE_RULE I [POLYHEDRON_INTER_AFFINE_MINIMAL]) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`f:(real^N->bool)->bool`; `a:(real^N->bool)->real^N`;
    `b:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `f:(real^N->bool)->bool`;
                 `a:(real^N->bool)->real^N`; `b:(real^N->bool)->real`]
        RELATIVE_INTERIOR_POLYHEDRON_EXPLICIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPEC `s:real^N->bool`
    AFFINE_HULL_FINITE_INTERSECTION_HYPERPLANES) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  SIMP_TAC[LEFT_IMP_EXISTS_THM; RIGHT_AND_EXISTS_THM; LEFT_AND_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC
   [`g:(real^N->bool)->bool`; `c:(real^N->bool)->real^N`;
    `d:(real^N->bool)->real`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^N. x IN s <=>
               (!h. h IN g ==> (c:(real^N->bool)->real^N) h dot x = d h) /\
               (!h. h IN f ==> (a:(real^N->bool)->real^N) h dot x <= b h)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN
    UNDISCH_TAC `s:real^N->bool = affine hull s INTER INTERS f` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    REWRITE_TAC[IN_INTER] THEN
    UNDISCH_TAC `affine hull s:real^N->bool = INTERS g` THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[IN_INTERS] THEN
    BINOP_TAC THEN EQ_TAC THEN REPEAT STRIP_TAC THENL
     [UNDISCH_TAC `!h:real^N->bool. h IN g ==> x IN h` THEN
      DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `h = {x:real^N | (c:(real^N->bool)->real^N) h dot x = d h}`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
       [ASM_MESON_TAC[]; REWRITE_TAC[IN_ELIM_THM]];
      SUBGOAL_THEN `t = {x:real^N | (c:(real^N->bool)->real^N) t dot x = d t}`
       SUBST1_TAC THENL [ASM_MESON_TAC[]; ASM_SIMP_TAC[IN_ELIM_THM]];
      UNDISCH_TAC `!t:real^N->bool. t IN f ==> x IN t` THEN
      DISCH_THEN(MP_TAC o SPEC `h:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `h = {x:real^N | (a:(real^N->bool)->real^N) h dot x <= b h}`
       (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
       [ASM_MESON_TAC[]; REWRITE_TAC[IN_ELIM_THM]];
      SUBGOAL_THEN `t = {x:real^N | (a:(real^N->bool)->real^N) t dot x <= b t}`
       SUBST1_TAC THENL [ASM_MESON_TAC[]; ASM_SIMP_TAC[IN_ELIM_THM]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN relative_interior s <=>
               (!h. h IN g ==> (c:(real^N->bool)->real^N) h dot x = d h) /\
               (!h. h IN f ==> (a:(real^N->bool)->real^N) h dot x < b h)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN
    UNDISCH_TAC `relative_interior s =
                 {x:real^N | x IN s /\
                    !h. h IN f
                        ==> (a:(real^N->bool)->real^N) h dot x < b h}` THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[REAL_LT_IMP_LE];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (\h:real^N->bool. ((a:(real^N->bool)->real^N) h,
                                       (b:(real^N->bool)->real) h)) f UNION
              IMAGE (\h:real^N->bool. ((c:(real^N->bool)->real^N) h,
                                       (d:(real^N->bool)->real) h)) g` THEN
  ASM_SIMP_TAC[FINITE_UNION; FINITE_IMAGE] THEN
  SUBGOAL_THEN `~(relative_interior s:real^N->bool = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; POLYHEDRON_IMP_CONVEX];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY]] THEN
  DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN
  REWRITE_TAC[HYPERPLANE_CELL] THEN EXISTS_TAC `z:real^N` THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
  REWRITE_TAC[IN_ELIM_THM; hyperplane_equiv; FORALL_IN_UNION;
              FORALL_IN_IMAGE; hyperplane_side] THEN
  UNDISCH_TAC `(z:real^N) IN relative_interior s` THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(!h. h IN f
         ==> (real_sgn ((a:(real^N->bool)->real^N) h dot z - b h) =
              real_sgn (a h dot y - b h) <=> a h dot y < b h)) /\
    (!h. h IN g
         ==> (real_sgn ((c:(real^N->bool)->real^N) h dot z - d h) =
              real_sgn (c h dot y - d h) <=> c h dot y = d h))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN X_GEN_TAC `h:real^N->bool` THEN DISCH_TAC THENL
     [W(MP_TAC o PART_MATCH (lhand o rand) MOI_FEU_SGN_NEG o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_SUB_LT; REAL_ARITH `x - y < &0 <=> x < y`] THEN
        ASM_SIMP_TAC[];
        DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC];
      W(MP_TAC o PART_MATCH (lhand o rand) MOI_FEU_SGN_ZERO o lhand o snd) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_SUB_0] THEN ASM_SIMP_TAC[];
        DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC]];
    ALL_TAC] THEN
  ASM_SIMP_TAC[] THEN MESON_TAC[REAL_LT_IMP_LE]);;

let MOI_FEU_EULER_RELATIVE_INTERIOR = prove
 (`!s:real^N->bool.
        polyhedron s /\ ~(s = {})
        ==> moi_feu_euler (relative_interior s)
                          ((-- &1) pow (num_of_int(aff_dim s)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^N->bool` MOI_FEU_RELATIVE_INTERIOR_HYPERPLANE_CELL) THEN
  ASM_REWRITE_TAC[moi_feu_euler] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `A:(real^N#real)->bool` THEN
  STRIP_TAC THEN
  ASM_SIMP_TAC[HYPERPLANE_CELL_CELLCOMPLEX; EULER_CHARACTERISTIC_CELL] THEN
  ASM_SIMP_TAC[AFF_DIM_RELATIVE_INTERIOR; POLYHEDRON_IMP_CONVEX]);;

(* ------------------------------------------------------------------------- *)
(* 4. Values of polyhedra (sum over the nonempty faces), of finite          *)
(* simplicial complexes (complex_euler), and invariance of complex_euler   *)
(* under change of triangulation of the same polyhedron.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_FEU_EULER_POLYHEDRON_FACES = prove
 (`!p:real^N->bool.
        polyhedron p
        ==> moi_feu_euler p
              (sum {f | f face_of p /\ ~(f = {})}
                   (\f. (-- &1) pow (num_of_int(aff_dim f))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `p = UNIONS (IMAGE relative_interior
                      {f:real^N->bool | f face_of p /\ ~(f = {})})`
   (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THENL
   [GEN_REWRITE_TAC LAND_CONV
     [GSYM(MATCH_MP CONVEX_FACIAL_PARTITION
       (MATCH_MP POLYHEDRON_IMP_CONVEX
         (ASSUME `polyhedron(p:real^N->bool)`)))] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FEU_EULER_UNIONS THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{f:real^N->bool | f face_of p}` THEN
    ASM_SIMP_TAC[FINITE_POLYHEDRON_FACES] THEN SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM; DISJOINT] THEN
    MAP_EVERY X_GEN_TAC [`f1:real^N->bool`; `f2:real^N->bool`] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC CELL_COMPLEX_DISJOINT_RELATIVE_INTERIORS THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACE_OF_FACE; FACE_OF_INTER; INTER_SUBSET];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FEU_EULER_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[FACE_OF_POLYHEDRON_POLYHEDRON]]);;

let MOI_FEU_EULER_SIMPLICIAL_COMPLEX = prove
 (`!c:(real^N->bool)->bool.
        simplicial_complex c ==> moi_feu_euler (UNIONS c) (complex_euler c)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o GEN_REWRITE_RULE I
   [simplicial_complex]) THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM] THEN
  SUBGOAL_THEN
   `UNIONS c = UNIONS (IMAGE relative_interior
                             {s:real^N->bool | s IN c /\ ~(s = {})})`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
        IN_RELATIVE_INTERIOR_OF_FACE) THEN
      ANTS_TAC THENL
       [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_complex];
        ASM_MESON_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY]];
      REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
      MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FEU_EULER_UNIONS THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT];
    REWRITE_TAC[IN_ELIM_THM; DISJOINT] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC SIMPLICIAL_COMPLEX_DISJOINT_RELATIVE_INTERIORS THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FEU_EULER_RELATIVE_INTERIOR THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYHEDRON]]);;

let MOI_FEU_COMPLEX_EULER_SAME_POLYHEDRON = prove
 (`!c d:(real^N->bool)->bool.
        simplicial_complex c /\ simplicial_complex d /\ UNIONS c = UNIONS d
        ==> complex_euler c = complex_euler d`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FEU_EULER_UNIQUE THEN
  EXISTS_TAC `UNIONS c:real^N->bool` THEN
  ASM_SIMP_TAC[MOI_FEU_EULER_SIMPLICIAL_COMPLEX] THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  ASM_SIMP_TAC[MOI_FEU_EULER_SIMPLICIAL_COMPLEX]);;

let MOI_FEU_COMPLEX_EULER_EQ_EULER = prove
 (`!c:(real^N->bool)->bool v.
        simplicial_complex c /\ moi_feu_euler (UNIONS c) v
        ==> complex_euler c = v`,
  MESON_TAC[MOI_FEU_EULER_SIMPLICIAL_COMPLEX; MOI_FEU_EULER_UNIQUE]);;

(* Faces of a simplex and of a full-dimensional polytope.                    *)

let MOI_FEU_SUM_POWERSET_SIGN = prove
 (`!v:A->bool.
        FINITE v
        ==> sum {w | w SUBSET v} (\w. (-- &1) pow (CARD w)) =
            if v = {} then &1 else &0`,
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[POWERSET_CLAUSES; SUM_SING; CARD_CLAUSES; real_pow];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`a:A`; `v:A->bool`] THEN STRIP_TAC THEN
  REWRITE_TAC[NOT_INSERT_EMPTY; POWERSET_CLAUSES] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_UNION o lhand o snd) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_POWERSET; FINITE_IMAGE] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; IN_IMAGE;
                NOT_IN_EMPTY] THEN
    ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o rand o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  SUBGOAL_THEN
   `sum {w | w SUBSET v} (\w. (-- &1) pow CARD ((a:A) INSERT w)) =
    --(sum {w | w SUBSET v} (\w. (-- &1) pow CARD w))`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM SUM_NEG] THEN MATCH_MP_TAC SUM_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `w:A->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `FINITE(w:A->bool) /\ ~((a:A) IN w)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FINITE_SUBSET; SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; real_pow] THEN REAL_ARITH_TAC;
    REWRITE_TAC[REAL_ADD_RINV]]);;

let MOI_FEU_FACES_SUM_SIMPLEX = prove
 (`!n k:real^N->bool.
        n simplex k /\ ~(k = {})
        ==> sum {f | f face_of k /\ ~(f = {})}
                (\f. (-- &1) pow (num_of_int(aff_dim f))) = &1`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP SIMPLEX_EXTREME_POINTS) THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP FACES_OF_SIMPLEX) THEN
  ABBREV_TAC `v = {x:real^N | x extreme_point_of k}` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `{f:real^N->bool | f face_of k /\ ~(f = {})} =
    IMAGE (\w. convex hull w) ({w | w SUBSET v} DELETE {})`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `!f:real^N->bool. f face_of k <=>
                                   ?c. c SUBSET v /\ f = convex hull c`
    ASSUME_TAC THENL
     [UNDISCH_TAC `{f:real^N->bool | f face_of k} =
                   {convex hull c | c SUBSET v}` THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [EXTENSION] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `f:real^N->bool` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; IN_DELETE] THEN
    MESON_TAC[CONVEX_HULL_EQ_EMPTY];
    ALL_TAC] THEN
  W(MP_TAC o PART_MATCH (lhand o rand) SUM_IMAGE o lhand o snd) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN
    MAP_EVERY X_GEN_TAC [`w1:real^N->bool`; `w2:real^N->bool`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPEC `w1:real^N->bool`
      EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    MP_TAC(ISPEC `w2:real^N->bool`
      EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET];
    DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[o_DEF] THEN
  SUBGOAL_THEN
   `sum ({w | w SUBSET v} DELETE {})
        (\w. (-- &1) pow num_of_int (aff_dim (convex hull w:real^N->bool))) =
    sum ({w | w SUBSET v} DELETE {}) (\w. --((-- &1) pow CARD w))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN REWRITE_TAC[IN_ELIM_THM; IN_DELETE] THEN
    X_GEN_TAC `w:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~affine_dependent(w:real^N->bool) /\ FINITE w`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET; FINITE_SUBSET]; ALL_TAC] THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    SUBGOAL_THEN `?m. CARD(w:real^N->bool) = SUC m` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[CARD_EQ_0; num_CASES]; ALL_TAC] THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_SUC; INT_ARITH `(x + &1) - &1:int = x`;
                    NUM_OF_INT_OF_NUM; real_pow] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SUM_NEG] THEN
  SUBGOAL_THEN `FINITE {w:real^N->bool | w SUBSET v} /\
                {} IN {w:real^N->bool | w SUBSET v}`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[FINITE_POWERSET] THEN REWRITE_TAC[IN_ELIM_THM; EMPTY_SUBSET];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_DELETE; MOI_FEU_SUM_POWERSET_SIGN] THEN
  SUBGOAL_THEN `~(v:real^N->bool = {})` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[CONVEX_HULL_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[CARD_CLAUSES; real_pow] THEN REAL_ARITH_TAC);;

let MOI_FEU_FACES_SUM_FULL = prove
 (`!p:real^N->bool.
        polytope p /\ aff_dim p = &(dimindex(:N))
        ==> sum {f | f face_of p /\ ~(f = {})}
                (\f. (-- &1) pow (num_of_int(aff_dim f))) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `{f:real^N->bool | f face_of p}` MOI_FEU_COMPLEX_EULER_SUM) THEN
  ASM_SIMP_TAC[FINITE_POLYTOPE_FACES; IN_ELIM_THM] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[complex_euler; IN_ELIM_THM] THEN
  MATCH_MP_TAC EULER_POINCARE_FULL THEN ASM_REWRITE_TAC[]);;

let MOI_FEU_EULER_SIMPLEX = prove
 (`!n k:real^N->bool. n simplex k /\ ~(k = {}) ==> moi_feu_euler k (&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_FEU_EULER_POLYHEDRON_FACES) THEN
  ASM_MESON_TAC[SIMPLEX_IMP_POLYHEDRON; MOI_FEU_FACES_SUM_SIMPLEX]);;

let MOI_FEU_EULER_POLYTOPE_FULL = prove
 (`!p:real^N->bool.
        polytope p /\ aff_dim p = &(dimindex(:N)) ==> moi_feu_euler p (&1)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `p:real^N->bool` MOI_FEU_EULER_POLYHEDRON_FACES) THEN
  ASM_MESON_TAC[POLYTOPE_IMP_POLYHEDRON; MOI_FEU_FACES_SUM_FULL]);;

(* ------------------------------------------------------------------------- *)
(* 5. PL invariance (Moise 21.4-21.5, 21.9 in the form of common            *)
(* subdivisions; here in every dimension, without the Hauptvermutung).      *)
(* A PL homeomorphism is affine on the simplices of a subdivision t of the  *)
(* domain (SIMPLICIAL_SUBDIVISION_PL_MAP); the images of the open simplices *)
(* of t are open cells partitioning the target, of the same dimensions.     *)
(* ------------------------------------------------------------------------- *)

(* The same as MOI_PTR_AFF_DIM_AFFINE_IMAGE_LE (pc_moi_ptri.ml, not loaded). *)

let MOI_FEU_AFF_DIM_AFFINE_IMAGE_LE = prove
 (`!(l:real^M->real^N) y s.
     linear l ==> aff_dim (IMAGE (\z. l z + y) s) <= aff_dim s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\z. (l:real^M->real^N) z + y) s =
                IMAGE (\x. y + x) (IMAGE l s)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    REWRITE_TAC[VECTOR_ADD_SYM];
    REWRITE_TAC[AFF_DIM_TRANSLATION_EQ] THEN
    ASM_SIMP_TAC[AFF_DIM_LINEAR_IMAGE_LE]]);;

let MOI_FEU_AFF_DIM_AFFINE_INJECTIVE = prove
 (`!(l:real^M->real^N) y k.
        linear l /\ convex k /\
        (!x x'. x IN k /\ x' IN k /\ l x + y = l x' + y ==> x = x')
        ==> aff_dim (IMAGE (\x. l x + y) k) = aff_dim k`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_LE_ANTISYM] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[MOI_FEU_AFF_DIM_AFFINE_IMAGE_LE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `y:real^N`; `k:real^M->bool`]
    MOI_PLM_AFFINE_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M` (X_CHOOSE_THEN `y':real^M`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `k = IMAGE (\w. (l':real^N->real^M) w + y')
              (IMAGE (\x. (l:real^M->real^N) x + y) k)`
   (fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^M. x IN k ==> f x = x) ==> k = IMAGE f k`) THEN
    ASM_SIMP_TAC[];
    ASM_SIMP_TAC[MOI_FEU_AFF_DIM_AFFINE_IMAGE_LE]]);;

let MOI_FEU_RELATIVE_INTERIOR_AFFINE_IMAGE = prove
 (`!(l:real^M->real^N) y k.
        linear l /\ convex k
        ==> relative_interior (IMAGE (\x. l x + y) k) =
            IMAGE (\x. l x + y) (relative_interior k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!s. IMAGE (\x. (l:real^M->real^N) x + y) s =
                    IMAGE (\x. y + x) (IMAGE l s)`
   (fun th -> REWRITE_TAC[th]) THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN REWRITE_TAC[VECTOR_ADD_SYM];
    ALL_TAC] THEN
  REWRITE_TAC[RELATIVE_INTERIOR_TRANSLATION] THEN AP_TERM_TAC THEN
  MATCH_MP_TAC RELATIVE_INTERIOR_LINEAR_IMAGE_CONVEX THEN ASM_REWRITE_TAC[]);;

let MOI_FEU_UNIONS_RELATIVE_INTERIORS = prove
 (`!c:(real^N->bool)->bool.
        simplicial_complex c
        ==> UNIONS c =
            UNIONS (IMAGE relative_interior {s | s IN c /\ ~(s = {})})`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`]
      IN_RELATIVE_INTERIOR_OF_FACE) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      ASM_MESON_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY]];
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]]);;

let MOI_FEU_COMPLEX_EULER_PL_HOMEOMORPHIC = prove
 (`!(c:(real^M->bool)->bool) (d:(real^N->bool)->bool) f g.
     simplicial_complex c /\ simplicial_complex d /\
     pl_homeomorphism (UNIONS c,UNIONS d) (f,g)
     ==> complex_euler c = complex_euler d`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^M->bool)->bool`; `f:real^M->real^N`]
    SIMPLICIAL_SUBDIVISION_PL_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^M->bool)->bool`
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 (K ALL_TAC) MP_TAC)))) THEN
  GEN_REWRITE_TAC (LAND_CONV o TOP_DEPTH_CONV)
   [RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
  REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`L:(real^M->bool)->real^M->real^N`;
                       `Y:(real^M->bool)->real^N`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `complex_euler (c:(real^M->bool)->bool) =
                complex_euler (t:(real^M->bool)->bool)`
  SUBST1_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_FEU_COMPLEX_EULER_SAME_POLYHEDRON THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (t:(real^M->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x x'. x IN UNIONS c /\ x' IN UNIONS c /\
           (f:real^M->real^N) x = f x' ==> x = x'`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!s. s IN t
        ==> s SUBSET UNIONS c /\ convex s /\ polytope s /\
            IMAGE (f:real^M->real^N) (relative_interior s) =
            relative_interior
             (IMAGE (\x. (L:(real^M->bool)->real^M->real^N) s x +
                         (Y:(real^M->bool)->real^N) s) s) /\
            aff_dim (IMAGE (\x. L s x + Y s) s) = aff_dim s`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^M->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `s SUBSET UNIONS (c:(real^M->bool)->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS t = UNIONS (c:(real^M->bool)->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `polytope (s:real^M->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
    SUBGOAL_THEN `convex (s:real^M->bool)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX]; ALL_TAC] THEN
    SUBGOAL_THEN `linear ((L:(real^M->bool)->real^M->real^N) s) /\
                  !x. x IN s ==> (f:real^M->real^N) x = L s x + Y s`
    STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`(L:(real^M->bool)->real^M->real^N) s`;
                     `(Y:(real^M->bool)->real^N) s`; `s:real^M->bool`]
        MOI_FEU_RELATIVE_INTERIOR_AFFINE_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC(SET_RULE
       `(!x:real^M. x IN u ==> (f:real^M->real^N) x = g x)
        ==> IMAGE f u = IMAGE g u`) THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      MP_TAC(ISPECL [`(L:(real^M->bool)->real^M->real^N) s`;
                     `(Y:(real^M->bool)->real^N) s`; `s:real^M->bool`]
        MOI_FEU_AFF_DIM_AFFINE_INJECTIVE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
      MAP_EVERY X_GEN_TAC [`x:real^M`; `x':real^M`] THEN STRIP_TAC THEN
      UNDISCH_TAC
       `!x x'. x IN UNIONS c /\ x' IN UNIONS c /\
               (f:real^M->real^N) x = f x' ==> x = x'` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS d =
    UNIONS (IMAGE (\s. IMAGE (f:real^M->real^N) (relative_interior s))
                  {s:real^M->bool | s IN t /\ ~(s = {})})`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `UNIONS d = IMAGE (f:real^M->real^N) (UNIONS c)`
     SUBST1_TAC THENL [ASM_MESON_TAC[homeomorphism]; ALL_TAC] THEN
    UNDISCH_TAC `UNIONS t = UNIONS (c:(real^M->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    FIRST_ASSUM(SUBST1_TAC o MATCH_MP MOI_FEU_UNIONS_RELATIVE_INTERIORS) THEN
    REWRITE_TAC[IMAGE_UNIONS; GSYM IMAGE_o; o_DEF];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_SYM THEN MATCH_MP_TAC MOI_FEU_COMPLEX_EULER_EQ_EULER THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM] THEN
  MATCH_MP_TAC MOI_FEU_EULER_UNIONS THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[FINITE_RESTRICT];
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`i:real^M->bool`; `j:real^M->bool`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^M->bool)->bool`; `i:real^M->bool`;
                   `j:real^M->bool`]
      SIMPLICIAL_COMPLEX_DISJOINT_RELATIVE_INTERIORS) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `relative_interior i SUBSET UNIONS (c:(real^M->bool)->bool) /\
                  relative_interior j SUBSET UNIONS c`
    MP_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
    UNDISCH_TAC
     `!x x'. x IN UNIONS c /\ x' IN UNIONS c /\
             (f:real^M->real^N) x = f x' ==> x = x'` THEN
    SET_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `s:real^M->bool` THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^M->bool` o
      check (fun th -> can (find_term ((=) `aff_dim:(real^M->bool)->int`))
                           (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC MOI_FEU_EULER_RELATIVE_INTERIOR THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    MATCH_MP_TAC POLYTOPE_IMP_POLYHEDRON THEN
    MP_TAC(ISPECL [`(L:(real^M->bool)->real^M->real^N) s`;
                   `(Y:(real^M->bool)->real^N) s`; `s:real^M->bool`]
      MOI_PLM_POLYTOPE_AFFINE_IMAGE) THEN
    ASM_SIMP_TAC[]]);;

let COMPLEX_EULER_PL_INVARIANT = prove
 (`!(c:(real^M->bool)->bool) (d:(real^N->bool)->bool) f g.
     simplicial_complex c /\ simplicial_complex d /\
     (!s. s IN c ==> aff_dim s <= &2) /\ (!s. s IN d ==> aff_dim s <= &2) /\
     pl_homeomorphism (UNIONS c,UNIONS d) (f,g)
     ==> complex_euler c = complex_euler d`,
  MESON_TAC[MOI_FEU_COMPLEX_EULER_PL_HOMEOMORPHIC]);;

(* ------------------------------------------------------------------------- *)
(* 6. From the valuation to complex_euler: compact unions of cells are      *)
(* PL polyhedra (closures of cells are polyhedra), so a PL homeomorphism    *)
(* from such a set onto a triangulated polyhedron carries its value.        *)
(* Values of simplices, of their relative frontiers and of rectangles.      *)
(* ------------------------------------------------------------------------- *)

let MOI_FEU_CLOSURE_HYPERPLANE_CELL = prove
 (`!A c:real^N->bool.
        FINITE A /\ hyperplane_cell A c ==> polyhedron (closure c)`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REWRITE_TAC[HYPERPLANE_CELL_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[CLOSURE_UNIV; POLYHEDRON_UNIV];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_PAIR_THM] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real`; `A:(real^N#real)->bool`] THEN
  STRIP_TAC THEN X_GEN_TAC `c:real^N->bool` THEN
  ONCE_REWRITE_TAC[SET_RULE
   `((a:real^N),(b:real)) INSERT s = {(a,b)} UNION s`] THEN
  REWRITE_TAC[HYPERPLANE_CELL_UNION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `c1:real^N->bool` (X_CHOOSE_THEN `c2:real^N->bool`
     STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `relative_interior c1 = c1:real^N->bool /\
                relative_interior c2 = c2:real^N->bool /\
                convex (c1:real^N->bool) /\ convex (c2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    ASM_MESON_TAC[HYPERPLANE_CELL_RELATIVE_INTERIOR; HYPERPLANE_CELL_CONVEX;
                  FINITE_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `closure (c1 INTER c2:real^N->bool) = closure c1 INTER closure c2`
  SUBST1_TAC THENL
   [MATCH_MP_TAC CLOSURE_INTER_CONVEX THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC POLYHEDRON_INTER THEN CONJ_TAC THENL
     [UNDISCH_TAC `hyperplane_cell {((a:real^N),(b:real))} c1` THEN
      REWRITE_TAC[HYPERPLANE_CELL_SING] THEN COND_CASES_TAC THEN
      STRIP_TAC THEN
      ASM_SIMP_TAC[CLOSURE_UNIV; POLYHEDRON_UNIV; CLOSURE_HYPERPLANE;
                   CLOSURE_HALFSPACE_LT; CLOSURE_HALFSPACE_GT;
                   POLYHEDRON_HYPERPLANE; POLYHEDRON_HALFSPACE_LE;
                   POLYHEDRON_HALFSPACE_GE];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let MOI_FEU_CELLCOMPLEX_COMPACT_PL_POLYHEDRON = prove
 (`!A s:real^N->bool.
        FINITE A /\ hyperplane_cellcomplex A s /\ compact s
        ==> pl_polyhedron s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[hyperplane_cellcomplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
   (X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  REWRITE_TAC[pl_polyhedron] THEN
  EXISTS_TAC `IMAGE closure (t:(real^N->bool)->bool)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{c:real^N->bool | hyperplane_cell A c}` THEN
    ASM_SIMP_TAC[FINITE_HYPERPLANE_CELLS] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN X_GEN_TAC `c:real^N->bool` THEN
    DISCH_TAC THEN REWRITE_TAC[POLYTOPE_EQ_BOUNDED_POLYHEDRON] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FEU_CLOSURE_HYPERPLANE_CELL THEN
      EXISTS_TAC `A:(real^N#real)->bool` THEN ASM_MESON_TAC[];
      MATCH_MP_TAC BOUNDED_CLOSURE THEN MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
      ASM SET_TAC[]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `s = UNIONS t /\ (!c:real^N->bool. c IN t ==> c SUBSET f c)
        ==> s SUBSET UNIONS (IMAGE f t)`) THEN
      ASM_REWRITE_TAC[CLOSURE_SUBSET];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN
      X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      ASM SET_TAC[]]]);;

let MOI_FEU_EULER_COMPACT_PL_POLYHEDRON = prove
 (`!(s:real^N->bool) v.
        moi_feu_euler s v /\ compact s ==> pl_polyhedron s`,
  REWRITE_TAC[moi_feu_euler] THEN
  MESON_TAC[MOI_FEU_CELLCOMPLEX_COMPACT_PL_POLYHEDRON]);;

let MOI_FEU_PL_HOMEOMORPHIC_EULER = prove
 (`!(s:real^M->bool) v (c:(real^N->bool)->bool) f g.
        moi_feu_euler s v /\ compact s /\ simplicial_complex c /\
        pl_homeomorphism (s,UNIONS c) (f,g)
        ==> complex_euler c = v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `pl_polyhedron (s:real^M->bool)` MP_TAC THENL
   [ASM_MESON_TAC[MOI_FEU_EULER_COMPACT_PL_POLYHEDRON]; ALL_TAC] THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `complex_euler (t:(real^M->bool)->bool)` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_FEU_COMPLEX_EULER_PL_HOMEOMORPHIC THEN
    MAP_EVERY EXISTS_TAC [`f:real^M->real^N`; `g:real^N->real^M`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FEU_COMPLEX_EULER_EQ_EULER THEN ASM_REWRITE_TAC[]]);;

let MOI_FEU_EULER_SIMPLEX_FRONTIER = prove
 (`!n k:real^N->bool.
        &n simplex k
        ==> moi_feu_euler (relative_frontier k) (&1 - (-- &1) pow n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(k:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `&n simplex (k:real^N->bool)` THEN
    ASM_REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_frontier k = k DIFF relative_interior (k:real^N->bool)`
  SUBST1_TAC THENL
   [ASM_MESON_TAC[relative_frontier; CLOSURE_CLOSED; SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FEU_EULER_DIFF THEN
  REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FEU_EULER_SIMPLEX];
    SUBGOAL_THEN `(-- &1) pow n =
                  (-- &1) pow (num_of_int(aff_dim (k:real^N->bool)))`
    SUBST1_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_SIMPLEX; NUM_OF_INT_OF_NUM];
      MATCH_MP_TAC MOI_FEU_EULER_RELATIVE_INTERIOR THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYHEDRON]]]);;

(* Rectangles in the plane: closed ones have value 1, open ones value 1.    *)

let MOI_FEU_EULER_INTERVAL_2 = prove
 (`!a b:real^2.
        a$1 < b$1 /\ a$2 < b$2
        ==> moi_feu_euler (interval[a,b]) (&1) /\
            moi_feu_euler (interval(a,b)) (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(interval(a:real^2,b) = {})` ASSUME_TAC THENL
   [REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(interval[a:real^2,b]) = &(dimindex(:2))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC AFF_DIM_NONEMPTY_INTERIOR THEN
    ASM_REWRITE_TAC[INTERIOR_CLOSED_INTERVAL];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FEU_EULER_POLYTOPE_FULL THEN
    ASM_REWRITE_TAC[POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval(a:real^2,b) = relative_interior(interval[a,b])`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_NONEMPTY_INTERIOR; INTERIOR_CLOSED_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 = (-- &1) pow (num_of_int(aff_dim(interval[a:real^2,b])))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[DIMINDEX_2; NUM_OF_INT_OF_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FEU_EULER_RELATIVE_INTERIOR THEN
  REWRITE_TAC[POLYHEDRON_INTERVAL] THEN
  UNDISCH_TAC `~(interval(a:real^2,b) = {})` THEN
  MP_TAC(ISPECL [`a:real^2`; `b:real^2`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 7. The standard models: annulus, disk with k holes, PL torus.             *)
(* ------------------------------------------------------------------------- *)

let MOI_FEU_FACES_DISJOINT_RELATIVE_INTERIORS = prove
 (`!p f g:real^N->bool.
        f face_of p /\ g face_of p /\ ~(f = g)
        ==> DISJOINT (relative_interior f) (relative_interior g)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT] THEN
  MATCH_MP_TAC CELL_COMPLEX_DISJOINT_RELATIVE_INTERIORS THEN
  ASM_MESON_TAC[FACE_OF_FACE; FACE_OF_INTER; INTER_SUBSET]);;

let MOI_FEU_EULER_FACES_UNIONS = prove
 (`!p:real^N->bool fs.
        polyhedron p /\ (!f. f IN fs ==> f face_of p /\ ~(f = {}))
        ==> moi_feu_euler (UNIONS (IMAGE relative_interior fs))
                          (sum fs (\f. (-- &1) pow (num_of_int(aff_dim f))))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FEU_EULER_UNIONS THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{f:real^N->bool | f face_of p}` THEN
    ASM_SIMP_TAC[FINITE_POLYHEDRON_FACES] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[MOI_FEU_FACES_DISJOINT_RELATIVE_INTERIORS];
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FEU_EULER_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[FACE_OF_POLYHEDRON_POLYHEDRON]]);;

(* The annulus model of pl_annulus (pc_moi_core_stmt.ml).                    *)

let MOI_FEU_EULER_ANNULUS_MODEL = prove
 (`moi_feu_euler (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                  interval(--vector[&1;&1]:real^2,vector[&1;&1])) (&0) /\
   compact (interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
            interval(--vector[&1;&1]:real^2,vector[&1;&1]))`,
  CONJ_TAC THENL
   [SUBGOAL_THEN `&0 = &1 - &1` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FEU_EULER_DIFF THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`--vector[&2;&2]:real^2`; `vector[&2;&2]:real^2`]
        MOI_FEU_EULER_INTERVAL_2) THEN
      REWRITE_TAC[VECTOR_NEG_COMPONENT; VECTOR_2] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
      MP_TAC(ISPECL [`--vector[&1;&1]:real^2`; `vector[&1;&1]:real^2`]
        MOI_FEU_EULER_INTERVAL_2) THEN
      REWRITE_TAC[VECTOR_NEG_COMPONENT; VECTOR_2] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV THEN SIMP_TAC[];
      REWRITE_TAC[SUBSET_INTERVAL; DIMINDEX_2; FORALL_2;
                  VECTOR_NEG_COMPONENT; VECTOR_2] THEN
      CONV_TAC REAL_RAT_REDUCE_CONV];
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
    SIMP_TAC[CLOSED_DIFF; CLOSED_INTERVAL; OPEN_INTERVAL; BOUNDED_DIFF;
             BOUNDED_INTERVAL]]);;

(* The disk with k holes (holed_disk_model, pc_moi_fnd_stmt.ml).             *)

let MOI_FEU_EULER_HOLED_DISK_MODEL = prove
 (`!k. moi_feu_euler (holed_disk_model k) (&1 - &k) /\
       compact (holed_disk_model k)`,
  GEN_TAC THEN REWRITE_TAC[holed_disk_model] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FEU_EULER_DIFF THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`vec 0:real^2`; `vector[&4 * &k + &4; &4]:real^2`]
        MOI_FEU_EULER_INTERVAL_2) THEN
      REWRITE_TAC[VEC_COMPONENT; VECTOR_2] THEN
      ANTS_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_MUL; REAL_OF_NUM_ADD; REAL_OF_NUM_LT] THEN
        ARITH_TAC;
        SIMP_TAC[]];
      SUBGOAL_THEN `&k = sum {i | i < k} (\i:num. &1)` SUBST1_TAC THENL
       [SIMP_TAC[SUM_CONST; FINITE_NUMSEG_LT; CARD_NUMSEG_LT] THEN
        REAL_ARITH_TAC;
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_FEU_EULER_UNIONS THEN
      REWRITE_TAC[FINITE_NUMSEG_LT; IN_ELIM_THM] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
        REWRITE_TAC[DISJOINT; DISJOINT_INTERVAL; DIMINDEX_2] THEN
        EXISTS_TAC `1` THEN REWRITE_TAC[VECTOR_2; ARITH] THEN
        SUBGOAL_THEN `i + 1 <= j \/ j + 1 <= i` MP_TAC THENL
         [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[GSYM REAL_OF_NUM_LE; GSYM REAL_OF_NUM_ADD] THEN
        REAL_ARITH_TAC;
        X_GEN_TAC `i:num` THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`vector[&4 * &i + &2; &1]:real^2`;
                       `vector[&4 * &i + &4; &3]:real^2`]
          MOI_FEU_EULER_INTERVAL_2) THEN
        REWRITE_TAC[VECTOR_2] THEN ANTS_TAC THENL
         [REAL_ARITH_TAC; SIMP_TAC[]]];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      REWRITE_TAC[SUBSET_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
                  VEC_COMPONENT] THEN
      SUBGOAL_THEN `&i + &1 <= &k` MP_TAC THENL
       [REWRITE_TAC[REAL_OF_NUM_ADD; REAL_OF_NUM_LE] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `&0 <= &i` MP_TAC THENL [REWRITE_TAC[REAL_POS]; ALL_TAC] THEN
      REAL_ARITH_TAC];
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN
    SIMP_TAC[BOUNDED_DIFF; BOUNDED_INTERVAL] THEN
    MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_INTERVAL] THEN
    MATCH_MP_TAC OPEN_UNIONS THEN
    REWRITE_TAC[FORALL_IN_IMAGE; OPEN_INTERVAL]]);;

(* The PL torus model (pl_torus_model, pc_moi_core_stmt.ml): the product of *)
(* two square circles.  The open cells relint f PCROSS relint g, f and g    *)
(* proper nonempty faces of the square, partition it; the alternating sum  *)
(* over the faces of the square circle is 0, so the total is 0.             *)

let MOI_FEU_EULER_RELINT_PCROSS = prove
 (`!(f:real^M->bool) (g:real^N->bool).
        polytope f /\ polytope g /\ ~(f = {}) /\ ~(g = {})
        ==> moi_feu_euler (relative_interior f PCROSS relative_interior g)
                          ((-- &1) pow (num_of_int(aff_dim f)) *
                           (-- &1) pow (num_of_int(aff_dim g)))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM RELATIVE_INTERIOR_PCROSS] THEN
  SUBGOAL_THEN
   `(-- &1) pow (num_of_int(aff_dim (f:real^M->bool))) *
    (-- &1) pow (num_of_int(aff_dim (g:real^N->bool))) =
    (-- &1) pow (num_of_int(aff_dim (f PCROSS g)))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[AFF_DIM_PCROSS] THEN
    SUBGOAL_THEN `?m. aff_dim (f:real^M->bool) = &m` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_EXISTS; AFF_DIM_POS_LE]; ALL_TAC] THEN
    SUBGOAL_THEN `?n. aff_dim (g:real^N->bool) = &n` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[INT_OF_NUM_EXISTS; AFF_DIM_POS_LE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[INT_OF_NUM_ADD; NUM_OF_INT_OF_NUM; REAL_POW_ADD];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FEU_EULER_RELATIVE_INTERIOR THEN
  ASM_SIMP_TAC[POLYTOPE_PCROSS; POLYTOPE_IMP_POLYHEDRON; PCROSS_EQ_EMPTY]);;

let MOI_FEU_SQUARE_FRONTIER_FACES = prove
 (`relative_frontier(interval[--vec 1:real^2,vec 1]) =
   UNIONS (IMAGE relative_interior
     {f | f face_of interval[--vec 1:real^2,vec 1] /\
          ~(f = interval[--vec 1,vec 1]) /\ ~(f = {})}) /\
   sum {f | f face_of interval[--vec 1:real^2,vec 1] /\
            ~(f = interval[--vec 1,vec 1]) /\ ~(f = {})}
       (\f. (-- &1) pow (num_of_int(aff_dim f))) = &0`,
  SUBGOAL_THEN
   `relative_frontier(interval[--vec 1:real^2,vec 1]) =
    UNIONS (IMAGE relative_interior
      {f | f face_of interval[--vec 1:real^2,vec 1] /\
           ~(f = interval[--vec 1,vec 1]) /\ ~(f = {})})`
  (fun th -> REWRITE_TAC[th] THEN ASSUME_TAC th) THENL
   [MP_TAC(ISPEC `interval[--vec 1:real^2,vec 1]`
      RELATIVE_FRONTIER_FACIAL_PARTITION_ALT) THEN
    REWRITE_TAC[CONVEX_INTERVAL; CLOSED_INTERVAL] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_IMAGE; IN_ELIM_THM] THEN
    MESON_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MATCH_MP_TAC(INST_TYPE [`:2`,`:N`] MOI_FEU_EULER_UNIQUE) THEN
  EXISTS_TAC `relative_frontier(interval[--vec 1:real^2,vec 1])` THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM SUBST1_TAC THEN
    MATCH_MP_TAC MOI_FEU_EULER_FACES_UNIONS THEN
    EXISTS_TAC `interval[--vec 1:real^2,vec 1]` THEN
    SIMP_TAC[POLYHEDRON_INTERVAL; IN_ELIM_THM];
    POP_ASSUM(K ALL_TAC)] THEN
  SUBGOAL_THEN `~(interior(interval[--vec 1:real^2,vec 1]) = {})`
  ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2;
                FORALL_2; VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[relative_frontier; CLOSURE_INTERVAL;
               RELATIVE_INTERIOR_NONEMPTY_INTERIOR] THEN
  REWRITE_TAC[INTERIOR_CLOSED_INTERVAL] THEN
  MP_TAC(ISPECL [`--vec 1:real^2`; `vec 1:real^2`]
    MOI_FEU_EULER_INTERVAL_2) THEN
  REWRITE_TAC[VECTOR_NEG_COMPONENT; VEC_COMPONENT] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 = &1 - &1` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FEU_EULER_DIFF THEN
  ASM_REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED]);;

let MOI_FEU_EULER_TORUS_MODEL = prove
 (`moi_feu_euler pl_torus_model (&0) /\ compact pl_torus_model`,
  REWRITE_TAC[pl_torus_model] THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC COMPACT_PCROSS THEN
    SIMP_TAC[COMPACT_RELATIVE_FRONTIER; COMPACT_INTERVAL]] THEN
  MP_TAC MOI_FEU_SQUARE_FRONTIER_FACES THEN
  ABBREV_TAC `fs = {f | f face_of interval[--vec 1:real^2,vec 1] /\
                        ~(f = interval[--vec 1,vec 1]) /\ ~(f = {})}` THEN
  ABBREV_TAC `sq = relative_frontier(interval[--vec 1:real^2,vec 1])` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "sq") (LABEL_TAC "sum")) THEN
  SUBGOAL_THEN
   `!f:real^2->bool. f IN fs
         ==> polytope f /\ ~(f = {}) /\
             f face_of interval[--vec 1:real^2,vec 1]`
  (LABEL_TAC "fs") THENL
   [EXPAND_TAC "fs" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; POLYTOPE_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (fs:(real^2->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC
     `{f:real^2->bool | f face_of interval[--vec 1:real^2,vec 1]}` THEN
    SIMP_TAC[FINITE_POLYTOPE_FACES; POLYTOPE_INTERVAL] THEN
    EXPAND_TAC "fs" THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f g:real^2->bool. f IN fs /\ g IN fs /\ ~(f = g)
        ==> DISJOINT (relative_interior f) (relative_interior g)`
  (LABEL_TAC "dis") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FEU_FACES_DISJOINT_RELATIVE_INTERIORS THEN
    EXISTS_TAC `interval[--vec 1:real^2,vec 1]` THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!f:real^2->bool. f IN fs
        ==> moi_feu_euler (relative_interior f PCROSS (sq:real^2->bool)) (&0)`
  (LABEL_TAC "row") THENL
   [X_GEN_TAC `f:real^2->bool` THEN DISCH_TAC THEN
    USE_THEN "sq" (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o
                                              RAND_CONV) [th]) THEN
    REWRITE_TAC[PCROSS_UNIONS] THEN
    REWRITE_TAC[SET_RULE
     `{(s:real^2->bool) PCROSS t |
       t IN IMAGE (r:(real^2->bool)->real^2->bool) fs} =
      IMAGE (\g. s PCROSS r g) fs`] THEN
    SUBGOAL_THEN
     `&0 = sum fs (\g:real^2->bool.
             (-- &1) pow (num_of_int(aff_dim (f:real^2->bool))) *
             (-- &1) pow (num_of_int(aff_dim g)))`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[SUM_LMUL] THEN REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FEU_EULER_UNIONS THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT_PCROSS] THEN DISJ2_TAC THEN
      USE_THEN "dis" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FEU_EULER_RELINT_PCROSS THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  USE_THEN "sq" (fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV o
                                            LAND_CONV) [th]) THEN
  REWRITE_TAC[PCROSS_UNIONS] THEN
  REWRITE_TAC[SET_RULE
   `{s PCROSS (t:real^2->bool) |
     s IN IMAGE (r:(real^2->bool)->real^2->bool) fs} =
    IMAGE (\f. r f PCROSS t) fs`] THEN
  SUBGOAL_THEN `&0 = sum fs (\f:real^2->bool. &0)` SUBST1_TAC THENL
   [REWRITE_TAC[SUM_0]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FEU_EULER_UNIONS THEN
  REWRITE_TAC[ASSUME `FINITE (fs:(real^2->bool)->bool)`] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[DISJOINT_PCROSS] THEN DISJ1_TAC THEN
    USE_THEN "dis" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "row" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* COMPLEX_EULER_VALUES: the Euler characteristics of the standard pieces.   *)

let MOI_FEU_EULER_EQ = prove
 (`!(s:real^N->bool) v w. moi_feu_euler s v /\ v = w ==> moi_feu_euler s w`,
  MESON_TAC[]);;

let COMPLEX_EULER_VALUES = prove
 (`!c:(real^N->bool)->bool.
     simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2)
     ==> (pl_sphere 1 (UNIONS c) ==> complex_euler c = &0) /\
         (pl_ball 1 (UNIONS c) ==> complex_euler c = &1) /\
         (pl_ball 2 (UNIONS c) ==> complex_euler c = &1) /\
         (pl_sphere 2 (UNIONS c) ==> complex_euler c = &2) /\
         (pl_annulus (UNIONS c) ==> complex_euler c = &0) /\
         ((?(f:real^(2,2)finite_sum->real^N) g.
              pl_homeomorphism (pl_torus_model,UNIONS c) (f,g))
          ==> complex_euler c = &0) /\
         (!k. pl_holed_disk k (UNIONS c) ==> complex_euler c = &1 - &k)`,
  GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[pl_sphere; pl_ball; pl_annulus; pl_holed_disk;
              LEFT_IMP_EXISTS_THM] THEN
  REPEAT CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                         `g:real^N->real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:N`,`:M`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
    MAP_EVERY EXISTS_TAC [`relative_frontier k:real^N->bool`;
                          `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FEU_EULER_EQ THEN
      EXISTS_TAC `&1 - (-- &1) pow (1 + 1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FEU_EULER_SIMPLEX_FRONTIER THEN ASM_REWRITE_TAC[];
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER THEN
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]];
    MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                         `g:real^N->real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:N`,`:M`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`;
                          `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(k:real^N->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `&1 simplex (k:real^N->bool)` THEN
      ASM_REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC;
      ASM_MESON_TAC[MOI_FEU_EULER_SIMPLEX; SIMPLEX_IMP_COMPACT]];
    MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                         `g:real^N->real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:N`,`:M`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`;
                          `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(k:real^N->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `&2 simplex (k:real^N->bool)` THEN
      ASM_REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC;
      ASM_MESON_TAC[MOI_FEU_EULER_SIMPLEX; SIMPLEX_IMP_COMPACT]];
    MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                         `g:real^N->real^N`] THEN STRIP_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:N`,`:M`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
    MAP_EVERY EXISTS_TAC [`relative_frontier k:real^N->bool`;
                          `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FEU_EULER_EQ THEN
      EXISTS_TAC `&1 - (-- &1) pow (2 + 1)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FEU_EULER_SIMPLEX_FRONTIER THEN ASM_REWRITE_TAC[];
        CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC REAL_RAT_REDUCE_CONV];
      MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER THEN
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]];
    MAP_EVERY X_GEN_TAC [`f:real^2->real^N`; `g:real^N->real^2`] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:2`,`:M`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
    MAP_EVERY EXISTS_TAC
     [`interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
       interval(--vector[&1;&1]:real^2,vector[&1;&1])`;
      `f:real^2->real^N`; `g:real^N->real^2`] THEN
    ASM_REWRITE_TAC[MOI_FEU_EULER_ANNULUS_MODEL];
    MAP_EVERY X_GEN_TAC [`f:real^(2,2)finite_sum->real^N`;
                         `g:real^N->real^(2,2)finite_sum`] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:(2,2)finite_sum`,`:M`]
                 MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
    MAP_EVERY EXISTS_TAC
     [`pl_torus_model`; `f:real^(2,2)finite_sum->real^N`;
      `g:real^N->real^(2,2)finite_sum`] THEN
    ASM_REWRITE_TAC[MOI_FEU_EULER_TORUS_MODEL];
    MAP_EVERY X_GEN_TAC [`k:num`; `f:real^2->real^N`; `g:real^N->real^2`] THEN
    DISCH_TAC THEN
    MATCH_MP_TAC(INST_TYPE [`:2`,`:M`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
    MAP_EVERY EXISTS_TAC
     [`holed_disk_model k`; `f:real^2->real^N`; `g:real^N->real^2`] THEN
    ASM_REWRITE_TAC[MOI_FEU_EULER_HOLED_DISK_MODEL]]);;

(* ------------------------------------------------------------------------- *)
(* 8. The disk with one hole is a PL annulus: the map                        *)
(* (x,y) -> (phi x, y - 2), phi piecewise affine on [0,2], [2,4], [4,8],     *)
(* carries holed_disk_model 1 = [0,8]x[0,4] minus (2,4)x(1,3) onto the       *)
(* model [-2,2]^2 minus (-1,1)^2 of pl_annulus.                              *)
(* ------------------------------------------------------------------------- *)

let moi_feu_hd1_map = new_definition
 `moi_feu_hd1_map (z:real^2) =
    vector[if z$1 <= &2 then z$1 / &2 - &2
           else if z$1 <= &4 then z$1 - &3 else z$1 / &4; z$2 - &2]:real^2`;;

let moi_feu_hd1_inv = new_definition
 `moi_feu_hd1_inv (w:real^2) =
    vector[if w$1 <= -- &1 then &2 * w$1 + &4
           else if w$1 <= &1 then w$1 + &3 else &4 * w$1; w$2 + &2]:real^2`;;

let MOI_FEU_HOLED_DISK_MODEL_1 = prove
 (`holed_disk_model 1 =
   interval[vec 0:real^2,vector[&8; &4]] DIFF
   interval(vector[&2; &1]:real^2,vector[&4; &3])`,
  REWRITE_TAC[holed_disk_model; ARITH_RULE `i < 1 <=> i = 0`] THEN
  REWRITE_TAC[SET_RULE `{(f:num->real^2->bool) i | i | i = 0} = {f 0}`] THEN
  REWRITE_TAC[UNIONS_1] THEN CONV_TAC REAL_RAT_REDUCE_CONV);;

let MOI_FEU_IN_HD1 = prove
 (`!z:real^2.
        z IN holed_disk_model 1 <=>
        (&0 <= z$1 /\ z$1 <= &8 /\ &0 <= z$2 /\ z$2 <= &4) /\
        ~(&2 < z$1 /\ z$1 < &4 /\ &1 < z$2 /\ z$2 < &3)`,
  REWRITE_TAC[MOI_FEU_HOLED_DISK_MODEL_1; IN_DIFF; IN_INTERVAL; DIMINDEX_2;
              FORALL_2; VECTOR_2; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_FEU_IN_ANNULUS_MODEL = prove
 (`!w:real^2.
        w IN interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
             interval(--vector[&1;&1]:real^2,vector[&1;&1]) <=>
        (-- &2 <= w$1 /\ w$1 <= &2 /\ -- &2 <= w$2 /\ w$2 <= &2) /\
        ~(-- &1 < w$1 /\ w$1 < &1 /\ -- &1 < w$2 /\ w$2 < &1)`,
  REWRITE_TAC[IN_DIFF; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_NEG_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_FEU_HD1_MAP_COMPONENTS = prove
 (`!z:real^2.
        (moi_feu_hd1_map z)$1 =
          (if z$1 <= &2 then z$1 / &2 - &2
           else if z$1 <= &4 then z$1 - &3 else z$1 / &4) /\
        (moi_feu_hd1_map z)$2 = z$2 - &2`,
  REWRITE_TAC[moi_feu_hd1_map; VECTOR_2]);;

let MOI_FEU_HD1_INV_COMPONENTS = prove
 (`!w:real^2.
        (moi_feu_hd1_inv w)$1 =
          (if w$1 <= -- &1 then &2 * w$1 + &4
           else if w$1 <= &1 then w$1 + &3 else &4 * w$1) /\
        (moi_feu_hd1_inv w)$2 = w$2 + &2`,
  REWRITE_TAC[moi_feu_hd1_inv; VECTOR_2]);;

let MOI_FEU_HD1_IMAGE = prove
 (`IMAGE moi_feu_hd1_map (holed_disk_model 1) =
   interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
   interval(--vector[&1;&1]:real^2,vector[&1;&1])`,
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; MOI_FEU_IN_HD1;
                MOI_FEU_IN_ANNULUS_MODEL; MOI_FEU_HD1_MAP_COMPONENTS] THEN
    X_GEN_TAC `z:real^2` THEN
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `w:real^2` THEN
    DISCH_TAC THEN EXISTS_TAC `moi_feu_hd1_inv w` THEN CONJ_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2;
                  MOI_FEU_HD1_MAP_COMPONENTS; MOI_FEU_HD1_INV_COMPONENTS] THEN
      UNDISCH_TAC `(w:real^2) IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
                   interval(--vector[&1;&1],vector[&1;&1])` THEN
      REWRITE_TAC[MOI_FEU_IN_ANNULUS_MODEL] THEN
      REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(w:real^2) IN interval[--vector[&2;&2],vector[&2;&2]] DIFF
                   interval(--vector[&1;&1],vector[&1;&1])` THEN
      REWRITE_TAC[MOI_FEU_IN_ANNULUS_MODEL; MOI_FEU_IN_HD1;
                  MOI_FEU_HD1_INV_COMPONENTS] THEN
      REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]]);;

let MOI_FEU_HD1_INJECTIVE = prove
 (`!z z':real^2.
        z IN holed_disk_model 1 /\ z' IN holed_disk_model 1 /\
        moi_feu_hd1_map z = moi_feu_hd1_map z'
        ==> z = z'`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; MOI_FEU_HD1_MAP_COMPONENTS] THEN
  REWRITE_TAC[MOI_FEU_IN_HD1] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_FEU_LINEAR_SCALE_FIRST = prove
 (`!a. linear (\z:real^2. vector[a * z$1; z$2]:real^2)`,
  GEN_TAC THEN
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_2;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_FEU_HD1_PL = prove
 (`pl_map_on (holed_disk_model 1) moi_feu_hd1_map`,
  REWRITE_TAC[pl_map_on] THEN X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN
  EXISTS_TAC `{interval[vec 0:real^2,vector[&2;&4]],
               interval[vector[&2;&0]:real^2,vector[&4;&1]],
               interval[vector[&2;&3]:real^2,vector[&4;&4]],
               interval[vector[&4;&0]:real^2,vector[&8;&4]]}` THEN
  EXISTS_TAC `(:real^2)` THEN
  REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY; OPEN_UNIV; IN_UNIV; INTER_UNIV] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; UNIONS_INSERT; UNIONS_0; UNION_EMPTY; IN_UNION;
                MOI_FEU_IN_HD1; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
                VEC_COMPONENT] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY; POLYTOPE_INTERVAL] THEN
  REWRITE_TAC[SUBSET; MOI_FEU_IN_HD1; IN_INTERVAL; DIMINDEX_2; FORALL_2;
              VECTOR_2; VEC_COMPONENT] THEN
  REPEAT CONJ_TAC THEN TRY REAL_ARITH_TAC THENL
   [MAP_EVERY EXISTS_TAC [`\z:real^2. vector[&1 / &2 * z$1; z$2]:real^2`;
                          `vector[-- &2; -- &2]:real^2`] THEN
    REWRITE_TAC[MOI_FEU_LINEAR_SCALE_FIRST];
    MAP_EVERY EXISTS_TAC [`\z:real^2. vector[&1 * z$1; z$2]:real^2`;
                          `vector[-- &3; -- &2]:real^2`] THEN
    REWRITE_TAC[MOI_FEU_LINEAR_SCALE_FIRST];
    MAP_EVERY EXISTS_TAC [`\z:real^2. vector[&1 * z$1; z$2]:real^2`;
                          `vector[-- &3; -- &2]:real^2`] THEN
    REWRITE_TAC[MOI_FEU_LINEAR_SCALE_FIRST];
    MAP_EVERY EXISTS_TAC [`\z:real^2. vector[&1 / &4 * z$1; z$2]:real^2`;
                          `vector[&0; -- &2]:real^2`] THEN
    REWRITE_TAC[MOI_FEU_LINEAR_SCALE_FIRST]] THEN
  X_GEN_TAC `z:real^2` THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2; VECTOR_ADD_COMPONENT; VECTOR_2;
              MOI_FEU_HD1_MAP_COMPONENTS] THEN
  REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC);;

let MOI_FEU_HD1_PL_HOMEOMORPHISM = prove
 (`?g. pl_homeomorphism
         (holed_disk_model 1,
          interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
          interval(--vector[&1;&1]:real^2,vector[&1;&1]))
         (moi_feu_hd1_map,g)`,
  MP_TAC(ISPECL [`holed_disk_model 1`; `moi_feu_hd1_map`;
                 `interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                  interval(--vector[&1;&1]:real^2,vector[&1;&1])`]
    HOMEOMORPHISM_COMPACT) THEN
  REWRITE_TAC[MOI_FEU_HD1_IMAGE; MOI_FEU_EULER_HOLED_DISK_MODEL] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
      REWRITE_TAC[MOI_FEU_HD1_PL];
      REWRITE_TAC[MOI_FEU_HD1_INJECTIVE]];
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `g:real^2->real^2` THEN
    DISCH_TAC THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN
    ASM_REWRITE_TAC[MOI_FEU_HD1_PL]]);;

let PL_HOLED_DISK_1_ANNULUS = prove
 (`!a:real^N->bool. pl_holed_disk 1 a <=> pl_annulus a`,
  GEN_TAC THEN REWRITE_TAC[pl_holed_disk; pl_annulus] THEN
  X_CHOOSE_TAC `h:real^2->real^2` MOI_FEU_HD1_PL_HOMEOMORPHISM THEN
  EQ_TAC THEN REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`f:real^2->real^N`; `g:real^N->real^2`] THEN
  DISCH_TAC THENL
   [MAP_EVERY EXISTS_TAC [`(f:real^2->real^N) o (h:real^2->real^2)`;
                          `moi_feu_hd1_map o (g:real^N->real^2)`] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `holed_disk_model 1` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`(f:real^2->real^N) o moi_feu_hd1_map`;
                          `(h:real^2->real^2) o (g:real^N->real^2)`] THEN
    MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                interval(--vector[&1;&1]:real^2,vector[&1;&1])` THEN
    ASM_REWRITE_TAC[]]);;

