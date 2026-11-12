(* ========================================================================= *)
(* pc_moi_lt_gpb1b: the cut complex and its cone triangulation for the chart *)
(* step of the loop theorem (pc_moi_lt_gpb1, CHART_STEP =                    *)
(* MOI_LGB_CHART_STEP).  For a map a affine on the simplices of a source     *)
(* complex and a target complex H, the cells (the sets of the x IN r with a  *)
(* x IN S, for r a source simplex and S in H) are polytopes whose faces and  *)
(* intersections are cells; the cells of dimension at most 1 are simplices;  *)
(* coning the 2-cells from points of their relative interiors gives a        *)
(* simplicial complex refining both (MOI_CON_GLUE_CONE).                     *)
(* ========================================================================= *)

needs "src/pc_moi_lt_gpb1a.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* B1. Faces under affine maps: preimages of faces are faces (on a convex   *)
(* domain where the map is affine); images of faces under injective affine  *)
(* maps are faces.                                                           *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_FACE_OF_AFFINE_PREIMAGE = prove
 (`!(a:real^M->real^N) r s f l y.
     convex r /\ linear l /\ (!x. x IN r ==> a x = l x + y) /\
     convex s /\ f face_of s
     ==> {x | x IN r /\ a x IN f} face_of {x | x IN r /\ a x IN s}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!p q u. p IN r /\ q IN r /\ &0 <= u /\ u <= &1
                        ==> ((&1 - u) % p + u % q:real^M) IN r /\
                            (a:real^M->real^N)((&1 - u) % p + u % q) =
                            (&1 - u) % a p + u % a q`
  (LABEL_TAC "aff") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `((&1 - u) % p + u % q:real^M) IN r` ASSUME_TAC THENL
     [ASM_MESON_TAC[CONVEX_ALT]; ALL_TAC] THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[face_of] THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[CONVEX_ALT; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:real^M`; `q:real^M`; `u:real`] THEN STRIP_TAC THEN
    USE_THEN "aff" (MP_TAC o SPECL [`p:real^M`; `q:real^M`; `u:real`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `f:real^N->bool`] FACE_OF_IMP_CONVEX) THEN
    ASM_REWRITE_TAC[CONVEX_ALT] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`p:real^M`; `q:real^M`; `z:real^M`] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(a:real^M->real^N) p = a q` THENL
     [SUBGOAL_THEN `(a:real^M->real^N) z = a p` ASSUME_TAC THENL
       [UNDISCH_TAC `(z:real^M) IN segment(p,q)` THEN
        REWRITE_TAC[IN_SEGMENT] THEN
        DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real`
          STRIP_ASSUME_TAC)) THEN
        USE_THEN "aff" (MP_TAC o SPECL [`p:real^M`; `q:real^M`; `u:real`]) THEN
        ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
        DISCH_THEN(fun th -> ASM_REWRITE_TAC[CONJUNCT2 th]) THEN
        VECTOR_ARITH_TAC;
        REMOVE_THEN "aff" (K ALL_TAC) THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    MP_TAC(REWRITE_RULE[face_of] (ASSUME `(f:real^N->bool) face_of s`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`(a:real^M->real^N) p`; `(a:real^M->real^N) q`;
                              `(a:real^M->real^N) z`] o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^M) IN segment(p,q)` THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "aff" (MP_TAC o SPECL [`p:real^M`; `q:real^M`; `u:real`]) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; SIMP_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* B2. Cells (the x IN r with a x IN s): polytopes; intersections; faces of *)
(* cells                                                                     *)
(* are cells of faces and conversely; cells of a simplex mapped into one    *)
(* simplex of the target are faces of it.                                    *)
(* ------------------------------------------------------------------------- *)

let moi_lgb1_cell = new_definition
 `moi_lgb1_cell (a:real^M->real^N) r s = {x | x IN r /\ a x IN s}`;;

let MOI_LGB1_CELL_INTER = prove
 (`!(a:real^M->real^N) r s r' s'.
     moi_lgb1_cell a r s INTER moi_lgb1_cell a r' s' =
     moi_lgb1_cell a (r INTER r') (s INTER s')`,
  REWRITE_TAC[moi_lgb1_cell] THEN SET_TAC[]);;

let MOI_LGB1_CELL_SUBSET = prove
 (`!(a:real^M->real^N) r s. moi_lgb1_cell a r s SUBSET r`,
  REWRITE_TAC[moi_lgb1_cell] THEN SET_TAC[]);;

let MOI_LGB1_CELL_IMAGE = prove
 (`!(a:real^M->real^N) r s. IMAGE a (moi_lgb1_cell a r s) = IMAGE a r INTER s`,
  REWRITE_TAC[moi_lgb1_cell] THEN SET_TAC[]);;

let MOI_LGB1_CELL_ALT = prove
 (`!(a:real^M->real^N) r s l y.
     (!x. x IN r ==> a x = l x + y)
     ==> moi_lgb1_cell a r s = r INTER {x | l x + y IN s}`,
  REWRITE_TAC[moi_lgb1_cell] THEN SET_TAC[]);;

let MOI_LGB1_AFFINE_PREIMAGE_POLYHEDRON = prove
 (`!(l:real^M->real^N) y s.
     linear l /\ polyhedron s ==> polyhedron {x | l x + y IN s}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{x | (l:real^M->real^N) x + y IN s} =
                {x | l x IN IMAGE (\z. --y + z) s}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN
    MESON_TAC[VECTOR_ARITH `(l:real^N) + y = z <=> l = --y + z`];
    MATCH_MP_TAC POLYHEDRON_LINEAR_PREIMAGE THEN
    ASM_REWRITE_TAC[POLYHEDRON_TRANSLATION_EQ]]);;

let MOI_LGB1_CELL_POLYTOPE = prove
 (`!(a:real^M->real^N) r s l y.
     polytope r /\ polytope s /\ linear l /\ (!x. x IN r ==> a x = l x + y)
     ==> polytope (moi_lgb1_cell a r s)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_LGB1_CELL_ALT] THEN
  MATCH_MP_TAC POLYTOPE_INTER_POLYHEDRON THEN
  ASM_SIMP_TAC[MOI_LGB1_AFFINE_PREIMAGE_POLYHEDRON; POLYTOPE_IMP_POLYHEDRON]);;

let MOI_LGB1_AFFINE_PREIMAGE_CONVEX = prove
 (`!(l:real^M->real^N) y s.
     linear l /\ convex s ==> convex {x | l x + y IN s}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[CONVEX_ALT; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`p:real^M`; `q:real^M`; `u:real`] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
  REWRITE_TAC[VECTOR_ARITH
   `((&1 - u) % lp + u % lq) + y:real^N = (&1 - u) % (lp + y) + u % (lq + y)`] THEN
  ASM_MESON_TAC[CONVEX_ALT]);;

let MOI_LGB1_CELL_CONVEX = prove
 (`!(a:real^M->real^N) r s l y.
     convex r /\ convex s /\ linear l /\ (!x. x IN r ==> a x = l x + y)
     ==> convex (moi_lgb1_cell a r s)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_LGB1_CELL_ALT] THEN
  MATCH_MP_TAC CONVEX_INTER THEN ASM_SIMP_TAC[MOI_LGB1_AFFINE_PREIMAGE_CONVEX]);;

let MOI_LGB1_CELL_FACE_OF = prove
 (`!(a:real^M->real^N) r s r0 s0 l y.
     convex r /\ convex s /\ linear l /\ (!x. x IN r ==> a x = l x + y) /\
     r0 face_of r /\ s0 face_of s
     ==> moi_lgb1_cell a r0 s0 face_of moi_lgb1_cell a r s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r0:real^M->bool) SUBSET r /\ (s0:real^N->bool) SUBSET s`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_lgb1_cell (a:real^M->real^N) r0 s0 =
                (r0 INTER {x | (l:real^M->real^N) x + y IN s}) INTER moi_lgb1_cell a r s0`
  SUBST1_TAC THENL
   [REWRITE_TAC[moi_lgb1_cell] THEN UNDISCH_TAC `(r0:real^M->bool) SUBSET r` THEN
    UNDISCH_TAC `(s0:real^N->bool) SUBSET s` THEN
    UNDISCH_TAC `!x:real^M. x IN r ==> (a:real^M->real^N) x = l x + y` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC FACE_OF_INTER THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[MOI_LGB1_CELL_ALT] THEN MATCH_MP_TAC FACE_OF_SLICE THEN
    ASM_SIMP_TAC[MOI_LGB1_AFFINE_PREIMAGE_CONVEX];
    REWRITE_TAC[moi_lgb1_cell] THEN MATCH_MP_TAC MOI_LGB1_FACE_OF_AFFINE_PREIMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB1_FACE_OF_AFFINE_IMAGE_INJ = prove
 (`!(a:real^M->real^N) k f l y.
     convex k /\ linear l /\ (!x. x IN k ==> a x = l x + y) /\
     (!x x'. x IN k /\ x' IN k /\ a x = a x' ==> x = x') /\ f face_of k
     ==> IMAGE a f face_of IMAGE a k`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "eq") (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(f:real^M->bool) SUBSET k /\ convex f` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; FACE_OF_IMP_CONVEX]; ALL_TAC] THEN
  REWRITE_TAC[face_of] THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    SUBGOAL_THEN `IMAGE (a:real^M->real^N) f = IMAGE (\x. l x + y) f` SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(!x:real^M. x IN s ==> (f:real^M->real^N) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
      ASM SET_TAC[];
      ASM_SIMP_TAC[MOI_FGP_CONVEX_AFFINE_IMAGE]];
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `p:real^M` THEN DISCH_TAC THEN X_GEN_TAC `q:real^M` THEN DISCH_TAC THEN
    X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `((&1 - u) % p + u % q:real^M) IN k` ASSUME_TAC THENL
     [MATCH_MP_TAC(REWRITE_RULE[CONVEX_ALT] (ASSUME `convex(k:real^M->bool)`)) THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ALL_TAC] THEN
    SUBGOAL_THEN `z:real^M = (&1 - u) % p + u % q` ASSUME_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> rand(concl th) =
        `(&1 - u) % (a:real^M->real^N) p + u % a q`)) THEN
      ASM_SIMP_TAC[] THEN ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(REWRITE_RULE[face_of] (ASSUME `(f:real^M->bool) face_of k`)) THEN
    DISCH_THEN(MP_TAC o SPECL [`p:real^M`; `q:real^M`; `z:real^M`] o
      CONJUNCT2 o CONJUNCT2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
        EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[]];
      STRIP_TAC THEN CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_LGB1_CELL_FACES = prove
 (`!(a:real^M->real^N) r s f l y.
     convex r /\ convex s /\ linear l /\ (!x. x IN r ==> a x = l x + y) /\
     (!x x'. x IN r /\ x' IN r /\ a x = a x' ==> x = x') /\
     f face_of moi_lgb1_cell a r s
     ==> ?r0 s0. r0 face_of r /\ s0 face_of s /\ f = moi_lgb1_cell a r0 s0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex(moi_lgb1_cell (a:real^M->real^N) r s)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_CELL_CONVEX THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (a:real^M->real^N) f face_of IMAGE a r INTER s` MP_TAC THENL
   [REWRITE_TAC[GSYM MOI_LGB1_CELL_IMAGE] THEN
    MATCH_MP_TAC MOI_LGB1_FACE_OF_AFFINE_IMAGE_INJ THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`a:real^M->real^N`; `r:real^M->bool`; `s:real^N->bool`]
      MOI_LGB1_CELL_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(IMAGE (a:real^M->real^N) r)` ASSUME_TAC THENL
   [SUBGOAL_THEN `IMAGE (a:real^M->real^N) r = IMAGE (\x. l x + y) r` SUBST1_TAC THENL
     [MATCH_MP_TAC(SET_RULE `(!x:real^M. x IN s ==> (f:real^M->real^N) x = g x) ==> IMAGE f s = IMAGE g s`) THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MOI_FGP_CONVEX_AFFINE_IMAGE]];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`IMAGE (a:real^M->real^N) r`; `s:real^N->bool`;
                 `IMAGE (a:real^M->real^N) f`] FACE_OF_INTER_AS_INTER_OF_FACE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^N->bool` (X_CHOOSE_THEN `l1:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`moi_lgb1_cell (a:real^M->real^N) r k1`; `l1:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `r = {x:real^M | x IN r /\ (a:real^M->real^N) x IN IMAGE a r}`
    (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THENL
     [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_lgb1_cell] THEN MATCH_MP_TAC MOI_LGB1_FACE_OF_AFFINE_PREIMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `(f:real^M->bool) SUBSET r` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`moi_lgb1_cell (a:real^M->real^N) r s`; `f:real^M->bool`]
        FACE_OF_IMP_SUBSET) THEN
      MP_TAC(ISPECL [`a:real^M->real^N`; `r:real^M->bool`; `s:real^N->bool`]
        MOI_LGB1_CELL_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_lgb1_cell; EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `x:real^M` THEN
    EQ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(a:real^M->real^N) x IN k1 INTER l1` MP_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `(a:real^M->real^N) x IN IMAGE a f` MP_TAC THENL
       [UNDISCH_TAC `k1 INTER l1 = IMAGE (a:real^M->real^N) f` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER];
        ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^M` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `x:real^M = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
        check (fun th -> can (find_term ((=) `x':real^M`)) (concl th))) THEN
      ASM SET_TAC[]]]);;

let MOI_LGB1_CELL_UNMOVED = prove
 (`!(a:real^M->real^N) r s s0 l y.
     convex r /\ linear l /\ (!x. x IN r ==> a x = l x + y) /\ convex s0 /\
     IMAGE a r SUBSET s0 /\ (s INTER s0) face_of s0
     ==> moi_lgb1_cell a r s face_of r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_lgb1_cell (a:real^M->real^N) r s =
                {x | x IN r /\ a x IN s INTER s0}` SUBST1_TAC THENL
   [REWRITE_TAC[moi_lgb1_cell] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{x | x IN r /\ (a:real^M->real^N) x IN s INTER s0} face_of
                {x | x IN r /\ a x IN s0}` MP_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_FACE_OF_AFFINE_PREIMAGE THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x | x IN r /\ (a:real^M->real^N) x IN s0} = r`
    (fun th -> REWRITE_TAC[th]) THEN
  ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* B3. Coning a convex compact set from a relative interior point over a    *)
(* triangulation of its relative frontier (MOI_CON_CONE_OVER_RF without the *)
(* simplex hypothesis); the proper faces of a polytope of dimension at most *)
(* 2 form a simplicial complex triangulating its relative frontier.         *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_CONE_OVER_RF_GEN = prove
 (`!K (t:real^N->bool) b.
        convex t /\ compact t /\ b IN relative_interior t /\
        ~(relative_frontier t = {}) /\
        simplicial_complex K /\ UNIONS K = relative_frontier t
        ==> simplicial_complex (K UNION {convex hull (b INSERT s) | s IN K}) /\
            UNIONS (K UNION {convex hull (b INSERT s) | s IN K}) = t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `b:real^N`]
    SIMPLICIAL_CONE_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_RF_SEGMENT THEN
      EXISTS_TAC `t:real^N->bool` THEN EXISTS_TAC `b:real^N` THEN
      ASM_MESON_TAC[]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_CON_CONE_RF THEN ASM_REWRITE_TAC[]]);;

let MOI_LGB1_BOUNDARY_COMPLEX = prove
 (`!p:real^N->bool.
     polytope p /\ aff_dim p <= &2
     ==> simplicial_complex {f | f face_of p /\ ~(f = p)} /\
         UNIONS {f | f face_of p /\ ~(f = p)} = relative_frontier p`,
  REPEAT STRIP_TAC THENL
   [REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{f:real^N->bool | f face_of p}` THEN
      ASM_SIMP_TAC[FINITE_POLYTOPE_FACES] THEN SET_TAC[];
      X_GEN_TAC `f:real^N->bool` THEN STRIP_TAC THEN
      MATCH_MP_TAC POLYTOPE_LOWDIM_IMP_SIMPLEX THEN CONJ_TAC THENL
       [ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE];
        MP_TAC(ISPECL [`f:real^N->bool`; `p:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
        ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN ASM_ARITH_TAC];
      MAP_EVERY X_GEN_TAC [`g:real^N->bool`; `f:real^N->bool`] THEN STRIP_TAC THEN
      CONJ_TAC THENL [ASM_MESON_TAC[FACE_OF_TRANS]; ALL_TAC] THEN
      DISCH_THEN SUBST_ALL_TAC THEN
      SUBGOAL_THEN `(p:real^N->bool) SUBSET f /\ f SUBSET p` MP_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ASM SET_TAC[]];
      MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `f':real^N->bool`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(f INTER f':real^N->bool) face_of p` ASSUME_TAC THENL
       [ASM_SIMP_TAC[FACE_OF_INTER]; ALL_TAC] THEN
      CONJ_TAC THEN MATCH_MP_TAC FACE_OF_SUBSET THEN
      EXISTS_TAC `p:real^N->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET] THEN
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN
      MESON_TAC[FACE_OF_SUBSET_RELATIVE_FRONTIER];
      ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON; POLYTOPE_IMP_POLYHEDRON] THEN
      MATCH_MP_TAC SUBSET_UNIONS THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `f:real^N->bool` THEN REWRITE_TAC[facet_of] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* B4. The cut complex.  mv: the simplices to be cut (closed upwards in L); *)
(* a affine on every face of them and injective on them; the faces of them *)
(* not in mv map into single simplices of H.  The unmoved simplices and the *)
(* cells of dimension <= 1 form a complex l0 (MOI_LGB1_CUT_L0_COMPLEX); the  *)
(* cones over the 2-cells are glued in one at a time.                        *)
(* ------------------------------------------------------------------------- *)

let moi_lgb1_cutsetup = new_definition
 `moi_lgb1_cutsetup (L:(real^M->bool)->bool) mv (a:real^M->real^N)
                    (H:(real^N->bool)->bool) <=>
    simplicial_complex L /\ simplicial_complex H /\ mv SUBSET L /\
    (!r. r IN L ==> aff_dim r <= &2) /\
    (!r r'. r IN mv /\ r' IN L /\ r SUBSET r' ==> r' IN mv) /\
    (!r. r IN L /\ (?r'. r' IN mv /\ r SUBSET r')
         ==> ?l y. linear l /\ !x. x IN r ==> a x = l x + y) /\
    (!r x y. r IN mv /\ x IN r /\ y IN r /\ a x = a y ==> x = y) /\
    (!r. r IN mv ==> IMAGE a r SUBSET UNIONS H) /\
    (!r. r IN L /\ ~(r IN mv) /\ (?r'. r' IN mv /\ r SUBSET r')
         ==> ?s. s IN H /\ IMAGE a r SUBSET s)`;;

let moi_lgb1_cut = new_definition
 `moi_lgb1_cut (L:(real^M->bool)->bool) mv (a:real^M->real^N)
               (H:(real^N->bool)->bool) (b:(real^M->bool)->real^M) =
    {r | r IN L /\ ~(r IN mv)} UNION
    {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) <= &1} UNION
    {convex hull (b p INSERT f) | p,f |
       p IN {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\
                                         aff_dim (moi_lgb1_cell a r s) = &2} /\
       f face_of p /\ ~(f = p)}`;;

(* Basic facts available in the setup.                                       *)

let MOI_LGB1_SETUP_FACTS = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) H r.
     moi_lgb1_cutsetup L mv a H /\ r IN mv
     ==> r IN L /\ convex r /\ polytope r /\
         (?l y. linear l /\ !x. x IN r ==> a x = l x + y) /\
         (!x y. x IN r /\ y IN r /\ a x = a y ==> x = y)`,
  REWRITE_TAC[moi_lgb1_cutsetup; simplicial_complex] THEN REPEAT STRIP_TAC THENL
   [ASM SET_TAC[];
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SUBSET];
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; SUBSET];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `linear:(real^M->real^N)->bool`)) (concl th))) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; EXISTS_TAC `r:real^M->bool` THEN
                    ASM_REWRITE_TAC[SUBSET_REFL]];
    ASM_MESON_TAC[]]);;

let MOI_LGB1_CUT_CELL_FACE_IN = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) H r s f.
     moi_lgb1_cutsetup L mv a H /\ r IN mv /\ s IN H /\
     f face_of moi_lgb1_cell a r s /\ aff_dim f <= &1
     ==> (f IN L /\ ~(f IN mv)) \/
         (?r0 s0. r0 IN mv /\ s0 IN H /\ f = moi_lgb1_cell a r0 s0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`]
    MOI_LGB1_SETUP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^M->real^N`
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lgb1_cutsetup]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex] o
    check (fun th -> concl th = `simplicial_complex (L:(real^M->bool)->bool)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex] o
    check (fun th -> concl th = `simplicial_complex (H:(real^N->bool)->bool)`)) THEN
  MP_TAC(ISPECL [`a:real^M->real^N`; `r:real^M->bool`; `s:real^N->bool`;
                 `f:real^M->bool`; `l:real^M->real^N`; `y:real^N`]
    MOI_LGB1_CELL_FACES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real^M->bool` (X_CHOOSE_THEN `s0:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(r0:real^M->bool) IN L /\ (s0:real^N->bool) IN H` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  ASM_CASES_TAC `(r0:real^M->bool) IN mv` THENL
   [DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`r0:real^M->bool`; `s0:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    DISJ1_TAC] THEN
  SUBGOAL_THEN `(r0:real^M->bool) SUBSET r` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?s1:real^N->bool. s1 IN H /\ IMAGE (a:real^M->real^N) r0 SUBSET s1`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `UNIONS (H:(real^N->bool)->bool)`)) (concl th) = false &&
      can (find_term ((=) `IMAGE (a:real^M->real^N)`)) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `r:real^M->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->bool) face_of r0` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB1_CELL_UNMOVED THEN
    MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `l:real^M->real^N`; `y:real^N`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM SET_TAC[];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[INTER_COMM]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  UNDISCH_TAC `~((r0:real^M->bool) IN mv)` THEN REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term ((=) `r':real^M->bool`)) (concl th) &&
    not (can (find_term ((=) `linear:(real^M->real^N)->bool`)) (concl th)) &&
    not (can (find_term ((=) `H:(real^N->bool)->bool`)) (concl th)))) THEN
  EXISTS_TAC `f:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[FACE_OF_IMP_SUBSET]);;

let MOI_LGB1_CUT_CELL_INTER = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) H r s r' s'.
     moi_lgb1_cutsetup L mv a H /\ r IN mv /\ s IN H /\ r' IN L /\ s' IN H
     ==> (moi_lgb1_cell a r s INTER moi_lgb1_cell a r' s') face_of
         moi_lgb1_cell a r s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`]
    MOI_LGB1_SETUP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^M->real^N`
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lgb1_cutsetup]) THEN
  REWRITE_TAC[MOI_LGB1_CELL_INTER] THEN MATCH_MP_TAC MOI_LGB1_CELL_FACE_OF THEN
  MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX]);;

let MOI_LGB1_CUT_UNMOVED_INTER = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) H u r s.
     moi_lgb1_cutsetup L mv a H /\ u IN L /\ ~(u IN mv) /\ r IN mv /\ s IN H
     ==> (u INTER moi_lgb1_cell a r s) face_of moi_lgb1_cell a r s /\
         (u INTER moi_lgb1_cell a r s) face_of u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`]
    MOI_LGB1_SETUP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^M->real^N`
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) ASSUME_TAC)))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lgb1_cutsetup]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex] o
    check (fun th -> concl th = `simplicial_complex (L:(real^M->bool)->bool)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex] o
    check (fun th -> concl th = `simplicial_complex (H:(real^N->bool)->bool)`)) THEN
  SUBGOAL_THEN `u INTER moi_lgb1_cell (a:real^M->real^N) r s =
                moi_lgb1_cell a (r INTER u) s` SUBST1_TAC THENL
   [REWRITE_TAC[moi_lgb1_cell] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(r INTER u:real^M->bool) face_of r /\ (r INTER u) face_of u /\
                (r INTER u) IN L` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((r INTER u:real^M->bool) IN mv)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((u:real^M->bool) IN mv)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `r':real^M->bool`)) (concl th) &&
      not (can (find_term ((=) `linear:(real^M->real^N)->bool`)) (concl th)) &&
      not (can (find_term ((=) `H:(real^N->bool)->bool`)) (concl th)))) THEN
    EXISTS_TAC `r INTER u:real^M->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `?s1:real^N->bool. s1 IN H /\
                  IMAGE (a:real^M->real^N) (r INTER u) SUBSET s1`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `UNIONS (H:(real^N->bool)->bool)`)) (concl th) = false &&
      can (find_term ((=) `IMAGE (a:real^M->real^N)`)) (concl th) &&
      is_forall (concl th))) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `r:real^M->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_CELL_FACE_OF THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; FACE_OF_REFL];
    MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `r INTER u:real^M->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB1_CELL_UNMOVED THEN
    MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `l:real^M->real^N`; `y:real^N`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
      ASM SET_TAC[];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[INTER_COMM]]]);;

let MOI_LGB1_CUT_CELLS_FINITE = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) H P.
     moi_lgb1_cutsetup L mv a H
     ==> FINITE {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ P r s}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN H}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(REWRITE_RULE[] (ISPECL
      [`\r s. moi_lgb1_cell (a:real^M->real^N) r s`; `mv:(real^M->bool)->bool`;
       `\r:real^M->bool. (H:(real^N->bool)->bool)`] FINITE_PRODUCT_DEPENDENT)) THEN
    FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lgb1_cutsetup]) THEN
    ASM_MESON_TAC[simplicial_complex; FINITE_SUBSET];
    SET_TAC[]]);;

let MOI_LGB1_CUT_L0_COMPLEX = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) H.
     moi_lgb1_cutsetup L mv a H
     ==> simplicial_complex
          ({r | r IN L /\ ~(r IN mv)} UNION
           {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\
                                        aff_dim (moi_lgb1_cell a r s) <= &1})`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lgb1_cutsetup]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex] o
    check (fun th -> concl th = `simplicial_complex (L:(real^M->bool)->bool)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex] o
    check (fun th -> concl th = `simplicial_complex (H:(real^N->bool)->bool)`)) THEN
  GEN_REWRITE_TAC I [simplicial_complex] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[FINITE_UNION] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[FINITE_RESTRICT];
      MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                     `a:real^M->real^N`; `H:(real^N->bool)->bool`;
                     `\r s. aff_dim(moi_lgb1_cell (a:real^M->real^N) r s) <= &1`]
        MOI_LGB1_CUT_CELLS_FINITE) THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN X_GEN_TAC `t:real^M->bool` THEN
    STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC POLYTOPE_LOWDIM_IMP_SIMPLEX THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                   `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`]
      MOI_LGB1_SETUP_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_LGB1_CELL_POLYTOPE THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`f:real^M->bool`; `t:real^M->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN STRIP_TAC THENL
     [DISJ1_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((t:real^M->bool) IN mv)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        can (find_term ((=) `r':real^M->bool`)) (concl th) &&
        not (can (find_term ((=) `linear:(real^M->real^N)->bool`)) (concl th)) &&
        not (can (find_term ((=) `H:(real^N->bool)->bool`)) (concl th)))) THEN
      EXISTS_TAC `f:real^M->bool` THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                     `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`;
                     `s:real^N->bool`; `f:real^M->bool`] MOI_LGB1_CUT_CELL_FACE_IN) THEN
      SUBGOAL_THEN `aff_dim(f:real^M->bool) <= &1` ASSUME_TAC THENL
       [MATCH_MP_TAC INT_LE_TRANS THEN
        EXISTS_TAC `aff_dim(moi_lgb1_cell (a:real^M->real^N) r s)` THEN
        ASM_MESON_TAC[AFF_DIM_SUBSET; FACE_OF_IMP_SUBSET];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
      MAP_EVERY EXISTS_TAC [`r0:real^M->bool`; `s0:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`t:real^M->bool`; `t':real^M->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                     `a:real^M->real^N`; `H:(real^N->bool)->bool`; `t:real^M->bool`;
                     `r:real^M->bool`; `s:real^N->bool`] MOI_LGB1_CUT_UNMOVED_INTER) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                     `a:real^M->real^N`; `H:(real^N->bool)->bool`; `t':real^M->bool`;
                     `r:real^M->bool`; `s:real^N->bool`] MOI_LGB1_CUT_UNMOVED_INTER) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[INTER_COMM];
      REPEAT(FIRST_X_ASSUM SUBST_ALL_TAC) THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_LGB1_CUT_CELL_INTER;
        ONCE_REWRITE_TAC[INTER_COMM] THEN MATCH_MP_TAC MOI_LGB1_CUT_CELL_INTER] THEN
      EXISTS_TAC `L:(real^M->bool)->bool` THEN ASM_MESON_TAC[SUBSET]]]);;

(* ------------------------------------------------------------------------- *)
(* B5. The cut complex.                                                      *)
(* For a cell p = moi_lgb1_cell a r s of dimension 2, its proper faces lie  *)
(* in l0 (MOI_LGB1_CUT_BOUNDARY_IN_L0) and the members of l0 and the other  *)
(* 2-cells meet p only in its relative frontier (MOI_LGB1_CUT_L0_OUTSIDE,   *)
(* MOI_LGB1_CUT_C2_OUTSIDE); the cone from b p over the boundary complex of *)
(* p triangulates p (MOI_LGB1_CUT_CONE_PIECE).  Gluing the cones one 2-cell *)
(* at a time (MOI_CON_GLUE_CONE, MOI_CON_CONE_INTER_OUTSIDE, induction over *)
(* finite sets of 2-cells: MOI_LGB1_CUT_GLUE) gives MOI_LGB1_CUT_COMPLEX_GEN *)
(* under moi_lgb1_cutsetup and the theorem MOI_LGB1_CUT_COMPLEX (real^2 to   *)
(* real^3, where aff_dim r <= 2 is automatic).                               *)
(* ------------------------------------------------------------------------- *)

let MOI_LGB1_CUT_CELL_BASICS = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) (H:(real^N->bool)->bool) r s.
     moi_lgb1_cutsetup L mv a H /\ r IN mv /\ s IN H
     ==> polytope (moi_lgb1_cell a r s) /\ convex (moi_lgb1_cell a r s) /\
         compact (moi_lgb1_cell a r s) /\ closed (moi_lgb1_cell a r s) /\
         moi_lgb1_cell a r s SUBSET r /\ aff_dim (moi_lgb1_cell a r s) <= &2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`]
    MOI_LGB1_SETUP_FACTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real^M->real^N`
      (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) ASSUME_TAC)))) THEN
  SUBGOAL_THEN `polytope (s:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_cutsetup (L:(real^M->bool)->bool) mv (a:real^M->real^N) H` THEN
    REWRITE_TAC[moi_lgb1_cutsetup; simplicial_complex] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN `polytope (moi_lgb1_cell (a:real^M->real^N) r s)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LGB1_CELL_POLYTOPE THEN
    MAP_EVERY EXISTS_TAC [`l:real^M->real^N`; `y:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX; POLYTOPE_IMP_COMPACT; POLYTOPE_IMP_CLOSED;
               MOI_LGB1_CELL_SUBSET] THEN
  MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim (r:real^M->bool)` THEN
  SIMP_TAC[AFF_DIM_SUBSET; MOI_LGB1_CELL_SUBSET] THEN
  UNDISCH_TAC `moi_lgb1_cutsetup (L:(real^M->bool)->bool) mv (a:real^M->real^N) H` THEN
  REWRITE_TAC[moi_lgb1_cutsetup] THEN ASM_MESON_TAC[]);;

let MOI_LGB1_CUT_BOUNDARY_IN_L0 = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) (H:(real^N->bool)->bool) r s f.
     moi_lgb1_cutsetup L mv a H /\ r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) = &2 /\
     f face_of moi_lgb1_cell a r s /\ ~(f = moi_lgb1_cell a r s)
     ==> f IN ({r | r IN L /\ ~(r IN mv)} UNION
           {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) <= &1})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`;
                 `s:real^N->bool`] MOI_LGB1_CUT_CELL_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim (f:real^M->bool) <= &1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->bool`; `moi_lgb1_cell (a:real^M->real^N) r s`]
      FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`;
                 `s:real^N->bool`; `f:real^M->bool`] MOI_LGB1_CUT_CELL_FACE_IN) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  MAP_EVERY EXISTS_TAC [`r0:real^M->bool`; `s0:real^N->bool`] THEN
  ASM_MESON_TAC[]);;

let MOI_LGB1_CUT_L0_OUTSIDE = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) (H:(real^N->bool)->bool) u r s.
     moi_lgb1_cutsetup L mv a H /\ u IN ({r | r IN L /\ ~(r IN mv)} UNION
           {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) <= &1}) /\
     r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) = &2
     ==> u INTER moi_lgb1_cell a r s SUBSET relative_frontier (moi_lgb1_cell a r s)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`;
                 `s:real^N->bool`] MOI_LGB1_CUT_CELL_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
  DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `r1:real^M->bool` (X_CHOOSE_THEN `s1:real^N->bool`
      STRIP_ASSUME_TAC))) THENL
   [MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN
    MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                   `a:real^M->real^N`; `H:(real^N->bool)->bool`; `u:real^M->bool`;
                   `r:real^M->bool`; `s:real^N->bool`] MOI_LGB1_CUT_UNMOVED_INTER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `moi_lgb1_cutsetup (L:(real^M->bool)->bool) mv (a:real^M->real^N) H` THEN
    REWRITE_TAC[moi_lgb1_cutsetup; simplicial_complex] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(r:real^M->bool) IN L` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(u INTER r:real^M->bool) face_of r` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `u INTER r:real^M->bool = r` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`u INTER r:real^M->bool`; `r:real^M->bool`] FACE_OF_AFF_DIM_LT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
      SUBGOAL_THEN `aff_dim (moi_lgb1_cell (a:real^M->real^N) r s) <= aff_dim (u INTER r)`
      MP_TAC THENL
       [MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `aff_dim (r:real^M->bool) <= &2` MP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    UNDISCH_TAC `~((u:real^M->bool) IN mv)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (find_term ((=) `r':real^M->bool`)) (concl th) &&
      not (can (find_term ((=) `linear:(real^M->real^N)->bool`)) (concl th)) &&
      not (can (find_term ((=) `H:(real^N->bool)->bool`)) (concl th)))) THEN
    EXISTS_TAC `r:real^M->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `u:real^M->bool`)) THEN
    MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                   `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`;
                   `s:real^N->bool`; `r1:real^M->bool`; `s1:real^N->bool`]
      MOI_LGB1_CUT_CELL_INTER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_lgb1_cutsetup (L:(real^M->bool)->bool) mv (a:real^M->real^N) H` THEN
      REWRITE_TAC[moi_lgb1_cutsetup] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(ASSUME_TAC o ONCE_REWRITE_RULE[INTER_COMM]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `aff_dim (moi_lgb1_cell (a:real^M->real^N) r s) <=
                  aff_dim (moi_lgb1_cell a r1 s1)` MP_TAC THENL
     [MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

let MOI_LGB1_CUT_C2_OUTSIDE = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) (H:(real^N->bool)->bool) r s r' s'.
     moi_lgb1_cutsetup L mv a H /\ r IN mv /\ s IN H /\ r' IN mv /\ s' IN H /\
     aff_dim (moi_lgb1_cell a r s) = &2 /\ aff_dim (moi_lgb1_cell a r' s') = &2 /\
     ~(moi_lgb1_cell a r' s' = moi_lgb1_cell a r s)
     ==> moi_lgb1_cell a r' s' INTER moi_lgb1_cell a r s SUBSET
         relative_frontier (moi_lgb1_cell a r s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^M->bool) IN L /\ (r':real^M->bool) IN L` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_cutsetup (L:(real^M->bool)->bool) mv (a:real^M->real^N) H` THEN
    REWRITE_TAC[moi_lgb1_cutsetup] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r':real^M->bool`;
                 `s':real^N->bool`] MOI_LGB1_CUT_CELL_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(moi_lgb1_cell (a:real^M->real^N) r s INTER moi_lgb1_cell a r' s') face_of
    moi_lgb1_cell a r s /\
    (moi_lgb1_cell (a:real^M->real^N) r' s' INTER moi_lgb1_cell a r s) face_of
    moi_lgb1_cell a r' s'`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LGB1_CUT_CELL_INTER THEN
    MAP_EVERY EXISTS_TAC [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                          `H:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_lgb1_cell (a:real^M->real^N) r' s' INTER moi_lgb1_cell a r s =
                moi_lgb1_cell a r s INTER moi_lgb1_cell a r' s'` SUBST1_TAC THENL
   [REWRITE_TAC[INTER_COMM]; ALL_TAC] THEN
  MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  UNDISCH_TAC `(moi_lgb1_cell (a:real^M->real^N) r' s' INTER moi_lgb1_cell a r s)
               face_of moi_lgb1_cell a r' s'` THEN
  SUBGOAL_THEN `moi_lgb1_cell (a:real^M->real^N) r' s' INTER moi_lgb1_cell a r s =
                moi_lgb1_cell a r s` SUBST1_TAC THENL
   [ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`moi_lgb1_cell (a:real^M->real^N) r s`;
                 `moi_lgb1_cell (a:real^M->real^N) r' s'`] FACE_OF_AFF_DIM_LT) THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_LGB1_CUT_CONE_PIECE = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) (H:(real^N->bool)->bool) (b:(real^M->bool)->real^M) r s.
     moi_lgb1_cutsetup L mv a H /\ r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) = &2 /\
     b (moi_lgb1_cell a r s) IN relative_interior (moi_lgb1_cell a r s)
     ==> simplicial_complex
          ({f | f face_of moi_lgb1_cell a r s /\ ~(f = moi_lgb1_cell a r s)} UNION
           {convex hull (b (moi_lgb1_cell a r s) INSERT f) | f |
            f IN {f | f face_of moi_lgb1_cell a r s /\ ~(f = moi_lgb1_cell a r s)}}) /\
         UNIONS
          ({f | f face_of moi_lgb1_cell a r s /\ ~(f = moi_lgb1_cell a r s)} UNION
           {convex hull (b (moi_lgb1_cell a r s) INSERT f) | f |
            f IN {f | f face_of moi_lgb1_cell a r s /\ ~(f = moi_lgb1_cell a r s)}}) =
         moi_lgb1_cell a r s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`;
                 `s:real^N->bool`] MOI_LGB1_CUT_CELL_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `moi_lgb1_cell (a:real^M->real^N) r s` MOI_LGB1_BOUNDARY_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_LGB1_CONE_OVER_RF_GEN THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `moi_lgb1_cell (a:real^M->real^N) r s` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN STRIP_TAC THEN
  UNDISCH_TAC `aff_dim (moi_lgb1_cell (a:real^M->real^N) r s) = &2` THEN
  ASM_REWRITE_TAC[AFF_DIM_EMPTY; AFF_DIM_SING] THEN INT_ARITH_TAC);;

let MOI_LGB1_CUT_GLUE = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) (H:(real^N->bool)->bool) (b:(real^M->bool)->real^M).
     moi_lgb1_cutsetup L mv a H /\ (!p. p IN {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) = &2} ==> b p IN relative_interior p)
     ==> !D. FINITE D /\ D SUBSET {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) = &2}
             ==> simplicial_complex (({r | r IN L /\ ~(r IN mv)} UNION
           {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) <= &1}) UNION {convex hull (b p INSERT f) | p,f | p IN D /\ f face_of p /\ ~(f = p)}) /\
                 (!p u. p IN {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) = &2} /\ ~(p IN D) /\ u IN ({r | r IN L /\ ~(r IN mv)} UNION
           {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) <= &1}) UNION {convex hull (b p INSERT f) | p,f | p IN D /\ f face_of p /\ ~(f = p)}
                        ==> u INTER p SUBSET relative_frontier p)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bc")) THEN
  GEN_REWRITE_TAC BINDER_CONV [IMP_CONJ] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [SUBGOAL_THEN `{convex hull ((b:(real^M->bool)->real^M) p INSERT f) | p,f |
             p IN {} /\ f face_of p /\ ~(f = p)} = {}` SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; NOT_IN_EMPTY];
      ALL_TAC] THEN
    REWRITE_TAC[UNION_EMPTY; EMPTY_SUBSET; NOT_IN_EMPTY] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LGB1_CUT_L0_COMPLEX THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`p:real^M->bool`; `u:real^M->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `r:real^M->bool` (X_CHOOSE_THEN `s:real^N->bool`
      STRIP_ASSUME_TAC) o REWRITE_RULE[IN_ELIM_THM]) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LGB1_CUT_L0_OUTSIDE THEN
    MAP_EVERY EXISTS_TAC [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                          `H:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p0:real^M->bool`; `D:(real^M->bool)->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ih") STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[INSERT_SUBSET] THEN STRIP_TAC THEN
  USE_THEN "ih" (MP_TAC o C MATCH_MP (ASSUME `(D:(real^M->bool)->bool) SUBSET {moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
             aff_dim (moi_lgb1_cell a r s) = &2}`)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inv")) THEN
  UNDISCH_TAC `(p0:real^M->bool) IN {moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
             aff_dim (moi_lgb1_cell a r s) = &2}` THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real^M->bool` (X_CHOOSE_THEN `s0:real^N->bool`
    STRIP_ASSUME_TAC) o REWRITE_RULE[IN_ELIM_THM]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `p0:real^M->bool`)) THEN
  SUBGOAL_THEN `(moi_lgb1_cell (a:real^M->real^N) r0 s0) IN {moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
             aff_dim (moi_lgb1_cell a r s) = &2}` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(b:(real^M->bool)->real^M) (moi_lgb1_cell (a:real^M->real^N) r0 s0) IN relative_interior (moi_lgb1_cell (a:real^M->real^N) r0 s0)` ASSUME_TAC THENL
   [USE_THEN "bc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r0:real^M->bool`;
                 `s0:real^N->bool`] MOI_LGB1_CUT_CELL_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `b:(real^M->bool)->real^M`;
                 `r0:real^M->bool`; `s0:real^N->bool`] MOI_LGB1_CUT_CONE_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `{convex hull ((b:(real^M->bool)->real^M) p INSERT f) | p,f |
             p IN ((moi_lgb1_cell (a:real^M->real^N) r0 s0) INSERT D) /\ f face_of p /\ ~(f = p)} = {convex hull ((b:(real^M->bool)->real^M) p INSERT f) | p,f |
             p IN D /\ f face_of p /\ ~(f = p)} UNION {convex hull ((b:(real^M->bool)->real^M) (moi_lgb1_cell (a:real^M->real^N) r0 s0) INSERT f) | f | f IN {f | f face_of moi_lgb1_cell (a:real^M->real^N) r0 s0 /\ ~(f = moi_lgb1_cell (a:real^M->real^N) r0 s0)}}` SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^M->bool` THEN
    REWRITE_TAC[IN_UNION; IN_ELIM_THM; IN_INSERT] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f. f IN {f | f face_of moi_lgb1_cell (a:real^M->real^N) r0 s0 /\ ~(f = moi_lgb1_cell (a:real^M->real^N) r0 s0)} ==> f IN ({r | r IN (L:(real^M->bool)->bool) /\ ~(r IN mv)} UNION
           {moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
             aff_dim (moi_lgb1_cell a r s) <= &1})` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_LGB1_CUT_BOUNDARY_IN_L0 THEN
    MAP_EVERY EXISTS_TAC [`r0:real^M->bool`; `s0:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u. u IN {convex hull ((b:(real^M->bool)->real^M) (moi_lgb1_cell (a:real^M->real^N) r0 s0) INSERT f) | f | f IN {f | f face_of moi_lgb1_cell (a:real^M->real^N) r0 s0 /\ ~(f = moi_lgb1_cell (a:real^M->real^N) r0 s0)}} ==> u SUBSET moi_lgb1_cell (a:real^M->real^N) r0 s0` ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[INSERT_SUBSET] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; FACE_OF_IMP_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM UNION_ASSOC] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CON_GLUE_CONE THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(SET_RULE `(x:real^M->bool) IN s ==> x IN s UNION t`) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`f:real^M->bool`; `u:real^M->bool`] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_CON_CONE_INTER_OUTSIDE THEN EXISTS_TAC `moi_lgb1_cell (a:real^M->real^N) r0 s0` THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_CONVEX];
      MATCH_MP_TAC FACE_OF_SUBSET_RELATIVE_FRONTIER THEN ASM_REWRITE_TAC[];
      USE_THEN "inv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`p:real^M->bool`; `u:real^M->bool`] THEN
  REWRITE_TAC[IN_INSERT; DE_MORGAN_THM] THEN ONCE_REWRITE_TAC[IN_UNION] THEN
  STRIP_TAC THENL [USE_THEN "inv" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(moi_lgb1_cell (a:real^M->real^N) r0 s0) INTER p` THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(p:real^M->bool) IN {moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
             aff_dim (moi_lgb1_cell a r s) = &2}` THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` (X_CHOOSE_THEN `s:real^N->bool`
    STRIP_ASSUME_TAC) o REWRITE_RULE[IN_ELIM_THM]) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `p:real^M->bool`)) THEN
  MATCH_MP_TAC MOI_LGB1_CUT_C2_OUTSIDE THEN
  MAP_EVERY EXISTS_TAC [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                        `H:(real^N->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_LGB1_CUT_CONE_SUBSET = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) (H:(real^N->bool)->bool) (b:(real^M->bool)->real^M) p f.
     moi_lgb1_cutsetup L mv a H /\ (!p. p IN {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) = &2} ==> b p IN relative_interior p) /\ p IN {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) = &2} /\ f face_of p
     ==> convex hull (b p INSERT f) SUBSET p /\
         ?r s. r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) = &2 /\
               p = moi_lgb1_cell a r s /\ p SUBSET r /\ r IN L`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "bc")
    (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC))) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` (X_CHOOSE_THEN `s:real^N->bool`
    STRIP_ASSUME_TAC) o REWRITE_RULE[IN_ELIM_THM]) THEN
  FIRST_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `p:real^M->bool`)) THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`;
                 `s:real^N->bool`] MOI_LGB1_CUT_CELL_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!x:real^M. x IN relative_interior t /\ relative_interior t SUBSET t
                            ==> x IN t`) THEN
      REWRITE_TAC[RELATIVE_INTERIOR_SUBSET] THEN USE_THEN "bc" MATCH_MP_TAC THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
    MAP_EVERY EXISTS_TAC [`r:real^M->bool`; `s:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_lgb1_cutsetup (L:(real^M->bool)->bool) mv (a:real^M->real^N) H` THEN
    REWRITE_TAC[moi_lgb1_cutsetup] THEN ASM SET_TAC[]]);;

let MOI_LGB1_CUT_COMPLEX_GEN = prove
 (`!(L:(real^M->bool)->bool) mv (a:real^M->real^N) (H:(real^N->bool)->bool) (b:(real^M->bool)->real^M).
     moi_lgb1_cutsetup L mv a H /\ (!p. p IN {moi_lgb1_cell a r s | r,s | r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) = &2} ==> b p IN relative_interior p)
     ==> simplicial_complex (moi_lgb1_cut L mv a H b) /\
         UNIONS (moi_lgb1_cut L mv a H b) = UNIONS L /\
         (!t. t IN moi_lgb1_cut L mv a H b ==> ?r. r IN L /\ t SUBSET r) /\
         (!t. t IN moi_lgb1_cut L mv a H b
              ==> (t IN L /\ ~(t IN mv)) \/
                  ?r s. r IN mv /\ s IN H /\ t SUBSET moi_lgb1_cell a r s)`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "bc")) THEN
  SUBGOAL_THEN `moi_lgb1_cut (L:(real^M->bool)->bool) mv (a:real^M->real^N) (H:(real^N->bool)->bool) (b:(real^M->bool)->real^M) = ({r | r IN (L:(real^M->bool)->bool) /\ ~(r IN mv)} UNION
           {moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
             aff_dim (moi_lgb1_cell a r s) <= &1}) UNION {convex hull ((b:(real^M->bool)->real^M) p INSERT f) | p,f |
             p IN {moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
             aff_dim (moi_lgb1_cell a r s) = &2} /\ f face_of p /\ ~(f = p)}` SUBST1_TAC THENL
   [REWRITE_TAC[moi_lgb1_cut; UNION_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
             aff_dim (moi_lgb1_cell a r s) = &2}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                   `a:real^M->real^N`; `H:(real^N->bool)->bool`;
                   `\r s. aff_dim (moi_lgb1_cell (a:real^M->real^N) r s) = &2`]
      MOI_LGB1_CUT_CELLS_FINITE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `b:(real^M->bool)->real^M`]
    MOI_LGB1_CUT_GLUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `{moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
             aff_dim (moi_lgb1_cell a r s) = &2}`) THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  SUBGOAL_THEN
   `!t. t IN ({r | r IN (L:(real^M->bool)->bool) /\ ~(r IN mv)} UNION
           {moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
             aff_dim (moi_lgb1_cell a r s) <= &1}) UNION {convex hull ((b:(real^M->bool)->real^M) p INSERT f) | p,f |
             p IN {moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
             aff_dim (moi_lgb1_cell a r s) = &2} /\ f face_of p /\ ~(f = p)}
        ==> ?r s. r IN L /\ t SUBSET r /\
                  ((t IN L /\ ~(t IN mv)) \/
                   (r IN mv /\ s IN H /\ t SUBSET moi_lgb1_cell (a:real^M->real^N) r s))`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^M->bool` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`t:real^M->bool`; `ARB:real^N->bool`] THEN
      UNDISCH_TAC `(t:real^M->bool) IN {r | r IN L /\ ~(r IN mv)}` THEN
      REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[SUBSET_REFL];
      UNDISCH_TAC `(t:real^M->bool) IN {moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
                     aff_dim (moi_lgb1_cell a r s) <= &1}` THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` (X_CHOOSE_THEN `s:real^N->bool`
        STRIP_ASSUME_TAC) o REWRITE_RULE[IN_ELIM_THM]) THEN
      MAP_EVERY EXISTS_TAC [`r:real^M->bool`; `s:real^N->bool`] THEN
      ASM_REWRITE_TAC[SUBSET_REFL; MOI_LGB1_CELL_SUBSET] THEN
      UNDISCH_TAC `moi_lgb1_cutsetup (L:(real^M->bool)->bool) mv (a:real^M->real^N) H` THEN
      REWRITE_TAC[moi_lgb1_cutsetup] THEN ASM SET_TAC[];
      UNDISCH_TAC `(t:real^M->bool) IN {convex hull ((b:(real^M->bool)->real^M) p INSERT f) | p,f |
             p IN {moi_lgb1_cell (a:real^M->real^N) r s | r,s | r IN mv /\ s IN (H:(real^N->bool)->bool) /\
             aff_dim (moi_lgb1_cell a r s) = &2} /\ f face_of p /\ ~(f = p)}` THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^M->bool` (X_CHOOSE_THEN `f:real^M->bool`
        STRIP_ASSUME_TAC) o REWRITE_RULE[IN_ELIM_THM]) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `p:real^M->bool`)) THEN
      MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                     `a:real^M->real^N`; `H:(real^N->bool)->bool`;
                     `b:(real^M->bool)->real^M`; `moi_lgb1_cell (a:real^M->real^N) r s`;
                     `f:real^M->bool`] MOI_LGB1_CUT_CONE_SUBSET) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
        DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
      MAP_EVERY EXISTS_TAC [`r:real^M->bool`; `s:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(r:real^M->bool) IN L` ASSUME_TAC THENL
       [UNDISCH_TAC `moi_lgb1_cutsetup (L:(real^M->bool)->bool) mv (a:real^M->real^N) H` THEN
        REWRITE_TAC[moi_lgb1_cutsetup] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN MP_TAC(ISPECL [`a:real^M->real^N`; `r:real^M->bool`;
        `s:real^N->bool`] MOI_LGB1_CELL_SUBSET) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[]; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `x:real^M` THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^M->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(r:real^M->bool) IN mv` THENL
   [ALL_TAC;
    EXISTS_TAC `r:real^M->bool` THEN ASM_REWRITE_TAC[IN_UNION; IN_ELIM_THM]] THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN H /\ (a:real^M->real^N) x IN s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lgb1_cutsetup (L:(real^M->bool)->bool) mv (a:real^M->real^N) H` THEN
    REWRITE_TAC[moi_lgb1_cutsetup] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(a:real^M->real^N) x IN UNIONS H` MP_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^M) IN moi_lgb1_cell (a:real^M->real^N) r s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_lgb1_cell; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `r:real^M->bool`;
                 `s:real^N->bool`] MOI_LGB1_CUT_CELL_BASICS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `aff_dim (moi_lgb1_cell (a:real^M->real^N) r s) <= &1` THENL
   [EXISTS_TAC `moi_lgb1_cell (a:real^M->real^N) r s` THEN
    ASM_REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (moi_lgb1_cell (a:real^M->real^N) r s) = &2` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^M->bool)->bool`; `mv:(real^M->bool)->bool`;
                 `a:real^M->real^N`; `H:(real^N->bool)->bool`; `b:(real^M->bool)->real^M`;
                 `r:real^M->bool`; `s:real^N->bool`] MOI_LGB1_CUT_CONE_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN USE_THEN "bc" MATCH_MP_TAC THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  GEN_REWRITE_TAC LAND_CONV [EQ_SYM_EQ] THEN
  DISCH_THEN(fun th -> UNDISCH_TAC `(x:real^M) IN moi_lgb1_cell (a:real^M->real^N) r s` THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[IN_UNIONS; IN_UNION] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^M->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^M->bool` THEN ASM_REWRITE_TAC[] THENL
   [DISJ1_TAC THEN REWRITE_TAC[GSYM IN_UNION] THEN
    MATCH_MP_TAC MOI_LGB1_CUT_BOUNDARY_IN_L0 THEN
    MAP_EVERY EXISTS_TAC [`r:real^M->bool`; `s:real^N->bool`] THEN
    UNDISCH_TAC `(t:real^M->bool) IN
                 {f | f face_of moi_lgb1_cell (a:real^M->real^N) r s /\
                      ~(f = moi_lgb1_cell a r s)}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    DISJ2_TAC THEN
    UNDISCH_TAC `(t:real^M->bool) IN
                 {convex hull ((b:(real^M->bool)->real^M) (moi_lgb1_cell (a:real^M->real^N) r s)
                               INSERT f) | f |
                  f IN {f | f face_of moi_lgb1_cell a r s /\ ~(f = moi_lgb1_cell a r s)}}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^M->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`moi_lgb1_cell (a:real^M->real^N) r s`; `f:real^M->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MOI_LGB1_CUT_COMPLEX = prove
 (`!(L:(real^2->bool)->bool) mv (a:real^2->real^3) H b.
     simplicial_complex L /\ simplicial_complex H /\ mv SUBSET L /\
     (!r r'. r IN mv /\ r' IN L /\ r SUBSET r' ==> r' IN mv) /\
     (!r. r IN L /\ (?r'. r' IN mv /\ r SUBSET r')
          ==> ?l y. linear l /\ !x. x IN r ==> a x = l x + y) /\
     (!r x y. r IN mv /\ x IN r /\ y IN r /\ a x = a y ==> x = y) /\
     (!r. r IN mv ==> IMAGE a r SUBSET UNIONS H) /\
     (!r. r IN L /\ ~(r IN mv) /\ (?r'. r' IN mv /\ r SUBSET r')
          ==> ?s. s IN H /\ IMAGE a r SUBSET s) /\
     (!r s. r IN mv /\ s IN H /\ aff_dim (moi_lgb1_cell a r s) = &2
            ==> b (moi_lgb1_cell a r s) IN relative_interior (moi_lgb1_cell a r s))
     ==> simplicial_complex (moi_lgb1_cut L mv a H b) /\
         UNIONS (moi_lgb1_cut L mv a H b) = UNIONS L /\
         (!t. t IN moi_lgb1_cut L mv a H b ==> ?r. r IN L /\ t SUBSET r) /\
         (!t. t IN moi_lgb1_cut L mv a H b
              ==> (t IN L /\ ~(t IN mv)) \/
                  ?r s. r IN mv /\ s IN H /\ t SUBSET moi_lgb1_cell a r s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_LGB1_CUT_COMPLEX_GEN THEN
  ASM_REWRITE_TAC[moi_lgb1_cutsetup] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^2->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `r:real^2->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_2];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN ASM_MESON_TAC[]]);;

