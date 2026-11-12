(* ========================================================================= *)
(* pc_moi_bary: barycentres of simplices and the barycentric subdivision of  *)
(* (locally finite) simplicial complexes, for the Moise part of the          *)
(* development.  Sources: Moise GTM 47 Sec 7; Rourke-Sanderson Ch 2;         *)
(* Munkres, Elements of Algebraic Topology Sec 15.                           *)
(* ========================================================================= *)

needs "src/pc_moi_stmt.ml";;

prioritize_real();;
type_invention_error := true;;

let simplex_barycentre = new_definition
 `simplex_barycentre (s:real^N->bool) =
    inv(&(CARD {v:real^N | v extreme_point_of s})) %
    vsum {v | v extreme_point_of s} (\v. v)`;;

let barycentric_subdivision = new_definition
 `barycentric_subdivision (c:(real^N->bool)->bool) =
    {convex hull (IMAGE simplex_barycentre f) |
     f | f SUBSET c /\ FINITE f /\ ~({} IN f) /\
         (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)}`;;

(* ------------------------------------------------------------------------- *)
(* Auxiliary notions: chains of nonempty members of c (the index sets of the *)
(* barycentric subdivision) and the three conditions shared by HOL's         *)
(* simplicial_complex and lf_simplicial_complex (no finiteness).             *)
(* ------------------------------------------------------------------------- *)

let moi_bar_chain = new_definition
 `moi_bar_chain (c:(real^N->bool)->bool) (f:(real^N->bool)->bool) <=>
    f SUBSET c /\ FINITE f /\ ~({} IN f) /\
    (!s t. s IN f /\ t IN f ==> s SUBSET t \/ t SUBSET s)`;;

let moi_bar_complex = new_definition
 `moi_bar_complex (c:(real^N->bool)->bool) <=>
    (!s. s IN c ==> ?n. n simplex s) /\
    (!f s. s IN c /\ f face_of s ==> f IN c) /\
    (!s s'. s IN c /\ s' IN c
            ==> (s INTER s') face_of s /\ (s INTER s') face_of s')`;;

let MOI_BAR_IN_SUBDIVISION = prove
 (`!c s:real^N->bool.
        s IN barycentric_subdivision c <=>
        ?f. moi_bar_chain c f /\ s = convex hull (IMAGE simplex_barycentre f)`,
  REWRITE_TAC[barycentric_subdivision; moi_bar_chain; IN_ELIM_THM]);;

let MOI_BAR_SIMPLICIAL_COMPLEX = prove
 (`!c:(real^N->bool)->bool.
        simplicial_complex c <=> FINITE c /\ moi_bar_complex c`,
  REWRITE_TAC[simplicial_complex; moi_bar_complex]);;

let MOI_BAR_LF_SIMPLICIAL_COMPLEX = prove
 (`!c:(real^N->bool)->bool.
        lf_simplicial_complex c <=>
        moi_bar_complex c /\
        (!x. x IN UNIONS c
             ==> ?u. open u /\ x IN u /\
                     FINITE {s | s IN c /\ ~(s INTER u = {})})`,
  REWRITE_TAC[lf_simplicial_complex; moi_bar_complex; GSYM CONJ_ASSOC]);;

let MOI_BAR_COMPLEX_SIMPLEX = prove
 (`!c s:real^N->bool. moi_bar_complex c /\ s IN c ==> ?n. n simplex s`,
  SIMP_TAC[moi_bar_complex]);;

let MOI_BAR_COMPLEX_FACE = prove
 (`!c s t:real^N->bool.
        moi_bar_complex c /\ s IN c /\ t face_of s ==> t IN c`,
  MESON_TAC[moi_bar_complex]);;

let MOI_BAR_COMPLEX_INTER = prove
 (`!c s t:real^N->bool.
        moi_bar_complex c /\ s IN c /\ t IN c
        ==> (s INTER t) face_of s /\ (s INTER t) face_of t`,
  SIMP_TAC[moi_bar_complex]);;

(* ------------------------------------------------------------------------- *)
(* Barycentres of simplices.                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_BAR_SIMPLEX_BARYCENTRE_EQ = prove
 (`!s:real^N->bool.
        FINITE {v | v extreme_point_of s}
        ==> simplex_barycentre s = barycentre {v | v extreme_point_of s}`,
  SIMP_TAC[simplex_barycentre; barycentre; VSUM_LMUL]);;

let MOI_BAR_SIMPLEX_BARYCENTRE_HULL = prove
 (`!k:real^N->bool.
        ~affine_dependent k
        ==> simplex_barycentre (convex hull k) = barycentre k`,
  SIMP_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_EQ;
           EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
           AFFINE_INDEPENDENT_IMP_FINITE]);;

let SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR = prove
 (`!n s:real^N->bool.
     n simplex s /\ ~(s = {}) ==> simplex_barycentre s IN relative_interior s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM_SIMP_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_HULL] THEN
  MATCH_MP_TAC BARYCENTRE_IN_RELATIVE_INTERIOR THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_IMP_FINITE] THEN
  ASM_MESON_TAC[CONVEX_HULL_EMPTY]);;

let MOI_BAR_SIMPLEX_BARYCENTRE_IN = prove
 (`!n s:real^N->bool.
        n simplex s /\ ~(s = {}) ==> simplex_barycentre s IN s`,
  MESON_TAC[SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR; SUBSET;
            RELATIVE_INTERIOR_SUBSET]);;

(* The barycentre of a simplex avoids the affine hull of each proper face.  *)

let MOI_BAR_SIMPLEX_BARYCENTRE_NOT_IN_FACE = prove
 (`!n s t:real^N->bool.
        n simplex s /\ t face_of s /\ ~(t = s)
        ==> ~(simplex_barycentre s IN affine hull t)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `t:real^N->bool`]
    AFFINE_HULL_FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `simplex_barycentre(s:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
  EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[FACE_OF_EMPTY]);;

let MOI_BAR_SIMPLEX_BARYCENTRE_NOT_IN_FACE_ALT = prove
 (`!n s t:real^N->bool.
        n simplex s /\ t face_of s /\ ~(t = s)
        ==> ~(simplex_barycentre s IN t)`,
  MESON_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_NOT_IN_FACE; HULL_SUBSET; SUBSET]);;

(* ------------------------------------------------------------------------- *)
(* Chains: maxima, faces, injectivity of barycentres, affine independence.   *)
(* ------------------------------------------------------------------------- *)

let MOI_BAR_CHAIN_SUBSET = prove
 (`!c f g:(real^N->bool)->bool.
        moi_bar_chain c f /\ g SUBSET f ==> moi_bar_chain c g`,
  REWRITE_TAC[moi_bar_chain] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS];
    ASM_MESON_TAC[FINITE_SUBSET];
    ASM SET_TAC[];
    ASM_MESON_TAC[SUBSET]]);;

let MOI_BAR_CHAIN_MAX = prove
 (`!c f:(real^N->bool)->bool.
        moi_bar_chain c f /\ ~(f = {})
        ==> UNIONS f IN f /\ !t. t IN f ==> t SUBSET UNIONS f`,
  REWRITE_TAC[moi_bar_chain] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC UNIONS_IN_CHAIN THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]]);;

let MOI_BAR_COMPLEX_SUBSET_FACE = prove
 (`!c s t:real^N->bool.
        moi_bar_complex c /\ s IN c /\ t IN c /\ s SUBSET t ==> s face_of t`,
  REWRITE_TAC[moi_bar_complex] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s:real^N->bool = s INTER t` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[]]);;

let MOI_BAR_CHAIN_ELEMENT = prove
 (`!c f s:real^N->bool.
        moi_bar_complex c /\ moi_bar_chain c f /\ s IN f
        ==> s IN c /\ ~(s = {}) /\ (?n. n simplex s)`,
  REWRITE_TAC[moi_bar_complex; moi_bar_chain; SUBSET] THEN MESON_TAC[]);;

let MOI_BAR_CHAIN_FACE_OF_MAX = prove
 (`!c f s:real^N->bool.
        moi_bar_complex c /\ moi_bar_chain c f /\ s IN f
        ==> s face_of UNIONS f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
  ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]);;

let MOI_BAR_BARYCENTRE_INJ_SUBSET = prove
 (`!c s t:real^N->bool.
        moi_bar_complex c /\ s IN c /\ t IN c /\ ~(s = {}) /\ s SUBSET t /\
        simplex_barycentre s = simplex_barycentre t
        ==> s = t`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = t` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s:real^N->bool) face_of t` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_SUBSET_FACE]; ALL_TAC] THEN
  SUBGOAL_THEN `?m. m simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:int`; `t:real^N->bool`; `s:real^N->bool`]
    MOI_BAR_SIMPLEX_BARYCENTRE_NOT_IN_FACE_ALT) THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
    check (fun th -> can (find_term ((=) `simplex_barycentre:(real^N->bool)->real^N`)) (concl th))) THEN
  ASM_MESON_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_IN]);;

let MOI_BAR_CHAIN_BARYCENTRE_INJ = prove
 (`!c f s t:real^N->bool.
        moi_bar_complex c /\ moi_bar_chain c f /\ s IN f /\ t IN f /\
        simplex_barycentre s = simplex_barycentre t
        ==> s = t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET t \/ t SUBSET s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain];
    MATCH_MP_TAC MOI_BAR_BARYCENTRE_INJ_SUBSET THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_BAR_BARYCENTRE_INJ_SUBSET THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]]);;

let MOI_BAR_CHAIN_BARYCENTRE_IN = prove
 (`!c f s:real^N->bool.
        moi_bar_complex c /\ moi_bar_chain c f /\ s IN f
        ==> simplex_barycentre s IN s`,
  MESON_TAC[MOI_BAR_CHAIN_ELEMENT; MOI_BAR_SIMPLEX_BARYCENTRE_IN]);;

let MOI_BAR_CHAIN_IMAGE_SUBSET_MAX = prove
 (`!c f:(real^N->bool)->bool.
        moi_bar_complex c /\ moi_bar_chain c f
        ==> IMAGE simplex_barycentre f SUBSET UNIONS f`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_UNIONS] THEN
  ASM_MESON_TAC[MOI_BAR_CHAIN_BARYCENTRE_IN]);;

let MOI_BAR_CHAIN_HULL_SUBSET_MAX = prove
 (`!c f:(real^N->bool)->bool.
        moi_bar_complex c /\ moi_bar_chain c f /\ ~(f = {})
        ==> convex hull (IMAGE simplex_barycentre f) SUBSET UNIONS f`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_IMAGE_SUBSET_MAX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                 `UNIONS f:real^N->bool`] MOI_BAR_CHAIN_ELEMENT) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX]);;

let MOI_BAR_CHAIN_AFFINE_INDEPENDENT = prove
 (`!c f:(real^N->bool)->bool.
        moi_bar_complex c /\ moi_bar_chain c f
        ==> ~affine_dependent (IMAGE simplex_barycentre f)`,
  GEN_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `CARD(f:(real^N->bool)->bool)` THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; AFFINE_INDEPENDENT_EMPTY] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE(f:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE simplex_barycentre (f:(real^N->bool)->bool) =
    simplex_barycentre (UNIONS f) INSERT
    IMAGE simplex_barycentre (f DELETE UNIONS f)`
  SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
     [GSYM(MATCH_MP INSERT_DELETE th)]) THEN
    REWRITE_TAC[IMAGE_CLAUSES];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_bar_chain c ((f:(real^N->bool)->bool) DELETE UNIONS f)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[DELETE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC AFFINE_INDEPENDENT_INSERT THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP]) THEN
    ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[CARD_DELETE] THEN
    MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n - 1 < n`) THEN
    ASM_SIMP_TAC[CARD_EQ_0];
    ALL_TAC] THEN
  ASM_CASES_TAC `(f:(real^N->bool)->bool) DELETE UNIONS f = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; AFFINE_HULL_EMPTY; NOT_IN_EMPTY] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `(f:(real^N->bool)->bool) DELETE UNIONS f`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `affine hull (IMAGE simplex_barycentre (f DELETE UNIONS f)) SUBSET
    affine hull (UNIONS ((f:(real^N->bool)->bool) DELETE UNIONS f))`
  MP_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC MOI_BAR_CHAIN_IMAGE_SUBSET_MAX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `~((x:real^N) IN t) ==> s SUBSET t ==> ~(x IN s)`) THEN
  SUBGOAL_THEN `?n. n simplex (UNIONS f:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_NOT_IN_FACE THEN
  EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE]) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_BAR_CHAIN_FACE_OF_MAX THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_BAR_CHAIN_SIMPLEX = prove
 (`!c f:(real^N->bool)->bool.
        moi_bar_complex c /\ moi_bar_chain c f
        ==> (&(CARD f) - &1) simplex
            (convex hull (IMAGE simplex_barycentre f))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplex] THEN
  EXISTS_TAC `IMAGE simplex_barycentre (f:(real^N->bool)->bool)` THEN
  REWRITE_TAC[INT_ARITH `x - &1 + &1:int = x`; INT_OF_NUM_EQ] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_AFFINE_INDEPENDENT]; ALL_TAC] THEN
  MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_BARYCENTRE_INJ];
    ASM_MESON_TAC[moi_bar_chain]]);;

(* ------------------------------------------------------------------------- *)
(* Convex geometry: the relative interior of a cone over an affinely         *)
(* independent set, and uniqueness of the exit point of a ray from a         *)
(* relative interior point.                                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_BAR_RELATIVE_INTERIOR_INSERT = prove
 (`!a:real^N s x.
        ~affine_dependent (a INSERT s) /\ ~(a IN s) /\ ~(s = {}) /\
        x IN relative_interior (convex hull (a INSERT s))
        ==> ?u y. &0 < u /\ u < &1 /\
                  y IN relative_interior (convex hull s) /\
                  x = u % a + (&1 - u) % y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent(s:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
    EXISTS_TAC `(a:real^N) INSERT s` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE(s:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  UNDISCH_TAC
   `x IN relative_interior (convex hull ((a:real^N) INSERT s))` THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
  ASM_SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FORALL_IN_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < sum s (w:real^N->real)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_LT THEN ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN
    ASM_MESON_TAC[MEMBER_NOT_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < &1 - (w:real^N->real) a` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `(w:real^N->real) a` THEN
  EXISTS_TAC
   `inv(&1 - (w:real^N->real) a) % vsum s (\v:real^N. w v % v)` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC;
    EXISTS_TAC `\v:real^N. inv(&1 - (w:real^N->real) a) * w v` THEN
    REWRITE_TAC[SUM_LMUL; GSYM VECTOR_MUL_ASSOC; VSUM_LMUL] THEN
    ASM_SIMP_TAC[REAL_LT_MUL; REAL_LT_INV_EQ] THEN
    SUBGOAL_THEN `sum s (w:real^N->real) = &1 - w a` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ]];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
      check (fun th -> can (find_term ((=) `vsum:(real^N->bool)->(real^N->real^N)->real^N`)) (concl th))) THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID]]);;

let MOI_BAR_RAY_LT = prove
 (`!s a y z:real^N u v.
        convex s /\ a IN relative_interior s /\ z IN closure s /\
        ~(y IN relative_interior s) /\
        &0 <= u /\ u < v /\ v <= &1 /\
        u % a + (&1 - u) % y = v % a + (&1 - v) % z
        ==> F`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < &1 - u` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `(v - u) / (&1 - u)`; `z:real^N`;
                 `a:real^N`] IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; REAL_SUB_LT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `z - (v - u) / (&1 - u) % (z - a):real^N = y`
   (fun th -> ASM_REWRITE_TAC[th]) THEN
  SUBGOAL_THEN
   `(&1 - u) % (z - (v - u) / (&1 - u) % (z - a)) = (&1 - u) % (y:real^N)`
  MP_TAC THENL
   [REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_LT_IMP_NZ] THEN
    UNDISCH_TAC `u % a + (&1 - u) % y = v % a + (&1 - v) % (z:real^N)` THEN
    CONV_TAC VECTOR_ARITH;
    ASM_SIMP_TAC[VECTOR_MUL_LCANCEL; REAL_LT_IMP_NZ]]);;

let MOI_BAR_RAY_UNIQUE = prove
 (`!s a y z:real^N u v.
        convex s /\ a IN relative_interior s /\
        y IN closure s /\ z IN closure s /\
        ~(y IN relative_interior s) /\ ~(z IN relative_interior s) /\
        &0 <= u /\ u < &1 /\ &0 <= v /\ v < &1 /\
        u % a + (&1 - u) % y = v % a + (&1 - v) % z
        ==> u = v /\ y = z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `u:real = v` SUBST_ALL_TAC THENL
   [REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC
     (REAL_ARITH `u < v \/ v < u \/ u:real = v`) THEN
    ASM_REWRITE_TAC[] THENL
     [MATCH_MP_TAC(TAUT `F ==> p`) THEN
      MATCH_MP_TAC MOI_BAR_RAY_LT THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `a:real^N`; `y:real^N`;
                            `z:real^N`; `u:real`; `v:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      MATCH_MP_TAC MOI_BAR_RAY_LT THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `a:real^N`; `z:real^N`;
                            `y:real^N`; `v:real`; `u:real`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_LE]];
    REWRITE_TAC[] THEN
    UNDISCH_TAC `v % a + (&1 - v) % y = v % a + (&1 - v) % (z:real^N)` THEN
    REWRITE_TAC[VECTOR_ARITH `a + x:real^N = a + y <=> x = y`] THEN
    REWRITE_TAC[VECTOR_MUL_LCANCEL] THEN
    ASM_SIMP_TAC[REAL_ARITH `v < &1 ==> ~(&1 - v = &0)`]]);;

(* ------------------------------------------------------------------------- *)
(* Relative interiors of chain hulls.  The hull of the barycentres of a      *)
(* chain f with maximum m is the cone from the barycentre of m over the      *)
(* hull of the chain f DELETE m, which lies in a proper face of m.           *)
(* ------------------------------------------------------------------------- *)

let MOI_BAR_CHAIN_SING = prove
 (`!c f:(real^N->bool)->bool.
        moi_bar_chain c f /\ ~(f = {}) /\ f DELETE UNIONS f = {}
        ==> f = {UNIONS f}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `(m:real^N->bool) IN f /\ f DELETE m = {} ==> f = {m}`) THEN
  ASM_REWRITE_TAC[]);;

let MOI_BAR_CHAIN_IMAGE_INSERT = prove
 (`!c f:(real^N->bool)->bool.
        moi_bar_chain c f /\ ~(f = {})
        ==> IMAGE simplex_barycentre f =
            simplex_barycentre (UNIONS f) INSERT
            IMAGE simplex_barycentre (f DELETE UNIONS f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
   [GSYM(MATCH_MP INSERT_DELETE th)]) THEN
  REWRITE_TAC[IMAGE_CLAUSES]);;

let MOI_BAR_CHAIN_SPLIT = prove
 (`!c f:(real^N->bool)->bool x.
        moi_bar_complex c /\ moi_bar_chain c f /\
        ~(f DELETE UNIONS f = {}) /\
        x IN relative_interior (convex hull (IMAGE simplex_barycentre f))
        ==> ?u y. &0 < u /\ u < &1 /\
                  y IN relative_interior
                        (convex hull
                          (IMAGE simplex_barycentre (f DELETE UNIONS f))) /\
                  y IN UNIONS f /\ ~(y IN relative_interior (UNIONS f)) /\
                  x = u % simplex_barycentre (UNIONS f) + (&1 - u) % y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(f:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[EMPTY_DELETE]) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_bar_chain c ((f:(real^N->bool)->bool) DELETE UNIONS f)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[DELETE_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                 `(f:(real^N->bool)->bool) DELETE UNIONS f`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE]) THEN
  REWRITE_TAC[IN_DELETE] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`simplex_barycentre(UNIONS f:real^N->bool)`;
                 `IMAGE simplex_barycentre
                   ((f:(real^N->bool)->bool) DELETE UNIONS f)`;
                 `x:real^N`] MOI_BAR_RELATIVE_INTERIOR_INSERT) THEN
  ANTS_TAC THENL
   [SUBGOAL_THEN
     `simplex_barycentre (UNIONS f) INSERT
      IMAGE simplex_barycentre ((f:(real^N->bool)->bool) DELETE UNIONS f) =
      IMAGE simplex_barycentre f`
    SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_BAR_CHAIN_IMAGE_INSERT THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_AFFINE_INDEPENDENT]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~(t:real^N->bool = UNIONS f)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_BARYCENTRE_INJ THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`;
                          `f:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real` THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `y:real^N` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:real^N) IN UNIONS (f DELETE UNIONS f)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                   `(f:(real^N->bool)->bool) DELETE UNIONS f`]
      MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `convex hull (IMAGE simplex_barycentre
                   ((f:(real^N->bool)->bool) DELETE UNIONS f))`
      RELATIVE_INTERIOR_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS ((f:(real^N->bool)->bool) DELETE UNIONS f) face_of UNIONS f`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_FACE_OF_MAX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS ((f:(real^N->bool)->bool) DELETE UNIONS f)`;
                 `UNIONS (f:(real^N->bool)->bool)`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `(y:real^N) IN t ==> t INTER r = {} ==> ~(y IN r)`) THEN
  ASM_REWRITE_TAC[]);;

let MOI_BAR_CHAIN_SING_IMAGE = prove
 (`!c f:(real^N->bool)->bool.
        moi_bar_chain c f /\ ~(f = {}) /\ f DELETE UNIONS f = {}
        ==> IMAGE simplex_barycentre f = {simplex_barycentre (UNIONS f)}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_IMAGE_INSERT) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES]);;

let MOI_BAR_CHAIN_EMPTY_RI = prove
 (`!x:real^N.
        ~(x IN relative_interior (convex hull (IMAGE simplex_barycentre {})))`,
  REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; RELATIVE_INTERIOR_EMPTY;
              NOT_IN_EMPTY]);;

let MOI_BAR_CHAIN_RI_MAX = prove
 (`!c f:(real^N->bool)->bool x.
        moi_bar_complex c /\ moi_bar_chain c f /\
        x IN relative_interior (convex hull (IMAGE simplex_barycentre f))
        ==> x IN relative_interior (UNIONS f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_EMPTY_RI]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                 `UNIONS f:real^N->bool`] MOI_BAR_CHAIN_ELEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `n:int`))) THEN
  SUBGOAL_THEN
   `simplex_barycentre (UNIONS f:real^N->bool) IN
    relative_interior (UNIONS f)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(f:(real^N->bool)->bool) DELETE UNIONS f = {}` THENL
   [UNDISCH_TAC
     `x IN relative_interior
           (convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool)))` THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_SING_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[CONVEX_HULL_SING; RELATIVE_INTERIOR_SING; IN_SING] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                 `x:real^N`] MOI_BAR_CHAIN_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (is_var o lhs o concl)) THEN
  MP_TAC(ISPECL [`UNIONS f:real^N->bool`; `u:real`; `y:real^N`;
                 `simplex_barycentre(UNIONS f:real^N->bool)`]
    IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET];
      ASM_REAL_ARITH_TAC];
    MATCH_MP_TAC(SET_RULE `(x:real^N) = y ==> x IN s ==> y IN s`) THEN
    VECTOR_ARITH_TAC]);;

let MOI_BAR_CHAIN_RI_SAME_MAX = prove
 (`!c f g:(real^N->bool)->bool x.
        moi_bar_complex c /\ moi_bar_chain c f /\ moi_bar_chain c g /\
        x IN relative_interior (convex hull (IMAGE simplex_barycentre f)) /\
        x IN relative_interior (convex hull (IMAGE simplex_barycentre g))
        ==> UNIONS g = UNIONS f`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_EMPTY_RI]; ALL_TAC] THEN
  ASM_CASES_TAC `g:(real^N->bool)->bool = {}` THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_EMPTY_RI]; ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS f IN (c:(real^N->bool)->bool) /\ UNIONS g IN c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_MAX; MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`UNIONS g:real^N->bool`; `UNIONS f:real^N->bool`]
    CELL_COMPLEX_DISJOINT_RELATIVE_INTERIORS) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_INTER]; ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `x:real^N` THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_BAR_CHAIN_RI_MAX THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_BAR_CHAIN_RI_BARYCENTRE = prove
 (`!c g:(real^N->bool)->bool.
        moi_bar_complex c /\ moi_bar_chain c g /\ ~(g DELETE UNIONS g = {})
        ==> ~(simplex_barycentre (UNIONS g) IN
              relative_interior (convex hull (IMAGE simplex_barycentre g)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`;
                 `simplex_barycentre(UNIONS g:real^N->bool)`]
    MOI_BAR_CHAIN_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `z:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(&1 - v) % (z - simplex_barycentre (UNIONS g:real^N->bool)) = vec 0`
  MP_TAC THENL
   [UNDISCH_TAC
     `simplex_barycentre (UNIONS g:real^N->bool) =
      v % simplex_barycentre (UNIONS g) + (&1 - v) % z` THEN
    CONV_TAC VECTOR_ARITH;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
  ASM_SIMP_TAC[REAL_ARITH `v < &1 ==> ~(&1 - v = &0)`] THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC
   `~(simplex_barycentre (UNIONS g:real^N->bool) IN
      relative_interior (UNIONS g))` THEN
  REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[EMPTY_DELETE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`;
                 `UNIONS g:real^N->bool`] MOI_BAR_CHAIN_ELEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  MESON_TAC[SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR]);;

(* The open simplices of distinct chains are disjoint: a point determines     *)
(* the chain whose hull contains it in its relative interior.                 *)

let MOI_BAR_CHAIN_RI_UNIQUE = prove
 (`!c f g:(real^N->bool)->bool x.
        moi_bar_complex c /\ moi_bar_chain c f /\ moi_bar_chain c g /\
        x IN relative_interior (convex hull (IMAGE simplex_barycentre f)) /\
        x IN relative_interior (convex hull (IMAGE simplex_barycentre g))
        ==> f = g`,
  GEN_TAC THEN GEN_TAC THEN WF_INDUCT_TAC `CARD(f:(real^N->bool)->bool)` THEN
  MAP_EVERY X_GEN_TAC [`g:(real^N->bool)->bool`; `x:real^N`] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS g:real^N->bool = UNIONS f` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_RI_SAME_MAX THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_EMPTY_RI]; ALL_TAC] THEN
  ASM_CASES_TAC `g:(real^N->bool)->bool = {}` THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_EMPTY_RI]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(f:(real^N->bool)->bool) DELETE UNIONS f = {}` THEN
  ASM_CASES_TAC `(g:(real^N->bool)->bool) DELETE UNIONS g = {}` THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_SING) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_SING) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    SUBGOAL_THEN `x = simplex_barycentre(UNIONS f:real^N->bool)`
    ASSUME_TAC THENL
     [UNDISCH_TAC
       `x IN relative_interior
         (convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool)))` THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
        MOI_BAR_CHAIN_SING_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[CONVEX_HULL_SING; RELATIVE_INTERIOR_SING; IN_SING];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_RI_BARYCENTRE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    SUBGOAL_THEN `x = simplex_barycentre(UNIONS g:real^N->bool)`
    ASSUME_TAC THENL
     [UNDISCH_TAC
       `x IN relative_interior
         (convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool)))` THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
        MOI_BAR_CHAIN_SING_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[CONVEX_HULL_SING; RELATIVE_INTERIOR_SING; IN_SING] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_RI_BARYCENTRE) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                 `x:real^N`] MOI_BAR_CHAIN_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`;
                 `x:real^N`] MOI_BAR_CHAIN_SPLIT) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real` (X_CHOOSE_THEN `z:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                 `UNIONS f:real^N->bool`] MOI_BAR_CHAIN_ELEMENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_TAC `n:int`))) THEN
  MP_TAC(ISPECL [`UNIONS f:real^N->bool`;
                 `simplex_barycentre(UNIONS f:real^N->bool)`;
                 `y:real^N`; `z:real^N`; `u:real`; `v:real`]
    MOI_BAR_RAY_UNIQUE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
      EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET];
      ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET];
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[];
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[REAL_LT_IMP_LE];
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    DISCH_THEN(CONJUNCTS_THEN2 SUBST_ALL_TAC SUBST_ALL_TAC)] THEN
  SUBGOAL_THEN
   `(f:(real^N->bool)->bool) DELETE UNIONS f = g DELETE UNIONS g`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(f:(real^N->bool)->bool) DELETE UNIONS f`) THEN
    ANTS_TAC THENL
     [SUBGOAL_THEN `FINITE(f:(real^N->bool)->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_DELETE] THEN
      MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> n - 1 < n`) THEN
      ASM_SIMP_TAC[CARD_EQ_0];
      ALL_TAC] THEN
    DISCH_THEN MATCH_MP_TAC THEN EXISTS_TAC `z:real^N` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    ASM_MESON_TAC[DELETE_SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE
   `!m:real^N->bool. m IN f /\ m IN g /\ f DELETE m = g DELETE m ==> f = g`) THEN
  EXISTS_TAC `UNIONS f:real^N->bool` THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The barycentric subdivision is a complex: faces of chain hulls, and       *)
(* intersections of chain hulls                                              *)
(* (BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX).                             *)
(* ------------------------------------------------------------------------- *)

let MOI_BAR_CHAIN_HULL_RI = prove
 (`!c f:(real^N->bool)->bool x.
        moi_bar_complex c /\ moi_bar_chain c f /\
        x IN convex hull (IMAGE simplex_barycentre f)
        ==> ?g. g SUBSET f /\
                x IN relative_interior (convex hull (IMAGE simplex_barycentre g))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`convex hull (IMAGE simplex_barycentre
                                 (f:(real^N->bool)->bool))`; `x:real^N`]
    IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ASM_REWRITE_TAC[CONVEX_CONVEX_HULL] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`IMAGE simplex_barycentre (f:(real^N->bool)->bool)`;
                 `k:real^N->bool`] FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_AFFINE_INDEPENDENT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool`
    (CONJUNCTS_THEN2 MP_TAC SUBST_ALL_TAC)) THEN
  REWRITE_TAC[SUBSET_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_BAR_CHAIN_HULL_INTER = prove
 (`!c f g:(real^N->bool)->bool.
        moi_bar_complex c /\ moi_bar_chain c f /\ moi_bar_chain c g
        ==> convex hull (IMAGE simplex_barycentre f) INTER
            convex hull (IMAGE simplex_barycentre g) =
            convex hull (IMAGE simplex_barycentre (f INTER g))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                 `x:real^N`] MOI_BAR_CHAIN_HULL_RI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`;
                 `x:real^N`] MOI_BAR_CHAIN_HULL_RI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g':(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `f':(real^N->bool)->bool = g'` SUBST_ALL_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_RI_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE simplex_barycentre (g':(real^N->bool)->bool)) SUBSET
    convex hull (IMAGE simplex_barycentre (f INTER g))`
  MP_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[SUBSET_INTER];
    ALL_TAC] THEN
  MP_TAC(ISPEC `convex hull (IMAGE simplex_barycentre
                               (g':(real^N->bool)->bool))`
    RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC
   `x IN relative_interior
          (convex hull (IMAGE simplex_barycentre (g':(real^N->bool)->bool)))` THEN
  SET_TAC[]);;

let MOI_BAR_CHAIN_SUBCHAIN_FACE = prove
 (`!c f g:(real^N->bool)->bool.
        moi_bar_complex c /\ moi_bar_chain c f /\ g SUBSET f
        ==> convex hull (IMAGE simplex_barycentre g) face_of
            convex hull (IMAGE simplex_barycentre f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`IMAGE simplex_barycentre (f:(real^N->bool)->bool)`;
                 `convex hull (IMAGE simplex_barycentre
                                 (g:(real^N->bool)->bool))`]
    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_AFFINE_INDEPENDENT];
    DISCH_THEN SUBST1_TAC] THEN
  EXISTS_TAC `IMAGE simplex_barycentre (g:(real^N->bool)->bool)` THEN
  ASM_SIMP_TAC[IMAGE_SUBSET]);;

let MOI_BAR_SUBDIVISION_COMPLEX = prove
 (`!c:(real^N->bool)->bool.
        moi_bar_complex c ==> moi_bar_complex (barycentric_subdivision c)`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [moi_bar_complex] THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN REPEAT CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    EXISTS_TAC `&(CARD(f:(real^N->bool)->bool)) - &1:int` THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_SIMPLEX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `s:real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    UNDISCH_TAC
     `(t:real^N->bool) face_of
      convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
    MP_TAC(ISPECL [`IMAGE simplex_barycentre (f:(real^N->bool)->bool)`;
                   `t:real^N->bool`] FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_AFFINE_INDEPENDENT];
      DISCH_THEN SUBST1_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool`
      (CONJUNCTS_THEN2 MP_TAC SUBST1_TAC)) THEN
    REWRITE_TAC[SUBSET_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    EXISTS_TAC `g:(real^N->bool)->bool` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `f:(real^N->bool)->bool`
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))
     (X_CHOOSE_THEN `g:(real^N->bool)->bool`
       (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC))) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    CONJ_TAC THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET]]);;

let MOI_BAR_SUBDIVISION_FINITE = prove
 (`!c:(real^N->bool)->bool.
        FINITE c ==> FINITE (barycentric_subdivision c)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[barycentric_subdivision] THEN
  ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
  MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC `{f:(real^N->bool)->bool | f SUBSET c}` THEN
  ASM_SIMP_TAC[FINITE_POWERSET] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[]);;

let BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX = prove
 (`!c:(real^N->bool)->bool.
     simplicial_complex c ==> simplicial_complex (barycentric_subdivision c)`,
  SIMP_TAC[MOI_BAR_SIMPLICIAL_COMPLEX; MOI_BAR_SUBDIVISION_FINITE;
           MOI_BAR_SUBDIVISION_COMPLEX]);;

(* ------------------------------------------------------------------------- *)
(* Local finiteness (BARYCENTRIC_SUBDIVISION_LF).                            *)
(* ------------------------------------------------------------------------- *)

let MOI_BAR_UNIONS_SUBDIVISION_SUBSET = prove
 (`!c:(real^N->bool)->bool.
        moi_bar_complex c
        ==> UNIONS (barycentric_subdivision c) SUBSET UNIONS c`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; MOI_BAR_IN_SUBDIVISION] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
    (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
   [UNDISCH_TAC
     `(x:real^N) IN convex hull (IMAGE simplex_barycentre
                                   (f:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS f:real^N->bool` THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_MAX; MOI_BAR_CHAIN_ELEMENT];
    ASM_MESON_TAC[MOI_BAR_CHAIN_HULL_SUBSET_MAX; SUBSET]]);;

let MOI_BAR_SUBDIVISION_LOCALLY_FINITE = prove
 (`!c u:real^N->bool.
        moi_bar_complex c /\ FINITE {s | s IN c /\ ~(s INTER u = {})}
        ==> FINITE {t | t IN barycentric_subdivision c /\
                        ~(t INTER u = {})}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
  EXISTS_TAC
   `IMAGE (\f. convex hull (IMAGE simplex_barycentre f))
      {f:(real^N->bool)->bool |
       f SUBSET UNIONS (IMAGE (\s. {g | g face_of s})
                              {s | s IN c /\ ~(s INTER u = {})})}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_POWERSET THEN
    REWRITE_TAC[FINITE_UNIONS; FORALL_IN_IMAGE] THEN
    ASM_SIMP_TAC[FINITE_IMAGE] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX; FINITE_FACES_OF_SIMPLEX];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM; MOI_BAR_IN_SUBDIVISION; IN_IMAGE] THEN
  X_GEN_TAC `t:real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  EXISTS_TAC `f:(real^N->bool)->bool` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(f:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC
     `~(convex hull (IMAGE simplex_barycentre {}) INTER
        (u:real^N->bool) = {})` THEN
    REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; INTER_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `convex hull (IMAGE simplex_barycentre f) SUBSET
    UNIONS (f:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_HULL_SUBSET_MAX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `g:real^N->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN
  EXISTS_TAC `{h:real^N->bool | h face_of UNIONS f}` THEN CONJ_TAC THENL
   [EXISTS_TAC `UNIONS f:real^N->bool` THEN REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT];
      MATCH_MP_TAC(SET_RULE
       `!h:real^N->bool. ~(h INTER u = {}) /\ h SUBSET m
                         ==> ~(m INTER u = {})`) THEN
      EXISTS_TAC
       `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
      ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN MATCH_MP_TAC MOI_BAR_CHAIN_FACE_OF_MAX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

let BARYCENTRIC_SUBDIVISION_LF = prove
 (`!c:(real^N->bool)->bool.
     lf_simplicial_complex c ==> lf_simplicial_complex (barycentric_subdivision c)`,
  GEN_TAC THEN REWRITE_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_COMPLEX] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ANTS_TAC THENL
   [MP_TAC(ISPEC `c:(real^N->bool)->bool`
      MOI_BAR_UNIONS_SUBDIVISION_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN UNIONS (barycentric_subdivision c)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `u:real^N->bool` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_BAR_SUBDIVISION_LOCALLY_FINITE THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Covering: each point of a simplex lies in the hull of the barycentres of  *)
(* a chain of its nonempty faces (UNIONS_BARYCENTRIC_SUBDIVISION,            *)
(* BARYCENTRIC_SUBDIVISION_REFINES).                                         *)
(* ------------------------------------------------------------------------- *)

let MOI_BAR_RAY_EXIT = prove
 (`!s a x:real^N.
        convex s /\ bounded s /\ closed s /\
        a IN relative_interior s /\ x IN s /\ ~(x = a)
        ==> ?y t. y IN s /\ ~(y IN relative_interior s) /\
                  &0 < t /\ t <= &1 /\ x = (&1 - t) % a + t % y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `a:real^N`; `x - a:real^N`]
    RAY_TO_RELATIVE_FRONTIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_ARITH `a + (x - a):real^N = x`; VECTOR_SUB_EQ] THEN
    ASM_MESON_TAC[HULL_SUBSET; SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `a + d % (x - a) IN relative_frontier (s:real^N->bool)` THEN
  ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; IN_DIFF] THEN STRIP_TAC THEN
  SUBGOAL_THEN `&1 <= d` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM REAL_NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `&1 - d`; `x:real^N`; `a:real^N`]
      IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SHRINK) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[CLOSURE_CLOSED] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[VECTOR_ARITH
     `x - (&1 - d) % (x - a):real^N = a + d % (x - a)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `a + d % (x - a):real^N` THEN EXISTS_TAC `inv d` THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LT_INV THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC REAL_INV_LE_1 THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    SUBGOAL_THEN `inv d * d = &1` SUBST1_TAC THENL
     [MATCH_MP_TAC REAL_MUL_LINV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    VECTOR_ARITH_TAC]);;

let MOI_BAR_CHAIN_INSERT_TOP = prove
 (`!s u g:(real^N->bool)->bool.
        convex s /\ ~(s = {}) /\ u face_of s /\
        moi_bar_chain {t | t face_of u} g
        ==> moi_bar_chain {t | t face_of s} (s INSERT g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v:real^N->bool. v IN g ==> v face_of u` ASSUME_TAC THENL
   [UNDISCH_TAC `g SUBSET {t:real^N->bool | t face_of u}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N->bool. v IN g ==> v SUBSET s` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[INSERT_SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[FACE_OF_REFL];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[FACE_OF_TRANS]];
    ASM_REWRITE_TAC[FINITE_INSERT];
    REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[];
    REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[SUBSET_REFL]]);;

let MOI_BAR_SIMPLEX_COVERED = prove
 (`!n s x:real^N.
        n simplex s /\ x IN s
        ==> ?f. moi_bar_chain {t | t face_of s} f /\
                x IN convex hull (IMAGE simplex_barycentre f)`,
  SUBGOAL_THEN
   `!k n s x:real^N.
        n simplex s /\ n < &k /\ x IN s
        ==> ?f. moi_bar_chain {t | t face_of s} f /\
                x IN convex hull (IMAGE simplex_barycentre f)`
  ASSUME_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `dimindex(:N) + 1` THEN EXISTS_TAC `n:int` THEN
    ASM_REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
    MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_LE_UNIV) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `n:int`] AFF_DIM_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC] THEN
  INDUCT_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`n:int`; `s:real^N->bool`] SIMPLEX_DIM_GE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `n = -- &1:int` SUBST_ALL_TAC THENL
     [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    ASM_MESON_TAC[SIMPLEX_MINUS_1; NOT_IN_EMPTY];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) face_of s` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_REFL; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  ASM_CASES_TAC `x = simplex_barycentre(s:real^N->bool)` THENL
   [EXISTS_TAC `{s:real^N->bool}` THEN
    ASM_REWRITE_TAC[moi_bar_chain; IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING;
                    FINITE_SING; SING_SUBSET; IN_ELIM_THM] THEN
    MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `simplex_barycentre(s:real^N->bool)`;
                 `x:real^N`] MOI_BAR_RAY_EXIT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
      ASM_MESON_TAC[SIMPLEX_IMP_CLOSED];
      MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
      EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `t:real`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `y:real^N`]
    RELATIVE_BOUNDARY_POINT_IN_PROPER_FACE) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`n:int`; `s:real^N->bool`; `u:real^N->bool`]
    SIMPLEX_FACE_OF_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:int` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `m < n:int` ASSUME_TAC THENL
   [SUBGOAL_THEN `aff_dim(u:real^N->bool) < aff_dim(s:real^N->bool)`
    MP_TAC THENL
     [MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`u:real^N->bool`; `m:int`] AFF_DIM_SIMPLEX) THEN
    MP_TAC(ISPECL [`s:real^N->bool`; `n:int`] AFF_DIM_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`m:int`; `u:real^N->bool`; `y:real^N`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(n:int) < &(SUC k)` THEN UNDISCH_TAC `m:int < n` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `(s:real^N->bool) INSERT g` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_INSERT_TOP THEN
    EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES] THEN
  MATCH_MP_TAC IN_CONVEX_SET THEN
  ASM_SIMP_TAC[CONVEX_CONVEX_HULL; REAL_LT_IMP_LE] THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    UNDISCH_TAC
     `(y:real^N) IN convex hull (IMAGE simplex_barycentre
                                   (g:(real^N->bool)->bool))` THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (y:real^N) IN s ==> y IN t`) THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

let MOI_BAR_CHAIN_MONO = prove
 (`!c d f:(real^N->bool)->bool.
        moi_bar_chain c f /\ c SUBSET d ==> moi_bar_chain d f`,
  REWRITE_TAC[moi_bar_chain] THEN MESON_TAC[SUBSET_TRANS]);;

let MOI_BAR_FACES_SUBSET_COMPLEX = prove
 (`!c s:real^N->bool.
        moi_bar_complex c /\ s IN c ==> {t | t face_of s} SUBSET c`,
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[MOI_BAR_COMPLEX_FACE]);;

let MOI_BAR_FACE_CHAIN_HULL_SUBSET = prove
 (`!n t f:(real^N->bool)->bool.
        n simplex t /\ moi_bar_chain {u | u face_of t} f
        ==> convex hull (IMAGE simplex_barycentre f) SUBSET t`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
   [ALL_TAC; ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `v:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(v:real^N->bool) face_of t /\ ~(v = {})` STRIP_ASSUME_TAC
  THENL
   [UNDISCH_TAC `moi_bar_chain {u:real^N->bool | u face_of t} f` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:int`; `t:real^N->bool`; `v:real^N->bool`]
    SIMPLEX_FACE_OF_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `m:int` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m:int`; `v:real^N->bool`] MOI_BAR_SIMPLEX_BARYCENTRE_IN) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]);;

let MOI_BAR_UNIONS_SUBDIVISION = prove
 (`!c:(real^N->bool)->bool.
        moi_bar_complex c ==> UNIONS (barycentric_subdivision c) = UNIONS c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  ASM_SIMP_TAC[MOI_BAR_UNIONS_SUBDIVISION_SUBSET] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:int`; `s:real^N->bool`; `x:real^N`]
    MOI_BAR_SIMPLEX_COVERED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))` THEN
  ASM_REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  EXISTS_TAC `f:(real^N->bool)->bool` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
  EXISTS_TAC `{t:real^N->bool | t face_of s}` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_BAR_FACES_SUBSET_COMPLEX THEN ASM_REWRITE_TAC[]);;

let UNIONS_BARYCENTRIC_SUBDIVISION = prove
 (`!c:(real^N->bool)->bool.
     lf_simplicial_complex c ==> UNIONS (barycentric_subdivision c) = UNIONS c`,
  SIMP_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX; MOI_BAR_UNIONS_SUBDIVISION]);;

let BARYCENTRIC_SUBDIVISION_REFINES = prove
 (`!c:(real^N->bool)->bool.
     lf_simplicial_complex c
     ==> (!s. s IN barycentric_subdivision c /\ ~(s = {})
              ==> ?t. t IN c /\ s SUBSET t) /\
         (!t. t IN c ==> ?f. f SUBSET barycentric_subdivision c /\ t = UNIONS f)`,
  GEN_TAC THEN REWRITE_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    ASM_CASES_TAC `f:(real^N->bool)->bool = {}` THENL
     [UNDISCH_TAC
       `~(convex hull (IMAGE simplex_barycentre
                         (f:(real^N->bool)->bool)) = {})` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY];
      ALL_TAC] THEN
    EXISTS_TAC `UNIONS f:real^N->bool` THEN CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_MAX; MOI_BAR_CHAIN_ELEMENT];
      MATCH_MP_TAC MOI_BAR_CHAIN_HULL_SUBSET_MAX THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
  EXISTS_TAC `{convex hull (IMAGE simplex_barycentre f) |
               f | moi_bar_chain {u:real^N->bool | u face_of t} f}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; MOI_BAR_IN_SUBDIVISION] THEN
    X_GEN_TAC `f:(real^N->bool)->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
    EXISTS_TAC `{u:real^N->bool | u face_of t}` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_FACES_SUBSET_COMPLEX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`n:int`; `t:real^N->bool`; `x:real^N`]
      MOI_BAR_SIMPLEX_COVERED) THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `f:(real^N->bool)->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_BAR_FACE_CHAIN_HULL_SUBSET THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Vertices of the subdivision (BARYCENTRIC_SUBDIVISION_VERTICES).           *)
(* ------------------------------------------------------------------------- *)

let MOI_BAR_SUBDIVISION_VERTICES = prove
 (`!c:(real^N->bool)->bool.
        moi_bar_complex c
        ==> {v | {v} IN barycentric_subdivision c} =
            {simplex_barycentre s | s IN c /\ ~(s = {})}`,
  REPEAT STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `v:real^N` THEN
  REWRITE_TAC[IN_ELIM_THM; MOI_BAR_IN_SUBDIVISION] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `IMAGE simplex_barycentre (f:(real^N->bool)->bool) = {v:real^N}`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[CONVEX_HULL_EQ_SING]; ALL_TAC] THEN
    SUBGOAL_THEN `?s:real^N->bool. s IN f` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC
       `IMAGE simplex_barycentre ({}:(real^N->bool)->bool) = {v:real^N}` THEN
      REWRITE_TAC[IMAGE_CLAUSES] THEN SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `s:real^N->bool` THEN
    SUBGOAL_THEN `simplex_barycentre (s:real^N->bool) IN {v:real^N}`
    MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (is_eq o concl) o
        check (fun th -> can (find_term ((=) `IMAGE:((real^N->bool)->real^N)->((real^N->bool)->bool)->real^N->bool`)) (concl th))) THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]];
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{s:real^N->bool}` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; moi_bar_chain;
                    SING_SUBSET; FINITE_SING; IN_SING] THEN
    MESON_TAC[SUBSET_REFL]]);;

let BARYCENTRIC_SUBDIVISION_VERTICES = prove
 (`!c:(real^N->bool)->bool.
     lf_simplicial_complex c
     ==> {v | {v} IN barycentric_subdivision c} =
         {simplex_barycentre s | s IN c /\ ~(s = {})}`,
  SIMP_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX; MOI_BAR_SUBDIVISION_VERTICES]);;

(* ------------------------------------------------------------------------- *)
(* The mesh bound (BARYCENTRIC_SUBDIVISION_MESH): the barycentre of a face u *)
(* of a k-simplex s lies within k / (k + 1) times diameter s of the          *)
(* barycentre of s.                                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_BAR_BARYCENTRE_VERTEX_DIST = prove
 (`!k v w:real^N.
        FINITE v /\ CARD v = k + 1 /\ w IN v
        ==> norm(w - barycentre v) <= &k / (&k + &1) * diameter v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `w - barycentre v = vsum v (\x:real^N. inv(&k + &1) % (w - x))`
  SUBST1_TAC THENL
   [ASM_SIMP_TAC[barycentre; VSUM_LMUL; VSUM_SUB; VSUM_CONST] THEN
    REWRITE_TAC[GSYM REAL_OF_NUM_ADD] THEN
    REWRITE_TAC[VECTOR_SUB_LDISTRIB; VECTOR_MUL_ASSOC] THEN
    SIMP_TAC[REAL_MUL_LINV; REAL_ARITH `~(&k + &1 = &0)`] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `sum v (\x:real^N. norm(w - x)) <= &k * diameter v`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\x:real^N. norm(w - x)`; `v:real^N->bool`; `w:real^N`]
      SUM_DELETE) THEN
    ASM_REWRITE_TAC[VECTOR_SUB_REFL; NORM_0; REAL_SUB_RZERO] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `CARD(v DELETE (w:real^N)) = k` (SUBST1_TAC o SYM) THENL
     [ASM_SIMP_TAC[CARD_DELETE] THEN ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC SUM_BOUND THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
    ASM_SIMP_TAC[FINITE_IMP_BOUNDED];
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `sum v (\x:real^N. norm(inv(&k + &1) % (w - x)))` THEN
  ASM_SIMP_TAC[VSUM_NORM] THEN
  REWRITE_TAC[NORM_MUL; SUM_LMUL] THEN
  SUBGOAL_THEN `abs(inv(&k + &1)) = inv(&k + &1)` SUBST1_TAC THENL
   [REWRITE_TAC[REAL_ABS_REFL; REAL_LE_INV_EQ] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `&k / (&k + &1) * diameter(v:real^N->bool) =
    inv(&k + &1) * (&k * diameter v)`
  SUBST1_TAC THENL
   [REWRITE_TAC[real_div] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[REAL_LE_INV_EQ] THEN
  REAL_ARITH_TAC);;

let MOI_BAR_BARYCENTRE_HULL_DIST = prove
 (`!k v y:real^N.
        FINITE v /\ CARD v = k + 1 /\ y IN convex hull v
        ==> norm(y - barycentre v) <= &k / (&k + &1) * diameter v`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `convex hull v SUBSET
    cball(barycentre v:real^N, &k / (&k + &1) * diameter v)`
  MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN REWRITE_TAC[CONVEX_CBALL] THEN
    REWRITE_TAC[SUBSET; IN_CBALL] THEN REPEAT STRIP_TAC THEN
    ONCE_REWRITE_TAC[DIST_SYM] THEN REWRITE_TAC[dist] THEN
    MATCH_MP_TAC MOI_BAR_BARYCENTRE_VERTEX_DIST THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_CBALL; dist] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NORM_SUB]]);;

let MOI_BAR_DIST_BARYCENTRE_FACE = prove
 (`!k s u:real^N->bool.
        &k simplex s /\ u face_of s /\ ~(u = {})
        ==> dist(simplex_barycentre u, simplex_barycentre s) <=
            &k / (&k + &1) * diameter s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `s = convex hull (v:real^N->bool)` THEN
  DISCH_THEN SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[INT_OF_NUM_ADD; INT_OF_NUM_EQ]) THEN
  SUBGOAL_THEN `FINITE(v:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^N->bool`; `u:real^N->bool`]
    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `~affine_dependent(w:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_HULL; DIAMETER_CONVEX_HULL] THEN
  REWRITE_TAC[dist] THEN MATCH_MP_TAC MOI_BAR_BARYCENTRE_HULL_DIST THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `barycentre w IN convex hull (w:real^N->bool)` MP_TAC THENL
   [MATCH_MP_TAC BARYCENTRE_IN_CONVEX_HULL THEN
    CONJ_TAC THENL [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^N) IN s ==> x IN t`) THEN
  MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]);;

let MOI_BAR_SIMPLEX_NUM = prove
 (`!n s:real^N->bool.
        n simplex s /\ ~(s = {}) ==> ?k. &k simplex s /\ aff_dim s = &k`,
  REPEAT STRIP_TAC THEN EXISTS_TAC `num_of_int n` THEN
  SUBGOAL_THEN `&0 <= n:int` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:int`; `s:real^N->bool`] SIMPLEX_DIM_GE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(n = -- &1:int)` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[SIMPLEX_MINUS_1];
      INT_ARITH_TAC];
    ASM_SIMP_TAC[INT_OF_NUM_OF_INT] THEN ASM_MESON_TAC[AFF_DIM_SIMPLEX]]);;

let MOI_BAR_RATIO_MONO = prove
 (`!k d. k <= d ==> &k / (&k + &1) <= &d / (&d + &1)`,
  REPEAT STRIP_TAC THEN
  SIMP_TAC[RAT_LEMMA4; REAL_ARITH `&0 < &n + &1`] THEN
  UNDISCH_TAC `k:num <= d` THEN REWRITE_TAC[GSYM REAL_OF_NUM_LE] THEN
  REAL_ARITH_TAC);;

let MOI_BAR_CHAIN_DIAMETER = prove
 (`!c f:(real^N->bool)->bool d r.
        moi_bar_complex c /\ moi_bar_chain c f /\ &0 <= r /\
        (!s. s IN f ==> aff_dim s <= &d /\ diameter s <= r)
        ==> diameter (convex hull (IMAGE simplex_barycentre f)) <=
            &d / (&d + &1) * r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[DIAMETER_CONVEX_HULL] THEN
  MATCH_MP_TAC DIAMETER_LE THEN CONJ_TAC THENL
   [DISJ2_TAC THEN MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_IMAGE_2] THEN
  SUBGOAL_THEN
   `!s t:real^N->bool.
        s IN f /\ t IN f /\ s SUBSET t
        ==> norm(simplex_barycentre s - simplex_barycentre t) <=
            &d / (&d + &1) * r`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `t:real^N->bool`] MOI_BAR_CHAIN_ELEMENT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_TAC `n:int`))) THEN
    MP_TAC(ISPECL [`n:int`; `t:real^N->bool`] MOI_BAR_SIMPLEX_NUM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`k:num`; `t:real^N->bool`; `s:real^N->bool`]
      MOI_BAR_DIST_BARYCENTRE_FACE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
        EXISTS_TAC `c:(real^N->bool)->bool` THEN
        ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT];
        ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]];
      ALL_TAC] THEN
    REWRITE_TAC[dist] THEN
    MATCH_MP_TAC(REAL_ARITH `b <= c ==> a <= b ==> a <= c`) THEN
    MATCH_MP_TAC REAL_LE_MUL2 THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_DIV THEN REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_BAR_RATIO_MONO THEN
      REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC DIAMETER_POS_LE THEN
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `t:real^N->bool`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET t \/ t SUBSET s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain];
    ASM_SIMP_TAC[];
    ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_SIMP_TAC[]]);;

let MOI_BAR_SUBDIVISION_MESH = prove
 (`!(c:(real^N->bool)->bool) d r.
        moi_bar_complex c /\ &0 <= r /\
        (!s. s IN c ==> aff_dim s <= &d /\ diameter s <= r)
        ==> !s. s IN barycentric_subdivision c
                ==> diameter s <= &d / (&d + &1) * r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  X_GEN_TAC `s:real^N->bool` THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
  MATCH_MP_TAC MOI_BAR_CHAIN_DIAMETER THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[moi_bar_chain; SUBSET]);;

let BARYCENTRIC_SUBDIVISION_MESH = prove
 (`!(c:(real^N->bool)->bool) d r.
     lf_simplicial_complex c /\ &0 <= r /\
     (!s. s IN c ==> aff_dim s <= &d /\ diameter s <= r)
     ==> !s. s IN barycentric_subdivision c ==> diameter s <= &d / (&d + &1) * r`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_BAR_LF_SIMPLICIAL_COMPLEX] THEN
  STRIP_TAC THEN MATCH_MP_TAC MOI_BAR_SUBDIVISION_MESH THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Iterated subdivisions become arbitrarily fine                             *)
(* (ITERATED_BARYCENTRIC_SUBDIVISION_FINE).                                  *)
(* ------------------------------------------------------------------------- *)

let MOI_BAR_ITER_SUBDIVISION = prove
 (`!c:(real^N->bool)->bool.
        simplicial_complex c
        ==> !n. simplicial_complex (ITER n barycentric_subdivision c) /\
                !s. s IN ITER n barycentric_subdivision c
                    ==> diameter s <=
                        (&(dimindex(:N)) / (&(dimindex(:N)) + &1)) pow n *
                        diameter(UNIONS c)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `bounded(UNIONS (c:(real^N->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC BOUNDED_UNIONS THEN
    RULE_ASSUM_TAC(REWRITE_RULE[simplicial_complex]) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  INDUCT_TAC THEN REWRITE_TAC[ITER; real_pow; REAL_MUL_LID] THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC DIAMETER_SUBSET THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
     `(s:real^N->bool) IN c ==> s SUBSET UNIONS c`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX] THEN
  REWRITE_TAC[GSYM REAL_MUL_ASSOC] THEN
  MATCH_MP_TAC MOI_BAR_SUBDIVISION_MESH THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_SIMPLICIAL_COMPLEX];
    MATCH_MP_TAC REAL_LE_MUL THEN ASM_SIMP_TAC[DIAMETER_POS_LE] THEN
    MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
    REAL_ARITH_TAC;
    ASM_SIMP_TAC[AFF_DIM_LE_UNIV]]);;

let ITERATED_BARYCENTRIC_SUBDIVISION_FINE = prove
 (`!(c:(real^N->bool)->bool) e.
     simplicial_complex c /\ &0 < e
     ==> ?n. !s. s IN ITER n barycentric_subdivision c ==> diameter s < e`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_BAR_ITER_SUBDIVISION) THEN
  SUBGOAL_THEN `&0 <= diameter(UNIONS (c:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC DIAMETER_POS_LE THEN MATCH_MP_TAC BOUNDED_UNIONS THEN
    RULE_ASSUM_TAC(REWRITE_RULE[simplicial_complex]) THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&(dimindex(:N)) / (&(dimindex(:N)) + &1)`;
                 `e / (diameter(UNIONS (c:(real^N->bool)->bool)) + &1)`]
    REAL_ARCH_POW_INV) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      SIMP_TAC[REAL_LT_LDIV_EQ; REAL_ARITH `&0 < &n + &1`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT2 o
    SPEC `n:num`) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(REAL_ARITH `b < e ==> a <= b ==> a < e`) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `(&(dimindex(:N)) / (&(dimindex(:N)) + &1)) pow n *
              (diameter(UNIONS (c:(real^N->bool)->bool)) + &1)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_LMUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_POW_LE THEN MATCH_MP_TAC REAL_LE_DIV THEN
      REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ASM_SIMP_TAC[GSYM REAL_LT_RDIV_EQ;
                 REAL_ARITH `&0 <= r ==> &0 < r + &1`]]);;

