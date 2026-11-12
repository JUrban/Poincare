(* ========================================================================= *)
(* pc_moi_cone: cones over simplicial complexes, conewise extension of PL    *)
(* homeomorphisms of simplex boundaries, cones over PL spheres, and the      *)
(* relative subdivision of Moise GTM 47, proof of Thm 8.2 (p.59).           *)
(* ========================================================================= *)

needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_real.ml";;
needs "src/pc_moi_bary.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* 1. Cones from a point v over sets whose segments from v meet them only    *)
(* at their ends (the segment condition).                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_CON_NOT_IN_AFFINE_HULL = prove
 (`!s (v:real^N).
        convex s /\ bounded s /\ ~(s = {}) /\ ~(v IN s) /\
        (!x y. x IN s /\ y IN s /\ y IN segment[v,x] ==> y = x)
        ==> ~(v IN affine hull s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?x:real^N. x IN relative_interior s` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEMBER_NOT_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(v:real^N = x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `x:real^N`; `v - x:real^N`]
    RAY_TO_RELATIVE_FRONTIER) THEN
  ASM_REWRITE_TAC[VECTOR_ARITH `x + (v - x):real^N = v`; VECTOR_SUB_EQ] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (MP_TAC o SPEC `min (d / &2) (&1)` o CONJUNCT2))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL
   [`x:real^N`; `x + min (d / &2) (&1) % (v - x):real^N`]) THEN
  ASM_REWRITE_TAC[NOT_IMP] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `&1 - min (d / &2) (&1)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[VECTOR_ARITH `x + c % (v - x):real^N = x <=> c % (v - x) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN ASM_REAL_ARITH_TAC]);;

let MOI_CON_CONE_SIMPLEX = prove
 (`!s (v:real^N) n.
        n simplex s /\ ~(v IN affine hull s)
        ==> (n + &1) simplex (convex hull (v INSERT s))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN DISCH_TAC THEN
  EXISTS_TAC `(v:real^N) INSERT c` THEN
  SUBGOAL_THEN `FINITE (c:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN c)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_INSERT; CARD_CLAUSES] THEN
  REWRITE_TAC[GSYM HULL_INSERT] THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_SUC]);;

let MOI_CON_CONE_FACES = prove
 (`!s (v:real^N) n f.
        n simplex s /\ ~(v IN affine hull s) /\
        f face_of convex hull (v INSERT s)
        ==> f face_of s \/ ?g. g face_of s /\ f = convex hull (v INSERT g)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[AFFINE_HULL_CONVEX_HULL; GSYM HULL_INSERT] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent ((v:real^N) INSERT c)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFFINE_INDEPENDENT_INSERT]; ALL_TAC] THEN
  UNDISCH_TAC `f face_of convex hull ((v:real^N) INSERT c)` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(v:real^N) IN d` THENL
   [DISJ2_TAC THEN EXISTS_TAC `convex hull (d DELETE (v:real^N))` THEN
    CONJ_TAC THENL
     [EXISTS_TAC `d DELETE (v:real^N)` THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[GSYM HULL_INSERT] THEN AP_TERM_TAC THEN ASM SET_TAC[]];
    DISJ1_TAC THEN EXISTS_TAC `d:real^N->bool` THEN ASM SET_TAC[]]);;

let MOI_CON_CONE_FACE_OF = prove
 (`!s (v:real^N) n g.
        n simplex s /\ ~(v IN affine hull s) /\ g face_of s
        ==> convex hull (v INSERT g) face_of convex hull (v INSERT s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent ((v:real^N) INSERT c)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFFINE_INDEPENDENT_INSERT]; ALL_TAC] THEN
  UNDISCH_TAC `g face_of convex hull (c:real^N->bool)` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[GSYM HULL_INSERT] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  EXISTS_TAC `(v:real^N) INSERT d` THEN ASM SET_TAC[]);;

let MOI_CON_BASE_FACE_OF = prove
 (`!s (v:real^N) n.
        n simplex s /\ ~(v IN affine hull s)
        ==> s face_of convex hull (v INSERT s)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) MP_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  REWRITE_TAC[AFFINE_HULL_CONVEX_HULL] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~affine_dependent ((v:real^N) INSERT c)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFFINE_INDEPENDENT_INSERT]; ALL_TAC] THEN
  REWRITE_TAC[GSYM HULL_INSERT] THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  EXISTS_TAC `c:real^N->bool` THEN SET_TAC[]);;

let MOI_CON_SEGMENT_RAY = prove
 (`!v x y z:real^N.
        x IN segment[v,y] /\ x IN segment[v,z] /\ ~(x = v)
        ==> y IN segment[v,z] \/ z IN segment[v,y]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `a:real` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(a = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(x:real^N = v)` THEN
    UNDISCH_TAC `x:real^N = (&1 - &0) % v + &0 % y` THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(b = &0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(x:real^N = v)` THEN
    UNDISCH_TAC `x:real^N = (&1 - &0) % v + &0 % z` THEN
    DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - a) % v + a % y:real^N = (&1 - b) % v + b % z`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `a <= b` THENL
   [DISJ2_TAC THEN EXISTS_TAC `a / b` THEN
    SUBGOAL_THEN `&0 < b` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    SUBGOAL_THEN `b % z:real^N = b % ((&1 - a / b) % v + (a / b) % y)`
    MP_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN
      UNDISCH_TAC `(&1 - a) % v + a % y:real^N = (&1 - b) % v + b % z` THEN
      VECTOR_ARITH_TAC;
      ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL]];
    DISJ1_TAC THEN EXISTS_TAC `b / a` THEN
    SUBGOAL_THEN `&0 < a` ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LE_LDIV_EQ; REAL_MUL_LID] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `a % y:real^N = a % ((&1 - b / a) % v + (b / a) % z)`
    MP_TAC THENL
     [REWRITE_TAC[VECTOR_ADD_LDISTRIB; VECTOR_MUL_ASSOC] THEN
      ASM_SIMP_TAC[REAL_DIV_LMUL; REAL_SUB_LDISTRIB; REAL_MUL_RID] THEN
      UNDISCH_TAC `(&1 - a) % v + a % y:real^N = (&1 - b) % v + b % z` THEN
      VECTOR_ARITH_TAC;
      ASM_REWRITE_TAC[VECTOR_MUL_LCANCEL]]]);;

let MOI_CON_CONE_INTER = prove
 (`!a (v:real^N) s t.
        ~(v IN a) /\
        (!x y. x IN a /\ y IN a /\ y IN segment[v,x] ==> y = x) /\
        convex s /\ convex t /\ s SUBSET a /\ t SUBSET a
        ==> convex hull (v INSERT s) INTER convex hull (v INSERT t) =
            convex hull (v INSERT (s INTER t))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN
    SET_TAC[]] THEN
  REWRITE_TAC[CONVEX_HULL_INSERT_SEGMENTS] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[INTER_EMPTY; INTER_SUBSET] THEN
  ASM_CASES_TAC `t:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[INTER_EMPTY; INTER_SUBSET] THEN
  ASM_SIMP_TAC[HULL_P; CONVEX_INTER] THEN
  REWRITE_TAC[SUBSET; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)
   (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `x:real^N = v` THENL
   [COND_CASES_TAC THEN REWRITE_TAC[IN_SING; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[IN_INTER] THEN MESON_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `y:real^N = z` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`v:real^N`; `x:real^N`; `y:real^N`; `z:real^N`]
      MOI_CON_SEGMENT_RAY) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  COND_CASES_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `z:real^N` THEN
  ASM_REWRITE_TAC[IN_INTER]);;

let MOI_CON_CONE_INTER_BASE = prove
 (`!a (v:real^N) s u.
        ~(v IN a) /\
        (!x y. x IN a /\ y IN a /\ y IN segment[v,x] ==> y = x) /\
        convex s /\ s SUBSET a /\ u SUBSET a
        ==> convex hull (v INSERT s) INTER u = s INTER u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(SET_RULE
     `(s:real^N->bool) SUBSET t ==> s INTER u SUBSET t INTER u`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(v:real^N) INSERT s` THEN
    REWRITE_TAC[HULL_SUBSET] THEN SET_TAC[]] THEN
  REWRITE_TAC[CONVEX_HULL_INSERT_SEGMENTS] THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[] THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[HULL_P] THEN
  REWRITE_TAC[SUBSET; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  SUBGOAL_THEN `x:real^N = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* 2. The cone complex (SIMPLICIAL_CONE_COMPLEX).                            *)
(* ------------------------------------------------------------------------- *)

let MOI_CON_SC_NOT_IN_AFFINE_HULL = prove
 (`!l (v:real^N) s.
        simplicial_complex l /\ ~(v IN UNIONS l) /\
        (!x y. x IN UNIONS l /\ y IN UNIONS l /\ y IN segment[v,x] ==> y = x) /\
        s IN l
        ==> ~(v IN affine hull s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[AFFINE_HULL_EMPTY; NOT_IN_EMPTY] THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_CON_NOT_IN_AFFINE_HULL THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED];
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]);;

let MOI_CON_CC_FACE = prove
 (`!l (v:real^N) s t.
        simplicial_complex l /\ ~(v IN UNIONS l) /\
        (!x y. x IN UNIONS l /\ y IN UNIONS l /\ y IN segment[v,x] ==> y = x) /\
        s IN l /\ t IN l
        ==> (convex hull (v INSERT s) INTER convex hull (v INSERT t)) face_of
            convex hull (v INSERT s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?m. m simplex (t:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS l:real^N->bool`; `v:real^N`; `s:real^N->bool`;
                 `t:real^N->bool`] MOI_CON_CONE_INTER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]) THEN
    ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MOI_CON_CONE_FACE_OF THEN EXISTS_TAC `n:int` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CON_SC_NOT_IN_AFFINE_HULL THEN
    EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_CON_CB_FACE = prove
 (`!l (v:real^N) s u.
        simplicial_complex l /\ ~(v IN UNIONS l) /\
        (!x y. x IN UNIONS l /\ y IN UNIONS l /\ y IN segment[v,x] ==> y = x) /\
        s IN l /\ u IN l
        ==> (convex hull (v INSERT s) INTER u) face_of convex hull (v INSERT s) /\
            (convex hull (v INSERT s) INTER u) face_of u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS l:real^N->bool`; `v:real^N`; `s:real^N->bool`;
                 `u:real^N->bool`] MOI_CON_CONE_INTER_BASE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]) THEN
    ASM SET_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ASM_SIMP_TAC[] THEN MATCH_MP_TAC FACE_OF_TRANS THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC MOI_CON_BASE_FACE_OF THEN EXISTS_TAC `n:int` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_CON_SC_NOT_IN_AFFINE_HULL THEN
  EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let SIMPLICIAL_CONE_COMPLEX = prove
 (`!(l:(real^N->bool)->bool) v.
     simplicial_complex l /\ ~(UNIONS l = {}) /\ ~(v IN UNIONS l) /\
     (!x y. x IN UNIONS l /\ y IN UNIONS l /\ y IN segment[v,x] ==> y = x)
     ==> simplicial_complex (l UNION {convex hull (v INSERT s) | s IN l}) /\
         UNIONS (l UNION {convex hull (v INSERT s) | s IN l}) =
         UNIONS {segment[v,x] | x IN UNIONS l}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN l ==> ~(v IN affine hull s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
      MOI_CON_SC_NOT_IN_AFFINE_HULL) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  CONJ_TAC THENL
   [REWRITE_TAC[simplicial_complex] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[FINITE_UNION; SIMPLE_IMAGE] THEN ASM_SIMP_TAC[FINITE_IMAGE];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN GEN_TAC THEN STRIP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?n. n simplex (s':real^N->bool)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `n + &1:int` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_CON_CONE_SIMPLEX THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?n. n simplex (s':real^N->bool)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`s':real^N->bool`; `v:real^N`; `n:int`; `f:real^N->bool`]
        MOI_CON_CONE_FACES) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISJ2_TAC THEN EXISTS_TAC `g:real^N->bool` THEN ASM_MESON_TAC[];
      REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THENL
       [ASM_MESON_TAC[];
        ONCE_REWRITE_TAC[INTER_COMM] THEN
        MATCH_MP_TAC(TAUT `p /\ q ==> q /\ p`) THEN
        MATCH_MP_TAC MOI_CON_CB_FACE THEN
        EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_CON_CB_FACE THEN
        EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        CONJ_TAC THENL [ALL_TAC; ONCE_REWRITE_TAC[INTER_COMM]] THEN
        MATCH_MP_TAC MOI_CON_CC_FACE THEN EXISTS_TAC `l:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_UNION] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN
  CONJ_TAC THENL
   [REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC] THEN
      MESON_TAC[ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THENL
     [UNDISCH_TAC `(x:real^N) IN convex hull (v INSERT s)` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `~(UNIONS l:real^N->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
      MESON_TAC[ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex(s:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN convex hull (v INSERT s)` THEN
    ASM_SIMP_TAC[CONVEX_HULL_INSERT_SEGMENTS; HULL_P] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC] THEN ASM_MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC; IN_UNION] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    DISJ2_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^N) IN segment[v,x]` THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SPEC_TAC(`y:real^N`,`y:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 3. Relative subdivision (SIMPLICIAL_SUBDIVISION_EXTEND): auxiliary        *)
(* predicates for the hypotheses and the conclusion, and general lemmas.     *)
(* ------------------------------------------------------------------------- *)

let moi_con_relhyp = new_definition
 `moi_con_relhyp (l:(real^N->bool)->bool) f d <=>
    simplicial_complex l /\ simplicial_complex f /\ f SUBSET l /\
    simplicial_complex d /\ UNIONS d = UNIONS f /\
    (!s. s IN d ==> ?t. t IN f /\ s SUBSET t) /\
    (!t. t IN f ==> ?e. e SUBSET d /\ t = UNIONS e)`;;

let moi_con_relsub = new_definition
 `moi_con_relsub (l:(real^N->bool)->bool) f d l' <=>
    simplicial_complex l' /\ UNIONS l' = UNIONS l /\
    (!s. s IN l' ==> ?t. t IN l /\ s SUBSET t) /\
    (!t. t IN l ==> ?e. e SUBSET l' /\ t = UNIONS e) /\
    (!s. s IN d /\ ~(s = {}) ==> s IN l') /\
    (!s. s IN l' /\ ~(s = {}) /\ s SUBSET UNIONS f ==> s IN d) /\
    (!t. t IN l /\ DISJOINT t (UNIONS f) ==> t IN l')`;;

let MOI_CON_SIMPLICIAL_COMPLEX_UNION = prove
 (`!a b:(real^N->bool)->bool.
        simplicial_complex a /\ simplicial_complex b /\
        (!s t. s IN a /\ t IN b
               ==> (s INTER t) face_of s /\ (s INTER t) face_of t)
        ==> simplicial_complex (a UNION b)`,
  REWRITE_TAC[simplicial_complex; FINITE_UNION; IN_UNION] THEN
  MESON_TAC[INTER_COMM]);;

let MOI_CON_RF_SEGMENT = prove
 (`!t (b:real^N) x y.
        convex t /\ b IN relative_interior t /\
        x IN relative_frontier t /\ y IN relative_frontier t /\
        y IN segment[b,x]
        ==> y = x`,
  REWRITE_TAC[relative_frontier; IN_DIFF] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `b:real^N`; `x:real^N`]
    IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
  UNDISCH_TAC `(y:real^N) IN segment[b,x]` THEN
  REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_MESON_TAC[]);;

let MOI_CON_CONE_RF = prove
 (`!t (b:real^N).
        convex t /\ compact t /\ b IN relative_interior t /\
        ~(relative_frontier t = {})
        ==> UNIONS {segment[b,x] | x IN relative_frontier t} = t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closure t = (t:real^N->bool) /\ (b:real^N) IN t`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[relative_frontier; IN_DIFF] THEN STRIP_TAC THEN
    UNDISCH_TAC `convex(t:real^N->bool)` THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_GSPEC] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `z:real^N = b` THENL
   [UNDISCH_TAC `~(relative_frontier t:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `b:real^N`; `z:real^N`]
    MOI_BAR_RAY_EXIT) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED; COMPACT_IMP_CLOSED] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `u:real`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `y:real^N` THEN
  ASM_REWRITE_TAC[relative_frontier; IN_DIFF; IN_SEGMENT] THEN
  EXISTS_TAC `u:real` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_CON_INTER_MAXIMAL_RF = prove
 (`!l t w:real^N->bool.
        simplicial_complex l /\ t IN l /\ w IN l /\ ~(w = t) /\
        (!u. u IN l /\ t SUBSET u ==> u = t)
        ==> t INTER w SUBSET relative_frontier t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t INTER w) face_of (t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `~(t INTER w:real^N->bool = t)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(w:real^N->bool = t)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t INTER w:real^N->bool`; `t:real^N->bool`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[relative_frontier] THEN
  MP_TAC(ISPEC `t:real^N->bool` CLOSURE_SUBSET) THEN SET_TAC[]);;

let MOI_CON_SC_SIMPLEX = prove
 (`!c s:real^N->bool. simplicial_complex c /\ s IN c ==> ?n. n simplex s`,
  REWRITE_TAC[simplicial_complex] THEN MESON_TAC[]);;

let MOI_CON_SC_FACE = prove
 (`!c s f:real^N->bool.
        simplicial_complex c /\ s IN c /\ f face_of s ==> f IN c`,
  REWRITE_TAC[simplicial_complex] THEN MESON_TAC[]);;

let MOI_CON_SC_INTER = prove
 (`!c s t:real^N->bool.
        simplicial_complex c /\ s IN c /\ t IN c
        ==> (s INTER t) face_of s /\ (s INTER t) face_of t`,
  REWRITE_TAC[simplicial_complex] THEN MESON_TAC[]);;

let MOI_CON_SC_CONVEX = prove
 (`!c s:real^N->bool. simplicial_complex c /\ s IN c ==> convex s`,
  MESON_TAC[MOI_CON_SC_SIMPLEX; SIMPLEX_IMP_CONVEX]);;

let MOI_CON_SC_COMPACT = prove
 (`!c s:real^N->bool. simplicial_complex c /\ s IN c ==> compact s`,
  MESON_TAC[MOI_CON_SC_SIMPLEX; SIMPLEX_IMP_COMPACT]);;

let MOI_CON_SC_POLYTOPE = prove
 (`!c s:real^N->bool. simplicial_complex c /\ s IN c ==> polytope s`,
  MESON_TAC[MOI_CON_SC_SIMPLEX; SIMPLEX_IMP_POLYTOPE]);;

let MOI_CON_ACTIVE_RF_NONEMPTY = prove
 (`!l f t:real^N->bool.
        simplicial_complex l /\ simplicial_complex f /\ f SUBSET l /\
        t IN l /\ ~(t IN f) /\ ~DISJOINT t (UNIONS f)
        ==> ~(relative_frontier t = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_CON_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  SUBGOAL_THEN `bounded(t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. t = {a}` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
    ASM_REWRITE_TAC[GSYM RELATIVE_FRONTIER_EQ_EMPTY] THEN
    STRIP_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `~DISJOINT t (UNIONS f:real^N->bool)` THEN
  ASM_REWRITE_TAC[DISJOINT; IN_UNIONS; SET_RULE
    `{a:real^N} INTER s = {} <=> ~(a IN s)`] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N->bool) IN l` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`;
                 `w:real^N->bool`] MOI_CON_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{a:real^N} INTER w = {a}` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `~((t:real^N->bool) IN f)` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_CON_SC_FACE THEN EXISTS_TAC `w:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_CON_RI_NOT_IN_F = prove
 (`!l f t (b:real^N).
        simplicial_complex l /\ simplicial_complex f /\ f SUBSET l /\
        t IN l /\ ~(t IN f) /\ b IN relative_interior t
        ==> ~(b IN UNIONS f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N->bool) IN l /\ (b:real^N) IN t` STRIP_ASSUME_TAC
  THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`;
                 `w:real^N->bool`] MOI_CON_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^N->bool) SUBSET t INTER w` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `t INTER w:real^N->bool = t` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~((t:real^N->bool) IN f)` THEN REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_CON_SC_FACE THEN EXISTS_TAC `w:real^N->bool` THEN
  ASM_MESON_TAC[]);;

let MOI_CON_RF_SUBCOMPLEX = prove
 (`!l0 (t:real^N->bool) n.
        simplicial_complex l0 /\ n simplex t /\
        (!g. g face_of t /\ ~(g = t) ==> ?e. e SUBSET l0 /\ g = UNIONS e)
        ==> simplicial_complex {s | s IN l0 /\ s SUBSET relative_frontier t} /\
            UNIONS {s | s IN l0 /\ s SUBSET relative_frontier t} =
            relative_frontier t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
      ASM_MESON_TAC[MOI_CON_SC_SIMPLEX];
      REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_CON_SC_FACE];
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
      ASM_MESON_TAC[MOI_CON_SC_INTER]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier t = UNIONS {g:real^N->bool | g facet_of t}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_OF_POLYHEDRON THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYHEDRON];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?g:real^N->bool. g facet_of t /\ x IN g` STRIP_ASSUME_TAC
  THENL
   [UNDISCH_TAC `(x:real^N) IN relative_frontier t` THEN
    ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^N->bool) SUBSET relative_frontier t` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(g:real^N->bool) IN c ==> g SUBSET UNIONS c`) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->bool`) THEN
  ASM_SIMP_TAC[FACET_OF_IMP_FACE_OF; FACET_OF_IMP_PROPER] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN e /\ x IN s` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM SET_TAC[]);;

let MOI_CON_EXTEND_BASE = prove
 (`!l f d:(real^N->bool)->bool.
        moi_con_relhyp l f d /\ l DIFF f = {}
        ==> ?l'. moi_con_relsub l f d l'`,
  REWRITE_TAC[moi_con_relhyp; moi_con_relsub] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `l:(real^N->bool)->bool = f` SUBST_ALL_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  EXISTS_TAC `d UNION {s:real^N->bool | s IN f /\ s = {}}` THEN
  SUBGOAL_THEN `UNIONS {s:real^N->bool | s IN f /\ s = {}} = {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CON_SIMPLICIAL_COMPLEX_UNION THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
        MESON_TAC[SIMPLEX_EMPTY];
        REPEAT GEN_TAC THEN STRIP_TAC THEN
        FIRST_X_ASSUM(SUBST_ALL_TAC o check
          (fun th -> rhs(concl th) = `{}:real^N->bool`)) THEN
        ASM_MESON_TAC[FACE_OF_EMPTY];
        REPEAT GEN_TAC THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[INTER_EMPTY; EMPTY_FACE_OF]];
      REPEAT GEN_TAC THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[INTER_EMPTY; EMPTY_FACE_OF]];
    ASM_REWRITE_TAC[UNIONS_UNION; UNION_EMPTY];
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET_REFL];
    X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `t:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    SIMP_TAC[IN_UNION];
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN DISJ2_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(t:real^N->bool) SUBSET UNIONS f` MP_TAC THENL
     [ASM SET_TAC[]; ASM SET_TAC[]]]);;

let MOI_CON_MAXIMAL_INTER_FACE = prove
 (`!l l0 (t:real^N->bool).
        simplicial_complex l /\ simplicial_complex l0 /\ t IN l /\
        (!u. u IN l /\ t SUBSET u ==> u = t) /\
        (!s. s IN l0 ==> ?w. w IN l DELETE t /\ s SUBSET w) /\
        (!g. g face_of t /\ ~(g = t) ==> g IN l0)
        ==> !u. u IN l0 ==> (t INTER u) face_of t /\ (t INTER u) face_of u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
  UNDISCH_TAC
   `!s:real^N->bool. s IN l0 ==> ?w. w IN l DELETE t /\ s SUBSET w` THEN
  DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN
  ASM_REWRITE_TAC[IN_DELETE] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`;
                 `w:real^N->bool`] MOI_CON_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(t INTER w:real^N->bool = t)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(w:real^N->bool = t)` THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `t INTER w:real^N->bool = t` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t INTER w:real^N->bool) IN l0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l0:(real^N->bool)->bool`; `t INTER w:real^N->bool`;
                 `u:real^N->bool`] MOI_CON_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(t INTER w) INTER u:real^N->bool = t INTER u`
  SUBST1_TAC THENL
   [UNDISCH_TAC `(u:real^N->bool) SUBSET w` THEN SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `t INTER w:real^N->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_CON_EXTEND_STEP_DISJ = prove
 (`!(l:(real^N->bool)->bool) f d (t:real^N->bool) l0.
        moi_con_relhyp l f d /\ t IN l /\ ~(t IN f) /\
        DISJOINT t (UNIONS f) /\
        (!u. u IN l /\ t SUBSET u ==> u = t) /\
        moi_con_relsub (l DELETE t) f d l0
        ==> moi_con_relsub l f d (t INSERT l0)`,
  REWRITE_TAC[moi_con_relhyp; moi_con_relsub] THEN REPEAT GEN_TAC THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `!g:real^N->bool. g face_of t /\ ~(g = t) ==> g IN l0`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(g:real^N->bool) IN l` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_CON_SC_FACE THEN EXISTS_TAC `t:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (g:real^N->bool) (UNIONS f)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`t:real^N->bool`; `g:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
      UNDISCH_TAC `DISJOINT (t:real^N->bool) (UNIONS f)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC
     `!t':real^N->bool.
        t' IN l DELETE t /\ DISJOINT t' (UNIONS f) ==> t' IN l0` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `l0:(real^N->bool)->bool`;
                 `t:real^N->bool`] MOI_CON_MAXIMAL_INTER_FACE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[simplicial_complex; FINITE_INSERT; IN_INSERT] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (l0:(real^N->bool)->bool)` THEN
      SIMP_TAC[simplicial_complex];
      X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CON_SC_SIMPLEX THEN
        EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_CON_SC_SIMPLEX THEN
        EXISTS_TAC `l0:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`g:real^N->bool`; `s:real^N->bool`] THEN
      STRIP_TAC THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN
        ASM_CASES_TAC `g:real^N->bool = t` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN MATCH_MP_TAC MOI_CON_SC_FACE THEN
        EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
      MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `s':real^N->bool`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [REWRITE_TAC[INTER_IDEMPOT] THEN MATCH_MP_TAC FACE_OF_REFL THEN
        MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
        EXISTS_TAC `l:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[];
        ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_SIMP_TAC[];
        MATCH_MP_TAC MOI_CON_SC_INTER THEN
        EXISTS_TAC `l0:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]]];
    REWRITE_TAC[UNIONS_INSERT] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(t:real^N->bool) IN l` THEN SET_TAC[];
    REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `s:real^N->bool` THEN
    STRIP_TAC THENL
     [EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL];
      UNDISCH_TAC
       `!s:real^N->bool. s IN l0 ==> ?t'. t' IN l DELETE t /\ s SUBSET t'` THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN MESON_TAC[]];
    X_GEN_TAC `t':real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `t':real^N->bool = t` THENL
     [EXISTS_TAC `{t:real^N->bool}` THEN ASM_REWRITE_TAC[UNIONS_1] THEN
      SET_TAC[];
      UNDISCH_TAC
       `!t':real^N->bool. t' IN l DELETE t ==> ?e. e SUBSET l0 /\ t' = UNIONS e`
      THEN DISCH_THEN(MP_TAC o SPEC `t':real^N->bool`) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN MATCH_MP_TAC MONO_EXISTS THEN
      SET_TAC[]];
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_INSERT] THEN DISJ2_TAC THEN
    UNDISCH_TAC `!s:real^N->bool. s IN d /\ ~(s = {}) ==> s IN l0` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_INSERT] THEN X_GEN_TAC `s:real^N->bool` THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `DISJOINT (t:real^N->bool) (UNIONS f)` THEN
      UNDISCH_TAC `(s:real^N->bool) SUBSET UNIONS f` THEN
      UNDISCH_TAC `~(s:real^N->bool = {})` THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[];
      UNDISCH_TAC
       `!s:real^N->bool. s IN l0 /\ ~(s = {}) /\ s SUBSET UNIONS f ==> s IN d`
      THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `t':real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_INSERT] THEN
    ASM_CASES_TAC `t':real^N->bool = t` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC
     `!t':real^N->bool.
        t' IN l DELETE t /\ DISJOINT t' (UNIONS f) ==> t' IN l0` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE]]);;

(* ------------------------------------------------------------------------- *)
(* 4. The cone step of the relative subdivision: a maximal simplex t of l    *)
(* that is not in f but meets UNIONS f is replaced by the cone from its      *)
(* barycentre over the subdivision of its boundary obtained so far.          *)
(* ------------------------------------------------------------------------- *)

let MOI_CON_CONE_OVER_RF = prove
 (`!K (t:real^N->bool) n b.
        n simplex t /\ b IN relative_interior t /\
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
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_CON_CONE_RF THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]]);;

let MOI_CON_CONE_INTER_OUTSIDE = prove
 (`!t (b:real^N) s u.
        convex t /\ closed t /\ b IN relative_interior t /\
        convex s /\ s SUBSET relative_frontier t /\
        u INTER t SUBSET relative_frontier t
        ==> convex hull (b INSERT s) INTER u = s INTER u`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `relative_frontier t SUBSET (t:real^N->bool) /\ (b:real^N) IN t`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; SUBSET_DIFF] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull ((b:real^N) INSERT s) SUBSET t` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[INSERT_SUBSET] THEN
    ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier t:real^N->bool`; `b:real^N`;
                 `s:real^N->bool`; `relative_frontier t:real^N->bool`]
    MOI_CON_CONE_INTER_BASE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_RF_SEGMENT THEN
      MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `b:real^N`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET convex hull (b INSERT s)` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(b:real^N) INSERT s` THEN
    REWRITE_TAC[HULL_SUBSET] THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`u INTER t SUBSET relative_frontier (t:real^N->bool)`;
    `convex hull ((b:real^N) INSERT s) SUBSET t`] THEN
  SET_TAC[]);;

let MOI_CON_GLUE_CONE = prove
 (`!l0 K (b:real^N).
        simplicial_complex l0 /\ K SUBSET l0 /\
        simplicial_complex (K UNION {convex hull (b INSERT s) | s IN K}) /\
        (!s u. s IN K /\ u IN l0
               ==> convex hull (b INSERT s) INTER u = s INTER u)
        ==> simplicial_complex (l0 UNION {convex hull (b INSERT s) | s IN K})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `l0 UNION {convex hull ((b:real^N) INSERT s) | s IN K} =
    l0 UNION (K UNION {convex hull (b INSERT s) | s IN K})`
  SUBST1_TAC THENL
   [UNDISCH_TAC `(K:(real^N->bool)->bool) SUBSET l0` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_CON_SIMPLICIAL_COMPLEX_UNION THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`u:real^N->bool`; `c:real^N->bool`] THEN
  REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THENL
   [MATCH_MP_TAC MOI_CON_SC_INTER THEN EXISTS_TAC `l0:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN l0` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_SIMP_TAC[] THEN
  MP_TAC(ISPECL [`l0:(real^N->bool)->bool`; `s:real^N->bool`;
                 `u:real^N->bool`] MOI_CON_SC_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`K UNION {convex hull ((b:real^N) INSERT s) | s IN K}`;
                 `s:real^N->bool`; `convex hull ((b:real^N) INSERT s)`]
    MOI_CON_SC_INTER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `s INTER convex hull ((b:real^N) INSERT s) = s`
  (fun th -> SIMP_TAC[th]) THEN
  MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t ==> s INTER t = s`) THEN
  MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(b:real^N) INSERT s` THEN
  REWRITE_TAC[HULL_SUBSET] THEN SET_TAC[]);;

let MOI_CON_EXTEND_STEP_CONE = prove
 (`!(l:(real^N->bool)->bool) f d (t:real^N->bool) l0.
        moi_con_relhyp l f d /\ t IN l /\ ~(t IN f) /\
        ~DISJOINT t (UNIONS f) /\
        (!u. u IN l /\ t SUBSET u ==> u = t) /\
        moi_con_relsub (l DELETE t) f d l0
        ==> ?l'. moi_con_relsub l f d l'`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_con_relhyp] THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_con_relsub]) THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`]
    MOI_CON_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  SUBGOAL_THEN `convex (t:real^N->bool) /\ closed t /\ compact t`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `~DISJOINT (t:real^N->bool) (UNIONS f)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?b:real^N. b IN relative_interior t` STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `simplex_barycentre (t:real^N->bool)` THEN
    MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_frontier t:real^N->bool = {})` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CON_ACTIVE_RF_NONEMPTY THEN
    MAP_EVERY EXISTS_TAC [`l:(real^N->bool)->bool`; `f:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((b:real^N) IN UNIONS f)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_CON_RI_NOT_IN_F THEN
    MAP_EVERY EXISTS_TAC [`l:(real^N->bool)->bool`; `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l0:(real^N->bool)->bool`; `t:real^N->bool`; `n:int`]
    MOI_CON_RF_SUBCOMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC
     `!t':real^N->bool. t' IN l DELETE t ==> ?e. e SUBSET l0 /\ t' = UNIONS e`
    THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    MATCH_MP_TAC MOI_CON_SC_FACE THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`{s:real^N->bool | s IN l0 /\ s SUBSET relative_frontier t}`;
    `t:real^N->bool`; `n:int`; `b:real^N`] MOI_CON_CONE_OVER_RF) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!u:real^N->bool. u IN l0 ==> u INTER t SUBSET relative_frontier t`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N->bool` THEN DISCH_TAC THEN
    UNDISCH_TAC
     `!s:real^N->bool. s IN l0 ==> ?t'. t' IN l DELETE t /\ s SUBSET t'` THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN
    ASM_REWRITE_TAC[IN_DELETE] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`;
                   `w:real^N->bool`] MOI_CON_INTER_MAXIMAL_RF) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(u:real^N->bool) SUBSET w` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s u:real^N->bool.
        s IN {s | s IN l0 /\ s SUBSET relative_frontier t} /\ u IN l0
        ==> convex hull (b INSERT s) INTER u = s INTER u`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_CON_CONE_INTER_OUTSIDE THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CON_SC_CONVEX THEN
      EXISTS_TAC `l0:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC
   `l0 UNION {convex hull ((b:real^N) INSERT s) |
              s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}` THEN
  REWRITE_TAC[moi_con_relsub] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CON_GLUE_CONE THEN ASM_REWRITE_TAC[SUBSET_RESTRICT];
    SUBGOAL_THEN `UNIONS l = t UNION UNIONS (l DELETE (t:real^N->bool))`
    SUBST1_TAC THENL
     [UNDISCH_TAC `(t:real^N->bool) IN l` THEN SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL
     [`{s:real^N->bool | s IN l0 /\ s SUBSET relative_frontier t}`;
      `l0:(real^N->bool)->bool`] SUBSET_UNIONS) THEN
    REWRITE_TAC[SUBSET_RESTRICT] THEN
    UNDISCH_TAC `UNIONS l0 = UNIONS (l DELETE (t:real^N->bool))` THEN
    UNDISCH_TAC
     `UNIONS ({s | s IN l0 /\ s SUBSET relative_frontier t} UNION
       {convex hull ((b:real^N) INSERT s) |
        s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}) = t` THEN
    REWRITE_TAC[UNIONS_UNION] THEN
    SPEC_TAC(`UNIONS {convex hull ((b:real^N) INSERT s) |
                      s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}`,
             `C:real^N->bool`) THEN
    SPEC_TAC(`UNIONS {s:real^N->bool | s IN l0 /\
                                      s SUBSET relative_frontier t}`,
             `Ks:real^N->bool`) THEN
    SPEC_TAC(`UNIONS (l DELETE (t:real^N->bool))`, `X:real^N->bool`) THEN
    SPEC_TAC(`UNIONS l0:real^N->bool`, `A:real^N->bool`) THEN SET_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
     [UNDISCH_TAC
       `!s:real^N->bool. s IN l0 ==> ?t'. t' IN l DELETE t /\ s SUBSET t'` THEN
      DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN MESON_TAC[];
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `UNIONS ({s | s IN l0 /\ s SUBSET relative_frontier t} UNION
         {convex hull ((b:real^N) INSERT s) |
          s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}) = t` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
      ASM_REWRITE_TAC[IN_UNION]];
    X_GEN_TAC `t':real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `t':real^N->bool = t` THENL
     [EXISTS_TAC
       `{s:real^N->bool | s IN l0 /\ s SUBSET relative_frontier t} UNION
        {convex hull ((b:real^N) INSERT s) |
         s IN {s | s IN l0 /\ s SUBSET relative_frontier t}}` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      UNDISCH_TAC
       `!t':real^N->bool. t' IN l DELETE t ==> ?e. e SUBSET l0 /\ t' = UNIONS e`
      THEN DISCH_THEN(MP_TAC o SPEC `t':real^N->bool`) THEN
      ASM_REWRITE_TAC[IN_DELETE] THEN MATCH_MP_TAC MONO_EXISTS THEN
      SET_TAC[]];
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
    UNDISCH_TAC `!s:real^N->bool. s IN d /\ ~(s = {}) ==> s IN l0` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC
       `!s:real^N->bool. s IN l0 /\ ~(s = {}) /\ s SUBSET UNIONS f ==> s IN d`
      THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(b:real^N) IN s` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN
        REWRITE_TAC[IN_INSERT];
        UNDISCH_TAC `~((b:real^N) IN UNIONS f)` THEN
        UNDISCH_TAC `(s:real^N->bool) SUBSET UNIONS f` THEN
        UNDISCH_TAC `(b:real^N) IN s` THEN SET_TAC[]]];
    X_GEN_TAC `t':real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[IN_UNION] THEN DISJ1_TAC THEN
    UNDISCH_TAC
     `!t':real^N->bool.
        t' IN l DELETE t /\ DISJOINT t' (UNIONS f) ==> t' IN l0` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_DELETE] THEN
    DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 5. Induction on the number of simplices of l not in f                     *)
(* (SIMPLICIAL_SUBDIVISION_EXTEND).                                          *)
(* ------------------------------------------------------------------------- *)

let MOI_CON_SC_DELETE_MAXIMAL = prove
 (`!l t:real^N->bool.
        simplicial_complex l /\ t IN l /\
        (!u. u IN l /\ t SUBSET u ==> u = t)
        ==> simplicial_complex (l DELETE t)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[simplicial_complex; IN_DELETE; FINITE_DELETE] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`g:real^N->bool`; `s:real^N->bool`] THEN
    STRIP_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(s:real^N->bool = t)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
    ASM_MESON_TAC[]]);;

let MOI_CON_EXTEND_INDUCT = prove
 (`!(f:(real^N->bool)->bool) d n l.
        moi_con_relhyp l f d /\ CARD (l DIFF f) = n
        ==> ?l'. moi_con_relsub l f d l'`,
  GEN_TAC THEN GEN_TAC THEN MATCH_MP_TAC num_WF THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  X_GEN_TAC `l:(real^N->bool)->bool` THEN STRIP_TAC THEN
  ASM_CASES_TAC `l DIFF f:(real^N->bool)->bool = {}` THENL
   [MATCH_MP_TAC MOI_CON_EXTEND_BASE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_con_relhyp]) THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?t:real^N->bool. t IN l /\ ~(t IN f) /\
                     !u. u IN l /\ ~(u IN f) ==> ~(t PSUBSET u)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(PSUBSET):(real^N->bool)->(real^N->bool)->bool`;
                   `l DIFF f:(real^N->bool)->bool`]
      FINITE_TRANSITIVITY_CHAIN) THEN
    ASM_SIMP_TAC[FINITE_DIFF; PSUBSET_IRREFL] THEN
    REWRITE_TAC[IN_DIFF] THEN MESON_TAC[PSUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N->bool. u IN l /\ t SUBSET u ==> u = t`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `(u:real^N->bool) IN f` THENL
     [MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `t:real^N->bool`;
                     `u:real^N->bool`] MOI_CON_SC_INTER) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `t INTER u:real^N->bool = t` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) IN f` MP_TAC THENL
       [MATCH_MP_TAC MOI_CON_SC_FACE THEN EXISTS_TAC `u:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      UNDISCH_TAC
       `!u:real^N->bool. u IN l /\ ~(u IN f) ==> ~(t PSUBSET u)` THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN
      ASM_REWRITE_TAC[PSUBSET] THEN MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `n - 1`) THEN ANTS_TAC THENL
   [SUBGOAL_THEN `~(n = 0)` MP_TAC THENL
     [EXPAND_TAC "n" THEN ASM_SIMP_TAC[CARD_EQ_0; FINITE_DIFF]; ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `l DELETE (t:real^N->bool)`) THEN ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[moi_con_relhyp] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_CON_SC_DELETE_MAXIMAL THEN ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      SUBGOAL_THEN `(l DELETE t) DIFF f = (l DIFF f) DELETE (t:real^N->bool)`
      SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[CARD_DELETE; FINITE_DIFF; IN_DIFF]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `l0:(real^N->bool)->bool`) THEN
  ASM_CASES_TAC `DISJOINT (t:real^N->bool) (UNIONS f)` THENL
   [EXISTS_TAC `(t:real^N->bool) INSERT l0` THEN
    MATCH_MP_TAC MOI_CON_EXTEND_STEP_DISJ THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_CON_EXTEND_STEP_CONE THEN
    MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `l0:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[]]);;

let SIMPLICIAL_SUBDIVISION_EXTEND = prove
 (`!(l:(real^N->bool)->bool) f d.
     simplicial_complex l /\ simplicial_complex f /\ f SUBSET l /\
     simplicial_complex d /\ UNIONS d = UNIONS f /\
     (!s. s IN d ==> ?t. t IN f /\ s SUBSET t) /\
     (!t. t IN f ==> ?e. e SUBSET d /\ t = UNIONS e)
     ==> ?l'. simplicial_complex l' /\ UNIONS l' = UNIONS l /\
              (!s. s IN l' ==> ?t. t IN l /\ s SUBSET t) /\
              (!t. t IN l ==> ?e. e SUBSET l' /\ t = UNIONS e) /\
              (!s. s IN d /\ ~(s = {}) ==> s IN l') /\
              (!s. s IN l' /\ ~(s = {}) /\ s SUBSET UNIONS f ==> s IN d) /\
              (!t. t IN l /\ DISJOINT t (UNIONS f) ==> t IN l')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`f:(real^N->bool)->bool`; `d:(real^N->bool)->bool`;
                 `CARD (l DIFF f:(real^N->bool)->bool)`;
                 `l:(real^N->bool)->bool`] MOI_CON_EXTEND_INDUCT) THEN
  ASM_REWRITE_TAC[moi_con_relhyp; moi_con_relsub]);;

(* ------------------------------------------------------------------------- *)
(* 6. The cone map: a map f on a set a extends conewise from u to v,         *)
(* p = u + r (x - u) going to v + r (f x - v).  A constant defined by        *)
(* Hilbert choice; well defined under the segment condition.                 *)
(* ------------------------------------------------------------------------- *)

let MOI_CON_IN_CONE = prove
 (`!a (u:real^N) p.
        p IN UNIONS {segment[u,x] | x IN a} <=>
        ?x r. x IN a /\ &0 <= r /\ r <= &1 /\ p = u + r % (x - u)`,
  REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_SEGMENT] THEN
  REWRITE_TAC[VECTOR_ARITH `(&1 - r) % u + r % x:real^N = u + r % (x - u)`] THEN
  MESON_TAC[]);;

let MOI_CON_RAY_UNIQUE = prove
 (`!a (u:real^N) x y r s.
        ~(u IN a) /\
        (!x y. x IN a /\ y IN a /\ y IN segment[u,x] ==> y = x) /\
        x IN a /\ y IN a /\ &0 <= r /\ r <= &1 /\ &0 <= s /\ s <= &1 /\
        u + r % (x - u) = u + s % (y - u)
        ==> r = s /\ (r = &0 \/ x = y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(x:real^N = u) /\ ~(y:real^N = u)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `u + r % (x - u):real^N = u` THENL
   [SUBGOAL_THEN `r = &0 /\ s = &0` (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `u + r % (x - u):real^N = u`;
      UNDISCH_TAC `u + r % (x - u):real^N = u` THEN ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[VECTOR_ARITH `u + c % (x - u):real^N = u <=> c % (x - u) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `x:real^N = y` SUBST_ALL_TAC THENL
   [MP_TAC(ISPECL [`u:real^N`; `u + r % (x - u):real^N`; `x:real^N`;
                   `y:real^N`] MOI_CON_SEGMENT_RAY) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_SEGMENT] THEN REPEAT CONJ_TAC THENL
       [EXISTS_TAC `r:real` THEN REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]; VECTOR_ARITH_TAC];
        EXISTS_TAC `s:real` THEN REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[];
          ONCE_REWRITE_TAC[ASSUME
            `u + r % (x - u):real^N = u + s % (y - u)`] THEN
          VECTOR_ARITH_TAC];
        ASM_REWRITE_TAC[]];
      STRIP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  UNDISCH_TAC `u + r % (y - u):real^N = u + s % (y - u)` THEN
  REWRITE_TAC[VECTOR_ARITH `u + r % (y - u):real^N = u + s % (y - u) <=>
                            r % (y - u) = s % (y - u)`] THEN
  ASM_REWRITE_TAC[VECTOR_MUL_RCANCEL; VECTOR_SUB_EQ]);;

let moi_con_conemap = new_definition
 `moi_con_conemap (a:real^M->bool) (u:real^M) (v:real^N) (f:real^M->real^N)
                  (p:real^M) =
    @q. ?x r. x IN a /\ &0 <= r /\ r <= &1 /\ p = u + r % (x - u) /\
              q = v + r % (f x - v)`;;

let MOI_CON_CONEMAP_EQ = prove
 (`!a (u:real^M) (v:real^N) f x r.
        ~(u IN a) /\
        (!x y. x IN a /\ y IN a /\ y IN segment[u,x] ==> y = x) /\
        x IN a /\ &0 <= r /\ r <= &1
        ==> moi_con_conemap a u v f (u + r % (x - u)) = v + r % (f x - v)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_con_conemap] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `q:real^N` THEN BETA_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `y:real^M` (X_CHOOSE_THEN `s:real`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`a:real^M->bool`; `u:real^M`; `x:real^M`; `y:real^M`;
                   `r:real`; `s:real`] MOI_CON_RAY_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO] THEN
    UNDISCH_TAC `r:real = s` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[VECTOR_MUL_LZERO];
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`x:real^M`; `r:real`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_CON_CONEMAP_ON_BASE = prove
 (`!a (u:real^M) (v:real^N) f x.
        ~(u IN a) /\
        (!x y. x IN a /\ y IN a /\ y IN segment[u,x] ==> y = x) /\
        x IN a
        ==> moi_con_conemap a u v f x = f x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`a:real^M->bool`; `u:real^M`; `v:real^N`; `f:real^M->real^N`;
                 `x:real^M`; `&1`] MOI_CON_CONEMAP_EQ) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
  REWRITE_TAC[VECTOR_MUL_LID; VECTOR_ARITH `u + (x - u):real^N = x`]);;

let MOI_CON_CONEMAP_APEX = prove
 (`!a (u:real^M) (v:real^N) f.
        ~(u IN a) /\
        (!x y. x IN a /\ y IN a /\ y IN segment[u,x] ==> y = x) /\
        ~(a = {})
        ==> moi_con_conemap a u v f u = v`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `x:real^M` o GEN_REWRITE_RULE I
    [GSYM MEMBER_NOT_EMPTY]) THEN
  MP_TAC(ISPECL [`a:real^M->bool`; `u:real^M`; `v:real^N`; `f:real^M->real^N`;
                 `x:real^M`; `&0`] MOI_CON_CONEMAP_EQ) THEN
  ASM_REWRITE_TAC[REAL_POS; REAL_LE_REFL] THEN
  REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID; REAL_POS]);;

let MOI_CON_CONEMAP_AFFINE_CONE = prove
 (`!a (u:real^M) (v:real^N) f s n (L:real^M->real^N) c.
        ~(u IN a) /\
        (!x y. x IN a /\ y IN a /\ y IN segment[u,x] ==> y = x) /\
        ~(a = {}) /\ n simplex s /\ s SUBSET a /\ ~(u IN affine hull s) /\
        linear L /\ (!z. z IN s ==> f z = L z + c)
        ==> ?L' c'. linear L' /\
                    !z. z IN convex hull (u INSERT s)
                        ==> moi_con_conemap a u v f z = L' z + c'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real^M->bool = {}` THENL
   [EXISTS_TAC `(\x. vec 0):real^M->real^N` THEN EXISTS_TAC `v:real^N` THEN
    ASM_REWRITE_TAC[LINEAR_ZERO; CONVEX_HULL_SING; IN_SING] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_ADD_LID] THEN
    MATCH_MP_TAC MOI_CON_CONEMAP_APEX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `n simplex (s:real^M->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^M->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `~((u:real^M) IN affine hull V)` ASSUME_TAC THENL
   [UNDISCH_TAC `~((u:real^M) IN affine hull (convex hull V))` THEN
    REWRITE_TAC[AFFINE_HULL_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((u:real^M) IN V)` ASSUME_TAC THENL
   [ASM_MESON_TAC[HULL_INC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(u:real^M) INSERT V`;
                 `\w:real^M. if w = u then (v:real^N) else L w + c`]
    MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ASM_SIMP_TAC[AFFINE_INDEPENDENT_INSERT] THEN
  DISCH_THEN(X_CHOOSE_THEN `L':real^M->real^N` (X_CHOOSE_THEN `c':real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`L':real^M->real^N`; `c':real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(L':real^M->real^N) u + c' = v` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `u:real^M`) THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w:real^M. w IN convex hull V ==> (L':real^M->real^N) w + c' = L w + c`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_REAL_AFFINE_EQ_ON_CONVEX_HULL THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^M` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^M`) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN
    COND_CASES_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^M` THEN
  MP_TAC(ISPECL [`convex hull V:real^M->bool`; `u:real^M`]
    CONVEX_HULL_INSERT) THEN
  ASM_REWRITE_TAC[HULL_HULL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `al:real` (X_CHOOSE_THEN `be:real`
    (X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `z:real^M = u + be % (w - u)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `al = &1 - be` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^M) IN a` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^M->bool`; `u:real^M`; `v:real^N`; `f:real^M->real^N`;
                 `w:real^M`; `be:real`] MOI_CON_CONEMAP_EQ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `(f:real^M->real^N) w = L' w + c'` SUBST1_TAC THENL
   [ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBST1_TAC(SYM(ASSUME `(L':real^M->real^N) u + c' = v`)) THEN
  REWRITE_TAC[MATCH_MP LINEAR_ADD (ASSUME `linear (L':real^M->real^N)`);
              MATCH_MP LINEAR_CMUL (ASSUME `linear (L':real^M->real^N)`);
              MATCH_MP LINEAR_SUB (ASSUME `linear (L':real^M->real^N)`)] THEN
  VECTOR_ARITH_TAC);;

let MOI_CON_CONEMAP_PL = prove
 (`!a (u:real^M) (v:real^N) f.
        pl_polyhedron a /\ ~(a = {}) /\ ~(u IN a) /\
        (!x y. x IN a /\ y IN a /\ y IN segment[u,x] ==> y = x) /\
        pl_map_on a f
        ==> pl_map_on (UNIONS {segment[u,x] | x IN a})
                      (moi_con_conemap a u v f)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `pl_polyhedron (a:real^M->bool)` THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`cc:(real^M->bool)->bool`; `f:real^M->real^N`]
    SIMPLICIAL_SUBDIVISION_PL_MAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^M->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^M->bool)->bool`; `u:real^M`]
    SIMPLICIAL_CONE_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`moi_con_conemap (a:real^M->bool) u (v:real^N) f`;
                 `t UNION {convex hull ((u:real^M) INSERT s) | s IN t}`]
    MOI_REAL_PIECEWISE_AFFINE_UNIONS) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  X_GEN_TAC `k:real^M->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CON_SC_POLYTOPE THEN
    EXISTS_TAC `t UNION {convex hull ((u:real^M) INSERT s) | s IN t}` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `(k:real^M->bool) IN t UNION {convex hull (u INSERT s) | s IN t}` THEN
  REWRITE_TAC[IN_UNION; IN_ELIM_THM] THEN STRIP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k:real^M->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `L:real^M->real^N` (X_CHOOSE_THEN `c:real^N`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`L:real^M->real^N`; `c:real^N`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^M` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^M) IN a` ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS t:real^M->bool = a` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `k:real^M->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`a:real^M->bool`; `u:real^M`; `v:real^N`;
                   `f:real^M->real^N`; `z:real^M`] MOI_CON_CONEMAP_ON_BASE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^M->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^M->real^N` (X_CHOOSE_THEN `c:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^M->bool)->bool`; `s:real^M->bool`]
    MOI_CON_SC_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `n:int`) THEN
  MATCH_MP_TAC MOI_CON_CONEMAP_AFFINE_CONE THEN
  MAP_EVERY EXISTS_TAC [`n:int`; `L:real^M->real^N`; `c:real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `UNIONS t:real^M->bool = a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `(s:real^M->bool) IN t ==> s SUBSET UNIONS t`) THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_CON_SC_NOT_IN_AFFINE_HULL THEN
    EXISTS_TAC `t:(real^M->bool)->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_CON_CONEMAP_INTO = prove
 (`!a b (u:real^M) (v:real^N) f.
        ~(u IN a) /\
        (!x y. x IN a /\ y IN a /\ y IN segment[u,x] ==> y = x) /\
        (!x. x IN a ==> f x IN b)
        ==> !p. p IN UNIONS {segment[u,x] | x IN a}
                ==> moi_con_conemap a u v f p IN UNIONS {segment[v,y] | y IN b}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MOI_CON_IN_CONE] THEN
  X_GEN_TAC `p:real^M` THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^M` (X_CHOOSE_THEN `r:real`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  MP_TAC(ISPECL [`a:real^M->bool`; `u:real^M`; `v:real^N`; `f:real^M->real^N`;
                 `x:real^M`; `r:real`] MOI_CON_CONEMAP_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MAP_EVERY EXISTS_TAC [`(f:real^M->real^N) x`; `r:real`] THEN
  ASM_SIMP_TAC[]);;

let MOI_CON_CONEMAP_INVERSE = prove
 (`!a b (u:real^M) (v:real^N) f g.
        ~(u IN a) /\
        (!x y. x IN a /\ y IN a /\ y IN segment[u,x] ==> y = x) /\
        ~(v IN b) /\
        (!x y. x IN b /\ y IN b /\ y IN segment[v,x] ==> y = x) /\
        (!x. x IN a ==> f x IN b /\ g (f x) = x)
        ==> !p. p IN UNIONS {segment[u,x] | x IN a}
                ==> moi_con_conemap b v u g (moi_con_conemap a u v f p) = p`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[MOI_CON_IN_CONE] THEN
  X_GEN_TAC `p:real^M` THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^M` (X_CHOOSE_THEN `r:real`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN
  MP_TAC(ISPECL [`a:real^M->bool`; `u:real^M`; `v:real^N`; `f:real^M->real^N`;
                 `x:real^M`; `r:real`] MOI_CON_CONEMAP_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`b:real^N->bool`; `v:real^N`; `u:real^M`; `g:real^N->real^M`;
                 `(f:real^M->real^N) x`; `r:real`] MOI_CON_CONEMAP_EQ) THEN
  ASM_SIMP_TAC[]);;

let MOI_CON_CONE_MAP = prove
 (`!(a:real^M->bool) (b:real^N->bool) u v f g.
        pl_polyhedron a /\ ~(a = {}) /\ ~(u IN a) /\
        (!x y. x IN a /\ y IN a /\ y IN segment[u,x] ==> y = x) /\
        ~(v IN b) /\
        (!x y. x IN b /\ y IN b /\ y IN segment[v,x] ==> y = x) /\
        pl_homeomorphism (a,b) (f,g)
        ==> pl_homeomorphism (UNIONS {segment[u,x] | x IN a},
                              UNIONS {segment[v,y] | y IN b})
                             (moi_con_conemap a u v f,
                              moi_con_conemap b v u g) /\
            (!x. x IN a ==> moi_con_conemap a u v f x = f x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [pl_homeomorphism]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `pl_polyhedron (b:real^N->bool)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check
      (fun th -> is_eq(concl th) && rhs(concl th) = `b:real^N->bool`)) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(b:real^N->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^M->real^N) a = b` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^M. x IN a ==> (f:real^M->real^N) x IN b /\ (g:real^N->real^M)(f x) = x` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^M->real^N) a = b` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN b ==> (g:real^N->real^M) y IN a /\ (f:real^M->real^N)(g y) = y` ASSUME_TAC THENL
   [UNDISCH_TAC `IMAGE (g:real^N->real^M) b = a` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on (UNIONS {segment[u,x] | x IN a})
              (moi_con_conemap (a:real^M->bool) (u:real^M) (v:real^N) f) /\
    pl_map_on (UNIONS {segment[v,y] | y IN b})
              (moi_con_conemap (b:real^N->bool) (v:real^N) (u:real^M) g)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_CON_CONEMAP_PL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ALL_TAC;
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_CONEMAP_ON_BASE THEN
    ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM] THEN
  ASM_SIMP_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
  REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_CON_CONEMAP_INTO THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_CON_CONEMAP_INTO THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_CON_CONEMAP_INVERSE THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_CON_CONEMAP_INVERSE THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* 7. Conewise extension over simplex boundaries and cones over PL spheres   *)
(* (PL_HOMEOMORPHISM_CONE_EXTENSION and PL_BALL_CONE).                       *)
(* ------------------------------------------------------------------------- *)

let MOI_CON_SIMPLEX_RF_FACTS = prove
 (`!k:real^N->bool n.
        n simplex k /\ &1 <= n
        ==> pl_polyhedron (relative_frontier k) /\
            ~(relative_frontier k = {}) /\
            ~(simplex_barycentre k IN relative_frontier k) /\
            (!x y. x IN relative_frontier k /\ y IN relative_frontier k /\
                   y IN segment[simplex_barycentre k,x] ==> y = x) /\
            UNIONS {segment[simplex_barycentre k,x] | x |
                    x IN relative_frontier k} = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(k:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `n simplex ({}:real^N->bool)` THEN
    REWRITE_TAC[SIMPLEX_EMPTY] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (k:real^N->bool) IN relative_interior k`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ compact k /\ polytope k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT;
                  SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_frontier k:real^N->bool = {})` ASSUME_TAC THENL
   [REWRITE_TAC[RELATIVE_FRONTIER_EQ_EMPTY] THEN DISCH_TAC THEN
    MP_TAC(ISPEC `k:real^N->bool` AFFINE_BOUNDED_EQ_TRIVIAL) THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `n simplex {a:real^N}` THEN REWRITE_TAC[SIMPLEX_SING] THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `{f:real^N->bool | f facet_of k}` THEN
    ASM_SIMP_TAC[FINITE_POLYTOPE_FACETS; IN_ELIM_THM;
                 RELATIVE_FRONTIER_OF_POLYHEDRON; POLYTOPE_IMP_POLYHEDRON] THEN
    ASM_MESON_TAC[FACE_OF_POLYTOPE_POLYTOPE; facet_of];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_RF_SEGMENT THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `simplex_barycentre (k:real^N->bool)`]
    THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_CON_CONE_RF THEN ASM_REWRITE_TAC[]]);;

let PL_HOMEOMORPHISM_CONE_EXTENSION = prove
 (`!(k:real^N->bool) (k':real^M->bool) n f g.
     &n simplex k /\ &n simplex k' /\
     pl_homeomorphism (relative_frontier k,relative_frontier k') (f,g)
     ==> ?f' g'. pl_homeomorphism (k,k') (f',g') /\
                 !x. x IN relative_frontier k ==> f' x = f x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_CASES_TAC `n = 0` THENL
   [UNDISCH_TAC `&n simplex (k:real^N->bool)` THEN
    UNDISCH_TAC `&n simplex (k':real^M->bool)` THEN
    ASM_REWRITE_TAC[SIMPLEX_ZERO] THEN
    DISCH_THEN(X_CHOOSE_THEN `a':real^M` SUBST_ALL_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    MAP_EVERY EXISTS_TAC [`(\x. a'):real^N->real^M`; `(\x. a):real^M->real^N`] THEN
    REWRITE_TAC[RELATIVE_FRONTIER_SING; NOT_IN_EMPTY] THEN
    REWRITE_TAC[pl_homeomorphism; HOMEOMORPHISM] THEN
    SIMP_TAC[PL_MAP_ON_CONST; LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_SING;
             CONTINUOUS_ON_CONST] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&n:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  MP_TAC(ISPECL [`k':real^M->bool`; `&n:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier k:real^N->bool`;
                 `relative_frontier k':real^M->bool`;
                 `simplex_barycentre (k:real^N->bool)`;
                 `simplex_barycentre (k':real^M->bool)`;
                 `f:real^N->real^M`; `g:real^M->real^N`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[]);;

let PL_BALL_CONE = prove
 (`!n (s:real^N->bool) v.
     pl_sphere n s /\ ~(v IN s) /\
     (!x y. x IN s /\ y IN s /\ y IN segment[v,x] ==> y = x)
     ==> pl_ball (n + 1) (UNIONS {segment[v,x] | x IN s})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_ball] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
     (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC)))
   STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&(n + 1):int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ASM_REWRITE_TAC[INT_OF_NUM_LE] THEN
  ANTS_TAC THENL [ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier k:real^N->bool`; `s:real^N->bool`;
                 `simplex_barycentre (k:real^N->bool)`; `v:real^N`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC
   [`k:real^N->bool`;
    `moi_con_conemap (relative_frontier k) (simplex_barycentre k) (v:real^N)
                     (f:real^N->real^N)`;
    `moi_con_conemap (s:real^N->bool) (v:real^N)
                     (simplex_barycentre (k:real^N->bool)) (g:real^N->real^N)`]
  THEN ASM_REWRITE_TAC[]);;

