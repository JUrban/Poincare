(* ========================================================================= *)
(* pc_moi_lfopen: locally finite triangulations of relatively open subsets   *)
(* of polyhedra (Moise GTM 47, Theorem 8.2, printed pp.58-59), proved from   *)
(* the subdivision extension hypothesis SIMPLICIAL_SUBDIVISION_EXTEND        *)
(* (pc_moi_cone): the theorem LF_TRIANGULATION_OPEN_SUBSET_FROM_EXTEND.      *)
(* ========================================================================= *)

needs "src/pc_moi_assembly.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_bary.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: gluing finite simplicial complexes.                               *)
(* ------------------------------------------------------------------------- *)

(* A subset of a simplicial complex closed under faces is a complex.         *)

let MOI_LFO_SUBCOMPLEX = prove
 (`!(k:(real^N->bool)->bool) k'.
     simplicial_complex k /\ k' SUBSET k /\
     (!f s. s IN k' /\ f face_of s ==> f IN k')
     ==> simplicial_complex k'`,
  REWRITE_TAC[simplicial_complex; SUBSET] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `k:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[SUBSET];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[];
    ASM_MESON_TAC[]]);;

(* Two complexes whose polyhedra meet only along common simplices glue to a  *)
(* complex.  The intersection of s in x and t in y is the face              *)
(* t INTER (s INTER w) of both, where w is a common simplex through a point *)
(* of the relative interior of s INTER t.                                     *)

let MOI_LFO_UNION_COMPLEX_INTER = prove
 (`!(x:(real^N->bool)->bool) y s t.
     simplicial_complex x /\ simplicial_complex y /\
     UNIONS x INTER UNIONS y SUBSET UNIONS (x INTER y) /\
     s IN x /\ t IN y
     ==> (s INTER t) face_of s /\ (s INTER t) face_of t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s INTER t:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[EMPTY_FACE_OF]; ALL_TAC] THEN
  SUBGOAL_THEN `convex(s INTER t:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONVEX_INTER THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^N. z IN relative_interior(s INTER t)`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN s /\ z IN t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET; IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N) IN UNIONS (x INTER y:(real^N->bool)->bool)`
    MP_TAC THENL
   [FIRST_ASSUM (MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_INTER] THEN
  DISCH_THEN (X_CHOOSE_THEN `w:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(s INTER w:real^N->bool) face_of s /\ (s INTER w) face_of w`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(s INTER w:real^N->bool) IN y` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(t INTER (s INTER w):real^N->bool) face_of t /\
                (t INTER (s INTER w)) face_of (s INTER w)`
    STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(t INTER (s INTER w):real^N->bool) face_of s` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `s INTER t SUBSET (t INTER (s INTER w):real^N->bool)`
    ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[INTER_SUBSET; DISJOINT] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t INTER (s INTER w):real^N->bool = s INTER t`
    (fun th -> ASM_MESON_TAC[th]) THEN
  ASM SET_TAC[]);;

let MOI_LFO_UNION_COMPLEX = prove
 (`!(x:(real^N->bool)->bool) y.
     simplicial_complex x /\ simplicial_complex y /\
     UNIONS x INTER UNIONS y SUBSET UNIONS (x INTER y)
     ==> simplicial_complex (x UNION y)`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[simplicial_complex; IN_UNION] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; FINITE_UNION];
    ASM_MESON_TAC[simplicial_complex];
    ASM_MESON_TAC[simplicial_complex];
    REPEAT GEN_TAC THEN STRIP_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      ASM_MESON_TAC[MOI_LFO_UNION_COMPLEX_INTER];
      ONCE_REWRITE_TAC[INTER_COMM] THEN
      ASM_MESON_TAC[MOI_LFO_UNION_COMPLEX_INTER];
      ASM_MESON_TAC[simplicial_complex]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: an increasing union of finite complexes glued layer by layer is  *)
(* a locally finite complex.  The layer nc r covers a r minus a(r - 1), it  *)
(* meets a r only along common simplices of nc r and nc(r + 1), it misses   *)
(* a(r - 2), and a r lies in the interior of a(r + 1) relative to x0.        *)
(* ------------------------------------------------------------------------- *)

let MOI_LFO_IN_UNIONS_IMAGE = prove
 (`!(nc:num->A->bool) s. s IN UNIONS (IMAGE nc (:num)) <=> ?r. s IN nc r`,
  REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_UNIV] THEN MESON_TAC[]);;

let MOI_LFO_IN_UNIONS2 = prove
 (`!(nc:num->(A->bool)->bool) x.
     x IN UNIONS (UNIONS (IMAGE nc (:num))) <=> ?r s. s IN nc r /\ x IN s`,
  REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_UNIV] THEN MESON_TAC[]);;

let MOI_LFO_PREFIX_SUBSET = prove
 (`!(nc:num->A->bool) i r. i <= r ==> nc i SUBSET UNIONS (IMAGE nc (0..r))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_IMAGE; IN_NUMSEG] THEN
  X_GEN_TAC `s:A` THEN DISCH_TAC THEN EXISTS_TAC `(nc:num->A->bool) i` THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[LE_0]);;

let MOI_LFO_CHAIN_PREFIX = prove
 (`!(nc:num->(A->bool)->bool) (a:num->A->bool).
     UNIONS (nc 0) = a 0 /\
     (!r. a r UNION UNIONS (nc (SUC r)) = a (SUC r))
     ==> !r. UNIONS (UNIONS (IMAGE nc (0..r))) = a r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[NUMSEG_SING; IMAGE_CLAUSES; UNIONS_1];
    REWRITE_TAC[NUMSEG_CLAUSES; LE_0; IMAGE_CLAUSES; UNIONS_INSERT;
                UNIONS_UNION] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[UNION_COMM] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LFO_CHAIN_PREFIX_SC = prove
 (`!(nc:num->(real^N->bool)->bool) (a:num->real^N->bool).
     (!r. simplicial_complex (nc r)) /\
     UNIONS (nc 0) = a 0 /\
     (!r. a r UNION UNIONS (nc (SUC r)) = a (SUC r)) /\
     (!r. a r INTER UNIONS (nc (SUC r)) SUBSET UNIONS (nc r INTER nc (SUC r)))
     ==> !r. simplicial_complex (UNIONS (IMAGE nc (0..r)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`nc:num->(real^N->bool)->bool`; `a:num->real^N->bool`]
    MOI_LFO_CHAIN_PREFIX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN INDUCT_TAC THENL
   [ASM_REWRITE_TAC[NUMSEG_SING; IMAGE_CLAUSES; UNIONS_1];
    ALL_TAC] THEN
  REWRITE_TAC[NUMSEG_CLAUSES; LE_0; IMAGE_CLAUSES; UNIONS_INSERT] THEN
  ONCE_REWRITE_TAC[UNION_COMM] THEN MATCH_MP_TAC MOI_LFO_UNION_COMPLEX THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `UNIONS ((nc:num->(real^N->bool)->bool) r INTER nc (SUC r))` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_UNIONS THEN
  MP_TAC (ISPECL [`nc:num->(real^N->bool)->bool`; `r:num`; `r:num`]
    MOI_LFO_PREFIX_SUBSET) THEN
  REWRITE_TAC[LE_REFL] THEN SET_TAC[]);;

let MOI_LFO_CHAIN_LF = prove
 (`!(nc:num->(real^N->bool)->bool) (a:num->real^N->bool) (x0:real^N->bool).
     (!r. simplicial_complex (nc r)) /\
     UNIONS (nc 0) = a 0 /\
     (!r. a r UNION UNIONS (nc (SUC r)) = a (SUC r)) /\
     (!r. a r INTER UNIONS (nc (SUC r)) SUBSET UNIONS (nc r INTER nc (SUC r))) /\
     (!r. a r INTER UNIONS (nc (SUC (SUC r))) = {}) /\
     (!r. a r SUBSET x0) /\
     (!r x. x IN a r ==> ?v. open v /\ x IN v /\ v INTER x0 SUBSET a (SUC r))
     ==> lf_simplicial_complex (UNIONS (IMAGE nc (:num))) /\
         UNIONS (UNIONS (IMAGE nc (:num))) = UNIONS (IMAGE a (:num))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`nc:num->(real^N->bool)->bool`; `a:num->real^N->bool`]
    MOI_LFO_CHAIN_PREFIX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC (ISPECL [`nc:num->(real^N->bool)->bool`; `a:num->real^N->bool`]
    MOI_LFO_CHAIN_PREFIX_SC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!m n. m <= n ==> (a:num->real^N->bool) m SUBSET a n`
    ASSUME_TAC THENL
   [MATCH_MP_TAC TRANSITIVE_STEPWISE_LE THEN
    REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    X_GEN_TAC `n:num` THEN
    MP_TAC (SPEC `n:num` (ASSUME
     `!r. (a:num->real^N->bool) r UNION UNIONS (nc (SUC r)) = a (SUC r)`)) THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. UNIONS ((nc:num->(real^N->bool)->bool) r) SUBSET a r`
    ASSUME_TAC THENL
   [GEN_TAC THEN
    GEN_REWRITE_TAC RAND_CONV
     [GSYM (SPEC `r:num` (ASSUME
       `!r. UNIONS (UNIONS (IMAGE (nc:num->(real^N->bool)->bool) (0..r))) =
            a r`))] THEN
    MATCH_MP_TAC SUBSET_UNIONS THEN
    MATCH_MP_TAC MOI_LFO_PREFIX_SUBSET THEN REWRITE_TAC[LE_REFL];
    ALL_TAC] THEN
  REWRITE_TAC[lf_simplicial_complex; MOI_LFO_IN_UNIONS_IMAGE] THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_complex];
    ASM_MESON_TAC[simplicial_complex];
    REPEAT GEN_TAC THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `i:num`)
                                (X_CHOOSE_TAC `j:num`)) THEN
    SUBGOAL_THEN
     `(s:real^N->bool) IN UNIONS (IMAGE nc (0..i+j)) /\
      (s':real^N->bool) IN UNIONS (IMAGE nc (0..i+j))`
     STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      MATCH_MP_TAC (SET_RULE `!s t x:A. x IN s /\ s SUBSET t ==> x IN t`) THEN
      ASM_MESON_TAC[MOI_LFO_PREFIX_SUBSET; LE_ADD; LE_ADDR];
      ALL_TAC] THEN
    ASM_MESON_TAC[simplicial_complex];
    X_GEN_TAC `y:real^N` THEN REWRITE_TAC[MOI_LFO_IN_UNIONS2] THEN
    DISCH_THEN (X_CHOOSE_THEN `q:num`
      (X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^N) IN a (q:num)` ASSUME_TAC THENL
     [MP_TAC (SPEC `q:num` (ASSUME
       `!r. UNIONS ((nc:num->(real^N->bool)->bool) r) SUBSET a r`)) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC (MP (SPECL [`q:num`; `y:real^N`] (ASSUME
     `!r x. x IN (a:num->real^N->bool) r
            ==> ?v. open v /\ x IN v /\ v INTER x0 SUBSET a (SUC r)`))
     (ASSUME `(y:real^N) IN a (q:num)`)) THEN
    MATCH_MP_TAC MONO_EXISTS THEN
    X_GEN_TAC `v:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `UNIONS (IMAGE (nc:num->(real^N->bool)->bool) (0..SUC(SUC q)))` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN (CONJUNCTS_THEN2 (X_CHOOSE_TAC `p:num`) ASSUME_TAC) THEN
    ASM_CASES_TAC `p <= SUC(SUC q)` THENL
     [ASM_MESON_TAC[MOI_LFO_PREFIX_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `?p'. p = SUC(SUC p') /\ SUC q <= p'` STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `p - 2` THEN ASM_ARITH_TAC; ALL_TAC] THEN
    UNDISCH_TAC `p = SUC(SUC p')` THEN DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) INTER v = {}`
      (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS (nc (SUC (SUC p')))`
      ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET x0` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET_TRANS]; ALL_TAC] THEN
    MP_TAC (SPEC `p':num` (ASSUME
     `!r. (a:num->real^N->bool) r INTER UNIONS (nc (SUC (SUC r))) = {}`)) THEN
    SUBGOAL_THEN `(a:num->real^N->bool) (SUC q) SUBSET a p'` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `v INTER x0 SUBSET (a:num->real^N->bool) (SUC q)` THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET x0` THEN
    UNDISCH_TAC `(s:real^N->bool) SUBSET UNIONS (nc (SUC (SUC p')))` THEN
    SET_TAC[];
    REWRITE_TAC[EXTENSION; MOI_LFO_IN_UNIONS2; MOI_LFO_IN_UNIONS_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [REWRITE_TAC[LEFT_IMP_EXISTS_THM] THEN
      MAP_EVERY X_GEN_TAC [`q:num`; `s:real^N->bool`] THEN STRIP_TAC THEN
      EXISTS_TAC `q:num` THEN
      MP_TAC (SPEC `q:num` (ASSUME
       `!r. UNIONS ((nc:num->(real^N->bool)->bool) r) SUBSET a r`)) THEN
      REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[];
      DISCH_THEN (X_CHOOSE_TAC `q:num`) THEN
      SUBGOAL_THEN
       `(y:real^N) IN UNIONS (UNIONS (IMAGE (nc:num->(real^N->bool)->bool)
                                           (0..q)))`
       MP_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_NUMSEG] THEN MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: refinement between complexes, and the iterated barycentric       *)
(* subdivisions K_m = ITER m barycentric_subdivision c (Moise's K_1, K_2,   *)
(* ... with mesh tending to 0).                                              *)
(* ------------------------------------------------------------------------- *)

(* k' refines k: every nonempty simplex of k' lies in a simplex of k, and   *)
(* every simplex of k is covered by the simplices of k' inside it.          *)

let moi_lfo_refines = new_definition
 `moi_lfo_refines (k':(real^N->bool)->bool) (k:(real^N->bool)->bool) <=>
    (!s. s IN k' /\ ~(s = {}) ==> ?t. t IN k /\ s SUBSET t) /\
    (!t x. t IN k /\ x IN t ==> ?s. s IN k' /\ s SUBSET t /\ x IN s)`;;

let MOI_LFO_REFINES_REFL = prove
 (`!k:(real^N->bool)->bool. moi_lfo_refines k k`,
  REWRITE_TAC[moi_lfo_refines] THEN MESON_TAC[SUBSET_REFL]);;

let MOI_LFO_REFINES_TRANS = prove
 (`!k1 k2 k3:(real^N->bool)->bool.
     moi_lfo_refines k2 k1 /\ moi_lfo_refines k3 k2
     ==> moi_lfo_refines k3 k1`,
  REWRITE_TAC[moi_lfo_refines] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[SUBSET_TRANS; SUBSET_EMPTY];
    ASM_MESON_TAC[SUBSET_TRANS]]);;

let MOI_LFO_REFINES_UNIONS = prove
 (`!k k' t:real^N->bool.
     moi_lfo_refines k' k /\ t IN k
     ==> t = UNIONS {s | s IN k' /\ s SUBSET t}`,
  REWRITE_TAC[moi_lfo_refines] THEN REPEAT STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN MESON_TAC[]]);;

let MOI_LFO_REFINES_BSD = prove
 (`!k:(real^N->bool)->bool.
     simplicial_complex k ==> moi_lfo_refines (barycentric_subdivision k) k`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC (ISPEC `k:(real^N->bool)->bool` BARYCENTRIC_SUBDIVISION_REFINES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  STRIP_TAC THEN REWRITE_TAC[moi_lfo_refines] THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `x:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPEC `t:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN (X_CHOOSE_THEN `f:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS f` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]);;

let MOI_LFO_SIMPLEX_COMPACT = prove
 (`!k s:real^N->bool.
     simplicial_complex k /\ s IN k ==> compact s /\ convex s /\ bounded s`,
  REWRITE_TAC[simplicial_complex] THEN
  MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX; COMPACT_IMP_BOUNDED]);;

let MOI_LFO_ITER_SC = prove
 (`!(c:(real^N->bool)->bool) n.
     simplicial_complex c
     ==> simplicial_complex (ITER n barycentric_subdivision c)`,
  MESON_TAC[MOI_BAR_ITER_SUBDIVISION]);;

let MOI_LFO_ITER_UNIONS = prove
 (`!(c:(real^N->bool)->bool) n.
     simplicial_complex c
     ==> UNIONS (ITER n barycentric_subdivision c) = UNIONS c`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN SPEC_TAC (`n:num`,`n:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ITER] THEN
  FIRST_X_ASSUM (fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
  MATCH_MP_TAC UNIONS_BARYCENTRIC_SUBDIVISION THEN
  ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF; MOI_LFO_ITER_SC]);;

let MOI_LFO_ITER_REFINES = prove
 (`!(c:(real^N->bool)->bool) m n.
     simplicial_complex c /\ n <= m
     ==> moi_lfo_refines (ITER m barycentric_subdivision c)
                         (ITER n barycentric_subdivision c)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[LE_EXISTS] THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `d:num` SUBST1_TAC)) THEN
  SPEC_TAC (`d:num`,`d:num`) THEN
  INDUCT_TAC THEN REWRITE_TAC[ADD_CLAUSES; ITER; MOI_LFO_REFINES_REFL] THEN
  MATCH_MP_TAC MOI_LFO_REFINES_TRANS THEN
  EXISTS_TAC `ITER (n + d) barycentric_subdivision (c:(real^N->bool)->bool)` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LFO_REFINES_BSD THEN
  ASM_MESON_TAC[MOI_LFO_ITER_SC]);;

let MOI_LFO_ITER_SIMPLEX = prove
 (`!(c:(real^N->bool)->bool) m s.
     simplicial_complex c /\ s IN ITER m barycentric_subdivision c
     ==> bounded s /\ s SUBSET UNIONS c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_LFO_SIMPLEX_COMPACT; MOI_LFO_ITER_SC];
    ASM_MESON_TAC[MOI_LFO_ITER_UNIONS; SUBSET; IN_UNIONS]]);;

let MOI_LFO_ITER_FINE = prove
 (`!(c:(real^N->bool)->bool) e.
     simplicial_complex c /\ &0 < e
     ==> ?n. !m s. n <= m /\ s IN ITER m barycentric_subdivision c
                   ==> diameter s < e`,
  REPEAT STRIP_TAC THEN
  MP_TAC (ISPECL [`c:(real^N->bool)->bool`; `e:real`]
    ITERATED_BARYCENTRIC_SUBDIVISION_FINE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN
  MAP_EVERY X_GEN_TAC [`m:num`; `s:real^N->bool`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[DIAMETER_EMPTY]; ALL_TAC] THEN
  MP_TAC (ISPECL [`c:(real^N->bool)->bool`; `m:num`; `n:num`]
    MOI_LFO_ITER_REFINES) THEN
  ASM_REWRITE_TAC[moi_lfo_refines] THEN
  DISCH_THEN (MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `diameter(t:real^N->bool)` THEN
  CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
  MATCH_MP_TAC DIAMETER_SUBSET THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MOI_LFO_ITER_SIMPLEX]);;

(* ------------------------------------------------------------------------- *)
(* Part 4: the layers of Moise's proof, for a complex k (= K_(n_r)), the    *)
(* next complex k' (= K_(n_(r+1))) refining it, the open set u and the      *)
(* union b of the earlier layers.                                            *)
(*   moi_lfo_poly k u      the union of the simplices of k inside u;        *)
(*   moi_lfo_layer k u b   the simplices of k inside u but not inside b,    *)
(*                         with their faces (Moise's L_r);                   *)
(*   moi_lfo_outer k u b   the simplices of the layer missing b (the part    *)
(*                         that is subdivided);                              *)
(*   moi_lfo_restrict k' f the simplices of k' inside a simplex of f.        *)
(* ------------------------------------------------------------------------- *)

let moi_lfo_poly = new_definition
 `moi_lfo_poly (k:(real^N->bool)->bool) (u:real^N->bool) =
    UNIONS {s | s IN k /\ s SUBSET u}`;;

let moi_lfo_layer = new_definition
 `moi_lfo_layer (k:(real^N->bool)->bool) (u:real^N->bool) (b:real^N->bool) =
    {t | ?s. s IN k /\ s SUBSET u /\ ~(s SUBSET b) /\ t face_of s}`;;

let moi_lfo_outer = new_definition
 `moi_lfo_outer (k:(real^N->bool)->bool) (u:real^N->bool) (b:real^N->bool) =
    {s | s IN moi_lfo_layer k u b /\ s INTER b = {}}`;;

let moi_lfo_restrict = new_definition
 `moi_lfo_restrict (k':(real^N->bool)->bool) (f:(real^N->bool)->bool) =
    {s | s IN k' /\ ?t. t IN f /\ s SUBSET t}`;;

let MOI_LFO_IN_POLY = prove
 (`!k u (x:real^N).
     x IN moi_lfo_poly k u <=> ?s. s IN k /\ s SUBSET u /\ x IN s`,
  REWRITE_TAC[moi_lfo_poly; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_LFO_IN_LAYER = prove
 (`!k u b (t:real^N->bool).
     t IN moi_lfo_layer k u b <=>
     ?s. s IN k /\ s SUBSET u /\ ~(s SUBSET b) /\ t face_of s`,
  REWRITE_TAC[moi_lfo_layer; IN_ELIM_THM]);;

let MOI_LFO_IN_OUTER = prove
 (`!k u b (s:real^N->bool).
     s IN moi_lfo_outer k u b <=> s IN moi_lfo_layer k u b /\ s INTER b = {}`,
  REWRITE_TAC[moi_lfo_outer; IN_ELIM_THM]);;

let MOI_LFO_IN_RESTRICT = prove
 (`!k' f (s:real^N->bool).
     s IN moi_lfo_restrict k' f <=> s IN k' /\ ?t. t IN f /\ s SUBSET t`,
  REWRITE_TAC[moi_lfo_restrict; IN_ELIM_THM]);;

let MOI_LFO_POLY_SUBSET = prove
 (`!k (u:real^N->bool).
     moi_lfo_poly k u SUBSET u /\ moi_lfo_poly k u SUBSET UNIONS k`,
  REWRITE_TAC[SUBSET; MOI_LFO_IN_POLY; IN_UNIONS] THEN MESON_TAC[]);;

let MOI_LFO_POLY_COMPACT = prove
 (`!k (u:real^N->bool).
     simplicial_complex k ==> compact (moi_lfo_poly k u)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_lfo_poly] THEN
  MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[MOI_LFO_SIMPLEX_COMPACT]]);;

let MOI_LFO_POLY_MONO = prove
 (`!k k' (u:real^N->bool).
     moi_lfo_refines k' k ==> moi_lfo_poly k u SUBSET moi_lfo_poly k' u`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lfo_refines] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[MOI_LFO_IN_POLY] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_MESON_TAC[SUBSET_TRANS]);;

let MOI_LFO_LAYER_SUBSET = prove
 (`!k u (b:real^N->bool).
     simplicial_complex k ==> moi_lfo_layer k u b SUBSET k`,
  REWRITE_TAC[simplicial_complex; SUBSET; MOI_LFO_IN_LAYER] THEN MESON_TAC[]);;

let MOI_LFO_LAYER_SC = prove
 (`!k u (b:real^N->bool).
     simplicial_complex k ==> simplicial_complex (moi_lfo_layer k u b)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LFO_SUBCOMPLEX THEN
  EXISTS_TAC `k:(real^N->bool)->bool` THEN
  ASM_SIMP_TAC[MOI_LFO_LAYER_SUBSET] THEN
  REWRITE_TAC[MOI_LFO_IN_LAYER] THEN MESON_TAC[FACE_OF_TRANS]);;

let MOI_LFO_OUTER_SC = prove
 (`!k u (b:real^N->bool).
     simplicial_complex k
     ==> simplicial_complex (moi_lfo_outer k u b) /\
         moi_lfo_outer k u b SUBSET moi_lfo_layer k u b`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `moi_lfo_outer k u b SUBSET moi_lfo_layer k u (b:real^N->bool)`
    ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_LFO_IN_OUTER] THEN MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LFO_SUBCOMPLEX THEN
  EXISTS_TAC `moi_lfo_layer k u (b:real^N->bool)` THEN
  ASM_SIMP_TAC[MOI_LFO_LAYER_SC] THEN
  REWRITE_TAC[MOI_LFO_IN_OUTER] THEN
  MAP_EVERY X_GEN_TAC [`g:real^N->bool`; `s:real^N->bool`] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_LFO_LAYER_SC; simplicial_complex];
    MP_TAC (ISPECL [`s:real^N->bool`; `g:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
    ASM SET_TAC[]]);;

let MOI_LFO_UNIONS_LAYER = prove
 (`!k u (b:real^N->bool).
     simplicial_complex k /\ b SUBSET moi_lfo_poly k u
     ==> b UNION UNIONS (moi_lfo_layer k u b) = moi_lfo_poly k u`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ASM_REWRITE_TAC[UNION_SUBSET] THEN
    REWRITE_TAC[UNIONS_SUBSET; MOI_LFO_IN_LAYER] THEN
    X_GEN_TAC `t:real^N->bool` THEN
    DISCH_THEN (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[MOI_LFO_IN_POLY] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET];
    GEN_REWRITE_TAC I [SUBSET] THEN
    REWRITE_TAC[MOI_LFO_IN_POLY; IN_UNION; IN_UNIONS; MOI_LFO_IN_LAYER] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(s:real^N->bool) SUBSET b` THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISJ2_TAC THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FACE_OF_REFL THEN ASM_MESON_TAC[MOI_LFO_SIMPLEX_COMPACT]]);;

let MOI_LFO_RESTRICT_PROPS = prove
 (`!k k' (f:(real^N->bool)->bool).
     simplicial_complex k' /\ moi_lfo_refines k' k /\ f SUBSET k
     ==> simplicial_complex (moi_lfo_restrict k' f) /\
         UNIONS (moi_lfo_restrict k' f) = UNIONS f /\
         (!s. s IN moi_lfo_restrict k' f ==> ?t. t IN f /\ s SUBSET t) /\
         (!t. t IN f ==> ?e. e SUBSET moi_lfo_restrict k' f /\ t = UNIONS e)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LFO_SUBCOMPLEX THEN
    EXISTS_TAC `k':(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[MOI_LFO_IN_RESTRICT] THEN
      MESON_TAC[];
      REWRITE_TAC[MOI_LFO_IN_RESTRICT] THEN
      MAP_EVERY X_GEN_TAC [`g:real^N->bool`; `s:real^N->bool`] THEN
      STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_complex];
        ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]]];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; MOI_LFO_IN_RESTRICT] THEN
      MESON_TAC[SUBSET_TRANS;
                SET_RULE `!t (f:(real^N->bool)->bool).
                            t IN f ==> t SUBSET UNIONS f`];
      GEN_REWRITE_TAC I [SUBSET] THEN
      REWRITE_TAC[IN_UNIONS; MOI_LFO_IN_RESTRICT] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `moi_lfo_refines k' (k:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_lfo_refines] THEN
      DISCH_THEN (MP_TAC o SPECL [`t:real^N->bool`; `x:real^N`] o CONJUNCT2) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[MOI_LFO_IN_RESTRICT] THEN MESON_TAC[];
    X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `{s | s IN k' /\ (s:real^N->bool) SUBSET t}` THEN CONJ_TAC THENL
     [GEN_REWRITE_TAC I [SUBSET] THEN
      REWRITE_TAC[IN_ELIM_THM; MOI_LFO_IN_RESTRICT] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC MOI_LFO_REFINES_UNIONS THEN
      EXISTS_TAC `k:(real^N->bool)->bool` THEN ASM SET_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 5: how consecutive layers meet.  Here k = K_(n_r), k' = K_(n_(r+1)) *)
(* and b = the union of the layers before r; the hypothesis on b is the     *)
(* mesh condition of the recursion: simplices of k meeting b lie in u.      *)
(* ------------------------------------------------------------------------- *)

(* A point of moi_lfo_poly k u on the next layer lies in a simplex of the   *)
(* layer of k that misses b (this simplex is q INTER q', with t' SUBSET q). *)

let MOI_LFO_J = prove
 (`!k k' (u:real^N->bool) b x.
     simplicial_complex k /\ moi_lfo_refines k' k /\
     (!s. s IN k /\ ~(s INTER b = {}) ==> s SUBSET u) /\
     x IN moi_lfo_poly k u /\
     x IN UNIONS (moi_lfo_layer k' u (moi_lfo_poly k u))
     ==> x IN UNIONS (moi_lfo_outer k u b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS (moi_lfo_layer k' u (moi_lfo_poly k u))` THEN
  REWRITE_TAC[IN_UNIONS; MOI_LFO_IN_LAYER] THEN
  DISCH_THEN (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^N) IN t'` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?q:real^N->bool. q IN k /\ t' SUBSET q` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lfo_refines k' (k:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_lfo_refines] THEN
    DISCH_THEN (MATCH_MP_TAC o CONJUNCT1) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN q` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN moi_lfo_poly k u` THEN
  REWRITE_TAC[MOI_LFO_IN_POLY] THEN
  DISCH_THEN (X_CHOOSE_THEN `q':real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(q INTER q':real^N->bool) IN k` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(q INTER q':real^N->bool) INTER b = {}` ASSUME_TAC THENL
   [MATCH_MP_TAC (TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:real^N->bool) SUBSET u` ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((t':real^N->bool) SUBSET moi_lfo_poly k u)` THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[MOI_LFO_IN_POLY] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; MOI_LFO_IN_OUTER; MOI_LFO_IN_LAYER] THEN
  EXISTS_TAC `q INTER q':real^N->bool` THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  EXISTS_TAC `q INTER q':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC FACE_OF_REFL THEN ASM_MESON_TAC[MOI_LFO_SIMPLEX_COMPACT]]);;

(* A point of moi_lfo_poly k u on the next layer lies in a simplex of that  *)
(* layer inside moi_lfo_poly k u (namely t' INTER q', q' a simplex of k'    *)
(* inside a simplex of k inside u).                                          *)

let MOI_LFO_G = prove
 (`!k k' (u:real^N->bool) x.
     simplicial_complex k' /\ moi_lfo_refines k' k /\
     x IN moi_lfo_poly k u /\
     x IN UNIONS (moi_lfo_layer k' u (moi_lfo_poly k u))
     ==> ?g. x IN g /\ g IN moi_lfo_layer k' u (moi_lfo_poly k u) /\
             g SUBSET moi_lfo_poly k u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS (moi_lfo_layer k' u (moi_lfo_poly k u))` THEN
  REWRITE_TAC[IN_UNIONS; MOI_LFO_IN_LAYER] THEN
  DISCH_THEN (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^N) IN t'` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN moi_lfo_poly k u` THEN
  REWRITE_TAC[MOI_LFO_IN_POLY] THEN
  DISCH_THEN (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?q':real^N->bool. q' IN k' /\ q' SUBSET q /\ x IN q'`
    STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lfo_refines k' (k:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_lfo_refines] THEN
    DISCH_THEN (MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `t' INTER q':real^N->bool` THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[MOI_LFO_IN_LAYER] THEN EXISTS_TAC `t':real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_complex];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `q:real^N->bool` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[MOI_LFO_IN_POLY] THEN
    ASM_MESON_TAC[]]);;

(* The layer after next misses the current polyhedron (Moise's condition   *)
(* that the union of the first r layers is a neighbourhood of the first     *)
(* r - 1 ones, in combinatorial form).                                       *)

let MOI_LFO_F4 = prove
 (`!k k' k'' (u:real^N->bool).
     moi_lfo_refines k'' k' /\
     (!s. s IN k' /\ ~(s INTER moi_lfo_poly k u = {}) ==> s SUBSET u)
     ==> moi_lfo_poly k u INTER
         UNIONS (moi_lfo_layer k'' u (moi_lfo_poly k' u)) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; MOI_LFO_IN_LAYER] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^N->bool`
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC)
                     ASSUME_TAC))) THEN
  SUBGOAL_THEN `(x:real^N) IN t'` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?s':real^N->bool. s' IN k' /\ t' SUBSET s'` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_lfo_refines k'' (k':(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_lfo_refines] THEN
    DISCH_THEN (MATCH_MP_TAC o CONJUNCT1) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s':real^N->bool) SUBSET u` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~((t':real^N->bool) SUBSET moi_lfo_poly k' u)` THEN
  REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `s':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[MOI_LFO_IN_POLY] THEN
  ASM_MESON_TAC[]);;

(* The interface: where the next layer meets moi_lfo_poly k u it is covered *)
(* by simplices common to the two subdivided layers n1 and n2.              *)

let MOI_LFO_INTERFACE = prove
 (`!k k' (u:real^N->bool) b (n1:(real^N->bool)->bool) n2.
     simplicial_complex k /\ simplicial_complex k' /\ moi_lfo_refines k' k /\
     (!s. s IN k /\ ~(s INTER b = {}) ==> s SUBSET u) /\
     (!s. s IN moi_lfo_restrict k' (moi_lfo_outer k u b) /\ ~(s = {})
          ==> s IN n1) /\
     (!t. t IN moi_lfo_layer k' u (moi_lfo_poly k u) /\
          DISJOINT t (UNIONS (moi_lfo_outer k' u (moi_lfo_poly k u)))
          ==> t IN n2)
     ==> moi_lfo_poly k u INTER UNIONS (moi_lfo_layer k' u (moi_lfo_poly k u))
         SUBSET UNIONS (n1 INTER n2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTER] THEN
  X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  MP_TAC (ISPECL [`k:(real^N->bool)->bool`; `k':(real^N->bool)->bool`;
                  `u:real^N->bool`; `x:real^N`] MOI_LFO_G) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_UNIONS; IN_INTER] THEN EXISTS_TAC `g:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[MOI_LFO_IN_RESTRICT] THEN
    SUBGOAL_THEN `(g:real^N->bool) IN k'` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_LFO_LAYER_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `~(g:real^N->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PLT_SIMPLEX_IN_COVER THEN
    EXISTS_TAC `k':(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    MP_TAC (ISPECL [`k:(real^N->bool)->bool`; `k':(real^N->bool)->bool`;
                    `u:real^N->bool`; `b:real^N->bool`; `y:real^N`]
      MOI_LFO_J) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `kk:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `{s | s IN k' /\ (s:real^N->bool) SUBSET kk}` THEN
    REWRITE_TAC[SUBSET_RESTRICT] THEN
    MATCH_MP_TAC MOI_LFO_REFINES_UNIONS THEN
    EXISTS_TAC `k:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_LFO_OUTER_SC; MOI_LFO_LAYER_SUBSET; SUBSET];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_UNIONS; NOT_IN_EMPTY;
                MOI_LFO_IN_OUTER] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 6: the choice of the numbers n_r (Moise's mesh condition, via a     *)
(* Lebesgue number of the compact set moi_lfo_poly K_n u inside the open    *)
(* set u), and exhaustion of u by the polyhedra moi_lfo_poly K_m u.          *)
(* ------------------------------------------------------------------------- *)

let MOI_LFO_NEXT = prove
 (`!(c:(real^N->bool)->bool) u.
     simplicial_complex c /\ open_in (subtopology euclidean (UNIONS c)) u
     ==> !n. ?m. n < m /\
           (!s. s IN ITER m barycentric_subdivision c /\
                ~(s INTER moi_lfo_poly (ITER n barycentric_subdivision c) u = {})
                ==> s SUBSET u) /\
           (!x. x IN moi_lfo_poly (ITER n barycentric_subdivision c) u
                ==> ?v. open v /\ x IN v /\
                        v INTER UNIONS c SUBSET
                        moi_lfo_poly (ITER m barycentric_subdivision c) u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `n:num` THEN
  FIRST_X_ASSUM (X_CHOOSE_THEN `w:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) o REWRITE_RULE[OPEN_IN_OPEN]) THEN
  DISCH_THEN (fun th ->
    SUBGOAL_THEN `(!y:real^N. y IN UNIONS c /\ y IN w ==> y IN u) /\
                  (u:real^N->bool) SUBSET w`
    MP_TAC THENL [REWRITE_TAC[th] THEN SET_TAC[]; ALL_TAC]) THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "uw") ASSUME_TAC) THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !x y:real^N. x IN moi_lfo_poly (ITER n barycentric_subdivision c) u /\
                     dist(x,y) < d ==> y IN w`
   (X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep")))
  THENL
   [MP_TAC (ISPECL
     [`moi_lfo_poly (ITER n barycentric_subdivision c) (u:real^N->bool)`;
      `(:real^N) DIFF w`] SEPARATE_COMPACT_CLOSED) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_LFO_POLY_COMPACT; MOI_LFO_ITER_SC];
        ASM_SIMP_TAC[CLOSED_DIFF; CLOSED_UNIV];
        MP_TAC (ISPECL
         [`ITER n barycentric_subdivision (c:(real^N->bool)->bool)`;
          `u:real^N->bool`] MOI_LFO_POLY_SUBSET) THEN
        ASM SET_TAC[]];
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
      MATCH_MP_TAC (TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      FIRST_X_ASSUM (MP_TAC o SPECL [`x:real^N`; `y:real^N`]) THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC (ISPECL [`c:(real^N->bool)->bool`; `d / &2`] MOI_LFO_ITER_FINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN (X_CHOOSE_TAC `m0:num`) THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN ITER (m0 + n + 1) barycentric_subdivision c
                     ==> bounded s /\ s SUBSET UNIONS c /\ diameter s < d / &2`
   (LABEL_TAC "mesh") THENL
   [GEN_TAC THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_LFO_ITER_SIMPLEX];
      ASM_MESON_TAC[MOI_LFO_ITER_SIMPLEX];
      FIRST_X_ASSUM (MATCH_MP_TAC o SPEC `m0 + n + 1`) THEN
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `m0 + n + 1` THEN REPEAT CONJ_TAC THENL
   [ARITH_TAC;
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    USE_THEN "mesh" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    UNDISCH_TAC `~(s INTER moi_lfo_poly (ITER n barycentric_subdivision c)
                   (u:real^N->bool) = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    USE_THEN "uw" MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      USE_THEN "sep" MATCH_MP_TAC THEN EXISTS_TAC `z:real^N` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `diameter(s:real^N->bool)` THEN CONJ_TAC THENL
       [REWRITE_TAC[dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
        ASM_REWRITE_TAC[];
        ASM_REAL_ARITH_TAC]];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    EXISTS_TAC `ball(x:real^N, d / &2)` THEN
    REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `?s:real^N->bool. s IN ITER (m0 + n + 1) barycentric_subdivision c /\
                       y IN s`
     STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[GSYM IN_UNIONS] THEN ASM_SIMP_TAC[MOI_LFO_ITER_UNIONS];
      ALL_TAC] THEN
    USE_THEN "mesh" (MP_TAC o SPEC `s:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    REWRITE_TAC[MOI_LFO_IN_POLY] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    USE_THEN "uw" MATCH_MP_TAC THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      USE_THEN "sep" MATCH_MP_TAC THEN EXISTS_TAC `x:real^N` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `dist(y:real^N,z) <= diameter(s:real^N->bool)` MP_TAC THENL
       [REWRITE_TAC[dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `dist(x:real^N,y) < d / &2` THEN
      UNDISCH_TAC `diameter(s:real^N->bool) < d / &2` THEN
      CONV_TAC NORM_ARITH]]);;

let MOI_LFO_EXHAUST = prove
 (`!(c:(real^N->bool)->bool) u x.
     simplicial_complex c /\ open_in (subtopology euclidean (UNIONS c)) u /\
     x IN u
     ==> ?n. !m. n <= m
                 ==> x IN moi_lfo_poly (ITER m barycentric_subdivision c) u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (X_CHOOSE_THEN `w:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) o REWRITE_RULE[OPEN_IN_OPEN]) THEN
  DISCH_THEN (fun th ->
    SUBGOAL_THEN `(!y:real^N. y IN UNIONS c /\ y IN w ==> y IN u) /\
                  (x:real^N) IN UNIONS c /\ x IN w`
    MP_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN u` THEN REWRITE_TAC[th] THEN SET_TAC[];
      ALL_TAC]) THEN
  DISCH_THEN (CONJUNCTS_THEN2 (LABEL_TAC "uw") STRIP_ASSUME_TAC) THEN
  MP_TAC (ISPEC `w:real^N->bool` OPEN_CONTAINS_BALL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN (MP_TAC o SPEC `x:real^N`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC (ISPECL [`c:(real^N->bool)->bool`; `e:real`] MOI_LFO_ITER_FINE) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `n:num` THEN DISCH_TAC THEN X_GEN_TAC `m:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `?s:real^N->bool. s IN ITER m barycentric_subdivision c /\ x IN s`
   STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM IN_UNIONS] THEN ASM_SIMP_TAC[MOI_LFO_ITER_UNIONS];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_LFO_IN_POLY] THEN EXISTS_TAC `s:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  USE_THEN "uw" MATCH_MP_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_LFO_ITER_SIMPLEX; SUBSET];
    UNDISCH_TAC `ball(x:real^N,e) SUBSET w` THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_BALL] THEN MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `diameter(s:real^N->bool)` THEN CONJ_TAC THENL
     [REWRITE_TAC[dist] THEN MATCH_MP_TAC DIAMETER_BOUNDED_BOUND THEN
      ASM_MESON_TAC[MOI_LFO_ITER_SIMPLEX];
      ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Part 7: Moise's subdivision of each layer (his L'_r), obtained from the  *)
(* extension hypothesis applied to the layer, its part missing b, and the   *)
(* restriction of the next complex to that part; then the main theorem.     *)
(* ------------------------------------------------------------------------- *)

let MOI_LFO_LAYER_EXT = prove
 (`!k k' (u:real^N->bool) b.
     (!(l:(real^N->bool)->bool) f d.
        simplicial_complex l /\ simplicial_complex f /\ f SUBSET l /\
        simplicial_complex d /\ UNIONS d = UNIONS f /\
        (!s. s IN d ==> ?t. t IN f /\ s SUBSET t) /\
        (!t. t IN f ==> ?e. e SUBSET d /\ t = UNIONS e)
        ==> ?l'. simplicial_complex l' /\ UNIONS l' = UNIONS l /\
                 (!s. s IN l' ==> ?t. t IN l /\ s SUBSET t) /\
                 (!t. t IN l ==> ?e. e SUBSET l' /\ t = UNIONS e) /\
                 (!s. s IN d /\ ~(s = {}) ==> s IN l') /\
                 (!s. s IN l' /\ ~(s = {}) /\ s SUBSET UNIONS f ==> s IN d) /\
                 (!t. t IN l /\ DISJOINT t (UNIONS f) ==> t IN l')) /\
     simplicial_complex k /\ simplicial_complex k' /\ moi_lfo_refines k' k
     ==> ?n. simplicial_complex n /\
             UNIONS n = UNIONS (moi_lfo_layer k u b) /\
             (!s. s IN n ==> ?t. t IN moi_lfo_layer k u b /\ s SUBSET t) /\
             (!s. s IN moi_lfo_restrict k' (moi_lfo_outer k u b) /\ ~(s = {})
                  ==> s IN n) /\
             (!t. t IN moi_lfo_layer k u b /\
                  DISJOINT t (UNIONS (moi_lfo_outer k u b)) ==> t IN n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM (MP_TAC o SPECL
   [`moi_lfo_layer k u (b:real^N->bool)`; `moi_lfo_outer k u (b:real^N->bool)`;
    `moi_lfo_restrict k' (moi_lfo_outer k u (b:real^N->bool))`]) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_LFO_LAYER_SC; MOI_LFO_OUTER_SC] THEN
    MATCH_MP_TAC MOI_LFO_RESTRICT_PROPS THEN
    EXISTS_TAC `k:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[MOI_LFO_OUTER_SC; MOI_LFO_LAYER_SUBSET; SUBSET_TRANS];
    MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[]]);;

let LF_TRIANGULATION_OPEN_SUBSET_FROM_EXTEND = prove
 (`(!(l:(real^N->bool)->bool) f d.
     simplicial_complex l /\ simplicial_complex f /\ f SUBSET l /\
     simplicial_complex d /\ UNIONS d = UNIONS f /\
     (!s. s IN d ==> ?t. t IN f /\ s SUBSET t) /\
     (!t. t IN f ==> ?e. e SUBSET d /\ t = UNIONS e)
     ==> ?l'. simplicial_complex l' /\ UNIONS l' = UNIONS l /\
              (!s. s IN l' ==> ?t. t IN l /\ s SUBSET t) /\
              (!t. t IN l ==> ?e. e SUBSET l' /\ t = UNIONS e) /\
              (!s. s IN d /\ ~(s = {}) ==> s IN l') /\
              (!s. s IN l' /\ ~(s = {}) /\ s SUBSET UNIONS f ==> s IN d) /\
              (!t. t IN l /\ DISJOINT t (UNIONS f) ==> t IN l'))
 ==> (!(c:(real^N->bool)->bool) u.
     simplicial_complex c /\ open_in (subtopology euclidean (UNIONS c)) u
     ==> ?d. lf_simplicial_complex d /\ UNIONS d = u /\
             (!s. s IN d ==> ?t. t IN c /\ s SUBSET t))`,
  DISCH_THEN (LABEL_TAC "ext") THEN
  MAP_EVERY X_GEN_TAC [`c:(real^N->bool)->bool`; `u:real^N->bool`] THEN
  STRIP_TAC THEN
  ASM_CASES_TAC `u:real^N->bool = {}` THENL
   [EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[lf_simplicial_complex; NOT_IN_EMPTY; UNIONS_0];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_IMP_SUBSET THEN
    EXISTS_TAC `euclidean:(real^N)topology` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t0:real^N->bool. t0 IN c` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(u:real^N->bool = {})` THEN
    UNDISCH_TAC `(u:real^N->bool) SUBSET UNIONS c` THEN SET_TAC[];
    ALL_TAC] THEN
  (* The numbers n_r: nn r < nn (SUC r) with the mesh conditions.          *)
  MP_TAC (ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`] MOI_LFO_NEXT) THEN
  ASM_REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN (X_CHOOSE_THEN `nx:num->num` (LABEL_TAC "nx")) THEN
  MP_TAC (ISPECL [`0:num`; `\(a:num) (r:num). (nx:num->num) a`]
    num_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN (X_CHOOSE_THEN `nn:num->num` (LABEL_TAC "rec" o CONJUNCT2)) THEN
  SUBGOAL_THEN
   `(!r. (nn:num->num) r < nn (SUC r)) /\
    (!r s. s IN ITER (nn (SUC r)) barycentric_subdivision
                       (c:(real^N->bool)->bool) /\
           ~(s INTER moi_lfo_poly (ITER (nn r) barycentric_subdivision c)
                                  (u:real^N->bool) = {})
           ==> s SUBSET u) /\
    (!r x. x IN moi_lfo_poly (ITER (nn r) barycentric_subdivision c) u
           ==> ?v. open v /\ x IN v /\
                   v INTER UNIONS c SUBSET
                   moi_lfo_poly (ITER (nn (SUC r)) barycentric_subdivision c) u)`
   (CONJUNCTS_THEN2 (LABEL_TAC "nn1")
     (CONJUNCTS_THEN2 (LABEL_TAC "nn2") (LABEL_TAC "nn3"))) THENL
   [USE_THEN "rec" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "nx" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  REMOVE_THEN "rec" (K ALL_TAC) THEN REMOVE_THEN "nx" (K ALL_TAC) THEN
  SUBGOAL_THEN `!r. r <= (nn:num->num) r` (LABEL_TAC "nn0") THENL
   [INDUCT_TAC THEN REWRITE_TAC[LE_0] THEN
    USE_THEN "nn1" (MP_TAC o SPEC `r:num`) THEN
    UNDISCH_TAC `r <= (nn:num->num) r` THEN ARITH_TAC;
    ALL_TAC] THEN
  (* The complexes K_(n_r) and their refinements.                          *)
  SUBGOAL_THEN
   `!r. simplicial_complex
          (ITER ((nn:num->num) r) barycentric_subdivision
                (c:(real^N->bool)->bool))`
   (LABEL_TAC "ksc") THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_LFO_ITER_SC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. moi_lfo_refines
          (ITER ((nn:num->num) (SUC r)) barycentric_subdivision
                (c:(real^N->bool)->bool))
          (ITER (nn r) barycentric_subdivision c)`
   (LABEL_TAC "kref") THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_LFO_ITER_REFINES THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC LT_IMP_LE THEN
    USE_THEN "nn1" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r. moi_lfo_refines
          (ITER ((nn:num->num) r) barycentric_subdivision
                (c:(real^N->bool)->bool)) c`
   (LABEL_TAC "kref0") THENL
   [GEN_TAC THEN
    MP_TAC (ISPECL [`c:(real^N->bool)->bool`; `(nn:num->num) r`; `0`]
      MOI_LFO_ITER_REFINES) THEN
    ASM_REWRITE_TAC[LE_0; ITER];
    ALL_TAC] THEN
  (* The unions bb r of the earlier layers: bb 0 = {}.                      *)
  MP_TAC (ISPECL [`{}:real^N->bool`;
    `\(x:real^N->bool) (r:num).
       moi_lfo_poly (ITER ((nn:num->num) r) barycentric_subdivision
                          (c:(real^N->bool)->bool)) (u:real^N->bool)`]
    num_RECURSION) THEN
  REWRITE_TAC[] THEN
  DISCH_THEN (X_CHOOSE_THEN `bb:num->real^N->bool`
    (CONJUNCTS_THEN2 (LABEL_TAC "bb0") (LABEL_TAC "bbs"))) THEN
  SUBGOAL_THEN
   `!r s. s IN ITER ((nn:num->num) r) barycentric_subdivision c /\
          ~(s INTER (bb:num->real^N->bool) r = {})
          ==> s SUBSET u`
   (LABEL_TAC "bb1") THENL
   [INDUCT_TAC THENL
     [USE_THEN "bb0" (fun th -> REWRITE_TAC[th; INTER_EMPTY]);
      USE_THEN "bbs" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "nn2" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  (* The subdivided layers nc r (Moise's L'_r).                            *)
  SUBGOAL_THEN
   `!r. ?n. simplicial_complex n /\
            UNIONS n = UNIONS (moi_lfo_layer
              (ITER ((nn:num->num) r) barycentric_subdivision c) u
              ((bb:num->real^N->bool) r)) /\
            (!s. s IN n ==> ?t. t IN moi_lfo_layer
                 (ITER (nn r) barycentric_subdivision c) u (bb r) /\
                 s SUBSET t) /\
            (!s. s IN moi_lfo_restrict
                   (ITER (nn (SUC r)) barycentric_subdivision c)
                   (moi_lfo_outer (ITER (nn r) barycentric_subdivision c) u
                                  (bb r)) /\
                 ~(s = {})
                 ==> s IN n) /\
            (!t. t IN moi_lfo_layer
                   (ITER (nn r) barycentric_subdivision c) u (bb r) /\
                 DISJOINT t (UNIONS (moi_lfo_outer
                   (ITER (nn r) barycentric_subdivision c) u (bb r)))
                 ==> t IN n)`
   MP_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_LFO_LAYER_EXT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN (X_CHOOSE_THEN `nc:num->(real^N->bool)->bool` (LABEL_TAC "nc")) THEN
  REMOVE_THEN "ext" (K ALL_TAC) THEN
  (* The union of the nc r is the required complex.                         *)
  MP_TAC (ISPECL
   [`nc:num->(real^N->bool)->bool`;
    `\r. moi_lfo_poly (ITER ((nn:num->num) r) barycentric_subdivision c)
                      (u:real^N->bool)`;
    `UNIONS (c:(real^N->bool)->bool)`] MOI_LFO_CHAIN_LF) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [USE_THEN "nc" (fun th -> REWRITE_TAC[th]);
      USE_THEN "nc" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "bb0" (fun th -> REWRITE_TAC[th]) THEN
      MP_TAC (ISPECL
       [`ITER ((nn:num->num) 0) barycentric_subdivision (c:(real^N->bool)->bool)`;
        `u:real^N->bool`; `{}:real^N->bool`] MOI_LFO_UNIONS_LAYER) THEN
      REWRITE_TAC[EMPTY_SUBSET; UNION_EMPTY] THEN DISCH_THEN MATCH_MP_TAC THEN
      USE_THEN "ksc" (fun th -> REWRITE_TAC[th]);
      X_GEN_TAC `r:num` THEN
      USE_THEN "nc" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "bbs" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC MOI_LFO_UNIONS_LAYER THEN
      USE_THEN "ksc" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC MOI_LFO_POLY_MONO THEN
      USE_THEN "kref" (fun th -> REWRITE_TAC[th]);
      X_GEN_TAC `r:num` THEN
      USE_THEN "nc" (MP_TAC o SPEC `SUC r`) THEN
      USE_THEN "bbs" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
      USE_THEN "nc" (MP_TAC o SPEC `r:num`) THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_LFO_INTERFACE THEN
      EXISTS_TAC `(bb:num->real^N->bool) r` THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r:num` THEN
      USE_THEN "nc" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "bbs" (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC MOI_LFO_F4 THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `r:num` THEN
      MP_TAC (ISPECL
       [`ITER ((nn:num->num) r) barycentric_subdivision (c:(real^N->bool)->bool)`;
        `u:real^N->bool`] MOI_LFO_POLY_SUBSET) THEN
      ASM_SIMP_TAC[MOI_LFO_ITER_UNIONS];
      USE_THEN "nn3" (fun th -> REWRITE_TAC[th])];
    ALL_TAC] THEN
  STRIP_TAC THEN
  EXISTS_TAC `UNIONS (IMAGE (nc:num->(real^N->bool)->bool) (:num))` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[EXTENSION; MOI_LFO_IN_UNIONS_IMAGE] THEN
    X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
     [DISCH_THEN (X_CHOOSE_TAC `r:num`) THEN
      MP_TAC (ISPECL
       [`ITER ((nn:num->num) r) barycentric_subdivision (c:(real^N->bool)->bool)`;
        `u:real^N->bool`] MOI_LFO_POLY_SUBSET) THEN
      ASM SET_TAC[];
      DISCH_TAC THEN
      MP_TAC (ISPECL [`c:(real^N->bool)->bool`; `u:real^N->bool`; `x:real^N`]
        MOI_LFO_EXHAUST) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN (X_CHOOSE_TAC `n0:num`) THEN
      EXISTS_TAC `n0:num` THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      USE_THEN "nn0" (fun th -> REWRITE_TAC[th])];
    REWRITE_TAC[MOI_LFO_IN_UNIONS_IMAGE] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN (X_CHOOSE_TAC `r:num`) THEN
    USE_THEN "nc" (MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o SPEC `r:num`) THEN
    DISCH_THEN (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC o
      C MP (ASSUME `(s:real^N->bool) IN nc (r:num)`) o SPEC `s:real^N->bool`) THEN
    ASM_CASES_TAC `t:real^N->bool = {}` THENL
     [EXISTS_TAC `t0:real^N->bool` THEN ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(t:real^N->bool) IN ITER ((nn:num->num) r) barycentric_subdivision c`
     ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_LFO_LAYER_SUBSET; SUBSET]; ALL_TAC] THEN
    USE_THEN "kref0" (MP_TAC o SPEC `r:num`) THEN
    REWRITE_TAC[moi_lfo_refines] THEN
    DISCH_THEN (MP_TAC o SPEC `t:real^N->bool` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_TRANS]]);;

