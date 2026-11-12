(* ========================================================================= *)
(* pc_moi_sch3_gen: generic height directions on a finite simplicial complex *)
(* in real^3 exist near any direction (GENERIC_NEAR), the vertex crossing    *)
(* counts are stable under small changes of a generic direction              *)
(* (CROSSINGS_STABLE), and the filled PL 2-sphere s UNION inside s is        *)
(* triangulable (FILLING_TRIANGULATION).  The statements are in              *)
(* pc_moi_sch3_stmt.ml.                                                      *)
(* ========================================================================= *)

needs "src/pc_moi_sch3_stmt.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_lfopen.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* GENERIC_NEAR: the directions that are zero or put two distinct vertices  *)
(* at the same level form a finite union of a point and planes, which is    *)
(* negligible, so every ball of directions contains a generic one.          *)
(* ------------------------------------------------------------------------- *)

let MOI_SGN_GENERIC_NEAR = prove
 (`!c (a0:real^3) e.
     simplicial_complex c /\ &0 < e
     ==> ?a. moi_sch3_generic c a /\ norm(a - a0) < e`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `vv = {v:real^3 | {v} IN c}` THEN
  SUBGOAL_THEN `FINITE (vv:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "vv" THEN MATCH_MP_TAC MOI_SCD_VERTICES_FINITE THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {{a:real^3 | (v - w) dot a = &0} | v IN vv /\ w IN vv DELETE v}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[FINITE_DELETE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `negligible (UNIONS ({vec 0:real^3} INSERT
      {{a:real^3 | (v - w) dot a = &0} | v IN vv /\ w IN vv DELETE v}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC NEGLIGIBLE_UNIONS THEN ASM_REWRITE_TAC[FINITE_INSERT] THEN
    REWRITE_TAC[FORALL_IN_INSERT; NEGLIGIBLE_SING] THEN
    REWRITE_TAC[FORALL_IN_GSPEC; IN_DELETE] THEN
    MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC NEGLIGIBLE_HYPERPLANE THEN
    REWRITE_TAC[VECTOR_SUB_EQ] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?a:real^3. a IN ball(a0,e) /\ ~(a = vec 0) /\
      !v w. v IN vv /\ w IN vv /\ ~(w = v) ==> ~((v - w) dot a = &0)`
  (X_CHOOSE_THEN `a:real^3` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hyp")))) THENL
   [MP_TAC(ISPEC `ball(a0:real^3,e)` OPEN_NOT_NEGLIGIBLE) THEN
    ASM_REWRITE_TAC[OPEN_BALL; BALL_EQ_EMPTY; REAL_NOT_LE] THEN DISCH_TAC THEN
    MP_TAC(ISPECL
     [`UNIONS ({vec 0:real^3} INSERT
         {{a:real^3 | (v - w) dot a = &0} | v IN vv /\ w IN vv DELETE v})`;
      `ball(a0:real^3,e)`] NEGLIGIBLE_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; NOT_FORALL_THM; NOT_IMP] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `a:real^3` THEN
    REWRITE_TAC[UNIONS_INSERT] THEN
    REWRITE_TAC[IN_UNION; IN_SING; IN_UNIONS; EXISTS_IN_GSPEC;
                IN_DELETE; IN_ELIM_THM] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `a:real^3` THEN ASM_REWRITE_TAC[moi_sch3_generic] THEN
  CONJ_TAC THENL
   [MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `v:real^3 = w` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(v - w:real^3) dot a = &0` MP_TAC THENL
     [REWRITE_TAC[DOT_LSUB] THEN ONCE_REWRITE_TAC[DOT_SYM] THEN
      ASM_REWRITE_TAC[REAL_SUB_REFL];
      ALL_TAC] THEN
    REMOVE_THEN "hyp" (MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
    EXPAND_TAC "vv" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `(a:real^3) IN ball(a0,e)` THEN
    REWRITE_TAC[IN_BALL] THEN NORM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* CROSSINGS_STABLE: near a generic direction a, every direction a' is      *)
(* nonzero and orders each pair of distinct vertices as a does (an open     *)
(* condition: finitely many open half-spaces); so a' is generic and the     *)
(* crossing edges at each vertex are the same.                               *)
(* ------------------------------------------------------------------------- *)

let MOI_SGN_SEGMENT_VERTICES = prove
 (`!c (x:real^3) y.
     simplicial_complex c /\ segment[x,y] IN c ==> {x} IN c /\ {y} IN c`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    can (find_term (fun t -> t = `(face_of):(real^3->bool)->(real^3->bool)->bool`))
        (concl th) && is_forall(concl th) &&
    length(fst(strip_forall(concl th))) = 2)) THEN
  EXISTS_TAC `segment[x:real^3,y]` THEN
  ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

let MOI_SGN_SIGN_OPEN = prove
 (`!c (a:real^3).
     moi_sch3_generic c a
     ==> ?e. &0 < e /\
             !a'. norm(a' - a) < e
                  ==> ~(a' = vec 0) /\
                      !v w. {v} IN c /\ {w} IN c /\ ~(w = v)
                            ==> ((a dot (v - w)) % (v - w)) dot a' > &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_sch3_generic] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "inj"))) THEN
  ABBREV_TAC `vv = {v:real^3 | {v} IN c}` THEN
  SUBGOAL_THEN `FINITE (vv:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "vv" THEN MATCH_MP_TAC MOI_SCD_VERTICES_FINITE THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  ABBREV_TAC
   `g = ((:real^3) DELETE vec 0) INTER
        INTERS {{a':real^3 | ((a dot (v - w)) % (v - w)) dot a' > &0} |
                v IN vv /\ w IN vv DELETE v}` THEN
  SUBGOAL_THEN `open (g:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN MATCH_MP_TAC OPEN_INTER THEN
    SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN MATCH_MP_TAC OPEN_INTERS THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[FINITE_DELETE];
      REWRITE_TAC[FORALL_IN_GSPEC; OPEN_HALFSPACE_GT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3) IN g` ASSUME_TAC THENL
   [EXPAND_TAC "g" THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DELETE; IN_UNIV; IN_INTERS; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`] THEN
    REWRITE_TAC[IN_DELETE; IN_ELIM_THM] THEN STRIP_TAC THEN
    REWRITE_TAC[DOT_LMUL; real_gt] THEN
    GEN_REWRITE_TAC (RAND_CONV o RAND_CONV) [DOT_SYM] THEN
    REWRITE_TAC[REAL_LT_SQUARE] THEN
    REWRITE_TAC[DOT_RSUB; REAL_SUB_0] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(w:real^3 = v)` THEN REWRITE_TAC[] THEN
    CONV_TAC SYM_CONV THEN USE_THEN "inj" MATCH_MP_TAC THEN
    UNDISCH_TAC `(v:real^3) IN vv` THEN UNDISCH_TAC `(w:real^3) IN vv` THEN
    EXPAND_TAC "vv" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `g:real^3->bool` OPEN_CONTAINS_BALL) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^3`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a':real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(a':real^3) IN g` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_BALL] THEN ASM_MESON_TAC[DIST_SYM; dist];
    ALL_TAC] THEN
  EXPAND_TAC "g" THEN
  REWRITE_TAC[IN_INTER; IN_DELETE; IN_UNIV; IN_INTERS; FORALL_IN_GSPEC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^3`; `w:real^3`]) THEN
  EXPAND_TAC "vv" THEN ASM_REWRITE_TAC[IN_ELIM_THM; IN_DELETE]);;

let MOI_SGN_SIGN_SAME = prove
 (`!(a:real^3) a' x v.
     ((a dot (x - v)) % (x - v)) dot a' > &0
     ==> (a' dot x < a' dot v <=> a dot x < a dot v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[DOT_LMUL; real_gt; DOT_RSUB; DOT_LSUB] THEN
  REWRITE_TAC[DOT_SYM] THEN REWRITE_TAC[REAL_MUL_POS_LT] THEN REAL_ARITH_TAC);;

let MOI_SGN_CROSSINGS_STABLE = prove
 (`!c (a:real^3).
     moi_sch3_generic c a
     ==> ?e. &0 < e /\
             !a'. norm(a' - a) < e
                  ==> moi_sch3_generic c a' /\
                      !v. {v} IN c
                          ==> moi_sch3_crossings c a' v = moi_sch3_crossings c a v`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SGN_SIGN_OPEN) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_sch3_generic]) THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "near")) THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `a':real^3` THEN DISCH_TAC THEN
  REMOVE_THEN "near" (MP_TAC o SPEC `a':real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pos")) THEN
  SUBGOAL_THEN
   `!x v:real^3. {x} IN c /\ {v} IN c
                 ==> (a' dot x < a' dot v <=> a dot x < a dot v)`
  (LABEL_TAC "same") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `x:real^3 = v` THEN ASM_REWRITE_TAC[REAL_LT_REFL] THEN
    MATCH_MP_TAC MOI_SGN_SIGN_SAME THEN
    USE_THEN "pos" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[moi_sch3_generic] THEN
    MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) &&
      can (find_term (fun t -> t = `a:real^3`)) (concl th) &&
      not (can (find_term (fun t -> t = `a':real^3`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "same" (fun th -> MP_TAC(MATCH_MP (SPECL [`v:real^3`; `w:real^3`] th)
      (CONJ (ASSUME `{v:real^3} IN c`) (ASSUME `{w:real^3} IN c`)))) THEN
    USE_THEN "same" (fun th -> MP_TAC(MATCH_MP (SPECL [`w:real^3`; `v:real^3`] th)
      (CONJ (ASSUME `{w:real^3} IN c`) (ASSUME `{v:real^3} IN c`)))) THEN
    ASM_REWRITE_TAC[REAL_LT_REFL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN REWRITE_TAC[moi_sch3_crossings] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `s:real^3->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
  ASM_CASES_TAC `(s:real^3->bool) IN simplicial_link c v` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(s:real^3->bool) IN c` ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^3->bool) IN simplicial_link c v` THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  EQ_TAC THEN
  (DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `y:real^3`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`x:real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `x:real^3`; `y:real^3`]
    MOI_SGN_SEGMENT_VERTICES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(s:real^3->bool) IN c` THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  USE_THEN "same" (fun th -> MP_TAC(MATCH_MP (SPECL [`x:real^3`; `v:real^3`] th)
    (CONJ (ASSUME `{x:real^3} IN c`) (ASSUME `{v:real^3} IN c`)))) THEN
  USE_THEN "same" (fun th -> MP_TAC(MATCH_MP (SPECL [`v:real^3`; `y:real^3`] th)
    (CONJ (ASSUME `{v:real^3} IN c`) (ASSUME `{y:real^3} IN c`)))) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[]));;

let GENERIC_NEAR = prove
 (MOI_SCH3_GENERIC_NEAR,
  ACCEPT_TAC MOI_SGN_GENERIC_NEAR);;

let CROSSINGS_STABLE = prove
 (MOI_SCH3_CROSSINGS_STABLE,
  ACCEPT_TAC MOI_SGN_CROSSINGS_STABLE);;

(* ------------------------------------------------------------------------- *)
(* FILLING_TRIANGULATION: triangulate a cube containing the PL 2-sphere s   *)
(* with s a union of simplices; a simplex whose relative interior meets the *)
(* inside of s has its relative interior in the inside (it misses s, being  *)
(* connected), so it lies in the closure of the inside; the simplices in   *)
(* s UNION inside s form the required complex.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_SGN_RELINT_MEETS = prove
 (`!t (q:(real^N->bool)->bool) f.
     simplicial_complex t /\ q SUBSET t /\ f IN t /\
     ~(relative_interior f INTER UNIONS q = {})
     ==> f SUBSET UNIONS q`,
  REPEAT GEN_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC
     (X_CHOOSE_THEN `y:real^N` (CONJUNCTS_THEN2 ASSUME_TAC
       (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC)))))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `(g:real^N->bool) IN t` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->bool) SUBSET f INTER g` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `f:real^N->bool` THEN
    ASM_SIMP_TAC[SUBSET_REFL] THEN REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ASM SET_TAC[]]);;

let MOI_SGN_FILLING_TRIANGULATION = prove
 (`!s:real^3->bool.
     pl_sphere 2 s ==> ?k. simplicial_complex k /\ UNIONS k = s UNION inside s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SCD_PL_SPHERE_POLYHEDRON) THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN MP_TAC th) THEN
  REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:(real^3->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  SUBGOAL_THEN `compact (s:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^3->bool` BOUNDED_SUBSET_CLOSED_INTERVAL_SYMMETRIC) THEN
  ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
  DISCH_THEN(X_CHOOSE_TAC `b:real^3`) THEN
  MP_TAC(ISPEC `(interval[--b,b]:real^3->bool) INSERT p`
    POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ASM_REWRITE_TAC[FINITE_INSERT; FORALL_IN_INSERT; POLYTOPE_INTERVAL] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^3->bool)->bool` (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pcs"))))) THEN
  SUBGOAL_THEN `UNIONS t = interval[--b:real^3,b]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNIONS_INSERT] THEN
    UNDISCH_TAC `(s:real^3->bool) SUBSET interval[--b,b]` THEN
    UNDISCH_TAC `UNIONS (p:(real^3->bool)->bool) = s` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `q = {f:real^3->bool | f IN t /\ f SUBSET s}` THEN
  SUBGOAL_THEN `(q:(real^3->bool)->bool) SUBSET t /\ UNIONS q = s`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^3` THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `?k:real^3->bool. k IN p /\ x IN k` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN s` THEN
      UNDISCH_TAC `UNIONS (p:(real^3->bool)->bool) = s` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS];
      ALL_TAC] THEN
    USE_THEN "pcs" (MP_TAC o C MATCH_MP (ASSUME `(k:real^3->bool) IN p`) o
      SPEC `k:real^3->bool`) THEN
    DISCH_THEN(X_CHOOSE_THEN `ff:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?f:real^3->bool. f IN ff /\ x IN f` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^3) IN k` THEN ASM_REWRITE_TAC[IN_UNIONS];
      ALL_TAC] THEN
    EXISTS_TAC `f:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `UNIONS (p:(real^3->bool)->bool) = s` THEN
    UNDISCH_TAC `(k:real^3->bool) IN p` THEN
    UNDISCH_TAC `(f:real^3->bool) IN ff` THEN
    UNDISCH_TAC `k = UNIONS (ff:(real^3->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `inside s SUBSET interval[--b:real^3,b]` ASSUME_TAC THENL
   [MATCH_MP_TAC INSIDE_SUBSET_CONVEX THEN ASM_REWRITE_TAC[CONVEX_INTERVAL];
    ALL_TAC] THEN
  SUBGOAL_THEN `closure(inside s) SUBSET (s:real^3->bool) UNION inside s`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSURE_INSIDE_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  EXISTS_TAC `{f:real^3->bool | f IN t /\ f SUBSET s UNION inside s}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LFO_SUBCOMPLEX THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC
     [`g:real^3->bool`; `f:real^3->bool`] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (t:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[IN_UNION] THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(x:real^3) IN UNIONS q` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "q" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?g:real^3->bool. g IN t /\ x IN g` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(x:real^3) IN UNIONS t` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^3) IN inside s` THEN
      UNDISCH_TAC `inside s SUBSET interval[--b:real^3,b]` THEN SET_TAC[];
      REWRITE_TAC[IN_UNIONS]];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex] o
    check (fun th -> concl th = `simplicial_complex (t:(real^3->bool)->bool)`)) THEN
  SUBGOAL_THEN `?n. n simplex (g:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^3->bool`; `x:real^3`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^3->bool) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?m. m simplex (f:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^3) IN s)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `s:real^3->bool` INSIDE_NO_OVERLAP) THEN
    UNDISCH_TAC `(x:real^3) IN inside s` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior f INTER (s:real^3->bool) = {}` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `q:(real^3->bool)->bool`;
                   `f:real^3->bool`] MOI_SGN_RELINT_MEETS) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^3) IN relative_interior f` THEN
    UNDISCH_TAC `~((x:real^3) IN s)` THEN
    MP_TAC(ISPEC `f:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior f SUBSET inside(s:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `relative_interior f SUBSET
                  connected_component ((:real^3) DIFF s) x` ASSUME_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR THEN
        ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
        UNDISCH_TAC `relative_interior f INTER (s:real^3->bool) = {}` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^3) IN inside s` THEN REWRITE_TAC[inside; IN_ELIM_THM] THEN
    STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `relative_interior f INTER (s:real^3->bool) = {}` THEN
      UNDISCH_TAC `(y:real^3) IN relative_interior f` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `connected_component ((:real^3) DIFF s) y =
                  connected_component ((:real^3) DIFF s) x`
      (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior f` THEN
    UNDISCH_TAC `relative_interior f SUBSET
                 connected_component ((:real^3) DIFF s) x` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `f:real^3->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure(inside(s:real^3->bool))` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `f = closure(relative_interior(f:real^3->bool))` SUBST1_TAC THENL
     [ASM_MESON_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED;
                    SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED];
      MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[]];
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]]);;

let FILLING_TRIANGULATION = prove
 (MOI_SCH3_FILLING_TRIANGULATION,
  ACCEPT_TAC MOI_SGN_FILLING_TRIANGULATION);;

