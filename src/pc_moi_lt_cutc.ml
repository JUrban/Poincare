needs "src/pc_moi_loop_stmt.ml";;
needs "src/pc_moi_polytope.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_lt_cutc: SOURCE_STRUCTURE, a step of the loop theorem.  The      *)
(* source double set of a normal singular disk (the points of             *)
(* std_triangle mapped into the double image) is a properly embedded       *)
(* compact PL 1-manifold: a finite combinatorial 1-manifold with boundary  *)
(* whose boundary vertices are exactly its points on the frontier of the   *)
(* triangle.  Route: a triangulation of                                    *)
(* the triangle on which f is affine and injective on simplices; a        *)
(* refinement s' of the double image complex with the images of these      *)
(* simplices as subcomplexes; the source complex of the preimages of the   *)
(* simplices of s'; degrees by counting (two preimages of each vertex and  *)
(* edge, f injective on the edges at a vertex); degrees in s' through the  *)
(* unit directions of the double image (the MOI_LCC_DIRS lemmas); the     *)
(* boundary points of the double image are vertices (crossing charts).    *)
(* Main theorem: SOURCE_STRUCTURE : |- MOI_LT_SOURCE_STRUCTURE.              *)
(* ========================================================================= *)

(* Copied from pc_moi_fnd_m3b.ml (MOI_FMB_SC_LF, renamed), which is not      *)
(* loaded here.                                                              *)

let MOI_LCC_SC_LF = prove
 (`!c:(real^N->bool)->bool. simplicial_complex c ==> lf_simplicial_complex c`,
  GEN_TAC THEN REWRITE_TAC[simplicial_complex; lf_simplicial_complex] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  EXISTS_TAC `(:real^N)` THEN REWRITE_TAC[OPEN_UNIV; IN_UNIV] THEN
  ASM_SIMP_TAC[FINITE_RESTRICT]);;

(* PL 0-balls are points and PL 0-spheres are pairs of distinct points.    *)

let MOI_LCC_PL_BALL_0 = prove
 (`!s:real^N->bool. pl_ball 0 s <=> ?q. s = {q}`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[pl_ball; pl_homeomorphism; homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
    REWRITE_TAC[AFF_DIM_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    EXISTS_TAC `(f:real^N->real^N) a` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `s:real^N->bool`)) THEN
    REWRITE_TAC[IMAGE_CLAUSES];
    DISCH_THEN(X_CHOOSE_THEN `q:real^N` SUBST1_TAC) THEN
    MATCH_MP_TAC PL_BALL_SIMPLEX THEN REWRITE_TAC[SIMPLEX_SING]]);;

let MOI_LCC_RELBD_SEGMENT = prove
 (`!a b:real^N. ~(a = b) ==> relative_frontier(segment[a,b]) = {a,b}`,
  REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[relative_frontier; RELATIVE_INTERIOR_SEGMENT; CLOSURE_SEGMENT] THEN
  REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_NOT_IN_SEGMENT) THEN SET_TAC[]);;

let MOI_LCC_PL_SPHERE_0 = prove
 (`!s:real^N->bool. pl_sphere 0 s <=> ?p q. ~(p = q) /\ s = {p,q}`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[pl_sphere; pl_homeomorphism; homeomorphism; ADD_CLAUSES] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `&1 simplex (k:real^N->bool)` THEN
    REWRITE_TAC[SIMPLEX; ARITH; INT_ARITH `&1 + &1:int = &2`; INT_OF_NUM_EQ] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(v:real^N->bool) HAS_SIZE 2` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `relative_frontier k = {a:real^N,b}` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
      MATCH_MP_TAC MOI_LCC_RELBD_SEGMENT THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`(f:real^N->real^N) a`; `(f:real^N->real^N) b`] THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(g:real^N->real^N) (f a) = a /\ g (f b) = b` MP_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) &&
          can (find_term ((=) `g:real^N->real^N`)) (concl th) &&
          can (find_term ((=) `f:real^N->real^N`)) (concl th) &&
          is_comb(rand(snd(dest_forall(concl th)))))) THEN
        ASM_REWRITE_TAC[IN_INSERT];
        ASM_MESON_TAC[]];
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rand(concl th) = `s:real^N->bool`)) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES]];
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{p:real^N,q} = relative_frontier(segment[p,q])` SUBST1_TAC THENL
     [ASM_SIMP_TAC[MOI_LCC_RELBD_SEGMENT]; ALL_TAC] THEN
    MATCH_MP_TAC PL_SPHERE_RELATIVE_FRONTIER_SIMPLEX THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; ADD_CLAUSES; ARITH] THEN
    MATCH_MP_TAC SIMPLEX_CONVEX_HULL THEN
    ASM_REWRITE_TAC[AFFINE_INDEPENDENT_2] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ARITH_TAC]);;

(* Unit directions of a set at a point: the germs of rays from w inside x. *)

let moi_lcc_dirs = new_definition
 `moi_lcc_dirs (x:real^N->bool) (w:real^N) =
    {d | norm d = &1 /\
         ?e. &0 < e /\ !t. &0 < t /\ t < e ==> w + t % d IN x}`;;

(* A ray germ covered by finitely many closed sets has points, other than   *)
(* its origin, in one of them that contains the origin.                     *)

let MOI_LCC_GERM = prove
 (`!(c:(real^N->bool)->bool) w d e.
     FINITE c /\ (!k. k IN c ==> closed k) /\ &0 < e /\
     (!t. &0 < t /\ t < e ==> w + t % d IN UNIONS c)
     ==> ?k t. k IN c /\ &0 < t /\ t < e /\ w IN k /\ w + t % d IN k`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `closed (UNIONS {k:real^N->bool | k IN c /\ ~(w IN k)})` MP_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
    ALL_TAC] THEN
  REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `t = min e (r / (norm(d:real^N) + &1)) / &2` THEN
  SUBGOAL_THEN `&0 < r / (norm(d:real^N) + &1)` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `d:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t /\ t < e /\ t * (norm(d:real^N) + &1) < r` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `&0 < r / (norm(d:real^N) + &1)` THEN
      REAL_ARITH_TAC;
      UNDISCH_TAC `&0 < e` THEN UNDISCH_TAC `&0 < r / (norm(d:real^N) + &1)` THEN
      REAL_ARITH_TAC;
      SUBGOAL_THEN `min e (r / (norm(d:real^N) + &1)) / &2 <= (r / (norm d + &1)) / &2`
      MP_TAC THENL
       [UNDISCH_TAC `&0 < r / (norm(d:real^N) + &1)` THEN REAL_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `&0 < norm(d:real^N) + &1` ASSUME_TAC THENL
       [MP_TAC(ISPEC `d:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(r / (norm(d:real^N) + &1)) / &2 * (norm d + &1)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_FIELD `&0 < m ==> r / m / &2 * m = r / &2`] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) + t % d IN UNIONS c` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `t:real`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `ball(w:real^N,r) SUBSET
               (:real^N) DIFF UNIONS {k | k IN c /\ ~(w IN k)}` THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `(w:real^N) + t % d`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `w - (w + t % d):real^N = --(t % d)`;
                NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < t ==> abs t = t`] THEN
    MP_TAC(ISPEC `d:real^N` NORM_POS_LE) THEN
    UNDISCH_TAC `t * (norm(d:real^N) + &1) < r` THEN UNDISCH_TAC `&0 < t` THEN
    REAL_ARITH_TAC;
    DISCH_THEN(MP_TAC o SPEC `k:real^N->bool`) THEN ASM_REWRITE_TAC[]]);;

(* Simplices of dimension at most 1, and vertices of edges in a complex.    *)

let MOI_LCC_SIMPLEX_LE1 = prove
 (`!(t:real^N->bool) n.
     n simplex t /\ aff_dim t <= &1
     ==> t = {} \/ (?a. t = {a}) \/ (?a b. ~(a = b) /\ t = segment[a,b])`,
  REPEAT GEN_TAC THEN REWRITE_TAC[SIMPLEX] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC)
    ASSUME_TAC) THEN
  SUBGOAL_THEN `CARD(v:real^N->bool) <= 2` MP_TAC THENL
   [UNDISCH_TAC `aff_dim(t:real^N->bool) <= &1` THEN
    UNDISCH_TAC `t = convex hull (v:real^N->bool)` THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT; ASSUME `~affine_dependent (v:real^N->bool)`] THEN
    REWRITE_TAC[INT_ARITH `a - &1:int <= &1 <=> a <= &2`; INT_OF_NUM_LE];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `!n. n <= 2 <=> n = 0 \/ n = 1 \/ n = 2`] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN UNDISCH_TAC `CARD(v:real^N->bool) = 0` THEN
    ASM_SIMP_TAC[CARD_EQ_0; CONVEX_HULL_EMPTY] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[CONVEX_HULL_EMPTY];
    DISJ2_TAC THEN DISJ1_TAC THEN
    SUBGOAL_THEN `(v:real^N->bool) HAS_SIZE 1` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[CONVEX_HULL_SING];
    DISJ2_TAC THEN DISJ2_TAC THEN
    SUBGOAL_THEN `(v:real^N->bool) HAS_SIZE 2` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL]]);;

let MOI_LCC_VERTEX_OF_EDGE = prove
 (`!(l:(real^N->bool)->bool) w a b.
     simplicial_complex l /\ {w} IN l /\ segment[a,b] IN l /\ w IN segment[a,b]
     ==> w = a \/ w = b`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{w:real^N} INTER segment[a,b] face_of segment[a,b]` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^N} INTER segment[a,b] = {w}` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

(* The link of a vertex w in a complex of dimension at most 1: the other   *)
(* ends of the edges at w.                                                  *)

let MOI_LCC_LINK_1 = prove
 (`!(l:(real^N->bool)->bool) w.
     simplicial_complex l /\ (!s. s IN l ==> aff_dim s <= &1) /\ {w} IN l
     ==> UNIONS (simplicial_link l w) = {u | ~(u = w) /\ segment[w,u] IN l}`,
  REPEAT STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[simplicial_link; IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))) ASSUME_TAC)) THEN
    SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:real^N->bool`; `n:int`] MOI_LCC_SIMPLEX_LE1) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `(w:real^N) IN t` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      MP_TAC(ISPECL [`t:real^N->bool`; `s:real^N->bool`] FACE_OF_IMP_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC [`(w:real^N) IN t`; `~((w:real^N) IN s)`;
                             `(x:real^N) IN s`] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `w:real^N`; `a:real^N`; `b:real^N`]
      MOI_LCC_VERTEX_OF_EDGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~affine_dependent {a:real^N,b}` ASSUME_TAC THENL
     [REWRITE_TAC[AFFINE_INDEPENDENT_2]; ALL_TAC] THEN
    UNDISCH_TAC `(s:real^N->bool) face_of t` THEN ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(v:real^N->bool) SUBSET s` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[HULL_SUBSET]; ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THENL
     [SUBGOAL_THEN `v SUBSET {b:real^N}` ASSUME_TAC THENL
       [UNDISCH_TAC `(v:real^N->bool) SUBSET {w,b}` THEN
        UNDISCH_TAC `(v:real^N->bool) SUBSET s` THEN
        UNDISCH_TAC `~((w:real^N) IN s)` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^N) = b` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `v:real^N->bool`; `{b:real^N}`]
          HULL_MONO) THEN
        ASM_REWRITE_TAC[CONVEX_HULL_SING] THEN SET_TAC[];
        ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN ASM_MESON_TAC[]];
      SUBGOAL_THEN `v SUBSET {a:real^N}` ASSUME_TAC THENL
       [UNDISCH_TAC `(v:real^N->bool) SUBSET {a,w}` THEN
        UNDISCH_TAC `(v:real^N->bool) SUBSET s` THEN
        UNDISCH_TAC `~((w:real^N) IN s)` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^N) = a` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `v:real^N->bool`; `{a:real^N}`]
          HULL_MONO) THEN
        ASM_REWRITE_TAC[CONVEX_HULL_SING] THEN SET_TAC[];
        CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `convex hull {w:real^N,a} = t /\ convex hull {a:real^N,w} = t`
        (fun th -> REWRITE_TAC[th] THEN ASM_REWRITE_TAC[]) THEN
        ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REPEAT CONJ_TAC THEN AP_TERM_TAC THEN
        SET_TAC[]]];
    STRIP_TAC THEN EXISTS_TAC `{x:real^N}` THEN REWRITE_TAC[IN_SING] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (l:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `segment[w:real^N,x]` THEN
      ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      ASM_MESON_TAC[];
      EXISTS_TAC `segment[w:real^N,x]` THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT; FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]]]);;
(* The subsets of a pair (as MOI_S6X_SUBSET_PAIR of pc_moi_s26_cross, which *)
(* is outside this closure).                                                *)

let MOI_LCC_SUBSET_PAIR = prove
 (`!(t:A->bool) b c.
     t SUBSET {b,c} ==> t = {} \/ t = {b} \/ t = {c} \/ t = {b,c}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(b:A) IN t` THEN ASM_CASES_TAC `(c:A) IN t` THENL
   [REPEAT DISJ2_TAC THEN ASM SET_TAC[];
    DISJ2_TAC THEN DISJ1_TAC THEN ASM SET_TAC[];
    DISJ2_TAC THEN DISJ2_TAC THEN DISJ1_TAC THEN ASM SET_TAC[];
    DISJ1_TAC THEN ASM SET_TAC[]]);;

(* A face of a segment containing two distinct points is the segment.      *)

let MOI_LCC_FACE_SEGMENT_TWO = prove
 (`!(a:real^N) b f x y.
     ~(a = b) /\ f face_of segment[a,b] /\ x IN f /\ y IN f /\ ~(x = y)
     ==> f = segment[a,b]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `f face_of segment[a:real^N,b]` THEN
  REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
  SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT; AFFINE_INDEPENDENT_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN AP_TERM_TAC THEN
  MP_TAC(ISPECL [`v:real^N->bool`; `a:real^N`; `b:real^N`] MOI_LCC_SUBSET_PAIR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[CONVEX_HULL_EMPTY; CONVEX_HULL_SING; NOT_IN_EMPTY;
                              IN_SING]) THEN
  ASM_MESON_TAC[]);;

(* A point at distance m from w along the direction of u - w lies in      *)
(* segment[w,u] when 0 <= m <= |u - w|.                                     *)

let MOI_LCC_RAY_IN_SEGMENT = prove
 (`!(w:real^N) u d m.
     ~(u = w) /\ u = w + norm(u - w) % d /\ &0 <= m /\ m <= norm(u - w)
     ==> w + m % d IN segment[w,u]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(u - w:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `m / norm(u - w:real^N)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_MUL_LID];
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (RAND_CONV o RAND_CONV o RAND_CONV)
      [th]) o check (fun th -> is_eq(concl th) && lhs(concl th) = `u:real^N`)) THEN
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - c) % w + c % (w + n % d):real^N = w + (c * n) % d`] THEN
    AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]]);;

(* Distinct edges at a vertex have distinct directions.                    *)

let MOI_LCC_DIRS_INJ = prove
 (`!(l:(real^N->bool)->bool) w u u'.
     simplicial_complex l /\
     ~(u = w) /\ segment[w,u] IN l /\ ~(u' = w) /\ segment[w,u'] IN l /\
     inv(norm(u - w)) % (u - w) = inv(norm(u' - w)) % (u' - w)
     ==> u = u'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(u - w:real^N) /\ &0 < norm(u' - w:real^N)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ABBREV_TAC `d:real^N = inv(norm(u' - w)) % (u' - w)` THEN
  SUBGOAL_THEN `u:real^N = w + norm(u - w) % d /\ u' = w + norm(u' - w) % d`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `inv(norm(u - w)) % (u - w):real^N = d` THEN
      DISCH_THEN(SUBST1_TAC o SYM);
      EXPAND_TAC "d"] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    CONV_TAC VECTOR_ARITH;
    ALL_TAC] THEN
  ABBREV_TAC `m = min (norm(u - w:real^N)) (norm(u' - w:real^N))` THEN
  SUBGOAL_THEN `~(d:real^N = vec 0)` ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0] THEN
    ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) + m % d IN segment[w,u] /\ w + m % d IN segment[w,u'] /\
                ~(w + m % d = w)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `&0 < norm(u - w:real^N)`) THEN
    MP_TAC(ASSUME `&0 < norm(u' - w:real^N)`) THEN
    REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LCC_RAY_IN_SEGMENT THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      EXPAND_TAC "m" THEN
      MAP_EVERY UNDISCH_TAC [`&0 < norm(u - w:real^N)`; `&0 < norm(u' - w:real^N)`] THEN
      REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_LCC_RAY_IN_SEGMENT THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      EXPAND_TAC "m" THEN
      MAP_EVERY UNDISCH_TAC [`&0 < norm(u - w:real^N)`; `&0 < norm(u' - w:real^N)`] THEN
      REAL_ARITH_TAC;
      REWRITE_TAC[VECTOR_ARITH `w + m % d:real^N = w <=> m % d = vec 0`;
                  VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN
      CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
      EXPAND_TAC "m" THEN
      MAP_EVERY UNDISCH_TAC [`&0 < norm(u - w:real^N)`; `&0 < norm(u' - w:real^N)`] THEN
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[w:real^N,u] INTER segment[w,u'] face_of segment[w,u] /\
                segment[w:real^N,u] INTER segment[w,u'] face_of segment[w,u']`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[w:real^N,u] = segment[w,u']` MP_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `segment[w:real^N,u] INTER segment[w,u']` THEN CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_LCC_FACE_SEGMENT_TWO THEN
      MAP_EVERY EXISTS_TAC [`w:real^N`; `w + m % d:real^N`] THEN
      ASM_REWRITE_TAC[IN_INTER; ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[];
      MATCH_MP_TAC MOI_LCC_FACE_SEGMENT_TWO THEN
      MAP_EVERY EXISTS_TAC [`w:real^N`; `w + m % d:real^N`] THEN
      ASM_REWRITE_TAC[IN_INTER; ENDS_IN_SEGMENT] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[SEGMENT_EQ] THEN
    UNDISCH_TAC `~(u:real^N = w)` THEN SET_TAC[]]);;
(* At a vertex w of a complex of dimension at most 1, the unit directions  *)
(* of the polyhedron are the directions of the edges at w.                  *)

let MOI_LCC_DIRS_VERTEX = prove
 (`!(l:(real^N->bool)->bool) w.
     simplicial_complex l /\ (!s. s IN l ==> aff_dim s <= &1) /\ {w} IN l
     ==> moi_lcc_dirs (UNIONS l) w =
         IMAGE (\u. inv(norm(u - w)) % (u - w))
               {u | ~(u = w) /\ segment[w,u] IN l}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool) /\ (!k. k IN l ==> closed k) /\
                (!k. k IN l ==> ?n. n simplex k)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (l:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `d:real^N` THEN
  REWRITE_TAC[moi_lcc_dirs; IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `w:real^N`; `d:real^N`; `e:real`]
      MOI_LCC_GERM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `t:real`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `?n. n simplex (k:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k:real^N->bool`; `n:int`] MOI_LCC_SIMPLEX_LE1) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~((w:real^N) + t % d = w)` ASSUME_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH `w + t % d:real^N = w <=> t % d = vec 0`;
                  VECTOR_MUL_EQ_0; DE_MORGAN_THM] THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_TAC THEN UNDISCH_TAC `norm(d:real^N) = &1` THEN
      ASM_REWRITE_TAC[NORM_0] THEN REAL_ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `(w:real^N) IN k` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY];
      MAP_EVERY UNDISCH_TAC [`(w:real^N) IN k`; `(w:real^N) + t % d IN k`] THEN
      ASM_REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `w:real^N`; `a:real^N`; `b:real^N`]
      MOI_LCC_VERTEX_OF_EDGE) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(LABEL_TAC "ab") THEN
    SUBGOAL_THEN `?u:real^N. ~(u = w) /\ k = segment[w,u]` STRIP_ASSUME_TAC THENL
     [USE_THEN "ab" DISJ_CASES_TAC THENL
       [EXISTS_TAC `b:real^N` THEN ASM_MESON_TAC[];
        EXISTS_TAC `a:real^N` THEN ASM_MESON_TAC[SEGMENT_SYM]];
      ALL_TAC] THEN
    EXISTS_TAC `u:real^N` THEN CONJ_TAC THENL
     [ALL_TAC; ASM_MESON_TAC[]] THEN
    UNDISCH_TAC `(w:real^N) + t % d IN k` THEN
    UNDISCH_THEN `k = segment[w:real^N,u]` SUBST1_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `t % d = s % (u - w:real^N)` ASSUME_TAC THENL
     [UNDISCH_TAC `(w:real^N) + t % d = (&1 - s) % w + s % u` THEN
      CONV_TAC VECTOR_ARITH;
      ALL_TAC] THEN
    SUBGOAL_THEN `t = s * norm(u - w:real^N)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:real^N->real`) THEN
      ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(u - w:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
    MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC `t:real` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < norm(u - w:real^N)` THEN CONV_TAC REAL_FIELD;
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 < norm(u - w:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      MATCH_MP_TAC REAL_MUL_LINV THEN ASM_SIMP_TAC[REAL_LT_IMP_NZ];
      ALL_TAC] THEN
    EXISTS_TAC `norm(u - w:real^N)` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `segment[w:real^N,u]` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_LCC_RAY_IN_SEGMENT THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_RINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID] THEN
    CONV_TAC VECTOR_ARITH]);;
(* At a point inside an edge of a complex of dimension at most 1 there are *)
(* exactly the two opposite directions of the edge.                         *)

let MOI_LCC_DIRS_RELINT = prove
 (`!(l:(real^N->bool)->bool) a b p.
     simplicial_complex l /\ (!s. s IN l ==> aff_dim s <= &1) /\
     segment[a,b] IN l /\ ~(a = b) /\ p IN segment(a,b)
     ==> moi_lcc_dirs (UNIONS l) p =
         {inv(norm(b - a)) % (b - a), --(inv(norm(b - a)) % (b - a))}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool) /\ (!k. k IN l ==> closed k)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (l:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < norm(b - a:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `norm(inv(norm(b - a)) % (b - a:real^N)) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N) IN segment[a,b]` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`a:real^N`; `b:real^N`] SEGMENT_OPEN_SUBSET_CLOSED) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(p:real^N) IN segment(a,b)` THEN REWRITE_TAC[IN_SEGMENT] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `d:real^N` THEN
  REWRITE_TAC[moi_lcc_dirs; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `p:real^N`; `d:real^N`; `e:real`]
      MOI_LCC_GERM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `t:real`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `segment[a:real^N,b] SUBSET k` ASSUME_TAC THENL
     [SUBGOAL_THEN `(k INTER segment[a:real^N,b]) face_of segment[a,b]` MP_TAC THENL
       [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`k INTER segment[a:real^N,b]`; `segment[a:real^N,b]`]
        FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN
      SUBGOAL_THEN `(p:real^N) IN segment(a,b)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `s0:real` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `k INTER segment[a:real^N,b] = segment[a,b]` THENL
       [DISCH_THEN(K ALL_TAC) THEN
        UNDISCH_TAC `k INTER segment[a:real^N,b] = segment[a,b]` THEN SET_TAC[];
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN MATCH_MP_TAC(TAUT `F ==> p`) THEN
        MAP_EVERY UNDISCH_TAC
         [`(k INTER segment[a:real^N,b]) INTER segment(a,b) = {}`;
          `(p:real^N) IN segment(a,b)`; `(p:real^N) IN k`;
          `(p:real^N) IN segment[a,b]`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(p:real^N) + t % d IN affine hull {a,b}` MP_TAC THENL
     [SUBGOAL_THEN `affine hull (segment[a,b]) = affine hull (k:real^N->bool)`
      MP_TAC THENL
       [MATCH_MP_TAC AFF_DIM_EQ_AFFINE_HULL THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[AFFINE_HULL_SEGMENT] THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC(REWRITE_RULE[SUBSET] HULL_SUBSET) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[AFFINE_HULL_2; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:real` (X_CHOOSE_THEN `x2:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `t % d = (x2 - s0) % (b - a:real^N)` ASSUME_TAC THENL
     [UNDISCH_TAC `(p:real^N) + t % d = x1 % a + x2 % b` THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `x1 + x2 = &1` THEN
      REWRITE_TAC[REAL_ARITH `x1 + x2 = &1 <=> x1 = &1 - x2`] THEN
      DISCH_THEN SUBST1_TAC THEN CONV_TAC VECTOR_ARITH;
      ALL_TAC] THEN
    ABBREV_TAC `c = ((x2 - s0) * norm(b - a:real^N)) / t` THEN
    SUBGOAL_THEN `d:real^N = c % (inv(norm(b - a)) % (b - a))` ASSUME_TAC THENL
     [MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC `t:real` THEN
      CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[VECTOR_MUL_ASSOC] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
      EXPAND_TAC "c" THEN UNDISCH_TAC `&0 < t` THEN
      UNDISCH_TAC `&0 < norm(b - a:real^N)` THEN CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `abs c = &1` MP_TAC THENL
     [UNDISCH_TAC `norm(d:real^N) = &1` THEN
      FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `d:real^N`)) THEN
      REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; REAL_MUL_RID];
      ALL_TAC] THEN
    REWRITE_TAC[REAL_ARITH `abs c = &1 <=> c = &1 \/ c = -- &1`] THEN
    STRIP_TAC THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `d:real^N`)) THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LID; VECTOR_MUL_LNEG];
    DISCH_TAC THEN
    SUBGOAL_THEN `norm(d:real^N) = &1` ASSUME_TAC THENL
     [FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[NORM_NEG]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `min s0 (&1 - s0) * norm(b - a:real^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `t:real` THEN STRIP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `segment[a:real^N,b]` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `t * inv(norm(b - a:real^N)) < min s0 (&1 - s0)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[GSYM real_div; REAL_LT_LDIV_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < t * inv(norm(b - a:real^N))` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LT_MUL THEN ASM_SIMP_TAC[REAL_LT_INV_EQ]; ALL_TAC] THEN
    REWRITE_TAC[IN_SEGMENT] THEN
    FIRST_X_ASSUM DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [EXISTS_TAC `s0 + t * inv(norm(b - a:real^N))`;
      EXISTS_TAC `s0 - t * inv(norm(b - a:real^N))`] THEN
    (CONJ_TAC THENL
      [UNDISCH_TAC `t * inv(norm(b - a:real^N)) < min s0 (&1 - s0)` THEN
       UNDISCH_TAC `&0 < t * inv(norm(b - a:real^N))` THEN ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
     CONJ_TAC THENL
      [UNDISCH_TAC `t * inv(norm(b - a:real^N)) < min s0 (&1 - s0)` THEN
       UNDISCH_TAC `&0 < t * inv(norm(b - a:real^N))` THEN ASM_REAL_ARITH_TAC;
       ALL_TAC] THEN
     CONV_TAC VECTOR_ARITH)]);;

(* ------------------------------------------------------------------------- *)
(* G. Generic helpers: small multiples, finite lf complexes, the dimension  *)
(* bound of combinatorial 1-manifolds, points near a vertex, injectivity of *)
(* locally injective affine maps on convex sets, affine maps on segments.   *)
(* ------------------------------------------------------------------------- *)

let MOI_LCC_SMALL_MUL = prove
 (`!(d:real^N) r.
     &0 < r ==> ?e. &0 < e /\ e <= &1 /\ !t. abs t <= e ==> norm(t % d) < r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(d:real^N) + &1` ASSUME_TAC THENL
   [MP_TAC(ISPEC `d:real^N` NORM_POS_LE) THEN REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r / (&2 * (norm(d:real^N) + &1))` ASSUME_TAC THENL
   [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `min (&1) (r / (&2 * (norm(d:real^N) + &1)))` THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN; REAL_LT_01];
    REAL_ARITH_TAC;
    X_GEN_TAC `t:real` THEN DISCH_TAC THEN REWRITE_TAC[NORM_MUL] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN
    EXISTS_TAC `r / (&2 * (norm(d:real^N) + &1)) * (norm d + &1)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_MUL2 THEN REWRITE_TAC[REAL_ABS_POS; NORM_POS_LE] THEN
      ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_FIELD `&0 < a ==> r / (&2 * a) * a = r / &2`] THEN
      ASM_REAL_ARITH_TAC]]);;

let MOI_LCC_LF_SC = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ lf_simplicial_complex c ==> simplicial_complex c`,
  GEN_TAC THEN REWRITE_TAC[simplicial_complex; lf_simplicial_complex] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_LCC_CMWB1_DIM = prove
 (`!l:(real^N->bool)->bool.
     combinatorial_manifold_with_boundary 1 l
     ==> !t. t IN l ==> aff_dim t <= &1`,
  GEN_TAC THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  REWRITE_TAC[MOI_LCC_PL_BALL_0; MOI_LCC_PL_SPHERE_0] THEN
  STRIP_TAC THEN X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [simplex]) THEN
  DISCH_THEN(X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (t:real^N->bool) = &(CARD (V:real^N->bool)) - &1`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT];
    ALL_TAC] THEN
  REWRITE_TAC[INT_ARITH `x - &1:int <= &1 <=> x <= &2`; INT_OF_NUM_LE] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `V:real^N->bool` CHOOSE_SUBSET) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `3`) THEN ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` MP_TAC) THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `{a:real^N,b,x} SUBSET V` ASSUME_TAC THENL
   [UNDISCH_TAC `(W:real^N->bool) SUBSET V` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^N->bool. c SUBSET V ==> convex hull c face_of t`
  ASSUME_TAC THENL
   [X_GEN_TAC `c:real^N->bool` THEN DISCH_TAC THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!c:real^N->bool. c SUBSET V ==> convex hull c IN l`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN l /\ segment[b:real^N,x] IN l` STRIP_ASSUME_TAC
  THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THENL
     [SUBST1_TAC(SYM(ISPEC `a:real^N` CONVEX_HULL_SING)); ALL_TAC] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((a:real^N) IN segment[b,x])` ASSUME_TAC THENL
   [UNDISCH_TAC `~affine_dependent (V:real^N->bool)` THEN
    REWRITE_TAC[affine_dependent; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N`) THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> ~(p /\ r) ==> ~q`) THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^N) IN s ==> x IN t`) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull {b:real^N,x}` THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL; CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[b:real^N,x] SUBSET UNIONS (simplicial_link l a)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!x:real^N->bool s. x IN s ==> x SUBSET UNIONS s`) THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      EXISTS_TAC `t:real^N->bool` THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `t = convex hull (V:real^N->bool)` THEN
        DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[];
        REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (UNIONS (simplicial_link l (a:real^N)))` MP_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o check (is_forall o concl)) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    DISCH_THEN(MP_TAC o MATCH_MP (REWRITE_RULE[IMP_CONJ] FINITE_SUBSET)) THEN
    DISCH_THEN(MP_TAC o SPEC `segment[b:real^N,x]`) THEN
    ASM_REWRITE_TAC[FINITE_SEGMENT]]);;

let MOI_LCC_NEAR_CLOSED = prove
 (`!(c:(real^N->bool)->bool) v.
     FINITE c /\ (!t. t IN c ==> closed t)
     ==> ?r. &0 < r /\ !t x. t IN c /\ x IN t /\ dist(v,x) < r ==> v IN t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS {t | t IN c /\ ~((v:real^N) IN t)}`; `v:real^N`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `x:real^N`] THEN
  STRIP_TAC THEN ASM_CASES_TAC `(v:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_REAL_ARITH_TAC]);;

let MOI_LCC_AFFINE_INJ = prove
 (`!(f:real^M->real^N) s k l y.
     convex k /\ k SUBSET s /\ linear l /\ (!z. z IN k ==> f z = l z + y) /\
     (!x. x IN s
          ==> ?n. open n /\ x IN n /\
                  !p q. p IN n INTER s /\ q IN n INTER s /\ f p = f q ==> p = q)
     ==> !x x'. x IN k /\ x' IN k /\ f x = f x' ==> x = x'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`x:real^M`; `x':real^M`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^M`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^M->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^M`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`x' - x:real^M`; `r:real`] MOI_LCC_SMALL_MUL) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `x + e % (x' - x:real^M) IN k` ASSUME_TAC THENL
   [SUBGOAL_THEN `x + e % (x' - x:real^M) = (&1 - e) % x + e % x'` SUBST1_TAC
    THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o GEN_REWRITE_RULE I [convex]) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^M->real^N) x' = l x` ASSUME_TAC THENL
   [UNDISCH_TAC `(f:real^M->real^N) x = f x'` THEN ASM_SIMP_TAC[] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^M->real^N)(x + e % (x' - x)) = f x` ASSUME_TAC THENL
   [ASM_SIMP_TAC[] THEN ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; LINEAR_SUB] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `x + e % (x' - x:real^M) = x` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
    REPEAT CONJ_TAC THEN TRY(ASM SET_TAC[]) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      can (find_term (fun t -> t = `ball:real^M#real->real^M->bool`)) (concl th))) THEN
    REWRITE_TAC[IN_BALL; NORM_ARITH `dist(x:real^M,x + d) = norm d`] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_ARITH
   `x + e % (x' - x:real^M) = x <=> e % (x' - x) = vec 0`] THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
  SUBGOAL_THEN `~(e = &0)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REAL_ARITH_TAC; MESON_TAC[]]);;

let MOI_LCC_AFFINE_SEG = prove
 (`!(f:real^M->real^N) l y a b.
     linear l /\ (!z. z IN segment[a,b] ==> f z = l z + y)
     ==> !t. &0 <= t /\ t <= &1 ==> f(a + t % (b - a)) = f a + t % (f b - f a)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `a + t % (b - a:real^M) IN segment[a,b]` ASSUME_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `t:real` THEN ASM_REWRITE_TAC[] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[ENDS_IN_SEGMENT; LINEAR_ADD; LINEAR_CMUL; LINEAR_SUB] THEN
  VECTOR_ARITH_TAC);;

let MOI_LCC_CARD_LE2 = prove
 (`!(s:A->bool) a b c.
     FINITE s /\ CARD s <= 2 /\ a IN s /\ b IN s /\ c IN s
     ==> a = b \/ a = c \/ b = c`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `a:A = b` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `a:A = c` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `b:A = c` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`{a:A,b,c}`; `s:A->bool`] CARD_SUBSET) THEN
  ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* D. Fibres and local preimages of a singular disk: a double point has     *)
(* exactly two preimages, f is injective on small balls, and double points  *)
(* near f v have a preimage near v (compactness).                           *)
(* ------------------------------------------------------------------------- *)

let MOI_LCC_FIBER_TWO = prove
 (`!c (f:real^2->real^N) v.
     moi_lt_singular_disk c f /\ v IN std_triangle /\
     f v IN moi_lt_double_image f
     ==> ?v'. v' IN std_triangle /\ ~(v' = v) /\ f v' = f v /\
              !x. x IN std_triangle /\ f x = f v ==> x = v \/ x = v'`,
  REWRITE_TAC[moi_lt_singular_disk; moi_lt_double_image; IN_ELIM_THM] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `x1:real^2` (X_CHOOSE_THEN `x2:real^2` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN
   `!a b d:real^2.
      a IN std_triangle /\ (f:real^2->real^N) a = f v /\
      b IN std_triangle /\ f b = f v /\ d IN std_triangle /\ f d = f v
      ==> a = b \/ a = d \/ b = d`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_LCC_CARD_LE2 THEN
    EXISTS_TAC `{x | x IN std_triangle /\ (f:real^2->real^N) x = f v}` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `x1:real^2 = v` THENL
   [EXISTS_TAC `x2:real^2` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `v:real^2`; `x2:real^2`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    EXISTS_TAC `x1:real^2` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`x:real^2`; `v:real^2`; `x1:real^2`]) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

let MOI_LCC_LOCINJ_BALL = prove
 (`!c (f:real^2->real^N) x.
     moi_lt_singular_disk c f /\ x IN std_triangle
     ==> ?r. &0 < r /\
             !y z. y IN std_triangle /\ z IN std_triangle /\
                   dist(x,y) < r /\ dist(x,z) < r /\ f y = f z ==> y = z`,
  REWRITE_TAC[moi_lt_singular_disk] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:real^2->bool` STRIP_ASSUME_TAC) THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^2`) THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    length(fst(strip_forall(concl th))) = 2)) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o
    check (fun th -> can (find_term (fun t ->
      t = `ball:real^2#real->real^2->bool`)) (concl th))) THEN
  ASM_REWRITE_TAC[IN_BALL]);;

let MOI_LCC_LOCAL_PREIMAGE = prove
 (`!c (f:real^2->real^N) v r.
     moi_lt_singular_disk c f /\ v IN std_triangle /\
     f v IN moi_lt_double_image f /\ &0 < r
     ==> ?e. &0 < e /\
             !y. y IN moi_lt_double_image f /\ dist(y,f v) < e
                 ==> ?x. x IN std_triangle /\ dist(v,x) < r /\ f x = y`,
  REPEAT STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `v:real^2`]
    MOI_LCC_FIBER_TWO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v':real^2` STRIP_ASSUME_TAC) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `v:real^2`]
    MOI_LCC_LOCINJ_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "i1"))) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `v':real^2`]
    MOI_LCC_LOCINJ_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "i2"))) THEN
  ABBREV_TAC `d = min r (min r1 r2)` THEN
  SUBGOAL_THEN `&0 < d /\ d <= r /\ d <= r1 /\ d <= r2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "d" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ABBREV_TAC
   `C = std_triangle DIFF (ball(v:real^2,d) UNION ball(v',d))` THEN
  SUBGOAL_THEN `compact (IMAGE (f:real^2->real^N) C)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `std_triangle` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN
        ASM_MESON_TAC[moi_lt_singular_disk];
        EXPAND_TAC "C" THEN SET_TAC[]];
      EXPAND_TAC "C" THEN MATCH_MP_TAC COMPACT_DIFF THEN
      REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN
      SIMP_TAC[OPEN_UNION; OPEN_BALL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`IMAGE (f:real^2->real^N) C`; `(f:real^2->real^N) v`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN EXPAND_TAC "C" THEN
    REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_UNION; IN_BALL; NOT_EXISTS_THM] THEN
    X_GEN_TAC `z:real^2` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^2` o check (fun th ->
      is_forall(concl th) && is_disj(snd(dest_imp(snd(dest_forall(concl th))))))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN UNDISCH_TAC `~(dist(v:real^2,z) < d \/ dist(v',z) < d)` THEN
    ASM_REWRITE_TAC[DIST_REFL];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "sep"))) THEN
  EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^2. x IN std_triangle /\ (f:real^2->real^N) x = y
               ==> dist(v,x) < d \/ dist(v',x) < d`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^2` THEN STRIP_TAC THEN
    REMOVE_THEN "sep" (MP_TAC o SPEC `(f:real^2->real^N) x`) THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[IN_IMAGE; IN_DIFF; IN_UNION; IN_BALL] THEN
    MATCH_MP_TAC(TAUT `(~r ==> p) /\ ~q ==> (p ==> q) ==> r`) THEN
    CONJ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `x:real^2` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `dist(y:real^N,f(v:real^2)) < e` THEN
      ASM_REWRITE_TAC[DIST_SYM] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(y:real^N) IN moi_lt_double_image f` THEN
  REWRITE_TAC[moi_lt_double_image; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `x1:real^2` (X_CHOOSE_THEN `x2:real^2`
    STRIP_ASSUME_TAC)) THEN
  ASM_CASES_TAC `dist(v:real^2,x1) < d` THENL
   [EXISTS_TAC `x1:real^2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `dist(v:real^2,x2) < d` THENL
   [EXISTS_TAC `x2:real^2` THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(v':real^2,x1) < d /\ dist(v',x2) < d` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~(x1:real^2 = x2)` THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  REMOVE_THEN "i2" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_REAL_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* P. The source complex: preimages of the simplices of the double image   *)
(* complex under the affine pieces of f are polytopes of dimension <= 1;   *)
(* a simplicial refinement of them, restricted to the simplices inside one *)
(* piece, triangulates the source double set.                               *)
(* ------------------------------------------------------------------------- *)

let MOI_LCC_AFF_DIM_AFFINE_IMAGE_LE = prove
 (`!(l:real^M->real^N) y s.
     linear l ==> aff_dim (IMAGE (\z. l z + y) s) <= aff_dim s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (\z. (l:real^M->real^N) z + y) s =
                IMAGE (\x. y + x) (IMAGE l s)` SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[AFF_DIM_TRANSLATION_EQ] THEN
    ASM_SIMP_TAC[AFF_DIM_LINEAR_IMAGE_LE]]);;

let MOI_LCC_PREIMAGE_POLYTOPE = prove
 (`!(f:real^M->real^N) k e l y.
     polytope k /\ polytope e /\ linear l /\ (!z. z IN k ==> f z = l z + y) /\
     (!x x'. x IN k /\ x' IN k /\ f x = f x' ==> x = x')
     ==> polytope {x | x IN k /\ f x IN e} /\
         aff_dim {x | x IN k /\ f x IN e} <= aff_dim e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`l:real^M->real^N`; `y:real^N`; `k:real^M->bool`]
    MOI_PLM_AFFINE_INJECTIVE_LEFT_INVERSE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `l':real^N->real^M` (X_CHOOSE_THEN `y':real^M`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `{x | x IN k /\ (f:real^M->real^N) x IN e} =
    IMAGE (\z. (l':real^N->real^M) z + y') (IMAGE (\z. l z + y) k INTER e)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE; IN_INTER] THEN
    X_GEN_TAC `x:real^M` THEN EQ_TAC THENL
     [STRIP_TAC THEN EXISTS_TAC `(l:real^M->real^N) x + y` THEN
      ASM_SIMP_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `x:real^M` THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` (CONJUNCTS_THEN2 SUBST1_TAC
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `w:real^M` STRIP_ASSUME_TAC)
         ASSUME_TAC))) THEN
      UNDISCH_TAC `(z:real^N) IN e` THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_PLM_POLYTOPE_AFFINE_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC POLYTOPE_INTER THEN ASM_SIMP_TAC[MOI_PLM_POLYTOPE_AFFINE_IMAGE];
    MATCH_MP_TAC INT_LE_TRANS THEN
    EXISTS_TAC `aff_dim (IMAGE (\z. (l:real^M->real^N) z + y) k INTER e)` THEN
    ASM_SIMP_TAC[MOI_LCC_AFF_DIM_AFFINE_IMAGE_LE] THEN
    MATCH_MP_TAC AFF_DIM_SUBSET THEN SET_TAC[]]);;

let MOI_LCC_SUBCOMPLEX = prove
 (`!(t:(real^N->bool)->bool) p.
     simplicial_complex t
     ==> simplicial_complex {s | s IN t /\ ?q. q IN p /\ s SUBSET q}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex; IN_ELIM_THM] THEN
  STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`f:real^N->bool`; `s:real^N->bool`] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET_TRANS];
    ASM_MESON_TAC[]]);;

let MOI_LCC_SOURCE_COMPLEX = prove
 (`!c (f:real^2->real^N) s.
     moi_lt_singular_disk c f /\ FINITE s /\
     (!e. e IN s ==> polytope e /\ aff_dim e <= &1) /\
     UNIONS s = moi_lt_double_image f
     ==> ?s0. simplicial_complex s0 /\
              UNIONS s0 =
                {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
              !t. t IN s0
                  ==> aff_dim t <= &1 /\ t SUBSET std_triangle /\
                      ?l y. linear l /\ !z. z IN t ==> f z = l z + y`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_lt_singular_disk]) THEN
  MP_TAC(ISPECL [`std_triangle`; `f:real^2->real^N`]
    MOI_PLM_PL_MAP_ON_COMPACT_FINITE) THEN
  ASM_REWRITE_TAC[MOI_LTD_STD_TRIANGLE_BASIC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^2->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (ASSUME_TAC o SYM) (LABEL_TAC "K")))) THEN
  ABBREV_TAC
   `S = {x | x IN std_triangle /\ (f:real^2->real^N) x IN moi_lt_double_image f}` THEN
  ABBREV_TAC
   `P = {{x | x IN k /\ (f:real^2->real^N) x IN e} | k IN K /\ e IN s}` THEN
  SUBGOAL_THEN `FINITE (P:(real^2->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q. q IN P
        ==> polytope q /\ aff_dim q <= &1 /\ q SUBSET (S:real^2->bool) /\
            ?k l y. k IN K /\ q SUBSET k /\ linear l /\
                    !z. z IN k ==> (f:real^2->real^N) z = l z + y`
  (LABEL_TAC "Pp") THENL
   [EXPAND_TAC "P" THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`k:real^2->bool`; `e:real^N->bool`] THEN STRIP_TAC THEN
    REMOVE_THEN "K" (MP_TAC o SPEC `k:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `y:real^N`
        STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN
     `!x x'. x IN k /\ x' IN k /\ (f:real^2->real^N) x = f x' ==> x = x'`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(ISPECL [`f:real^2->real^N`; `std_triangle`; `k:real^2->bool`;
                           `l:real^2->real^N`; `y:real^N`] MOI_LCC_AFFINE_INJ) THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_CONVEX];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`f:real^2->real^N`; `k:real^2->bool`; `e:real^N->bool`;
                   `l:real^2->real^N`; `y:real^N`] MOI_LCC_PREIMAGE_POLYTOPE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(e:real^N->bool)` THEN
      ASM_SIMP_TAC[];
      EXPAND_TAC "S" THEN
      UNDISCH_TAC `UNIONS s = moi_lt_double_image (f:real^2->real^N)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
      MAP_EVERY EXISTS_TAC [`k:real^2->bool`; `l:real^2->real^N`; `y:real^N`] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `P:(real^2->bool)->bool` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^2->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ref")))) THEN
  EXISTS_TAC `{r | r IN t /\ ?q. q IN P /\ r SUBSET (q:real^2->bool)}` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_LCC_SUBCOMPLEX THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^2` THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^2->bool` (CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:real^2->bool`
          STRIP_ASSUME_TAC)) ASSUME_TAC)) THEN
      REMOVE_THEN "Pp" (MP_TAC o SPEC `q:real^2->bool`) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^2` THEN EXPAND_TAC "S" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      SUBGOAL_THEN `?k:real^2->bool. k IN K /\ x IN k` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?e:real^N->bool. e IN s /\ (f:real^2->real^N) x IN e`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `{z | z IN k /\ (f:real^2->real^N) z IN e} IN P` ASSUME_TAC
      THENL
       [EXPAND_TAC "P" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`k:real^2->bool`; `e:real^N->bool`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REMOVE_THEN "ref" (MP_TAC o SPEC `{z | z IN k /\ (f:real^2->real^N) z IN e}`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `Fr:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(x:real^2) IN UNIONS Fr` MP_TAC THENL
       [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^2->bool` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `r:real^2->bool` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      EXISTS_TAC `{z | z IN k /\ (f:real^2->real^N) z IN e}` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `r:real^2->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:real^2->bool`
      STRIP_ASSUME_TAC)) THEN
    REMOVE_THEN "Pp" (MP_TAC o SPEC `q:real^2->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `k:real^2->bool`
        (X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `y:real^N`
          STRIP_ASSUME_TAC)))))) THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(q:real^2->bool)` THEN
      ASM_SIMP_TAC[AFF_DIM_SUBSET];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `S:real^2->bool` THEN
      CONJ_TAC THENL [ASM SET_TAC[]; EXPAND_TAC "S" THEN SET_TAC[]];
      MAP_EVERY EXISTS_TAC [`l:real^2->real^N`; `y:real^N`] THEN
      ASM_REWRITE_TAC[] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]]]);;


(* ------------------------------------------------------------------------- *)
(* E. Edges at a vertex v of the source complex correspond bijectively to   *)
(* the unit directions of the double image at f v.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_LCC_IN_SEG_PARAM = prove
 (`!(a:real^N) b t. &0 <= t /\ t <= &1 ==> a + t % (b - a) IN segment[a,b]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `t:real` THEN
  ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC);;

let MOI_LCC_DIR_SCALE = prove
 (`!(d:real^N) w t m.
     norm d = &1 /\ &0 < t /\ &0 < m /\ t % d = m % w
     ==> d = inv(norm w) % w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `t = m * norm(w:real^N)` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o AP_TERM `norm:real^N->real`) THEN
    ASM_REWRITE_TAC[NORM_MUL; REAL_MUL_RID] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < x ==> abs x = x`];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(norm(w:real^N) = &0)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `t = m * norm(w:real^N)` THEN
    ASM_REWRITE_TAC[REAL_MUL_RZERO] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC VECTOR_MUL_LCANCEL_IMP THEN EXISTS_TAC `t:real` THEN
  ASM_SIMP_TAC[REAL_LT_IMP_NZ; VECTOR_MUL_ASSOC] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(norm(w:real^N) = &0)` THEN CONV_TAC REAL_FIELD);;

let MOI_LCC_SRC_DIR_IN = prove
 (`!c (f:real^2->real^N) s0 v u.
     moi_lt_singular_disk c f /\ simplicial_complex s0 /\
     UNIONS s0 = {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
     (!t. t IN s0 ==> aff_dim t <= &1 /\ t SUBSET std_triangle /\
                      ?l y. linear l /\ !z. z IN t ==> f z = l z + y) /\
     ~(u = v) /\ segment[v,u] IN s0
     ==> ~(f u = f v) /\
         (!t. &0 <= t /\ t <= &1
              ==> f(v + t % (u - v)) = f v + t % (f u - f v)) /\
         inv(norm(f u - f v)) % (f u - f v) IN
         moi_lcc_dirs (moi_lt_double_image f) (f v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `segment[v:real^2,u]` o check (fun th ->
    is_forall(concl th) && is_imp(snd(dest_forall(concl th))))) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `l:real^2->real^N` (X_CHOOSE_THEN `y:real^N`
      STRIP_ASSUME_TAC)))) THEN
  MP_TAC(ISPECL [`f:real^2->real^N`; `l:real^2->real^N`; `y:real^N`;
                 `v:real^2`; `u:real^2`] MOI_LCC_AFFINE_SEG) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "aff") THEN
  SUBGOAL_THEN `~((f:real^2->real^N) u = f v)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`f:real^2->real^N`; `std_triangle`; `segment[v:real^2,u]`;
                   `l:real^2->real^N`; `y:real^N`] MOI_LCC_AFFINE_INJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[CONVEX_SEGMENT] THEN ASM_MESON_TAC[moi_lt_singular_disk];
      DISCH_THEN(MP_TAC o SPECL [`u:real^2`; `v:real^2`]) THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 < norm((f:real^2->real^N) u - f v)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  REWRITE_TAC[moi_lcc_dirs; IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[NORM_MUL; REAL_ABS_INV; REAL_ABS_NORM] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  EXISTS_TAC `norm((f:real^2->real^N) u - f v)` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `t:real` THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `(f:real^2->real^N) v + t % inv(norm(f u - f v)) % (f u - f v) =
    f(v + (t / norm(f u - f v)) % (u - v))`
  SUBST1_TAC THENL
   [REMOVE_THEN "aff" (fun th -> W(fun (_,w) ->
      MP_TAC(SPEC `t / norm((f:real^2->real^N) u - f v)` th))) THEN
    ANTS_TAC THENL
     [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; NORM_POS_LE; REAL_LE_LDIV_EQ] THEN
      ASM_REAL_ARITH_TAC;
      DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[real_div; VECTOR_MUL_ASSOC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `v + (t / norm((f:real^2->real^N) u - f v)) % (u - v) IN
                UNIONS s0` MP_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[v:real^2,u]` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_LCC_IN_SEG_PARAM THEN
    ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; NORM_POS_LE; REAL_LE_LDIV_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]]);;

let MOI_LCC_SRC_DIR_INJ = prove
 (`!c (f:real^2->real^N) s0 v u u'.
     moi_lt_singular_disk c f /\ simplicial_complex s0 /\
     UNIONS s0 = {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
     (!t. t IN s0 ==> aff_dim t <= &1 /\ t SUBSET std_triangle /\
                      ?l y. linear l /\ !z. z IN t ==> f z = l z + y) /\
     ~(u = v) /\ segment[v,u] IN s0 /\ ~(u' = v) /\ segment[v,u'] IN s0 /\
     inv(norm(f u - f v)) % (f u - f v) = inv(norm(f u' - f v)) % (f u' - f v)
     ==> u = u'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `s0:(real^2->bool)->bool`; `v:real^2`; `u:real^2`] MOI_LCC_SRC_DIR_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "au")
    ASSUME_TAC)) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `s0:(real^2->bool)->bool`; `v:real^2`; `u':real^2`] MOI_LCC_SRC_DIR_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "au'")
    ASSUME_TAC)) THEN
  SUBGOAL_THEN `segment[v:real^2,u] SUBSET std_triangle /\
                segment[v:real^2,u'] SUBSET std_triangle`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^2) IN std_triangle` ASSUME_TAC THENL
   [ASM_MESON_TAC[ENDS_IN_SEGMENT; SUBSET]; ALL_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `v:real^2`]
    MOI_LCC_LOCINJ_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "inj"))) THEN
  MP_TAC(ISPECL [`u - v:real^2`; `r:real`] MOI_LCC_SMALL_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s1")))) THEN
  MP_TAC(ISPECL [`u' - v:real^2`; `r:real`] MOI_LCC_SMALL_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s2")))) THEN
  SUBGOAL_THEN `&0 < norm((f:real^2->real^N) u - f v) /\
                &0 < norm((f:real^2->real^N) u' - f v)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  ABBREV_TAC `t = min (norm((f:real^2->real^N) u - f v) * e1)
                      (norm((f:real^2->real^N) u' - f v) * e2)` THEN
  SUBGOAL_THEN `&0 < t /\ t <= norm((f:real^2->real^N) u - f v) * e1 /\
                t <= norm((f:real^2->real^N) u' - f v) * e2`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN REWRITE_TAC[REAL_LT_MIN] THEN
    SIMP_TAC[REAL_LT_MUL; ASSUME `&0 < norm((f:real^2->real^N) u - f v)`;
             ASSUME `&0 < norm((f:real^2->real^N) u' - f v)`;
             ASSUME `&0 < e1`; ASSUME `&0 < e2`] THEN
    REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = t / norm((f:real^2->real^N) u - f v)` THEN
  ABBREV_TAC `m' = t / norm((f:real^2->real^N) u' - f v)` THEN
  SUBGOAL_THEN `&0 < m /\ m <= e1 /\ &0 < m' /\ m' <= e2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["m"; "m'"] THEN
    SIMP_TAC[REAL_LT_DIV; REAL_LE_LDIV_EQ; ASSUME `&0 < t`;
             ASSUME `&0 < norm((f:real^2->real^N) u - f v)`;
             ASSUME `&0 < norm((f:real^2->real^N) u' - f v)`] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(f:real^2->real^N)(v + m % (u - v)) = f(v + m' % (u' - v))`
  ASSUME_TAC THENL
   [USE_THEN "au" (MP_TAC o SPEC `m:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    USE_THEN "au'" (MP_TAC o SPEC `m':real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
    MAP_EVERY EXPAND_TAC ["m"; "m'"] THEN
    REWRITE_TAC[real_div; GSYM VECTOR_MUL_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `v + m % (u - v:real^2) = v + m' % (u' - v)` ASSUME_TAC THENL
   [REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[NORM_ARITH `dist(v:real^2,v + x) = norm x`] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `segment[v:real^2,u] SUBSET std_triangle`)) THEN
      MATCH_MP_TAC MOI_LCC_IN_SEG_PARAM THEN ASM_REAL_ARITH_TAC;
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        concl th = `segment[v:real^2,u'] SUBSET std_triangle`)) THEN
      MATCH_MP_TAC MOI_LCC_IN_SEG_PARAM THEN ASM_REAL_ARITH_TAC;
      REMOVE_THEN "s1" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC;
      REMOVE_THEN "s2" MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v + m % (u - v:real^2) = v)` ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_ARITH `v + m % (u - v:real^2) = v <=> m % (u - v) = vec 0`;
                VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `v + m % (u - v:real^2) IN segment[v,u] /\
                v + m % (u - v:real^2) IN segment[v,u']`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC MOI_LCC_IN_SEG_PARAM THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^2,u] INTER segment[v,u'] = segment[v,u] /\
                segment[v:real^2,u] INTER segment[v,u'] = segment[v,u']`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_LCC_FACE_SEGMENT_TWO THEN
    MAP_EVERY EXISTS_TAC [`v:real^2`; `v + m % (u - v:real^2)`] THEN
    ASM_REWRITE_TAC[IN_INTER; ENDS_IN_SEGMENT] THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (MESON[]
    `!a b c:real^2->bool. a = b /\ a = c ==> b = c`)) THEN
  REWRITE_TAC[SEGMENT_EQ] THEN ASM SET_TAC[]);;
let MOI_LCC_SRC_DIR_ONTO = prove
 (`!c (f:real^2->real^N) s0 v d.
     moi_lt_singular_disk c f /\ simplicial_complex s0 /\
     UNIONS s0 = {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
     (!t. t IN s0 ==> aff_dim t <= &1 /\ t SUBSET std_triangle /\
                      ?l y. linear l /\ !z. z IN t ==> f z = l z + y) /\
     {v} IN s0 /\ d IN moi_lcc_dirs (moi_lt_double_image f) (f v)
     ==> ?u. ~(u = v) /\ segment[v,u] IN s0 /\
             d = inv(norm(f u - f v)) % (f u - f v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^2) IN std_triangle /\
                (f:real^2->real^N) v IN moi_lt_double_image f`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(v:real^2) IN UNIONS s0` MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^2}` THEN
      ASM_REWRITE_TAC[IN_SING];
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  UNDISCH_TAC `d IN moi_lcc_dirs (moi_lt_double_image f) ((f:real^2->real^N) v)` THEN
  REWRITE_TAC[moi_lcc_dirs; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `e:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ray")))) THEN
  MP_TAC(ISPECL [`s0:(real^2->bool)->bool`; `v:real^2`] MOI_LCC_NEAR_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CLOSED]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "near"))) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `v:real^2`;
                `rho:real`] MOI_LCC_LOCAL_PREIMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "pre"))) THEN
  ABBREV_TAC `t = min e e0 / &2` THEN
  SUBGOAL_THEN `&0 < t /\ t < e /\ t < e0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REMOVE_THEN "pre" (MP_TAC o SPEC `(f:real^2->real^N) v + t % d`) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [USE_THEN "ray" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[NORM_ARITH `dist(a + x:real^N,a) = norm x`; NORM_MUL] THEN
      ASM_REWRITE_TAC[REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^2) IN UNIONS s0` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM] THEN USE_THEN "ray" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^2->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^2) IN sg` ASSUME_TAC THENL
   [REMOVE_THEN "near" MATCH_MP_TAC THEN EXISTS_TAC `x:real^2` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex (sg:real^2->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`sg:real^2->bool`; `n:int`] MOI_LCC_SIMPLEX_LE1) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[NOT_IN_EMPTY];
    SUBGOAL_THEN `x:real^2 = v` SUBST_ALL_TAC THENL
     [ASM_MESON_TAC[IN_SING]; ALL_TAC] THEN
    UNDISCH_TAC `(f:real^2->real^N) v = f v + t % d` THEN
    REWRITE_TAC[VECTOR_ARITH `a:real^N = a + x <=> x = vec 0`; VECTOR_MUL_EQ_0] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ; GSYM NORM_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> lhs(concl th) = `sg:real^2->bool`)) THEN
  SUBGOAL_THEN `?u. ~(u = v) /\ segment[v:real^2,u] IN s0 /\ x IN segment[v,u]`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s0:(real^2->bool)->bool`; `v:real^2`; `a:real^2`; `b:real^2`]
      MOI_LCC_VERTEX_OF_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [EXISTS_TAC `b:real^2` THEN ASM_MESON_TAC[];
      EXISTS_TAC `a:real^2` THEN ASM_MESON_TAC[SEGMENT_SYM]];
    ALL_TAC] THEN
  EXISTS_TAC `u:real^2` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `s0:(real^2->bool)->bool`; `v:real^2`; `u:real^2`] MOI_LCC_SRC_DIR_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "aff")
    ASSUME_TAC)) THEN
  UNDISCH_TAC `(x:real^2) IN segment[v,u]` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `t % d = m % ((f:real^2->real^N) u - f v)` ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:real^2->real^N) x = f v + m % (f u - f v)` MP_TAC THENL
     [SUBGOAL_THEN `x = v + m % (u - v:real^2)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      REMOVE_THEN "aff" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < m` ASSUME_TAC THENL
   [ASM_CASES_TAC `m = &0` THENL
     [UNDISCH_TAC `t % d = m % ((f:real^2->real^N) u - f v)` THEN
      ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_MUL_EQ_0] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ; GSYM NORM_EQ_0; REAL_OF_NUM_EQ; ARITH_EQ];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_LCC_DIR_SCALE THEN
  MAP_EVERY EXISTS_TAC [`t:real`; `m:real`] THEN ASM_REWRITE_TAC[]);;

let MOI_LCC_SRC_DEG = prove
 (`!c (f:real^2->real^N) s0 v.
     moi_lt_singular_disk c f /\ simplicial_complex s0 /\
     UNIONS s0 = {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
     (!t. t IN s0 ==> aff_dim t <= &1 /\ t SUBSET std_triangle /\
                      ?l y. linear l /\ !z. z IN t ==> f z = l z + y) /\
     {v} IN s0
     ==> !n. {u | ~(u = v) /\ segment[v,u] IN s0} HAS_SIZE n <=>
             moi_lcc_dirs (moi_lt_double_image f) (f v) HAS_SIZE n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_lcc_dirs (moi_lt_double_image f) ((f:real^2->real^N) v) =
    IMAGE (\u. inv(norm(f u - f v)) % (f u - f v))
          {u | ~(u = v) /\ segment[v,u] IN s0}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `d:real^N` THEN
    EQ_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
        `s0:(real^2->bool)->bool`; `v:real^2`; `d:real^N`] MOI_LCC_SRC_DIR_ONTO) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `u:real^2` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
        `s0:(real^2->bool)->bool`; `v:real^2`; `u:real^2`] MOI_LCC_SRC_DIR_IN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  GEN_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ_EQ THEN
  REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN
  MAP_EVERY X_GEN_TAC [`u:real^2`; `u':real^2`] THEN STRIP_TAC THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `s0:(real^2->bool)->bool`; `v:real^2`; `u:real^2`; `u':real^2`]
    MOI_LCC_SRC_DIR_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* C. A boundary double point is not inside a segment of the double image: *)
(* the crossing chart maps the double image near it injectively into a ray *)
(* starting at the image 0 of the point, and an injective continuous map   *)
(* of a segment into a ray cannot attain its minimum inside the segment.   *)
(* ------------------------------------------------------------------------- *)

let MOI_LCC_NOT_IN_SUBSEGMENT = prove
 (`!(p:real^N) q w. w IN segment(p,q) ==> ~(p IN segment[w,q])`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[open_segment; IN_DIFF; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  REWRITE_TAC[GSYM BETWEEN_IN_SEGMENT; between] THEN
  CONV_TAC NORM_ARITH);;

let MOI_LCC_RAY_NO_INTERIOR = prove
 (`!(h:real^N->real^3) p q w.
     h continuous_on segment[p,q] /\
     (!x x'. x IN segment[p,q] /\ x' IN segment[p,q] /\ h x = h x' ==> x = x') /\
     (!x. x IN segment[p,q]
          ==> (h x)$1 = &0 /\ (h x)$2 = &0 /\ (h w)$3 <= (h x)$3) /\
     w IN segment(p,q)
     ==> F`,
  SUBGOAL_THEN
   `!(h:real^N->real^3) p q w.
      h continuous_on segment[p,q] /\
      (!x x'. x IN segment[p,q] /\ x' IN segment[p,q] /\ h x = h x' ==> x = x') /\
      (!x. x IN segment[p,q]
           ==> (h x)$1 = &0 /\ (h x)$2 = &0 /\ (h w)$3 <= (h x)$3) /\
      w IN segment(p,q) /\ (h p)$3 <= (h q)$3
      ==> F`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "inj")
      (CONJUNCTS_THEN2 (LABEL_TAC "ray") STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `segment[w:real^N,q] SUBSET segment[p,q]` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT] THEN
      ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`IMAGE (h:real^N->real^3) (segment[w,q])`;
                   `(h:real^N->real^3) w`; `(h:real^N->real^3) q`;
                   `((h:real^N->real^3) p)$3`; `3`] CONNECTED_IVT_COMPONENT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN
        REWRITE_TAC[CONNECTED_SEGMENT] THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
        MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT];
        MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[ENDS_IN_SEGMENT];
        ARITH_TAC;
        REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
        USE_THEN "ray" (MP_TAC o SPEC `p:real^N`) THEN
        REWRITE_TAC[ENDS_IN_SEGMENT] THEN SIMP_TAC[];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[EXISTS_IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(r:real^N) IN segment[p,q]` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(h:real^N->real^3) r = h p` ASSUME_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3] THEN
      ASM_SIMP_TAC[ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `r:real^N = p` SUBST_ALL_TAC THENL
     [REMOVE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `w:real^N`]
      MOI_LCC_NOT_IN_SUBSEGMENT) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  DISJ_CASES_TAC(REAL_ARITH
   `((h:real^N->real^3) p)$3 <= (h q)$3 \/ ((h:real^N->real^3) q)$3 <= (h p)$3`)
  THENL
   [FIRST_X_ASSUM(MP_TAC o SPECL
      [`h:real^N->real^3`; `p:real^N`; `q:real^N`; `w:real^N`]) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL
      [`h:real^N->real^3`; `q:real^N`; `p:real^N`; `w:real^N`]) THEN
    SUBGOAL_THEN `segment[q:real^N,p] = segment[p,q] /\
                  segment(q:real^N,p) = segment(p,q)`
     (fun th -> REWRITE_TAC[th]) THENL [REWRITE_TAC[SEGMENT_SYM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LCC_SUBSEGMENT = prove
 (`!(a:real^N) b w u.
     w IN segment(a,b) /\ open u /\ w IN u
     ==> ?p q. w IN segment(p,q) /\ segment[p,q] SUBSET segment[a,b] /\
               segment[p,q] SUBSET u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [OPEN_CONTAINS_BALL]) THEN
  DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`a - w:real^N`; `r:real`] MOI_LCC_SMALL_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s1")))) THEN
  MP_TAC(ISPECL [`b - w:real^N`; `r:real`] MOI_LCC_SMALL_MUL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "s2")))) THEN
  SUBGOAL_THEN `(w:real^N) IN segment[a,b]` ASSUME_TAC THENL
   [ASM_MESON_TAC[SEGMENT_OPEN_SUBSET_CLOSED; SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(w:real^N) IN segment(a,b)` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `m:real`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (ASSUME_TAC o SYM))))) THEN
  MAP_EVERY EXISTS_TAC [`w + min e1 e2 % (a - w):real^N`;
                        `w + min e1 e2 % (b - w):real^N`] THEN
  SUBGOAL_THEN `&0 < min e1 e2 /\ min e1 e2 <= &1 /\
                abs(min e1 e2) <= e1 /\ abs(min e1 e2) <= e2`
  STRIP_ASSUME_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL
     [REWRITE_TAC[VECTOR_ARITH
       `w + e % (a - w) = w + e % (b - w):real^N <=> e % (a - b) = vec 0`] THEN
      ASM_SIMP_TAC[VECTOR_MUL_EQ_0; REAL_LT_IMP_NZ; VECTOR_SUB_EQ];
      EXISTS_TAC `m:real` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(&1 - m) % a + m % b = w:real^N` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_SEGMENT] THEN CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t x:real^N. x IN s /\ s SUBSET t ==> x IN t`) THENL
     [EXISTS_TAC `segment[w:real^N,a]`; EXISTS_TAC `segment[w:real^N,b]`] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC MOI_LCC_IN_SEG_PARAM THEN ASM_REAL_ARITH_TAC;
       ASM_REWRITE_TAC[SUBSET_SEGMENT; ENDS_IN_SEGMENT]]);
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(w:real^N,r)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(REWRITE_RULE[CONVEX_CONTAINS_SEGMENT] CONVEX_BALL) THEN
    REWRITE_TAC[IN_BALL; NORM_ARITH `dist(w:real^N,w + x) = norm x`] THEN
    CONJ_TAC THENL
     [REMOVE_THEN "s1" MATCH_MP_TAC; REMOVE_THEN "s2" MATCH_MP_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_LCC_BD_NOT_INTERIOR = prove
 (`!c (f:real^2->real^N) w a b.
     IMAGE f std_triangle SUBSET UNIONS c /\ moi_lt_crossing_at c f w /\
     w IN complex_boundary c /\ segment[a,b] SUBSET moi_lt_double_image f /\
     w IN segment(a,b)
     ==> F`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_crossing_at] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC
    STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^3`
    (X_CHOOSE_THEN `h':real^3->real^N` (X_CHOOSE_THEN `n1:real^2->bool`
      (X_CHOOSE_THEN `n2:real^2->bool` STRIP_ASSUME_TAC))))) THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^3) continuous_on u /\
                (!x. x IN u ==> (h':real^3->real^N) (h x) = x)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism; homeomorphism]; ALL_TAC] THEN
  UNDISCH_TAC `open_in (subtopology euclidean (UNIONS c)) (u:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN `moi_lt_double_image (f:real^2->real^N) SUBSET UNIONS c`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f:real^2->real^N) std_triangle` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[moi_lt_double_image; SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `w:real^N`; `U:real^N->bool`]
    MOI_LCC_SUBSEGMENT) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `segment[p:real^N,q] SUBSET moi_lt_double_image f INTER u`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`h:real^N->real^3`; `p:real^N`; `q:real^N`; `w:real^N`]
    MOI_LCC_RAY_NO_INTERIOR) THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^N->bool` THEN
    ASM SET_TAC[];
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[SUBSET; IN_INTER];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(h:real^N->real^3) x IN IMAGE h (moi_lt_double_image f INTER u)`
    MP_TAC THENL [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; VEC_COMPONENT] THEN SIMP_TAC[];
    FIRST_ASSUM ACCEPT_TAC]);;


(* ------------------------------------------------------------------------- *)
(* F. Unit directions of the double image: one at a boundary point, two     *)
(* elsewhere (vertices of the double image complex by its link condition,   *)
(* interior points of its edges by the crossing charts).                    *)
(* ------------------------------------------------------------------------- *)

let MOI_LCC_POINT_CASES = prove
 (`!(l:(real^N->bool)->bool) w.
     simplicial_complex l /\ (!t. t IN l ==> aff_dim t <= &1) /\ w IN UNIONS l
     ==> {w} IN l \/ ?a b. segment[a,b] IN l /\ ~(a = b) /\ w IN segment(a,b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(w:real^N) IN UNIONS l` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `n:int`] MOI_LCC_SIMPLEX_LE1) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [ASM_MESON_TAC[NOT_IN_EMPTY];
    DISJ1_TAC THEN ASM_MESON_TAC[IN_SING];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    lhs(concl th) = `t:real^N->bool`)) THEN
  SUBGOAL_THEN `(w:real^N) IN segment(a,b) \/ w = a \/ w = b`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(w:real^N) IN segment[a,b]` THEN
    REWRITE_TAC[SEGMENT_CLOSED_OPEN; IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    DISJ2_TAC THEN MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC; ALL_TAC] THEN
  DISJ1_TAC THEN FIRST_X_ASSUM SUBST1_TAC THEN
  FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [simplicial_complex]) THEN
  EXISTS_TAC `segment[a:real^N,b]` THEN
  ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

let MOI_LCC_DIRS_S_VERTEX = prove
 (`!(l:(real^N->bool)->bool) w.
     FINITE l /\ combinatorial_manifold_with_boundary 1 l /\ {w} IN l
     ==> (moi_lcc_dirs (UNIONS l) w HAS_SIZE 1 /\
          pl_ball 0 (UNIONS (simplicial_link l w))) \/
         (moi_lcc_dirs (UNIONS l) w HAS_SIZE 2 /\
          ~pl_ball 0 (UNIONS (simplicial_link l w)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LCC_LF_SC THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN l ==> aff_dim t <= &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LCC_CMWB1_DIM]; ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_sphere 0 (UNIONS (simplicial_link l (w:real^N))) \/
    pl_ball 0 (UNIONS (simplicial_link l w))`
  MP_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold_with_boundary 1 (l:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `w:real^N`] MOI_LCC_LINK_1) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `w:real^N`] MOI_LCC_DIRS_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `!n. IMAGE (\u. inv(norm(u - w)) % (u - w))
              {u | ~(u = w) /\ segment[w:real^N,u] IN l} HAS_SIZE n <=>
        {u | ~(u = w) /\ segment[w:real^N,u] IN l} HAS_SIZE n`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN MATCH_MP_TAC HAS_SIZE_IMAGE_INJ_EQ THEN
    REWRITE_TAC[IN_ELIM_THM] THEN BETA_TAC THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_LCC_DIRS_INJ THEN
    MAP_EVERY EXISTS_TAC [`l:(real^N->bool)->bool`; `w:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_LCC_PL_BALL_0; MOI_LCC_PL_SPHERE_0] THEN
  CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
   [DISJ2_TAC THEN CONJ_TAC THENL
     [MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[NOT_EXISTS_THM] THEN ASM SET_TAC[]];
    DISJ1_TAC THEN MESON_TAC[]]);;

let MOI_LCC_DIRS_S_EDGE = prove
 (`!(l:(real^N->bool)->bool) a b w.
     FINITE l /\ combinatorial_manifold_with_boundary 1 l /\
     segment[a,b] IN l /\ ~(a = b) /\ w IN segment(a,b)
     ==> moi_lcc_dirs (UNIONS l) w HAS_SIZE 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_LCC_LF_SC THEN
    ASM_MESON_TAC[combinatorial_manifold_with_boundary];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN l ==> aff_dim t <= &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_LCC_CMWB1_DIM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `a:real^N`; `b:real^N`; `w:real^N`]
    MOI_LCC_DIRS_RELINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  CONV_TAC HAS_SIZE_CONV THEN
  MAP_EVERY EXISTS_TAC [`inv(norm(b - a:real^N)) % (b - a)`;
                        `--(inv(norm(b - a:real^N)) % (b - a))`] THEN
  REWRITE_TAC[VECTOR_ARITH `x:real^N = --x <=> x = vec 0`] THEN
  REWRITE_TAC[VECTOR_MUL_EQ_0; REAL_INV_EQ_0; NORM_EQ_0; VECTOR_SUB_EQ] THEN
  ASM_MESON_TAC[]);;

let MOI_LCC_DIRS_DOUBLE = prove
 (`!c (f:real^2->real^N) w.
     moi_lt_normal_disk c f /\ w IN moi_lt_double_image f
     ==> (moi_lcc_dirs (moi_lt_double_image f) w HAS_SIZE 1 /\
          w IN complex_boundary c) \/
         (moi_lcc_dirs (moi_lt_double_image f) w HAS_SIZE 2 /\
          ~(w IN complex_boundary c))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_lt_normal_disk] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:(real^N->bool)->bool`
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
         (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "vert")))))
     (LABEL_TAC "cross"))) ASSUME_TAC) THEN
  SUBGOAL_THEN `simplicial_complex (l:(real^N->bool)->bool) /\
                (!t:real^N->bool. t IN l ==> aff_dim t <= &1)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LCC_LF_SC THEN
      ASM_MESON_TAC[combinatorial_manifold_with_boundary];
      ASM_MESON_TAC[MOI_LCC_CMWB1_DIM]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `w:real^N`] MOI_LCC_POINT_CASES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM((fun th -> SUBST1_TAC(SYM th)) o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `UNIONS(l:(real^N->bool)->bool)`)) THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `w:real^N`] MOI_LCC_DIRS_S_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    REMOVE_THEN "vert" (MP_TAC o SPEC `w:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN MESON_TAC[];
    DISJ2_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_LCC_DIRS_S_EDGE THEN
      MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[];
      DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`; `w:real^N`;
                     `a:real^N`; `b:real^N`] MOI_LCC_BD_NOT_INTERIOR) THEN
      REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[moi_lt_singular_disk];
        REMOVE_THEN "cross" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM((fun th -> SUBST1_TAC(SYM th)) o check (fun th ->
          is_eq(concl th) &&
          lhs(concl th) = `UNIONS(l:(real^N->bool)->bool)`)) THEN
        ASM SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC]]]);;


(* ------------------------------------------------------------------------- *)
(* S. The vertex count and the main theorem.                                *)
(* ------------------------------------------------------------------------- *)

let MOI_LCC_SRC_VERTEX = prove
 (`!c (f:real^2->real^N) s0 v.
     moi_lt_normal_disk c f /\ simplicial_complex s0 /\
     UNIONS s0 = {x | x IN std_triangle /\ f x IN moi_lt_double_image f} /\
     (!t. t IN s0 ==> aff_dim t <= &1 /\ t SUBSET std_triangle /\
                      ?l y. linear l /\ !z. z IN t ==> f z = l z + y) /\
     {v} IN s0
     ==> (UNIONS (simplicial_link s0 v) HAS_SIZE 1 /\
          v IN relative_frontier std_triangle) \/
         (UNIONS (simplicial_link s0 v) HAS_SIZE 2 /\
          ~(v IN relative_frontier std_triangle))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_lt_singular_disk c (f:real^2->real^N)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_lt_normal_disk]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^2) IN std_triangle /\
                (f:real^2->real^N) v IN moi_lt_double_image f`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(v:real^2) IN UNIONS s0` MP_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^2}` THEN
      ASM_REWRITE_TAC[IN_SING];
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^2) IN relative_frontier std_triangle <=>
                (f:real^2->real^N) v IN complex_boundary c`
  SUBST1_TAC THENL
   [UNDISCH_TAC `moi_lt_singular_disk c (f:real^2->real^N)` THEN
    REWRITE_TAC[moi_lt_singular_disk] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s0:(real^2->bool)->bool`; `v:real^2`] MOI_LCC_LINK_1) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
    `s0:(real^2->bool)->bool`; `v:real^2`] MOI_LCC_SRC_DEG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
  MATCH_MP_TAC MOI_LCC_DIRS_DOUBLE THEN ASM_REWRITE_TAC[]);;

let SOURCE_STRUCTURE = prove
 (MOI_LT_SOURCE_STRUCTURE,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_lt_normal_disk]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `l:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MP_TAC(SPECL [`c:(real^N->bool)->bool`; `f:real^2->real^N`;
                `l:(real^N->bool)->bool`] MOI_LCC_SOURCE_COMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN X_GEN_TAC `e:real^N->bool` THEN DISCH_TAC THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `?n. n simplex (e:real^N->bool)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[combinatorial_manifold_with_boundary;
                      lf_simplicial_complex];
        ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]];
      ASM_MESON_TAC[MOI_LCC_CMWB1_DIM]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:(real^2->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `s0:(real^2->bool)->bool` THEN
  SUBGOAL_THEN
   `!v. {v} IN s0
        ==> (UNIONS (simplicial_link s0 v) HAS_SIZE 1 /\
             v IN relative_frontier std_triangle) \/
            (UNIONS (simplicial_link s0 v) HAS_SIZE 2 /\
             ~(v IN relative_frontier std_triangle))`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_LCC_SRC_VERTEX THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `f:real^2->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_complex];
    REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_SIMP_TAC[MOI_LCC_SC_LF] THEN
    REWRITE_TAC[MOI_LCC_PL_BALL_0; MOI_LCC_PL_SPHERE_0] THEN
    X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^2`) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN MESON_TAC[];
    X_GEN_TAC `v:real^2` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `v:real^2`) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[MOI_LCC_PL_BALL_0] THEN
    CONV_TAC(ONCE_DEPTH_CONV HAS_SIZE_CONV) THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [MESON_TAC[];
      REWRITE_TAC[NOT_EXISTS_THM] THEN ASM SET_TAC[]]]);;


