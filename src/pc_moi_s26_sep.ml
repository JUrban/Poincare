needs "src/pc_moi_s26_local.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s26_sep: Moise Sec 26 Theorem 6 (MOISE_266, p.194).              *)
(* A connected closed combinatorial 2-manifold c in real^3 separates real^3 *)
(* into exactly two components, a bounded one and the outside, each with    *)
(* frontier |c|.  Route: every component has frontier |c| (the local sides  *)
(* LOCAL_TRI and LOCAL_EDGE, edges in exactly two triangles MOI_FSA_CM_EDGE2 *)
(* and dual connectivity MOI_FSA_ABS_DCONN, after a seed triangle found via *)
(* CONNECTED_OPEN_IN_DIFF_UNIONS_LOWDIM); at least two components, since a  *)
(* chain of segments joining the ends of a short transversal segment would *)
(* close up to a polygon crossing |c| once (EVEN_CROSSING); at most two, as *)
(* each component contains one of the two local sides at a fixed point.     *)
(* Main theorem: SEP_266 : |- MOI_S26_SEP.                                  *)
(* ========================================================================= *)

(* Two points of an open connected set of real^3 are joined by a chain of *)
(* segments in the set with consecutive vertices distinct.                 *)

let MOI_S6S_CHAIN = prove
 (`!s:real^3->bool a b.
     open s /\ connected s /\ a IN s /\ b IN s
     ==> ?(p:num->real^3) n.
           p 0 = a /\ p n = b /\
           (!i. i < n ==> ~(p i = p (SUC i)) /\ segment[p i,p (SUC i)] SUBSET s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL
   [`\x y:real^3. ?(p:num->real^3) n.
        p 0 = x /\ p n = y /\
        (!i. i < n ==> ~(p i = p (SUC i)) /\ segment[p i,p (SUC i)] SUBSET s)`;
    `s:real^3->bool`] CONNECTED_EQUIVALENCE_RELATION) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:num->real^3` (X_CHOOSE_THEN `n:num`
        STRIP_ASSUME_TAC)) THEN
      EXISTS_TAC `\i. (p:num->real^3) (n - i)` THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[SUB_0; SUB_REFL] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `n - SUC i`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `SUC (n - SUC i) = n - i` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `segment[(p:num->real^3) (n - i),p (n - SUC i)] =
                    segment[p (n - SUC i),p (n - i)]` SUBST1_TAC THENL
       [MATCH_ACCEPT_TAC (CONJUNCT1 SEGMENT_SYM); MESON_TAC[]];
      MAP_EVERY X_GEN_TAC [`x:real^3`; `y:real^3`; `z:real^3`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `p:num->real^3` (X_CHOOSE_THEN `n:num` STRIP_ASSUME_TAC))
        (X_CHOOSE_THEN `q:num->real^3` (X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC))) THEN
      EXISTS_TAC `\i. if i <= n then (p:num->real^3) i else q (i - n)` THEN
      EXISTS_TAC `n + m:num` THEN REWRITE_TAC[LE_0] THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [ASM_CASES_TAC `m = 0` THENL
         [UNDISCH_TAC `(q:num->real^3) m = z` THEN
          ASM_REWRITE_TAC[ADD_CLAUSES; LE_REFL] THEN MESON_TAC[];
          ASM_SIMP_TAC[ARITH_RULE `~(m = 0) ==> ~(n + m <= n)`; ADD_SUB2]];
        ALL_TAC] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i:num < n` THENL
       [ASM_SIMP_TAC[LT_IMP_LE; ARITH_RULE `i < n ==> SUC i <= n`];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `(if i <= n then (p:num->real^3) i else q (i - n)) = q (i - n) /\
        (if SUC i <= n then p (SUC i) else q (SUC i - n)) = q (SUC (i - n))`
      (CONJUNCTS_THEN SUBST1_TAC) THENL
       [CONJ_TAC THENL
         [COND_CASES_TAC THENL
           [SUBGOAL_THEN `i:num = n` SUBST1_TAC THENL
             [ASM_ARITH_TAC; ASM_REWRITE_TAC[SUB_REFL]];
            REFL_TAC];
          SUBGOAL_THEN `~(SUC i <= n) /\ SUC i - n = SUC (i - n)`
          (fun th -> REWRITE_TAC[th]) THEN ASM_ARITH_TAC];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC];
      X_GEN_TAC `a0:real^3` THEN DISCH_TAC THEN
      UNDISCH_TAC `open(s:real^3->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
      DISCH_THEN(MP_TAC o SPEC `a0:real^3`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `ball(a0:real^3,e)` THEN
      ASM_SIMP_TAC[OPEN_SUBSET; OPEN_BALL; CENTRE_IN_BALL] THEN
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      ASM_CASES_TAC `x:real^3 = a0` THENL
       [EXISTS_TAC `\i:num. (a0:real^3)` THEN EXISTS_TAC `0` THEN
        ASM_REWRITE_TAC[LT];
        EXISTS_TAC `\i:num. if i = 0 then (a0:real^3) else x` THEN EXISTS_TAC `1` THEN
        REWRITE_TAC[ARITH_RULE `i < 1 <=> i = 0`; ARITH_EQ; NOT_SUC] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        X_GEN_TAC `i:num` THEN DISCH_THEN SUBST1_TAC THEN
        REWRITE_TAC[ARITH_EQ; NOT_SUC] THEN
        CONV_TAC NUM_REDUCE_CONV THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(a0:real^3,e)` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
        ASM_REWRITE_TAC[CONVEX_BALL; CENTRE_IN_BALL]]];
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* Components of the complement of a closed set: open, connected, missing *)
(* the set, with frontier inside the set.                                   *)

let MOI_S6S_COMP_BASIC = prove
 (`!(k:real^3->bool) u.
     closed k /\ u IN components((:real^3) DIFF k)
     ==> open u /\ connected u /\ ~(u = {}) /\ u INTER k = {} /\
         frontier u SUBSET k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_COMPONENTS THEN EXISTS_TAC `(:real^3) DIFF k` THEN
    ASM_REWRITE_TAC[GSYM closed];
    ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
    ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
    FIRST_ASSUM(MP_TAC o MATCH_MP IN_COMPONENTS_SUBSET) THEN SET_TAC[];
    FIRST_ASSUM(MP_TAC o MATCH_MP FRONTIER_OF_COMPONENTS_SUBSET) THEN
    REWRITE_TAC[FRONTIER_COMPLEMENT] THEN
    MP_TAC(ISPEC `k:real^3->bool` FRONTIER_SUBSET_CLOSED) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

(* The local sides argument: if near y in the frontier of a component u the *)
(* set k is a sheet s0 whose complement in the ball has two connected sides *)
(* each accumulating on the sheet, the whole local sheet is in frontier u.  *)

let MOI_S6S_SIDES_FRONTIER = prove
 (`!(k:real^3->bool) u y r s0 a b.
     closed k /\ u IN components((:real^3) DIFF k) /\ y IN frontier u /\ &0 < r /\
     ball(y,r) INTER k = ball(y,r) INTER s0 /\
     connected a /\ connected b /\ a UNION b = ball(y,r) DIFF s0 /\
     ball(y,r) INTER s0 SUBSET closure a INTER closure b
     ==> ball(y,r) INTER k SUBSET frontier u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `u:real^3->bool`] MOI_S6S_COMP_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(ball(y:real^3,r) INTER u = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(y:real^3,r)`; `u:real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    UNDISCH_TAC `(y:real^3) IN frontier u` THEN REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3->bool) SUBSET (:real^3) DIFF k /\
                (b:real^3->bool) SUBSET (:real^3) DIFF k`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`ball(y:real^3,r) INTER k = ball(y,r) INTER s0`;
      `(a:real^3->bool) UNION b = ball(y,r) DIFF s0`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3->bool) SUBSET u \/ (b:real^3->bool) SUBSET u`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(u INTER (a:real^3->bool) = {}) \/ ~(u INTER (b:real^3->bool) = {})`
    STRIP_ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`~(ball(y:real^3,r) INTER u = {})`;
        `ball(y:real^3,r) INTER k = ball(y,r) INTER s0`;
        `(a:real^3->bool) UNION b = ball(y,r) DIFF s0`;
        `u INTER (k:real^3->bool) = {}`] THEN SET_TAC[];
      DISJ1_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
      EXISTS_TAC `(:real^3) DIFF k` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
      EXISTS_TAC `(:real^3) DIFF k` THEN ASM_REWRITE_TAC[]];
    ALL_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[frontier; INTERIOR_OPEN] THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP SUBSET_CLOSURE) THEN
  MAP_EVERY UNDISCH_TAC
   [`ball(y:real^3,r) INTER k = ball(y,r) INTER s0`;
    `ball(y:real^3,r) INTER s0 SUBSET closure a INTER closure b`;
    `u INTER (k:real^3->bool) = {}`] THEN
  SET_TAC[]);;

(* A component with y in its frontier contains one of the two local sides. *)

let MOI_S6S_SIDE_IN_COMP = prove
 (`!(k:real^3->bool) u y r s0 a b.
     closed k /\ u IN components((:real^3) DIFF k) /\ y IN frontier u /\ &0 < r /\
     ball(y,r) INTER k = ball(y,r) INTER s0 /\
     connected a /\ connected b /\ a UNION b = ball(y,r) DIFF s0
     ==> a SUBSET u \/ b SUBSET u`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `u:real^3->bool`] MOI_S6S_COMP_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(ball(y:real^3,r) INTER u = {})` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`ball(y:real^3,r)`; `u:real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    REWRITE_TAC[OPEN_BALL] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN
    UNDISCH_TAC `(y:real^3) IN frontier u` THEN REWRITE_TAC[frontier] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^3->bool) SUBSET (:real^3) DIFF k /\
                (b:real^3->bool) SUBSET (:real^3) DIFF k`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`ball(y:real^3,r) INTER k = ball(y,r) INTER s0`;
      `(a:real^3->bool) UNION b = ball(y,r) DIFF s0`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(u INTER (a:real^3->bool) = {}) \/ ~(u INTER (b:real^3->bool) = {})`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`~(ball(y:real^3,r) INTER u = {})`;
      `ball(y:real^3,r) INTER k = ball(y,r) INTER s0`;
      `(a:real^3->bool) UNION b = ball(y,r) DIFF s0`;
      `u INTER (k:real^3->bool) = {}`] THEN SET_TAC[];
    DISJ1_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `(:real^3) DIFF k` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `(:real^3) DIFF k` THEN ASM_REWRITE_TAC[]]);;

(* The polyhedron of a finite complex of simplices is closed.              *)

let MOI_S6S_UNIONS_CLOSED = prove
 (`!(c:(real^3->bool)->bool). simplicial_complex c ==> closed (UNIONS c) /\ compact (UNIONS c)`,
  REWRITE_TAC[simplicial_complex] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS; MATCH_MP_TAC COMPACT_UNIONS] THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_COMPACT]);;

(* If the frontier of a component meets the relative interior of a        *)
(* triangle, it contains the triangle.                                      *)

let MOI_S6S_TRI_FRONTIER = prove
 (`!(c:(real^3->bool)->bool) u q.
     simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     u IN components((:real^3) DIFF UNIONS c) /\ q IN c /\ aff_dim q = &2 /\
     ~(relative_interior q INTER frontier u = {})
     ==> q SUBSET frontier u`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6S_UNIONS_CLOSED) THEN
  SUBGOAL_THEN `convex (q:real^3->bool) /\ closed q` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^3. y IN relative_interior q /\ y IN frontier u
       ==> ?r. &0 < r /\ ball(y,r) INTER UNIONS c SUBSET frontier u`
  (LABEL_TAC "loc") THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`; `y:real^3`]
      LOCAL_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r0:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `a:real^3->bool`
      (X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `r0:real` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S6S_SIDES_FRONTIER THEN
    MAP_EVERY EXISTS_TAC [`affine hull q:real^3->bool`; `a:real^3->bool`;
                          `b:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior q SUBSET frontier (u:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `relative_interior q:real^3->bool` CONNECTED_CLOPEN) THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR] THEN
    DISCH_THEN(MP_TAC o SPEC `relative_interior q INTER frontier (u:real^3->bool)`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [REWRITE_TAC[OPEN_IN_CONTAINS_BALL; INTER_SUBSET] THEN
        X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
        USE_THEN "loc" (fun th -> MP_TAC(MATCH_MP th
          (CONJ (ASSUME `(y:real^3) IN relative_interior q`)
                (ASSUME `(y:real^3) IN frontier u`)))) THEN
        MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
        ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPEC `q:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
        UNDISCH_TAC `ball(y:real^3,r) INTER UNIONS c SUBSET frontier u` THEN
        UNDISCH_TAC `(q:real^3->bool) IN c` THEN SET_TAC[];
        MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN REWRITE_TAC[FRONTIER_CLOSED]];
      UNDISCH_TAC `~(relative_interior q INTER frontier (u:real^3->bool) = {})` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `q = closure(relative_interior q:real^3->bool)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
  MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[FRONTIER_CLOSED]);;

(* The frontier of a component passes from a triangle to the other         *)
(* triangle at each of its edges.                                           *)

let MOI_S6S_EDGE_FRONTIER = prove
 (`!(c:(real^3->bool)->bool) u e q q'.
     FINITE c /\ combinatorial_manifold 2 c /\
     u IN components((:real^3) DIFF UNIONS c) /\
     e IN c /\ aff_dim e = &1 /\ q IN c /\ aff_dim q = &2 /\ e SUBSET q /\
     q' IN c /\ aff_dim q' = &2 /\ e SUBSET q' /\ q SUBSET frontier u
     ==> q' SUBSET frontier u`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `q':real^3->bool = q` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool) /\
                (!s:real^3->bool. s IN c ==> aff_dim s <= &2)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC; MOI_FSA_CM_DIM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6S_UNIONS_CLOSED) THEN
  SUBGOAL_THEN `{t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = {q,q':real^3->bool}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSA_PAIR THEN ASM_REWRITE_TAC[IN_ELIM_THM; HAS_SIZE] THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[FINITE_RESTRICT]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FSA_CM_EDGE2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (e:real^3->bool) /\ convex (q':real^3->bool) /\ closed q'`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^3. y IN relative_interior e` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN
    DISCH_TAC THEN UNDISCH_TAC `aff_dim (e:real^3->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN e` ASSUME_TAC THENL
   [MP_TAC(ISPEC `e:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `e:real^3->bool`; `q:real^3->bool`;
                 `q':real^3->bool`; `y:real^3`] LOCAL_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r0:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `a:real^3->bool`
    (X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `ball(y:real^3,r0) INTER UNIONS c SUBSET frontier u` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S6S_SIDES_FRONTIER THEN
    MAP_EVERY EXISTS_TAC [`q UNION q':real^3->bool`; `a:real^3->bool`;
                          `b:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S6S_TRI_FRONTIER THEN
  EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(ball(y:real^3,r0) INTER relative_interior q' = {})` MP_TAC THENL
   [MP_TAC(ISPECL [`ball(y:real^3,r0)`; `relative_interior q':real^3->bool`]
      OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
    ASM_SIMP_TAC[OPEN_BALL; CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^3` THEN
    ASM_REWRITE_TAC[CENTRE_IN_BALL] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `q':real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC `ball(y:real^3,r0) INTER UNIONS c SUBSET frontier u` THEN
  UNDISCH_TAC `(q':real^3->bool) IN c` THEN SET_TAC[]);;

(* The frontier of a component meets the relative interior of some         *)
(* triangle: otherwise it lies in the union of the simplices of dimension *)
(* at most 1, whose complement is connected, and the component would be    *)
(* that whole complement.                                                   *)

let MOI_S6S_SEED = prove
 (`!(c:(real^3->bool)->bool) u.
     FINITE c /\ combinatorial_manifold 2 c /\ ~(UNIONS c = {}) /\
     u IN components((:real^3) DIFF UNIONS c)
     ==> ?q. q IN c /\ aff_dim q = &2 /\
             ~(relative_interior q INTER frontier u = {})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool) /\
                (!s:real^3->bool. s IN c ==> aff_dim s <= &2)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC; MOI_FSA_CM_DIM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6S_UNIONS_CLOSED) THEN
  MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `u:real^3->bool`] MOI_S6S_COMP_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?q0:real^3->bool. q0 IN c /\ aff_dim q0 = &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(UNIONS c:real^3->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `s:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_CM_PURE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `?q:real^3->bool. q IN c /\ aff_dim q = &2 /\
                                  ~(relative_interior q INTER frontier u = {})` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(LABEL_TAC "neg" o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  ABBREV_TAC `lo = {s:real^3->bool | s IN c /\ aff_dim s <= &1}` THEN
  SUBGOAL_THEN `frontier u SUBSET UNIONS (lo:(real^3->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^3) IN UNIONS c` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `aff_dim (s:real^3->bool) <= &1` THENL
     [EXPAND_TAC "lo" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim (s:real^3->bool) = &2` ASSUME_TAC THENL
     [SUBGOAL_THEN `aff_dim (s:real^3->bool) <= &2` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM_INT_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((x:real^3) IN relative_interior s)` ASSUME_TAC THENL
     [DISCH_TAC THEN USE_THEN "neg" (MP_TAC o SPEC `s:real^3->bool`) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN relative_frontier s` MP_TAC THENL
     [REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `s:real^3->bool` CLOSURE_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `s:real^3->bool`] MOI_S6X_SC_RELBD_TRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXPAND_TAC "lo" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[INT_LE_REFL];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS lo SUBSET UNIONS (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "lo" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `connected ((:real^3) DIFF UNIONS lo)` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_OPEN_IN_DIFF_UNIONS_LOWDIM THEN
    REWRITE_TAC[CONNECTED_UNIV; AFFINE_HULL_UNIV; OPEN_IN_REFL; AFF_DIM_UNIV;
                DIMINDEX_3] THEN
    EXPAND_TAC "lo" THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN
    REPEAT STRIP_TAC THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `u SUBSET (:real^3) DIFF UNIONS lo` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`u INTER UNIONS c:real^3->bool = {}`;
      `UNIONS lo SUBSET UNIONS (c:(real^3->bool)->bool)`] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `u = (:real^3) DIFF UNIONS lo` ASSUME_TAC THENL
   [MP_TAC(ISPEC `(:real^3) DIFF UNIONS lo` CONNECTED_CLOPEN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `u:real^3->bool`) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `u = ((:real^3) DIFF UNIONS lo) INTER closure u`
        SUBST1_TAC THENL
         [MP_TAC(ISPEC `u:real^3->bool` CLOSURE_UNION_FRONTIER) THEN
          MAP_EVERY UNDISCH_TAC
           [`u SUBSET (:real^3) DIFF UNIONS lo`;
            `frontier u SUBSET UNIONS (lo:(real^3->bool)->bool)`] THEN
          SET_TAC[];
          MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN REWRITE_TAC[CLOSED_CLOSURE]]];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^3. z IN relative_interior q0` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `convex (q0:real^3->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim (q0:real^3->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((z:real^3) IN UNIONS lo)` ASSUME_TAC THENL
   [EXPAND_TAC "lo" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q0:real^3->bool`; `z:real^3`;
                   `s:real^3->bool`] MOI_S6L_STAR_TRI) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim (s:real^3->bool) <= &1` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPEC `q0:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
  MAP_EVERY UNDISCH_TAC
   [`(z:real^3) IN relative_interior q0`; `~((z:real^3) IN UNIONS lo)`;
    `u = (:real^3) DIFF UNIONS lo`; `u INTER UNIONS c:real^3->bool = {}`;
    `(q0:real^3->bool) IN c`] THEN
  SET_TAC[]);;

(* Every component of the complement of a connected closed combinatorial   *)
(* 2-manifold in real^3 has the whole polyhedron as frontier: the frontier *)
(* contains one triangle (SEED), passes across edges (EDGE_FRONTIER) and so *)
(* contains every triangle by dual connectivity, hence every simplex.      *)

let MOI_S6S_FRONTIER_EQ = prove
 (`!(c:(real^3->bool)->bool) u.
     FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c) /\
     ~(UNIONS c = {}) /\ u IN components((:real^3) DIFF UNIONS c)
     ==> frontier u = UNIONS c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool) /\
                (!s:real^3->bool. s IN c ==> aff_dim s <= &2)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC; MOI_FSA_CM_DIM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6S_UNIONS_CLOSED) THEN
  MP_TAC(ISPECL [`UNIONS c:real^3->bool`; `u:real^3->bool`] MOI_S6S_COMP_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t:real^3->bool. t IN c /\ aff_dim t = &2 ==> t SUBSET frontier u`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `c:(real^3->bool)->bool` MOI_FSA_ABS_DCONN) THEN
    ASM_REWRITE_TAC[moi_fsa_dconn; MOI_FSA_ABS_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC
      `{moi_fsa_vs t | t IN c /\ aff_dim t = &2 /\ t SUBSET frontier (u:real^3->bool)}`) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_IMAGE; IN_ELIM_THM] THEN MESON_TAC[];
        MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `u:real^3->bool`] MOI_S6S_SEED) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(X_CHOOSE_THEN `q0:real^3->bool` STRIP_ASSUME_TAC) THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
        EXISTS_TAC `moi_fsa_vs (q0:real^3->bool)` THEN
        EXISTS_TAC `q0:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MOI_S6S_TRI_FRONTIER THEN
        EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
        MAP_EVERY X_GEN_TAC [`t1:real^3->bool`; `t2:real^3->bool`; `e:real^3->bool`] THEN
        REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
        DISCH_THEN(CONJUNCTS_THEN2
          (X_CHOOSE_THEN `T1:real^3->bool` STRIP_ASSUME_TAC)
          (CONJUNCTS_THEN2 (X_CHOOSE_THEN `T2:real^3->bool` STRIP_ASSUME_TAC)
            STRIP_ASSUME_TAC)) THEN
        EXISTS_TAC `T2:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(e:real^3->bool) SUBSET moi_fsa_vs T1 /\ e SUBSET moi_fsa_vs T2`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `T1:real^3->bool`] MOI_FSA_VS) THEN
        MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `T2:real^3->bool`] MOI_FSA_VS) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
        DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
        SUBGOAL_THEN `convex hull (e:real^3->bool) IN c /\
                      moi_fsa_vs (convex hull e) = e`
        STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC MOI_S6S_EDGE_FRONTIER THEN
        MAP_EVERY EXISTS_TAC [`c:(real^3->bool)->bool`; `convex hull e:real^3->bool`;
                              `T1:real^3->bool`] THEN
        ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
         [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `convex hull e:real^3->bool`]
            MOI_FSA_VS) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(e:real^3->bool) HAS_SIZE 2` THEN SIMP_TAC[HAS_SIZE] THEN
          REPEAT STRIP_TAC THEN ASM_INT_ARITH_TAC;
          MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `T1:real^3->bool`] MOI_FSA_VS) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [CONJUNCT1(CONJUNCT2 th)]) THEN
          MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[];
          MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `T2:real^3->bool`] MOI_FSA_VS) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [CONJUNCT1(CONJUNCT2 th)]) THEN
          MATCH_MP_TAC HULL_MONO THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    DISCH_TAC THEN X_GEN_TAC `t:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `moi_fsa_vs (t:real^3->bool) IN
      {moi_fsa_vs t | t IN c /\ aff_dim t = &2 /\ t SUBSET frontier u}`
    MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t':real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `t:real^3->bool = t'` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOI_FSA_VS_INJ THEN EXISTS_TAC `c:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `x:real^3` THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_CM_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(t:real^3->bool) SUBSET frontier u` MP_TAC THENL
   [ASM_MESON_TAC[]; ASM SET_TAC[]]);;

(* A scalar of size at most 1 times t, for t > 0.                          *)

let MOI_S6S_ABS_MUL_LE = prove
 (`!a t. abs a <= &1 /\ &0 < t ==> abs(a * t) <= t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_ABS_MUL] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN EXISTS_TAC `&1 * abs t` THEN CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[REAL_ABS_POS];
    ASM_REAL_ARITH_TAC]);;

(* A short segment through a relative interior point y of a triangle,     *)
(* normal to its plane: its ends miss the polyhedron, it meets the         *)
(* polyhedron only at y, and it is in general position with every simplex. *)

let MOI_S6S_TRANSVERSAL = prove
 (`!(c:(real^3->bool)->bool) q y.
     FINITE c /\ combinatorial_manifold 2 c /\ q IN c /\ aff_dim q = &2 /\
     y IN relative_interior q
     ==> ?P0 Q0. ~(P0 IN UNIONS c) /\ ~(Q0 IN UNIONS c) /\ ~(P0 = Q0) /\
                 (!x. x IN segment[Q0,P0] /\ x IN UNIONS c <=> x = y) /\
                 (!s. s IN c ==> affine_gp_3 (segment[Q0,P0]) s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool) /\
                (!s:real^3->bool. s IN c ==> aff_dim s <= &2)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC; MOI_FSA_CM_DIM]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN q /\ y IN affine hull q /\ y IN UNIONS c`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `q:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `q:real^3->bool`] HULL_SUBSET) THEN
    UNDISCH_TAC `(q:real^3->bool) IN c` THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior q` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`; `y:real^3`] LOCAL_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r0:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(ASSUME_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`q:real^3->bool`; `y:real^3`] MOI_S6L_PLANE_THROUGH) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `n:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `!x. x IN ball(y:real^3,r0) ==> (x IN UNIONS c <=> n dot (x - y) = &0)`
  (LABEL_TAC "kb") THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `ball(y:real^3,r0) INTER UNIONS c = ball(y,r0) INTER affine hull q` THEN
    ASM_REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `t = r0 / (&2 * norm(n:real^3))` THEN
  SUBGOAL_THEN `&0 < norm(n:real^3) /\ &0 < n dot n` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; DOT_POS_LT]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < t /\ t * norm(n:real^3) < r0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "t" THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      ASM_SIMP_TAC[REAL_FIELD `&0 < m ==> r / (&2 * m) * m = r / &2`] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `!k. abs k <= t ==> y + k % n IN ball(y:real^3,r0)` (LABEL_TAC "inb")
  THENL
   [X_GEN_TAC `k:real` THEN DISCH_TAC THEN
    REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `y - (y + k % n):real^3 = --(k % n)`;
                NORM_NEG; NORM_MUL] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `t * norm(n:real^3)` THEN
    ASM_SIMP_TAC[REAL_LE_RMUL; NORM_POS_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!k. abs k <= t ==> ((y:real^3) + k % n IN UNIONS c <=> k = &0)` (LABEL_TAC "kk") THENL
   [X_GEN_TAC `k:real` THEN DISCH_TAC THEN
    USE_THEN "kb" (fun th -> USE_THEN "inb" (fun th' ->
      REWRITE_TAC[MATCH_MP th (MATCH_MP th' (ASSUME `abs k <= t`))])) THEN
    REWRITE_TAC[VECTOR_ARITH `(y + k % n) - y:real^3 = k % n`; DOT_RMUL;
                REAL_ENTIRE] THEN
    ASM_SIMP_TAC[REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  EXISTS_TAC `y + t % n:real^3` THEN EXISTS_TAC `y + (--t) % n:real^3` THEN
  SUBGOAL_THEN
   `!x. x IN segment[y + (--t) % n,y + t % n] <=>
        ?l. &0 <= l /\ l <= &1 /\ x = y + ((&2 * l - &1) * t) % n:real^3`
  (LABEL_TAC "seg") THENL
   [GEN_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
    AP_TERM_TAC THEN ABS_TAC THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    AP_TERM_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [USE_THEN "kk" (MP_TAC o SPEC `t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    USE_THEN "kk" (MP_TAC o SPEC `--t:real`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VECTOR_ARITH `y + t % n:real^3 = y + (--t) % n <=> (&2 * t) % n = vec 0`;
                VECTOR_MUL_EQ_0] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    X_GEN_TAC `x:real^3` THEN USE_THEN "seg" (fun th -> REWRITE_TAC[th]) THEN
    EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "kk" (MP_TAC o SPEC `(&2 * l - &1) * t`) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC MOI_S6S_ABS_MUL_LE THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `&1 / &2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
      VECTOR_ARITH_TAC];
    X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^3) IN s` THENL
     [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`; `y:real^3`;
                     `s:real^3->bool`] MOI_S6L_STAR_TRI) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[affine_gp_3] THEN DISJ2_TAC THEN
      REWRITE_TAC[AFF_DIM_SEGMENT; AFFINE_HULL_SEGMENT] THEN
      REWRITE_TAC[VECTOR_ARITH `y + (--t) % n:real^3 = y + t % n <=> (&2 * t) % n = vec 0`;
                  VECTOR_MUL_EQ_0] THEN
      ASM_REWRITE_TAC[REAL_ARITH `&2 * t = &0 <=> t = &0`] THEN
      ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN CONV_TAC INT_REDUCE_CONV THEN
      SUBGOAL_THEN
       `affine hull {y + (--t) % n,y + t % n} INTER {x:real^3 | n dot (x - y) = &0} =
        {y}` SUBST1_TAC THENL
       [REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; IN_SING; AFFINE_HULL_2] THEN
        X_GEN_TAC `x:real^3` THEN EQ_TAC THENL
         [DISCH_THEN(CONJUNCTS_THEN2
            (X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real` STRIP_ASSUME_TAC))
            MP_TAC) THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `a % (y + --t % n) + b % (y + t % n) =
                        y + ((b - a) * t) % n:real^3` SUBST1_TAC THENL
           [UNDISCH_TAC `a + b = &1` THEN
            REWRITE_TAC[REAL_ARITH `a + b = &1 <=> a = &1 - b`] THEN
            DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC;
            ALL_TAC] THEN
          REWRITE_TAC[VECTOR_ARITH `(y + k % n) - y:real^3 = k % n`; DOT_RMUL;
                      REAL_ENTIRE] THEN
          ASM_SIMP_TAC[REAL_LT_IMP_NZ] THEN DISCH_THEN SUBST1_TAC THEN
          VECTOR_ARITH_TAC;
          DISCH_THEN SUBST1_TAC THEN
          REWRITE_TAC[VECTOR_SUB_REFL; DOT_RZERO] THEN
          MAP_EVERY EXISTS_TAC [`&1 / &2`; `&1 / &2`] THEN
          CONV_TAC REAL_RAT_REDUCE_CONV THEN VECTOR_ARITH_TAC];
        REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC];
      REWRITE_TAC[affine_gp_3] THEN DISJ1_TAC THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN
      SUBGOAL_THEN `x:real^3 = y` (fun th -> ASM_MESON_TAC[th]) THEN
      SUBGOAL_THEN `(x:real^3) IN UNIONS c` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(x:real^3) IN segment[y + (--t) % n,y + t % n]` THEN
      USE_THEN "seg" (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN(X_CHOOSE_THEN `l:real` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(x:real^3) IN UNIONS c` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "kk" (MP_TAC o SPEC `(&2 * l - &1) * t`) THEN
      ANTS_TAC THENL
       [MATCH_MP_TAC MOI_S6S_ABS_MUL_LE THEN ASM_REAL_ARITH_TAC;
        DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN VECTOR_ARITH_TAC]]]);;

(* At least two components: the two ends of the transversal segment lie in *)
(* different components, since otherwise a chain from one end to the other *)
(* closed by the segment would be a polygon crossing the polyhedron once,  *)
(* against the even crossing lemma.                                         *)

let MOI_S6S_TWO = prove
 (`!(c:(real^3->bool)->bool).
     FINITE c /\ combinatorial_manifold 2 c /\ ~(UNIONS c = {})
     ==> ?P0 Q0. ~(P0 IN UNIONS c) /\ ~(Q0 IN UNIONS c) /\
                 ~(connected_component ((:real^3) DIFF UNIONS c) P0 =
                   connected_component ((:real^3) DIFF UNIONS c) Q0)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool) /\
                (!s:real^3->bool. s IN c ==> aff_dim s <= &2)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC; MOI_FSA_CM_DIM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6S_UNIONS_CLOSED) THEN
  SUBGOAL_THEN `?q:real^3->bool. q IN c /\ aff_dim q = &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(UNIONS c:real^3->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `s:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_CM_PURE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^3. y IN relative_interior q` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `convex (q:real^3->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim (q:real^3->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`; `y:real^3`]
    MOI_S6S_TRANSVERSAL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P0:real^3` (X_CHOOSE_THEN `Q0:real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "cr")
        (LABEL_TAC "gp"))))))) THEN
  MAP_EVERY EXISTS_TAC [`P0:real^3`; `Q0:real^3`] THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(Q0:real^3) IN connected_component ((:real^3) DIFF UNIONS c) P0`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
    ALL_TAC] THEN
  UNDISCH_THEN
   `connected_component ((:real^3) DIFF UNIONS c) P0 =
    connected_component ((:real^3) DIFF UNIONS c) Q0` (K ALL_TAC) THEN
  ABBREV_TAC `u = connected_component ((:real^3) DIFF UNIONS c) P0` THEN
  SUBGOAL_THEN `open (u:real^3->bool) /\ connected u /\ (P0:real^3) IN u /\
                u INTER UNIONS c = {}` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_CONNECTED_COMPONENT THEN ASM_REWRITE_TAC[GSYM closed];
      REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT];
      REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
      MP_TAC(ISPECL [`(:real^3) DIFF UNIONS c`; `P0:real^3`]
        CONNECTED_COMPONENT_SUBSET) THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`u:real^3->bool`; `P0:real^3`; `Q0:real^3`] MOI_S6S_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num->real^3` (X_CHOOSE_THEN `m:num`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ch"))))) THEN
  SUBGOAL_THEN
   `!i. i < SUC m
        ==> ~((if i <= m then (p:num->real^3) i else P0) =
              (if SUC i <= m then p (SUC i) else P0)) /\
            ~((if i <= m then p i else P0) IN UNIONS c) /\
            (!s. s IN c
                 ==> affine_gp_3 (segment[(if i <= m then p i else P0),
                                          (if SUC i <= m then p (SUC i) else P0)]) s) /\
            (!x. x IN segment[(if i <= m then p i else P0),
                              (if SUC i <= m then p (SUC i) else P0)] /\
                 x IN UNIONS c <=> i = m /\ x = y)`
  (LABEL_TAC "idx") THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN ASM_CASES_TAC `i:num = m` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      REWRITE_TAC[LE_REFL; ARITH_RULE `~(SUC m <= m)`] THEN
      ASM_REWRITE_TAC[];
      SUBGOAL_THEN `i <= m /\ SUC i <= m /\ i < m` STRIP_ASSUME_TAC THENL
       [ASM_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "ch" (fun th -> STRIP_ASSUME_TAC(MATCH_MP th (ASSUME `i:num < m`))) THEN
      SUBGOAL_THEN `segment[(p:num->real^3) i,p (SUC i)] INTER UNIONS c = {}`
      ASSUME_TAC THENL
       [UNDISCH_TAC `segment[(p:num->real^3) i,p (SUC i)] SUBSET u` THEN
        UNDISCH_TAC `u INTER UNIONS c:real^3->bool = {}` THEN SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MP_TAC(ISPECL [`(p:num->real^3) i`; `(p:num->real^3) (SUC i)`] ENDS_IN_SEGMENT) THEN
        UNDISCH_TAC `segment[(p:num->real^3) i,p (SUC i)] INTER UNIONS c = {}` THEN
        SET_TAC[];
        X_GEN_TAC `s:real^3->bool` THEN DISCH_TAC THEN
        REWRITE_TAC[affine_gp_3] THEN DISJ1_TAC THEN
        SUBGOAL_THEN `(s:real^3->bool) SUBSET UNIONS c` MP_TAC THENL
         [UNDISCH_TAC `(s:real^3->bool) IN c` THEN SET_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `segment[(p:num->real^3) i,p (SUC i)] INTER UNIONS c = {}` THEN
        SET_TAC[];
        UNDISCH_TAC `segment[(p:num->real^3) i,p (SUC i)] INTER UNIONS c = {}` THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`;
                 `\i. if i <= m then (p:num->real^3) i else P0`; `SUC m`]
    EVEN_CROSSING) THEN
  BETA_TAC THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[LE_0; ARITH_RULE `~(SUC m <= m)`] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `e:real^3->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `e:real^3->bool`] MOI_FSA_CM_EDGE2) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONV_TAC NUM_REDUCE_CONV;
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "idx" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[];
      MAP_EVERY X_GEN_TAC [`i:num`; `s:real^3->bool`] THEN STRIP_TAC THEN
      USE_THEN "idx" (MP_TAC o SPEC `i:num`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN
   `{(i,x) | i < SUC m /\
             x IN segment[(if i <= m then (p:num->real^3) i else P0),
                          (if SUC i <= m then p (SUC i) else P0)] /\
             x IN UNIONS c} = {(m,y)}`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; FORALL_PAIR_THM; IN_ELIM_THM; IN_SING; PAIR_EQ] THEN
    MAP_EVERY X_GEN_TAC [`j:num`; `z:real^3`] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `i:num` (X_CHOOSE_THEN `x:real^3`
        (CONJUNCTS_THEN2 STRIP_ASSUME_TAC STRIP_ASSUME_TAC))) THEN
      USE_THEN "idx" (fun th -> MP_TAC(MATCH_MP th (ASSUME `i < SUC m`))) THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^3` o last o CONJUNCTS) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      STRIP_TAC THEN MAP_EVERY EXISTS_TAC [`m:num`; `y:real^3`] THEN
      ASM_REWRITE_TAC[ARITH_RULE `m < SUC m`] THEN
      USE_THEN "idx" (MP_TAC o SPEC `m:num`) THEN
      REWRITE_TAC[ARITH_RULE `m < SUC m`] THEN
      DISCH_THEN(MP_TAC o SPEC `y:real^3` o last o CONJUNCTS) THEN
      ASM_REWRITE_TAC[LE_REFL; ARITH_RULE `~(SUC m <= m)`]];
    REWRITE_TAC[CARD_SING] THEN CONV_TAC NUM_REDUCE_CONV]);;

(* Pigeonhole for two nonempty sides and three sets.                       *)

let MOI_S6S_PIGEON = prove
 (`!(a:real^3->bool) b u v w.
     ~(a = {}) /\ ~(b = {}) /\ (a SUBSET u \/ b SUBSET u) /\
     (a SUBSET v \/ b SUBSET v) /\ (a SUBSET w \/ b SUBSET w)
     ==> ~(u INTER v = {}) \/ ~(u INTER w = {}) \/ ~(v INTER w = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM SET_TAC[]);;

(* At most two components: every component has a relative interior point  *)
(* y of a fixed triangle in its frontier, hence contains one of the two     *)
(* local sides at y.                                                        *)

let MOI_S6S_AT_MOST_TWO = prove
 (`!(c:(real^3->bool)->bool) u v w.
     FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c) /\
     ~(UNIONS c = {}) /\
     u IN components((:real^3) DIFF UNIONS c) /\
     v IN components((:real^3) DIFF UNIONS c) /\
     w IN components((:real^3) DIFF UNIONS c)
     ==> u = v \/ u = w \/ v = w`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool) /\
                (!s:real^3->bool. s IN c ==> aff_dim s <= &2)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC; MOI_FSA_CM_DIM]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6S_UNIONS_CLOSED) THEN
  SUBGOAL_THEN `?q:real^3->bool. q IN c /\ aff_dim q = &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(UNIONS c:real^3->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `s:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_CM_PURE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^3. y IN relative_interior q` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `convex (q:real^3->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_complex (c:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim (q:real^3->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS c /\ y IN affine hull q` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `q:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPECL [`affine:(real^3->bool)->bool`; `q:real^3->bool`] HULL_SUBSET) THEN
    UNDISCH_TAC `(q:real^3->bool) IN c` THEN
    UNDISCH_TAC `(y:real^3) IN relative_interior q` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `q:real^3->bool`; `y:real^3`] LOCAL_TRI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r0:real`) THEN ASM_REWRITE_TAC[REAL_LE_REFL] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `a:real^3->bool`
    (X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(a:real^3->bool = {}) /\ ~(b:real^3->bool = {})` STRIP_ASSUME_TAC
  THENL
   [SUBGOAL_THEN `(y:real^3) IN closure a /\ y IN closure b` MP_TAC THENL
     [UNDISCH_TAC `ball(y:real^3,r0) INTER affine hull q SUBSET
                   closure a INTER closure b` THEN
      MP_TAC(ISPECL [`y:real^3`; `r0:real`] CENTRE_IN_BALL) THEN
      ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN affine hull q` THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[CLOSURE_EMPTY; NOT_IN_EMPTY]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^3->bool. x IN components((:real^3) DIFF UNIONS c)
                     ==> a SUBSET x \/ b SUBSET x`
  (LABEL_TAC "side") THENL
   [X_GEN_TAC `x:real^3->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC MOI_S6S_SIDE_IN_COMP THEN
    MAP_EVERY EXISTS_TAC [`UNIONS c:real^3->bool`; `y:real^3`; `r0:real`;
                          `affine hull q:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `x:real^3->bool`] MOI_S6S_FRONTIER_EQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^3) DIFF UNIONS c`; `u:real^3->bool`; `v:real^3->bool`]
    COMPONENTS_EQ) THEN
  MP_TAC(ISPECL [`(:real^3) DIFF UNIONS c`; `u:real^3->bool`; `w:real^3->bool`]
    COMPONENTS_EQ) THEN
  MP_TAC(ISPECL [`(:real^3) DIFF UNIONS c`; `v:real^3->bool`; `w:real^3->bool`]
    COMPONENTS_EQ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN SUBST1_TAC) THEN
  MATCH_MP_TAC MOI_S6S_PIGEON THEN
  MAP_EVERY EXISTS_TAC [`a:real^3->bool`; `b:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN USE_THEN "side" MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[]);;

(* The main theorem: Moise 26.6 from the even crossing lemma and the two     *)
(* local pictures, which are theorems here, so the antecedents of            *)
(* MOI_S26_SEP are not needed.                                               *)

let SEP_266 = prove
 (MOI_S26_SEP,
  DISCH_THEN(K ALL_TAC) THEN REWRITE_TAC[MOISE_266_STATEMENT] THEN
  X_GEN_TAC `c:(real^3->bool)->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6S_UNIONS_CLOSED) THEN
  SUBGOAL_THEN `bounded (UNIONS c:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]; ALL_TAC] THEN
  SUBGOAL_THEN `outside (UNIONS c) IN components((:real^3) DIFF UNIONS c)`
  ASSUME_TAC THENL
   [REWRITE_TAC[OUTSIDE_IN_COMPONENTS] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_OUTSIDE THEN ASM_REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
      MATCH_MP_TAC OUTSIDE_BOUNDED_NONEMPTY THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^3->bool)->bool` MOI_S6S_TWO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `P0:real^3` (X_CHOOSE_THEN `Q0:real^3` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `u1 = connected_component ((:real^3) DIFF UNIONS c) P0` THEN
  ABBREV_TAC `u2 = connected_component ((:real^3) DIFF UNIONS c) Q0` THEN
  SUBGOAL_THEN `(u1:real^3->bool) IN components((:real^3) DIFF UNIONS c) /\
                (u2:real^3->bool) IN components((:real^3) DIFF UNIONS c)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_COMPONENTS] THEN CONJ_TAC THENL
     [EXISTS_TAC `P0:real^3`; EXISTS_TAC `Q0:real^3`] THEN
    ASM_REWRITE_TAC[IN_DIFF; IN_UNIV];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w:real^3->bool. w IN components((:real^3) DIFF UNIONS c)
                                 ==> w = u1 \/ w = u2` (LABEL_TAC "two") THENL
   [X_GEN_TAC `w:real^3->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `u1:real^3->bool`; `u2:real^3->bool`;
                   `w:real^3->bool`] MOI_S6S_AT_MOST_TWO) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `components((:real^3) DIFF UNIONS c) = {u1,u2:real^3->bool}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `w:real^3->bool` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
     [USE_THEN "two" (fun th -> REWRITE_TAC[th]);
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?b:real^3->bool. {u1,u2} = {b,outside(UNIONS c)} /\ ~(b = outside(UNIONS c)) /\
                     b IN components((:real^3) DIFF UNIONS c)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `outside(UNIONS c) = u1 \/ outside(UNIONS c:real^3->bool) = u2`
    STRIP_ASSUME_TAC THENL
     [USE_THEN "two" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `u2:real^3->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      EXISTS_TAC `u1:real^3->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `b:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(TAUT `~ ~p ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ASSUME `(b:real^3->bool) IN components((:real^3) DIFF UNIONS c)`) THEN
    REWRITE_TAC[IN_COMPONENTS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(x:real^3) IN b /\ x IN outside(UNIONS c)` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[outside; IN_ELIM_THM] THEN
        UNDISCH_TAC `(x:real^3) IN (:real^3) DIFF UNIONS c` THEN
        REWRITE_TAC[IN_DIFF; IN_UNIV] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~bounded(b:real^3->bool)` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `~(b = outside(UNIONS c):real^3->bool)` THEN REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`(:real^3) DIFF UNIONS c`; `b:real^3->bool`;
                   `outside(UNIONS c):real^3->bool`] COMPONENTS_EQ) THEN
    ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN ASM SET_TAC[];
    CONJ_TAC THEN MATCH_MP_TAC MOI_S6S_FRONTIER_EQ THEN ASM_REWRITE_TAC[]]);;

