(* ========================================================================= *)
(* pc_moi_pl1m: generic PL 1-manifolds.  Compact PL polyhedra with line      *)
(* charts are finite unions of PL circles (MOI_S4L_LINE_CHART_CIRCLES); the  *)
(* crossing instance in real^3: the components of s INTER m are PL circles   *)
(* when s and m cross at every common point (MOI_S4L_CROSSING_CIRCLES).      *)
(* ========================================================================= *)

needs "src/pc_moi_core_stmt.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_polytope.ml";;
needs "src/pc_moi_smo_cf.ml";;
needs "src/pc_moi_sch3_lev.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Compact PL 1-manifolds.  A set with line charts (each point has a        *)
(* neighbourhood homeomorphic to an open subset of the line) triangulated   *)
(* by a finite simplicial complex has only vertices and edges, every vertex *)
(* in exactly two edges; its components are PL circles (MOI_SCF_CYCLE,      *)
(* MOI_SLV_POLYGON_SPHERE).                                                 *)
(* ========================================================================= *)

let moi_s4l_line_charts = new_definition
 `moi_s4l_line_charts (t:real^N->bool) <=>
    !x. x IN t
        ==> ?u (h:real^N->real^1) h'.
              open u /\ x IN u /\
              homeomorphism (t INTER u,IMAGE h (t INTER u)) (h,h') /\
              open (IMAGE h (t INTER u))`;;

let MOI_S4L_K1_CASES = prove
 (`!(K:(real^N->bool)->bool) s.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\ s IN K
     ==> s = {} \/
         (?a. s = {a} /\ {a} IN K) \/
         (?a b. ~(a = b) /\ s = segment[a,b] /\ {a} IN K /\ {b} IN K)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = -- &1 \/ aff_dim s = &0 \/ aff_dim s = &1`
  MP_TAC THENL
   [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[AFF_DIM_EQ_MINUS1; AFF_DIM_EQ_0] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> REWRITE_TAC[th]) MP_TAC) THEN
  DISCH_THEN(DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC)
    ASSUME_TAC) THENL
   [DISJ2_TAC THEN DISJ1_TAC THEN EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ2_TAC THEN DISJ2_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
  ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
  FIRST_ASSUM(MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
    GEN_REWRITE_RULE I [simplicial_complex]) THEN
  DISCH_THEN(fun th -> CONJ_TAC THEN MATCH_MP_TAC th THEN
    EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; FACE_OF_SING;
                    EXTREME_POINT_OF_SEGMENT]));;

let MOI_S4L_K1_ENDPOINT = prove
 (`!(K:(real^N->bool)->bool) v a b.
     simplicial_complex K /\ {v} IN K /\ segment[a,b] IN K /\ v IN segment[a,b]
     ==> v = a \/ v = b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N} face_of segment[a,b]` MP_TAC THENL
   [SUBGOAL_THEN `{v:real^N} = {v} INTER segment[a,b]` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [simplicial_complex]) THEN
    DISCH_THEN(MP_TAC o SPECL [`{v:real^N}`; `segment[a:real^N,b]`]) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]]);;

let MOI_S4L_SEGMENT_NEAR = prove
 (`!v w:real^N r.
     ~(w = v) /\ &0 < r ==> ?q. q IN segment[v,w] /\ ~(q = v) /\ q IN ball(v,r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `&0 < norm(w - v:real^N)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `?l. &0 < l /\ l <= &1 /\ l * norm(w - v:real^N) < r`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `min (&1 / &2) (r / (&2 * norm(w - v:real^N)))` THEN
    REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC;
      MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `(r / (&2 * norm(w - v:real^N))) * norm(w - v)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_RMUL THEN REWRITE_TAC[NORM_POS_LE] THEN
        REAL_ARITH_TAC;
        ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> (r / (&2 * n)) * n = r / &2`] THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  EXISTS_TAC `v + l % (w - v):real^N` THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `l:real` THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE] THEN VECTOR_ARITH_TAC;
    REWRITE_TAC[VECTOR_ARITH `v + l % (w - v):real^N = v <=> l % (w - v) = vec 0`] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[IN_BALL; dist;
                VECTOR_ARITH `v - (v + l % (w - v)):real^N = --(l % (w - v))`] THEN
    ASM_SIMP_TAC[NORM_NEG; NORM_MUL; REAL_ARITH `&0 < l ==> abs l = l`]]);;

let MOI_S4L_LC_DIM_LE1 = prove
 (`!(K:(real^N->bool)->bool) s.
     simplicial_complex K /\ moi_s4l_line_charts (UNIONS K) /\ s IN K
     ==> aff_dim s <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `convex(s:real^N->bool) /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&1 < aff_dim({}:real^N->bool)` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^N. x IN relative_interior s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN s` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS K` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o GEN_REWRITE_RULE I [moi_s4l_line_charts]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^1`
    (X_CHOOSE_THEN `h':real^1->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(x:real^N,r) SUBSET u` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  ABBREV_TAC `c = (s:real^N->bool) INTER ball(x,r)` THEN
  SUBGOAL_THEN `convex(c:real^N->bool) /\ (x:real^N) IN c /\
                aff_dim c = aff_dim(s:real^N->bool) /\
                c SUBSET UNIONS K INTER u`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "c" THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[CONVEX_INTER; CONVEX_BALL];
      ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
      MATCH_MP_TAC AFF_DIM_CONVEX_INTER_OPEN THEN
      ASM_REWRITE_TAC[OPEN_BALL; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[CENTRE_IN_BALL];
      REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^N. y IN c /\ ~(y = x)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(c SUBSET {x:real^N}) ==> ?y. y IN c /\ ~(y = x)`) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `c = {x:real^N}` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `aff_dim {x:real^N} = aff_dim(s:real^N->bool)` THEN
    UNDISCH_TAC `&1 < aff_dim(s:real^N->bool)` THEN
    REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^1) continuous_on c /\
                (!y z. y IN c /\ z IN c /\ h y = h z ==> y = z)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
      ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?w:real^N. w IN c /\
                (h:real^N->real^1) w = midpoint((h:real^N->real^1) x,h y)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `convex(IMAGE (h:real^N->real^1) c)` MP_TAC THENL
     [REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1; IS_INTERVAL_CONNECTED_1] THEN
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[CONVEX_CONNECTED];
      ALL_TAC] THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`(h:real^N->real^1) x`; `(h:real^N->real^1) y`]) THEN
    ASM_SIMP_TAC[FUN_IN_IMAGE] THEN
    DISCH_THEN(MP_TAC o SPEC `midpoint((h:real^N->real^1) x,h y)` o
      REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[MIDPOINT_IN_SEGMENT; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(w:real^N = x) /\ ~(w = y)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~((h:real^N->real^1) x = h y)` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[MIDPOINT_EQ_ENDPOINT];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(IMAGE (h:real^N->real^1) (c DELETE w))` MP_TAC THENL
   [REWRITE_TAC[GSYM IS_INTERVAL_CONVEX_1; IS_INTERVAL_CONNECTED_1] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; DELETE_SUBSET];
      MATCH_MP_TAC CONNECTED_PUNCTURED_CONVEX THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `&1 < aff_dim(s:real^N->bool)` THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`(h:real^N->real^1) x`; `(h:real^N->real^1) y`]) THEN
  ANTS_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `midpoint((h:real^N->real^1) x,h y)` o
    REWRITE_RULE[SUBSET]) THEN
  REWRITE_TAC[MIDPOINT_IN_SEGMENT; IN_IMAGE; IN_DELETE] THEN
  ASM_MESON_TAC[]);;

let MOI_S4L_K1_EDGE_AT = prove
 (`!(K:(real^N->bool)->bool) v e.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     {v} IN K /\ e IN K /\ aff_dim e = &1 /\ v IN e
     ==> ?w. ~(w = v) /\ e = segment[v,w] /\ {w} IN K`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `e:real^N->bool`] MOI_S4L_K1_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC[NOT_IN_EMPTY];
    UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN ASM_REWRITE_TAC[AFF_DIM_SING] THEN
    INT_ARITH_TAC;
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `a:real^N`; `b:real^N`]
      MOI_S4L_K1_ENDPOINT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `b:real^N` THEN ASM_MESON_TAC[];
      EXISTS_TAC `a:real^N` THEN ASM_MESON_TAC[SEGMENT_SYM]]]);;

let MOI_S4L_K1_EDGES_MEET = prove
 (`!(K:(real^N->bool)->bool) v w1 w2 y.
     simplicial_complex K /\ segment[v,w1] IN K /\ segment[v,w2] IN K /\
     ~(w1 = v) /\ ~(w2 = v) /\
     y IN segment[v,w1] /\ y IN segment[v,w2] /\
     ~(y = v) /\ ~(y = w1) /\ ~(y = w2)
     ==> segment[v,w1] = segment[v,w2]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!wa wb:real^N.
      segment[v,wa] IN K /\ segment[v,wb] IN K /\ ~(wa = v) /\
      y IN segment[v,wa] /\ y IN segment[v,wb] /\ ~(y = wa)
      ==> segment[v,wa] INTER segment[v,wb] = segment[v,wa]`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(v:real^N = wa)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`segment[v:real^N,wa]`;
                   `segment[v:real^N,wa] INTER segment[v,wb]`]
      FACE_OF_SUBSET_RELATIVE_FRONTIER) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
        GEN_REWRITE_RULE I [simplicial_complex]) THEN
      DISCH_THEN(MP_TAC o SPECL [`segment[v:real^N,wa]`; `segment[v:real^N,wb]`]) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; relative_frontier; IN_DIFF; CLOSURE_SEGMENT] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^N`) THEN
    ASM_REWRITE_TAC[IN_INTER; RELATIVE_INTERIOR_SEGMENT; IN_OPEN_SEGMENT_ALT] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(SET_RULE `(s:real^N->bool) INTER t = s /\ t INTER s = t ==> s = t`) THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_S4L_CONNECTED_IMAGE_BETWEEN = prove
 (`!(f:real^N->real^1) s a b c.
     f continuous_on s /\ connected s /\ a IN s /\ b IN s /\
     drop(f a) <= drop c /\ drop c <= drop(f b)
     ==> ?y. y IN s /\ f y = c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `is_interval(IMAGE (f:real^N->real^1) s)` MP_TAC THENL
   [REWRITE_TAC[IS_INTERVAL_CONNECTED_1] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IS_INTERVAL_1] THEN
  DISCH_THEN(MP_TAC o SPECL [`(f:real^N->real^1) a`; `(f:real^N->real^1) b`;
                             `c:real^1`]) THEN
  ASM_SIMP_TAC[FUN_IN_IMAGE] THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[]);;

let MOI_S4L_LC_DEGREE_2 = prove
 (`!(K:(real^N->bool)->bool) v.
     simplicial_complex K /\ moi_s4l_line_charts (UNIONS K) /\ {v} IN K
     ==> CARD {e | e IN K /\ aff_dim e = &1 /\ v IN e} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K ==> aff_dim s <= &1` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_LC_DIM_LE1]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {e | e IN K /\ aff_dim e = &1 /\ (v:real^N) IN e}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS K` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\ !s z. s IN K /\ ~((v:real^N) IN s) /\ z IN s ==> d <= dist(v,z)`
  (X_CHOOSE_THEN `d:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "sep"))) THENL
   [MP_TAC(ISPECL [`UNIONS {s | s IN K /\ ~((v:real^N) IN s)}`; `v:real^N`]
      SEPARATE_POINT_CLOSED) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
          REWRITE_TAC[IN_ELIM_THM] THEN
          ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED]];
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o GEN_REWRITE_RULE I [moi_s4l_line_charts]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` (X_CHOOSE_THEN `h:real^N->real^1`
    (X_CHOOSE_THEN `h':real^1->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(h:real^N->real^1) continuous_on (UNIONS K INTER u) /\
                (!y z. y IN UNIONS K INTER u /\ z IN UNIONS K INTER u /\ h y = h z
                       ==> y = z)`
  (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "inj")) THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(v:real^N,r) SUBSET u` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_CONTAINS_BALL]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < min d r /\ ball(v:real^N,min d r) SUBSET u /\
                (!z. z IN ball(v:real^N,min d r) ==> dist(v,z) < d)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_BALL] THEN REPEAT CONJ_TAC THENL
     [ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(v:real^N,r)` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  (* points of the complex near v lie on edges at v *)
  SUBGOAL_THEN
   `!x. x IN UNIONS K /\ x IN ball(v:real^N,min d r)
        ==> x = v \/ ?e. (e IN K /\ aff_dim e = &1 /\ v IN e) /\ x IN e`
  (LABEL_TAC "cover") THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    ASM_CASES_TAC `(v:real^N) IN s` THENL
     [ALL_TAC;
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      SUBGOAL_THEN `d <= dist(v:real^N,x) /\ dist(v,x) < d` MP_TAC THENL
       [ASM_MESON_TAC[]; REAL_ARITH_TAC]] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4L_K1_CASES) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
     [ASM_MESON_TAC[NOT_IN_EMPTY];
      DISJ1_TAC THEN ASM_MESON_TAC[IN_SING];
      DISJ2_TAC THEN EXISTS_TAC `s:real^N->bool` THEN
      SUBGOAL_THEN `aff_dim(s:real^N->bool) = &1` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[AFF_DIM_SEGMENT]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the image of the punctured neighbourhood is open *)
  SUBGOAL_THEN `open(IMAGE (h:real^N->real^1) (UNIONS K INTER ball(v,min d r)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN
    EXISTS_TAC `IMAGE (h:real^N->real^1) (UNIONS K INTER u)` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:real^N->real^1`; `h':real^1->real^N`;
                   `UNIONS K INTER (u:real^N->bool)`;
                   `IMAGE (h:real^N->real^1) (UNIONS K INTER u)`;
                   `UNIONS K INTER ball(v:real^N,min d r)`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `ball(v:real^N,min d r)` THEN
      REWRITE_TAC[OPEN_BALL] THEN ASM SET_TAC[];
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?ee. &0 < ee /\
                     ball((h:real^N->real^1) v,ee) SUBSET
                     IMAGE h (UNIONS K INTER ball(v,min d r))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `IMAGE (h:real^N->real^1) (UNIONS K INTER ball(v,min d r))`
      OPEN_CONTAINS_BALL) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    ALL_TAC] THEN
  (* each edge at v lies on one side of h v *)
  SUBGOAL_THEN
   `!e. e IN K /\ aff_dim e = &1 /\ (v:real^N) IN e
        ==> (!z. z IN IMAGE (h:real^N->real^1) ((e INTER ball(v,min d r)) DELETE v)
                 ==> drop(h v) < drop z) \/
            (!z. z IN IMAGE (h:real^N->real^1) ((e INTER ball(v,min d r)) DELETE v)
                 ==> drop z < drop(h v))`
  (LABEL_TAC "side") THENL
   [X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
      MOI_S4L_K1_EDGE_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(h:real^N->real^1) continuous_on ((e INTER ball(v,min d r)) DELETE v) /\
      connected ((e INTER ball(v:real^N,min d r)) DELETE v)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `UNIONS K INTER (u:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_DELETE; IN_UNIONS] THEN ASM_MESON_TAC[SUBSET];
        MATCH_MP_TAC CONVEX_CONNECTED THEN ASM_REWRITE_TAC[] THEN
        ONCE_REWRITE_TAC[SET_RULE
         `(s INTER t) DELETE (a:real^N) = (s DELETE a) INTER t`] THEN
        MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_SEMIOPEN_SEGMENT; CONVEX_BALL]];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~(~p /\ ~q) ==> p \/ q`) THEN
    REWRITE_TAC[NOT_FORALL_THM; NOT_IMP; REAL_NOT_LT; IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `z1:real^1` (CONJUNCTS_THEN2
         (X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC) ASSUME_TAC))
      (X_CHOOSE_THEN `z2:real^1` (CONJUNCTS_THEN2
         (X_CHOOSE_THEN `y2:real^N` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`h:real^N->real^1`; `(e INTER ball(v:real^N,min d r)) DELETE v`;
                   `y1:real^N`; `y2:real^N`; `(h:real^N->real^1) v`]
      MOI_S4L_CONNECTED_IMAGE_BETWEEN) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `q:real^N = v` MP_TAC THENL
     [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_DELETE; IN_INTER]) THEN
      REWRITE_TAC[IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[SUBSET];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the punctured ball around h v is covered by the edges *)
  SUBGOAL_THEN
   `!z. z IN ball((h:real^N->real^1) v,ee) /\ ~(z = h v)
        ==> ?e. (e IN K /\ aff_dim e = &1 /\ (v:real^N) IN e) /\
                z IN IMAGE h ((e INTER ball(v,min d r)) DELETE v)`
  (LABEL_TAC "punct") THENL
   [X_GEN_TAC `z:real^1` THEN STRIP_TAC THEN
    SUBGOAL_THEN `z IN IMAGE (h:real^N->real^1) (UNIONS K INTER ball(v,min d r))`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    USE_THEN "cover" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[IN_DELETE; IN_INTER] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* two edges meet only at v: they cannot be on the same side *)
  SUBGOAL_THEN
   `!e1 e2 z1 z2.
      (e1 IN K /\ aff_dim e1 = &1 /\ (v:real^N) IN e1) /\
      (e2 IN K /\ aff_dim e2 = &1 /\ v IN e2) /\ ~(e1 = e2) /\
      z1 IN IMAGE (h:real^N->real^1) ((e1 INTER ball(v,min d r)) DELETE v) /\
      z2 IN IMAGE (h:real^N->real^1) ((e2 INTER ball(v,min d r)) DELETE v)
      ==> ~(drop(h v) < drop z1 /\ drop(h v) < drop z2) /\
          ~(drop z1 < drop(h v) /\ drop z2 < drop(h v))`
  (LABEL_TAC "same") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `e1:real^N->bool`]
      MOI_S4L_K1_EDGE_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w1:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `e2:real^N->bool`]
      MOI_S4L_K1_EDGE_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w2:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `!c. (?y1. y1 IN e1 INTER ball(v:real^N,min d r) /\ (h:real^N->real^1) y1 = c) /\
          (?y2. y2 IN e2 INTER ball(v:real^N,min d r) /\ (h:real^N->real^1) y2 = c)
          ==> c = h v`
    (LABEL_TAC "meet") THENL
     [X_GEN_TAC `c:real^1` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `y1:real^N` STRIP_ASSUME_TAC)
                                 (X_CHOOSE_THEN `y2:real^N` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `y1:real^N = y2` ASSUME_TAC THENL
       [USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
        REWRITE_TAC[IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[SUBSET];
        ALL_TAC] THEN
      ASM_CASES_TAC `y1:real^N = v` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `~(e1:real^N->bool = e2)` THEN REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_S4L_K1_EDGES_MEET THEN
      MAP_EVERY EXISTS_TAC [`K:(real^N->bool)->bool`; `y1:real^N`] THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
      SUBGOAL_THEN `d <= dist(v:real^N,w1) /\ d <= dist(v,w2) /\
                    dist(v,y1) < d` STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [USE_THEN "sep" MATCH_MP_TAC THEN EXISTS_TAC `{w1:real^N}` THEN
          ASM_REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[];
          USE_THEN "sep" MATCH_MP_TAC THEN EXISTS_TAC `{w2:real^N}` THEN
          ASM_REWRITE_TAC[IN_SING] THEN ASM_MESON_TAC[];
          ASM_MESON_TAC[]];
        ALL_TAC] THEN
      ASM_MESON_TAC[REAL_LT_REFL; REAL_LET_TRANS];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `connected(e1 INTER ball(v:real^N,min d r)) /\
      connected(e2 INTER ball(v:real^N,min d r)) /\
      (h:real^N->real^1) continuous_on (e1 INTER ball(v,min d r)) /\
      (h:real^N->real^1) continuous_on (e2 INTER ball(v,min d r)) /\
      v IN e1 INTER ball(v,min d r) /\ v IN e2 INTER ball(v,min d r)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONVEX_CONNECTED THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_SEGMENT; CONVEX_BALL];
        MATCH_MP_TAC CONVEX_CONNECTED THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CONVEX_INTER THEN REWRITE_TAC[CONVEX_SEGMENT; CONVEX_BALL];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `UNIONS K INTER (u:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[SUBSET];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `UNIONS K INTER (u:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[SUBSET];
        ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
        ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL]];
      ALL_TAC] THEN
    RULE_ASSUM_TAC(REWRITE_RULE[IN_IMAGE; IN_DELETE]) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `x2:real^N` STRIP_ASSUME_TAC o
      check (fun th -> is_exists(concl th) &&
                       can (find_term ((=) `z2:real^1`)) (concl th))) THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC o
      check (fun th -> is_exists(concl th) &&
                       can (find_term ((=) `z1:real^1`)) (concl th))) THEN
    CONJ_TAC THEN STRIP_TAC THENL
     [ABBREV_TAC `c = lift((drop((h:real^N->real^1) v) + min (drop z1) (drop z2)) / &2)`;
      ABBREV_TAC `c = lift((drop((h:real^N->real^1) v) + max (drop z1) (drop z2)) / &2)`] THEN
    SUBGOAL_THEN `~(c = (h:real^N->real^1) v)` MP_TAC THENL
     [EXPAND_TAC "c" THEN REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC;
      EXPAND_TAC "c" THEN REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[] THEN REMOVE_THEN "meet" MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4L_CONNECTED_IMAGE_BETWEEN;
      MATCH_MP_TAC MOI_S4L_CONNECTED_IMAGE_BETWEEN;
      MATCH_MP_TAC MOI_S4L_CONNECTED_IMAGE_BETWEEN;
      MATCH_MP_TAC MOI_S4L_CONNECTED_IMAGE_BETWEEN] THENL
     [MAP_EVERY EXISTS_TAC [`v:real^N`; `x1:real^N`];
      MAP_EVERY EXISTS_TAC [`v:real^N`; `x2:real^N`];
      MAP_EVERY EXISTS_TAC [`x1:real^N`; `v:real^N`];
      MAP_EVERY EXISTS_TAC [`x2:real^N`; `v:real^N`]] THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "c" THEN REWRITE_TAC[LIFT_DROP] THEN
    UNDISCH_TAC `(z1:real^1) = (h:real^N->real^1) x1` THEN
    UNDISCH_TAC `(z2:real^1) = (h:real^N->real^1) x2` THEN
    REPEAT(DISCH_THEN(SUBST_ALL_TAC o SYM)) THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* conclusion: exactly two edges *)
  SUBGOAL_THEN
   `?ep. (ep IN K /\ aff_dim ep = &1 /\ (v:real^N) IN ep) /\
         ?z. z IN IMAGE (h:real^N->real^1) ((ep INTER ball(v,min d r)) DELETE v) /\
             drop(h v) < drop z`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "punct" (MP_TAC o SPEC `(h:real^N->real^1) v + lift(ee / &2)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `a - (a + b):real^1 = --b`; NORM_NEG;
                  NORM_LIFT; VECTOR_ARITH `a + b:real^1 = a <=> b = vec 0`] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `(h:real^N->real^1) v + lift(ee / &2)` THEN
      ASM_REWRITE_TAC[DROP_ADD; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?em. (em IN K /\ aff_dim em = &1 /\ (v:real^N) IN em) /\
         ?z. z IN IMAGE (h:real^N->real^1) ((em INTER ball(v,min d r)) DELETE v) /\
             drop z < drop(h v)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "punct" (MP_TAC o SPEC `(h:real^N->real^1) v - lift(ee / &2)`) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `a - (a - b):real^1 = b`;
                  NORM_LIFT; VECTOR_ARITH `a - b:real^1 = a <=> b = vec 0`] THEN
      REWRITE_TAC[GSYM DROP_EQ; DROP_VEC; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `(h:real^N->real^1) v - lift(ee / &2)` THEN
      ASM_REWRITE_TAC[DROP_SUB; LIFT_DROP] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(ep:real^N->bool = em)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    USE_THEN "side" (MP_TAC o SPEC `em:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[REAL_LT_ANTISYM];
    ALL_TAC] THEN
  MATCH_MP_TAC(ARITH_RULE `2 <= n /\ ~(3 <= n) ==> n = 2`) THEN CONJ_TAC THENL
   [SUBGOAL_THEN `CARD {ep:real^N->bool,em} <=
                  CARD {e | e IN K /\ aff_dim e = &1 /\ (v:real^N) IN e}`
    MP_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      ARITH_TAC];
    ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`3`; `{e | e IN K /\ aff_dim e = &1 /\ (v:real^N) IN e}`]
    CHOOSE_SUBSET_STRONG) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t3:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` (X_CHOOSE_THEN `e2:real^N->bool`
    (X_CHOOSE_THEN `e3:real^N->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `!e. e IN K /\ aff_dim e = &1 /\ (v:real^N) IN e
        ==> ?z. z IN IMAGE (h:real^N->real^1) ((e INTER ball(v,min d r)) DELETE v)`
  (LABEL_TAC "nonempty") THENL
   [X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
      MOI_S4L_K1_EDGE_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`v:real^N`; `w:real^N`; `min d r`] MOI_S4L_SEGMENT_NEAR) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(h:real^N->real^1) q` THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DELETE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(e1 IN K /\ aff_dim e1 = &1 /\ (v:real^N) IN e1) /\
    (e2 IN K /\ aff_dim e2 = &1 /\ v IN e2) /\
    (e3 IN K /\ aff_dim e3 = &1 /\ v IN e3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `t3 SUBSET {e | e IN K /\ aff_dim e = &1 /\ (v:real^N) IN e}` THEN
    ASM_REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e z. e IN K /\ aff_dim e = &1 /\ (v:real^N) IN e /\
          z IN IMAGE (h:real^N->real^1) ((e INTER ball(v,min d r)) DELETE v)
          ==> ~(drop z = drop(h v))`
  (LABEL_TAC "neq") THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[IN_IMAGE; IN_DELETE; IN_INTER] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[DROP_EQ] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(x:real^N = v)` THEN REWRITE_TAC[] THEN
    USE_THEN "inj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS] THEN ASM_MESON_TAC[SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z1. z1 IN IMAGE (h:real^N->real^1) ((e1 INTER ball(v,min d r)) DELETE v)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "nonempty" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?z2. z2 IN IMAGE (h:real^N->real^1) ((e2 INTER ball(v,min d r)) DELETE v)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "nonempty" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?z3. z3 IN IMAGE (h:real^N->real^1) ((e3 INTER ball(v,min d r)) DELETE v)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "nonempty" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(drop z1 = drop((h:real^N->real^1) v)) /\
                ~(drop z2 = drop((h:real^N->real^1) v)) /\
                ~(drop z3 = drop((h:real^N->real^1) v))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "neq" MATCH_MP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "same" (MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`;
                                   `z1:real^1`; `z2:real^1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "same" (MP_TAC o SPECL [`e1:real^N->bool`; `e3:real^N->bool`;
                                   `z1:real^1`; `z3:real^1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  USE_THEN "same" (MP_TAC o SPECL [`e2:real^N->bool`; `e3:real^N->bool`;
                                   `z2:real^1`; `z3:real^1`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  POP_ASSUM_LIST(MP_TAC o end_itlist CONJ o filter (fun th ->
    let c = concl th in not(is_forall c) &&
      (can (find_term ((=) `drop`)) c))) THEN
  REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A finite 1-dimensional complex with all vertex degrees 2: every         *)
(* component is the union of the edges of a vertex cycle.                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S4L_K1_VERTEX_IN = prove
 (`!(K:(real^N->bool)->bool) s.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     s IN K /\ ~(s = {})
     ==> ?a. {a} IN K /\ a IN s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4L_K1_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THEN
  ASM_MESON_TAC[IN_SING; ENDS_IN_SEGMENT]);;

let MOI_S4L_K1_COMMON_VERTEX = prove
 (`!(K:(real^N->bool)->bool) s1 s2.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     s1 IN K /\ s2 IN K /\ ~(s1 INTER s2 = {})
     ==> ?c. {c} IN K /\ c IN s1 /\ c IN s2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s1:real^N->bool) INTER s2 IN K` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o
      GEN_REWRITE_RULE I [simplicial_complex]) THEN
    EXISTS_TAC `s1:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `(s1:real^N->bool) INTER s2`]
    MOI_S4L_K1_VERTEX_IN) THEN
  ASM_REWRITE_TAC[IN_INTER]);;

let MOI_S4L_CYCLE_PRED = prove
 (`!n (S:num->A) i.
     3 <= n /\ (!i. S(i + n) = S i) /\
     (!i k. i < n /\ k < n /\ S i = S k ==> i = k) /\ i < n
     ==> ?p. p < n /\ S(SUC p) = S i /\ ~(S p = S(SUC i))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `i = 0` THENL
   [EXISTS_TAC `n - 1` THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      SUBGOAL_THEN `SUC(n - 1) = 0 + n` SUBST1_TAC THENL
       [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      DISCH_TAC THEN
      SUBGOAL_THEN `n - 1 = SUC 0` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC]];
    EXISTS_TAC `i - 1` THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC;
      AP_TERM_TAC THEN ASM_ARITH_TAC;
      DISCH_TAC THEN ASM_CASES_TAC `SUC i < n` THENL
       [SUBGOAL_THEN `i - 1 = SUC i` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
          ASM_ARITH_TAC];
        SUBGOAL_THEN `(S:num->A)(SUC i) = S 0` ASSUME_TAC THENL
         [SUBGOAL_THEN `SUC i = 0 + n` SUBST1_TAC THENL
           [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        SUBGOAL_THEN `i - 1 = 0` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
          ASM_ARITH_TAC]]]]);;

let MOI_S4L_CM1_CYCLE = prove
 (`!(K:(real^N->bool)->bool) j.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     (!v. {v} IN K ==> CARD {e | e IN K /\ aff_dim e = &1 /\ v IN e} = 2) /\
     j IN components (UNIONS K)
     ==> ?n S. 3 <= n /\ (!i. S(i + n) = S i) /\
               (!i k. i < n /\ k < n /\ S i = S k ==> i = k) /\
               (!i. {S i} IN K /\ segment[S i,S(SUC i)] IN K /\ S i IN j) /\
               j = UNIONS {segment[S i,S(SUC i)] | i < n} /\
               (!v. {v} IN K /\ v IN j ==> ?i. i < n /\ v = S i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K ==> connected s /\ closed s /\ s SUBSET UNIONS K`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
      ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K /\ ~(s INTER j = {}) ==> s SUBSET j`
  (LABEL_TAC "insj") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `UNIONS K:real^N->bool` THEN ASM_MESON_TAC[INTER_COMM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^N->bool) SUBSET UNIONS K` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  ABBREV_TAC `V = {a:real^N | {a} IN K /\ a IN j}` THEN
  ABBREV_TAC `R = \a b:real^N. ~(a = b) /\ segment[a,b] IN K` THEN
  (* two neighbours *)
  SUBGOAL_THEN
   `!x:real^N. x IN V ==> ?y z. y IN V /\ z IN V /\ ~(y = z) /\ R x y /\ R x z /\
                                !u. u IN V /\ R x u ==> u = y \/ u = z`
  (LABEL_TAC "two") THENL
   [X_GEN_TAC `a:real^N` THEN EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `{e | e IN K /\ aff_dim e = &1 /\ (a:real^N) IN e} HAS_SIZE 2`
    MP_TAC THENL
     [REWRITE_TAC[HAS_SIZE] THEN ASM_SIMP_TAC[] THEN
      MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` (X_CHOOSE_THEN `e2:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(e1 IN K /\ aff_dim e1 = &1 /\ (a:real^N) IN e1) /\
                  (e2 IN K /\ aff_dim e2 = &1 /\ a IN e2)`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        is_setenum(rand(concl th)))) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `a:real^N`; `e1:real^N->bool`]
      MOI_S4L_K1_EDGE_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `b1:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `a:real^N`; `e2:real^N->bool`]
      MOI_S4L_K1_EDGE_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `b2:real^N` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`b1:real^N`; `b2:real^N`] THEN
    EXPAND_TAC "V" THEN EXPAND_TAC "R" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `(e1:real^N->bool) SUBSET j /\ (e2:real^N->bool) SUBSET j`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "insj" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `(b1:real^N) IN j /\ b2 IN j` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(e1:real^N->bool) SUBSET j`;
        UNDISCH_TAC `(e2:real^N->bool) SUBSET j`] THEN
      ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(b1:real^N = b2)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `segment[a:real^N,b1] IN K /\ segment[a,b2] IN K /\
                  ~(a = b1) /\ ~(a = b2)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
     (X_GEN_TAC `c:real^N` THEN STRIP_TAC THEN
      SUBGOAL_THEN `segment[a:real^N,c] = e1 \/ segment[a,c] = e2` MP_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
          is_setenum(rand(concl th)))) THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `segment[a:real^N,c]`) THEN
        ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT];
        ASM_REWRITE_TAC[SEGMENT_EQ] THEN UNDISCH_TAC `~(a:real^N = c)` THEN
        SET_TAC[]]);
    ALL_TAC] THEN
  (* connectedness *)
  SUBGOAL_THEN
   `!U. U SUBSET V /\ ~(U = {}) /\ (!x y:real^N. x IN U /\ y IN V /\ R x y ==> y IN U)
        ==> U = V`
  ASSUME_TAC THENL
   [X_GEN_TAC `U:real^N->bool` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `?a0:real^N. a0 IN V /\ ~(a0 IN U)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~(U:real^N->bool = V)` THEN
      UNDISCH_TAC `(U:real^N->bool) SUBSET V` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!s a b:real^N. s IN K /\ s SUBSET j /\ {a} IN K /\ a IN s /\ {b} IN K /\ b IN s
                     ==> (a IN U <=> b IN U)`
    (LABEL_TAC "allin") THENL
     [REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4L_K1_CASES) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
       [ASM_MESON_TAC[NOT_IN_EMPTY];
        ASM_MESON_TAC[IN_SING];
        ALL_TAC] THEN
      SUBGOAL_THEN `(a = a' \/ a = b') /\ (b = a' \/ b = (b':real^N))` MP_TAC THENL
       [CONJ_TAC THEN MATCH_MP_TAC MOI_S4L_K1_ENDPOINT THEN
        EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(a':real^N) IN V /\ b' IN V` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
        ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
        ALL_TAC] THEN
      SUBGOAL_THEN `(R:real^N->real^N->bool) a' b' /\ R b' a'` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "R" THEN ASM_MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `X = UNIONS {s | s IN K /\ s SUBSET j /\
                               ?a:real^N. a IN U /\ {a} IN K /\ a IN s}` THEN
    ABBREV_TAC `Y = UNIONS {s | s IN K /\ s SUBSET j /\
                               ?a:real^N. a IN V DIFF U /\ {a} IN K /\ a IN s}` THEN
    SUBGOAL_THEN `closed(X:real^N->bool) /\ closed(Y:real^N->bool)` STRIP_ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN CONJ_TAC THEN
      MATCH_MP_TAC CLOSED_UNIONS THEN REWRITE_TAC[IN_ELIM_THM] THEN
      (CONJ_TAC THENL
        [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
         ASM_MESON_TAC[]]);
      ALL_TAC] THEN
    SUBGOAL_THEN `(j:real^N->bool) SUBSET X UNION Y` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?s:real^N->bool. s IN K /\ x IN s` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN j` THEN
        UNDISCH_TAC `(j:real^N->bool) SUBSET UNIONS K` THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(s:real^N->bool) SUBSET j` ASSUME_TAC THENL
       [USE_THEN "insj" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4L_K1_VERTEX_IN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(a:real^N) IN V` ASSUME_TAC THENL
       [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET];
        ALL_TAC] THEN
      MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      ASM_CASES_TAC `(a:real^N) IN U` THENL
       [DISJ1_TAC; DISJ2_TAC] THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[IN_DIFF];
      ALL_TAC] THEN
    SUBGOAL_THEN `X INTER Y INTER (j:real^N->bool) = {}` ASSUME_TAC THENL
     [MAP_EVERY EXPAND_TAC ["X"; "Y"] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (X_CHOOSE_THEN `s1:real^N->bool` (CONJUNCTS_THEN2
          (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
            (X_CHOOSE_THEN `a1:real^N` STRIP_ASSUME_TAC))) ASSUME_TAC))
        (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `s2:real^N->bool` (CONJUNCTS_THEN2
            (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
              (X_CHOOSE_THEN `a2:real^N` STRIP_ASSUME_TAC))) ASSUME_TAC))
          ASSUME_TAC)) THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s1:real^N->bool`; `s2:real^N->bool`]
        MOI_S4L_K1_COMMON_VERTEX) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `((a1:real^N) IN U <=> c IN U) /\ ((a2:real^N) IN U <=> c IN U)`
      MP_TAC THENL
       [CONJ_TAC THEN USE_THEN "allin" MATCH_MP_TAC THENL
         [EXISTS_TAC `s1:real^N->bool`; EXISTS_TAC `s2:real^N->bool`] THEN
        ASM_REWRITE_TAC[];
        RULE_ASSUM_TAC(REWRITE_RULE[IN_DIFF]) THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `j IN components(UNIONS K:real^N->bool)` THEN
    DISCH_THEN(MP_TAC o MATCH_MP IN_COMPONENTS_CONNECTED) THEN
    REWRITE_TAC[CONNECTED_CLOSED] THEN
    MAP_EVERY EXISTS_TAC [`X:real^N->bool`; `Y:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `?a:real^N. a IN U` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `a:real^N` THEN
      SUBGOAL_THEN `{a:real^N} IN K /\ a IN j` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(U:real^N->bool) SUBSET V` THEN EXPAND_TAC "V" THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "X" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `{a:real^N}` THEN ASM_REWRITE_TAC[IN_SING; SING_SUBSET] THEN
      ASM_MESON_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `a0:real^N` THEN
      SUBGOAL_THEN `{a0:real^N} IN K /\ a0 IN j` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(a0:real^N) IN V` THEN EXPAND_TAC "V" THEN
        REWRITE_TAC[IN_ELIM_THM];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "Y" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `{a0:real^N}` THEN ASM_REWRITE_TAC[IN_SING; SING_SUBSET] THEN
      EXISTS_TAC `a0:real^N` THEN ASM_REWRITE_TAC[IN_DIFF; IN_SING]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `R:real^N->real^N->bool`] MOI_SCF_CYCLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "V" THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `IMAGE (CHOICE:(real^N->bool)->real^N) K` THEN CONJ_TAC THENL
       [ASM_MESON_TAC[FINITE_IMAGE; simplicial_complex];
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN
        MESON_TAC[CHOICE_DEF; IN_SING; NOT_INSERT_EMPTY]];
      SUBGOAL_THEN `?x:real^N. x IN j` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
      SUBGOAL_THEN `?s:real^N->bool. s IN K /\ x IN s` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^N) IN j` THEN
        UNDISCH_TAC `(j:real^N->bool) SUBSET UNIONS K` THEN SET_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4L_K1_VERTEX_IN) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[NOT_IN_EMPTY]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(s:real^N->bool) SUBSET j` ASSUME_TAC THENL
       [USE_THEN "insj" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `a:real^N` THEN
      EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(s:real^N->bool) SUBSET j` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      EXPAND_TAC "R" THEN MESON_TAC[SEGMENT_SYM];
      EXPAND_TAC "R" THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `S:num->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 MP_TAC MP_TAC)))))) THEN
  EXPAND_TAC "V" THEN EXPAND_TAC "R" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(LABEL_TAC "Sonto") THEN DISCH_THEN(LABEL_TAC "Sfacts") THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `S:num->real^N`] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN X_GEN_TAC `i:num` THEN
    DISCH_TAC THEN USE_THEN "insj" MATCH_MP_TAC THEN
    USE_THEN "Sfacts" (MP_TAC o SPEC `i:num`) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `(S:num->real^N) i` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT]] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN K /\ x IN s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN j` THEN
    UNDISCH_TAC `(j:real^N->bool) SUBSET UNIONS K` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET j` ASSUME_TAC THENL
   [USE_THEN "insj" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S4L_K1_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN STRIP_ASSUME_TAC) THENL
   [ASM_MESON_TAC[NOT_IN_EMPTY];
    USE_THEN "Sonto" (MP_TAC o SPEC `a:real^N`) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `segment[(S:num->real^N) i,S(SUC i)]` THEN
    CONJ_TAC THENL [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[IN_SING] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN j /\ b IN j` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(s:real^N->bool) SUBSET j` THEN ASM_REWRITE_TAC[SUBSET] THEN
    MESON_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  USE_THEN "Sonto" (MP_TAC o SPEC `a:real^N`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`n:num`; `S:num->real^N`; `i:num`] MOI_S4L_CYCLE_PRED) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "two" (MP_TAC o SPEC `a:real^N`) THEN
  ANTS_TAC THENL [EXPAND_TAC "V" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  EXPAND_TAC "V" THEN EXPAND_TAC "R" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `z:real^N`
    (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (CONJUNCTS_THEN2 STRIP_ASSUME_TAC (LABEL_TAC "uniq")))))))) THEN
  USE_THEN "Sfacts" (MP_TAC o SPEC `i:num`) THEN
  USE_THEN "Sfacts" (MP_TAC o SPEC `p:num`) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `((S:num->real^N)(SUC i) = y \/ S(SUC i) = z) /\
                ((S:num->real^N) p = y \/ S p = z) /\ (b = y \/ b = z)`
  ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "uniq" MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SEGMENT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN `b = (S:num->real^N)(SUC i) \/ b = S p` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `segment[(S:num->real^N) i,S(SUC i)]` THEN
    CONJ_TAC THENL [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[];
    EXISTS_TAC `segment[(S:num->real^N) p,S(SUC p)]` THEN
    CONJ_TAC THENL [EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[SEGMENT_SYM]]);;

let MOI_S4L_CM1_CIRCLES = prove
 (`!K:(real^N->bool)->bool.
     2 <= dimindex(:N) /\ simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     (!v. {v} IN K ==> CARD {e | e IN K /\ aff_dim e = &1 /\ v IN e} = 2)
     ==> FINITE(components(UNIONS K)) /\
         !j. j IN components(UNIONS K) ==> pl_sphere 1 j`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `IMAGE (\s. connected_component (UNIONS K) (CHOICE s))
                      {s:real^N->bool | s IN K /\ ~(s = {})}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_RESTRICT THEN
      ASM_MESON_TAC[simplicial_complex];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; components; IN_ELIM_THM; IN_IMAGE] THEN
    X_GEN_TAC `c:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_UNIONS]) THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET connected_component (UNIONS K) (CHOICE s)`
    MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CHOICE_DEF THEN ASM SET_TAC[];
        ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; CONVEX_CONNECTED];
        ASM SET_TAC[]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `j:real^N->bool`] MOI_S4L_CM1_CYCLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `S:num->real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(S:num->real^N)(SUC(n - 1)) = S 0` ASSUME_TAC THENL
   [SUBGOAL_THEN `SUC(n - 1) = 0 + n` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `n - 1`; `S:num->real^N`]
    MOI_SLV_POLYGON_SPHERE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [FIRST_ASSUM ACCEPT_TAC;
      FIRST_ASSUM ACCEPT_TAC;
      ASM_ARITH_TAC;
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_ARITH_TAC;
      ASM_MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [th]) o
    check (fun th -> is_eq(concl th) && lhs(concl th) = `j:real^N->bool`)) THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  SUBGOAL_THEN `!i. i < n <=> i < n - 1 \/ i = n - 1` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Triangulations with line charts, and the instance of transverse          *)
(* crossings of two sets in real^3 (pl_crossing_at).                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4L_LINE_CHART_COMPLEX = prove
 (`!(t:real^N->bool) p.
     pl_polyhedron t /\ moi_s4l_line_charts t /\ FINITE p /\ p SUBSET t
     ==> ?K. simplicial_complex K /\ UNIONS K = t /\
             (!s. s IN K ==> aff_dim s <= &1) /\
             (!v. {v} IN K ==> CARD {e | e IN K /\ aff_dim e = &1 /\ v IN e} = 2) /\
             (!x. x IN p ==> {x} IN K)`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX]) THEN
  DISCH_THEN(X_CHOOSE_THEN `K0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`K0:(real^N->bool)->bool`; `IMAGE (\x:real^N. {x}) p`]
    SIMPLICIAL_COMPLEX_REFINE_POLYTOPES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE; POLYTOPE_SING] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (K ALL_TAC)
      (CONJUNCTS_THEN2 (K ALL_TAC) (LABEL_TAC "pts")))))) THEN
  EXISTS_TAC `K:(real^N->bool)->bool` THEN
  SUBGOAL_THEN `UNIONS K = (t:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_s4l_line_charts (UNIONS K:real^N->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_LC_DIM_LE1];
    ASM_MESON_TAC[MOI_S4L_LC_DEGREE_2];
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "pts" (MP_TAC o SPEC `{x:real^N}`) THEN
    ANTS_TAC THENL [REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?s:real^N->bool. s IN f /\ x IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `s = {x:real^N}` (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
    ASM SET_TAC[]]);;

let MOI_S4L_LINE_CHART_CIRCLES = prove
 (`!t:real^N->bool.
     2 <= dimindex(:N) /\ pl_polyhedron t /\ moi_s4l_line_charts t
     ==> FINITE(components t) /\ !j. j IN components t ==> pl_sphere 1 j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `{}:real^N->bool`] MOI_S4L_LINE_CHART_COMPLEX) THEN
  ASM_REWRITE_TAC[FINITE_EMPTY; EMPTY_SUBSET; NOT_IN_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `K:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rhs(concl th) = `t:real^N->bool`)) THEN
  MATCH_MP_TAC MOI_S4L_CM1_CIRCLES THEN ASM_REWRITE_TAC[]);;

let MOI_S4L_PL_POLYHEDRON_UNIONS = prove
 (`!f:(real^N->bool)->bool.
     FINITE f /\ (!s. s IN f ==> pl_polyhedron s) ==> pl_polyhedron(UNIONS f)`,
  REWRITE_TAC[IMP_CONJ] THEN MATCH_MP_TAC FINITE_INDUCT_STRONG THEN
  REWRITE_TAC[UNIONS_0; UNIONS_INSERT; FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `{}:(real^N->bool)->bool` THEN
    REWRITE_TAC[FINITE_EMPTY; NOT_IN_EMPTY; UNIONS_0];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC PL_POLYHEDRON_UNION THEN ASM_SIMP_TAC[]]);;

let MOI_S4L_POLYTOPE_AFFINE_PIECE = prove
 (`!(g:real^M->real^N) k l y.
     polytope k /\ linear l /\ (!z. z IN k ==> g z = l z + y)
     ==> polytope(IMAGE g k)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (g:real^M->real^N) k = IMAGE (\x. y + x) (IMAGE l k)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_IMAGE] THEN ASM_MESON_TAC[VECTOR_ADD_SYM];
    ASM_SIMP_TAC[POLYTOPE_TRANSLATION_EQ; POLYTOPE_LINEAR_IMAGE]]);;

let MOI_S4L_IN_SEGMENT_AXIS = prove
 (`!(a:real^N) c r. abs c <= r /\ &0 < r ==> c % a IN segment[--(r % a),r % a]`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_SEGMENT] THEN
  EXISTS_TAC `(c / r + &1) / &2` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC REAL_LE_DIV THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    MATCH_MP_TAC(REAL_ARITH `--(&1) <= x ==> &0 <= x + &1`) THEN
    ASM_SIMP_TAC[REAL_LE_RDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC(REAL_ARITH `x <= &1 ==> (x + &1) / &2 <= &1`) THEN
    ASM_SIMP_TAC[REAL_LE_LDIV_EQ] THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[VECTOR_ARITH
     `(&1 - u) % --(r % a) + u % (r % a):real^N = ((&2 * u - &1) * r) % a`] THEN
    AP_THM_TAC THEN AP_TERM_TAC THEN
    UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD]);;

let MOI_S4L_AXIS3 = prove
 (`(!y:real^3. y$1 = &0 /\ y$2 = &0 <=> y = (y$3) % basis 3) /\
   (!c. (c % basis 3:real^3)$1 = &0 /\ (c % basis 3:real^3)$2 = &0 /\
        (c % basis 3:real^3)$3 = c) /\
   (!c. norm(c % basis 3:real^3) = abs c) /\
   linear (\r:real^1. drop r % basis 3:real^3)`,
  REPEAT CONJ_TAC THENL
   [GEN_TAC THEN REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    SIMP_TAC[VECTOR_MUL_COMPONENT; BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN
    REAL_ARITH_TAC;
    SIMP_TAC[NORM_MUL; NORM_BASIS; DIMINDEX_3; ARITH; REAL_MUL_RID];
    MP_TAC(ISPECL [`\x:real^1. x`; `basis 3:real^3`] LINEAR_VMUL_DROP) THEN
    REWRITE_TAC[LINEAR_ID]]);;

let MOI_S4L_CROSSING_IMAGE = prove
 (`!(s:real^3->bool) m u (f:real^3->real^3) g.
     homeomorphism (u,IMAGE f u) (f,g) /\
     IMAGE f (s INTER u) = IMAGE f u INTER {y:real^3 | y$1 = &0} /\
     IMAGE f (m INTER u) = IMAGE f u INTER {y:real^3 | y$2 = &0}
     ==> IMAGE f ((s INTER m) INTER u) =
         IMAGE f u INTER {y:real^3 | y$1 = &0 /\ y$2 = &0}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `IMAGE (f:real^3->real^3) (s INTER u) INTER IMAGE f (m INTER u)` THEN
  CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [homeomorphism]) THEN
    SET_TAC[];
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_S4L_CROSSING_LINE_CHART = prove
 (`!(s:real^3->bool) m x.
     pl_crossing_at s m x
     ==> ?u (h:real^3->real^1) h'.
           open u /\ x IN u /\
           homeomorphism ((s INTER m) INTER u,IMAGE h ((s INTER m) INTER u)) (h,h') /\
           open (IMAGE h ((s INTER m) INTER u))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_crossing_at; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `m:real^3->bool`; `u:real^3->bool`;
                 `f:real^3->real^3`; `g:real^3->real^3`] MOI_S4L_CROSSING_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!z:real^3. z IN (s INTER m) INTER u
               ==> (f:real^3->real^3) z = ((f z)$3) % basis 3`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM(CONJUNCT1 MOI_S4L_AXIS3)] THEN
    SUBGOAL_THEN `(f:real^3->real^3) z IN IMAGE f ((s INTER m) INTER u)` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (\z:real^3. lift(((f:real^3->real^3) z)$3)) ((s INTER m) INTER u) =
    {r:real^1 | drop r % basis 3 IN IMAGE f u}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `r:real^1` THEN
    EQ_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[LIFT_DROP] THEN EXISTS_TAC `z:real^3` THEN
      RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN ASM_MESON_TAC[IN_INTER];
      DISCH_TAC THEN
      SUBGOAL_THEN `drop r % basis 3 IN
                    IMAGE (f:real^3->real^3) ((s INTER m) INTER u)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; MOI_S4L_AXIS3]; ALL_TAC] THEN
      REWRITE_TAC[IN_IMAGE] THEN MATCH_MP_TAC MONO_EXISTS THEN
      X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `drop r % basis 3 = (f:real^3->real^3) z` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[MOI_S4L_AXIS3; LIFT_DROP]];
    ALL_TAC] THEN
  EXISTS_TAC `u:real^3->bool` THEN
  EXISTS_TAC `\z:real^3. lift(((f:real^3->real^3) z)$3)` THEN
  EXISTS_TAC `\r:real^1. (g:real^3->real^3)(drop r % basis 3)` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC;
    UNDISCH_TAC
     `IMAGE (\z:real^3. lift(((f:real^3->real^3) z)$3)) ((s INTER m) INTER u) =
      {r:real^1 | drop r % basis 3 IN IMAGE f u}` THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE_UNIV THEN ASM_REWRITE_TAC[] THEN
    GEN_TAC THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN REWRITE_TAC[MOI_S4L_AXIS3]] THEN
  SUBGOAL_THEN
   `!z:real^3. z IN (s INTER m) INTER u
               ==> (g:real^3->real^3)(drop(lift(((f:real^3->real^3) z)$3)) % basis 3) = z`
  ASSUME_TAC THENL
   [REWRITE_TAC[LIFT_DROP] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `((f:real^3->real^3) z)$3 % basis 3 = f z` SUBST1_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[homeomorphism] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MATCH_MP_TAC CONTINUOUS_ON_LIFT_COMPONENT_COMPOSE THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[FORALL_IN_IMAGE] THEN ASM_SIMP_TAC[];
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `IMAGE (\x:real^3. x) ((s INTER m) INTER u)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(!x. x IN s ==> f x = x) ==> IMAGE f s = IMAGE (\x:real^3. x) s`) THEN
      ASM_SIMP_TAC[];
      REWRITE_TAC[IMAGE_ID]];
    UNDISCH_TAC
     `IMAGE (\z:real^3. lift(((f:real^3->real^3) z)$3)) ((s INTER m) INTER u) =
      {r:real^1 | drop r % basis 3 IN IMAGE f u}` THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN
     `(\r:real^1. (g:real^3->real^3)(drop r % basis 3)) =
      g o (\r. drop r % basis 3)` SUBST1_TAC THENL
     [REWRITE_TAC[o_DEF]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
     [MATCH_MP_TAC LINEAR_CONTINUOUS_ON THEN REWRITE_TAC[MOI_S4L_AXIS3];
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN SIMP_TAC[]]]);;

let MOI_S4L_AXIS_IN_SEGMENT3 = prove
 (`!(y:real^3) r.
     y$1 = &0 /\ y$2 = &0 /\ norm y < r
     ==> y IN segment[--(r % basis 3),r % basis 3]`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONJ_ASSOC; CONJUNCT1 MOI_S4L_AXIS3] THEN
  STRIP_TAC THEN
  FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [th]) o
    check (fun th -> is_eq(concl th) && lhs(concl th) = `y:real^3`)) THEN
  MATCH_MP_TAC MOI_S4L_IN_SEGMENT_AXIS THEN
  SUBGOAL_THEN `norm(y:real^3) = abs(y$3)` ASSUME_TAC THENL
   [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) o
      check (fun th -> is_eq(concl th) && lhs(concl th) = `y:real^3`)) THEN
    REWRITE_TAC[MOI_S4L_AXIS3];
    ASM_REAL_ARITH_TAC]);;

let MOI_S4L_CROSSING_LOCAL_PIECE = prove
 (`!(s:real^3->bool) m x.
     pl_crossing_at s m x
     ==> ?w p. open w /\ x IN w /\ (s INTER m) INTER w SUBSET p /\
               p SUBSET s INTER m /\ pl_polyhedron p`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_crossing_at; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
    (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `m:real^3->bool`; `u:real^3->bool`;
                 `f:real^3->real^3`; `g:real^3->real^3`] MOI_S4L_CROSSING_IMAGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `?r. &0 < r /\ cball(vec 0:real^3,r) SUBSET IMAGE (f:real^3->real^3) u`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open(IMAGE (f:real^3->real^3) u)` THEN
    REWRITE_TAC[OPEN_CONTAINS_CBALL] THEN DISCH_THEN MATCH_MP_TAC THEN
    UNDISCH_TAC `(f:real^3->real^3) x = vec 0` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[--(r % basis 3),r % basis 3] SUBSET
    IMAGE (f:real^3->real^3) ((s INTER m) INTER u)`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `cball(vec 0:real^3,r)` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`vec 0:real^3`; `r:real`] CONVEX_CBALL) THEN
      REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
      REWRITE_TAC[IN_CBALL_0; NORM_NEG; MOI_S4L_AXIS3] THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_SEGMENT; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                      VECTOR_NEG_COMPONENT; MOI_S4L_AXIS3] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`{z:real^3 | z IN u /\ (f:real^3->real^3) z IN ball(vec 0,r)}`;
    `IMAGE (g:real^3->real^3) (segment[--(r % basis 3),r % basis 3])`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `u:real^3->bool` THEN
    ASM_SIMP_TAC[CONTINUOUS_OPEN_IN_PREIMAGE; OPEN_BALL];
    ASM_REWRITE_TAC[IN_ELIM_THM; CENTRE_IN_BALL];
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM] THEN X_GEN_TAC `z:real^3` THEN
    STRIP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(f:real^3->real^3) z` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4L_AXIS_IN_SEGMENT3 THEN
    SUBGOAL_THEN `(f:real^3->real^3) z IN IMAGE f ((s INTER m) INTER u)` MP_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    UNDISCH_TAC `(f:real^3->real^3) z IN ball(vec 0,r)` THEN
    ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0] THEN SIMP_TAC[];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (f:real^3->real^3) ((s INTER m) INTER u)`
    MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(g:real^3->real^3) y = z` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (segment[--(r % basis 3),r % basis 3]) (g:real^3->real^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `IMAGE (f:real^3->real^3) u` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC LOCALLY_POLYHEDRAL_POLYTOPE THEN REWRITE_TAC[POLYTOPE_SEGMENT]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`segment[--(r % basis 3),r % basis 3]:real^3->bool`;
                 `g:real^3->real^3`] MOI_PLM_PL_MAP_ON_COMPACT_FINITE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[COMPACT_SEGMENT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^3->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "pieces")))) THEN
  REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `IMAGE (IMAGE (g:real^3->real^3)) c` THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN
    USE_THEN "pieces" (MP_TAC o SPEC `k:real^3->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `l:real^3->real^3` (X_CHOOSE_THEN `y:real^3`
        STRIP_ASSUME_TAC)))) THEN
    MATCH_MP_TAC MOI_S4L_POLYTOPE_AFFINE_PIECE THEN
    MAP_EVERY EXISTS_TAC [`l:real^3->real^3`; `y:real^3`] THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_UNIONS]]);;

let MOI_S4L_CROSSING_POLYHEDRON = prove
 (`!s m:real^3->bool.
     compact(s INTER m) /\ (!x. x IN s INTER m ==> pl_crossing_at s m x)
     ==> pl_polyhedron(s INTER m)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!x:real^3. ?w p. x IN (s:real^3->bool) INTER m
              ==> open w /\ x IN w /\ (s INTER m) INTER w SUBSET p /\
                  p SUBSET s INTER m /\ pl_polyhedron p`
  MP_TAC THENL
   [GEN_TAC THEN ASM_CASES_TAC `(x:real^3) IN s INTER m` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4L_CROSSING_LOCAL_PIECE THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`w:real^3->real^3->bool`; `p:real^3->real^3->bool`] THEN
  DISCH_THEN(LABEL_TAC "loc") THEN
  UNDISCH_TAC `compact(s INTER m:real^3->bool)` THEN
  REWRITE_TAC[COMPACT_EQ_HEINE_BOREL] THEN
  DISCH_THEN(MP_TAC o SPEC `IMAGE (w:real^3->real^3->bool) (s INTER m)`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[FORALL_IN_IMAGE; SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
      USE_THEN "loc" (MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
      X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN EXISTS_TAC `x:real^3` THEN
      ASM_REWRITE_TAC[] THEN
      USE_THEN "loc" (MP_TAC o SPEC `x:real^3`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ff:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`w:real^3->real^3->bool`; `s INTER m:real^3->bool`;
                 `ff:(real^3->bool)->bool`] FINITE_SUBSET_IMAGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `fs:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `s INTER m = UNIONS (IMAGE (p:real^3->real^3->bool) fs)`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN X_GEN_TAC `x:real^3` THEN
      DISCH_TAC THEN
      SUBGOAL_THEN `?y:real^3. y IN fs /\ (x:real^3) IN (w:real^3->real^3->bool) y`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `s INTER m SUBSET UNIONS (ff:(real^3->bool)->bool)` THEN
        ASM_REWRITE_TAC[SUBSET; IN_UNIONS; EXISTS_IN_IMAGE] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `y:real^3` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_INTER] THEN ASM_MESON_TAC[IN_INTER];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `y:real^3` THEN
      DISCH_TAC THEN USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S4L_PL_POLYHEDRON_UNIONS THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; SIMP_TAC[]]);;

let MOI_S4L_CROSSING_CHARTS = prove
 (`!s m:real^3->bool.
     (!x. x IN s INTER m ==> pl_crossing_at s m x)
     ==> moi_s4l_line_charts (s INTER m)`,
  REWRITE_TAC[moi_s4l_line_charts] THEN MESON_TAC[MOI_S4L_CROSSING_LINE_CHART]);;

let MOI_S4L_CROSSING_CIRCLES = prove
 (`!s m:real^3->bool.
     compact(s INTER m) /\ (!x. x IN s INTER m ==> pl_crossing_at s m x)
     ==> FINITE(components(s INTER m)) /\
         !j. j IN components(s INTER m) ==> pl_sphere 1 j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S4L_LINE_CHART_CIRCLES THEN
  ASM_SIMP_TAC[DIMINDEX_3; ARITH; MOI_S4L_CROSSING_POLYHEDRON;
               MOI_S4L_CROSSING_CHARTS]);;

(* ------------------------------------------------------------------------- *)
(* Pieces of a PL circle between consecutive marked points.  For a simple    *)
(* closed PL loop g with a finite set p of at least two marked points on it  *)
(* and a point x of the loop outside p, there is a PL arc h on the loop      *)
(* through x whose ends are marked, with no other marked point, and whose    *)
(* interior is open in the loop (its complement in the loop is closed).      *)
(* ------------------------------------------------------------------------- *)

let MOI_P1M_LOOP_ARC_COMPLEMENT = prove
 (`!(g:real^1->real^N) t1 t2.
     simple_path g /\ &0 <= t1 /\ t1 < t2 /\ t2 <= &1 /\ ~(g(lift t1) = g(lift t2))
     ==> path_image g DIFF
         (IMAGE g (interval[lift t1,lift t2]) DIFF {g(lift t1),g(lift t2)}) =
         IMAGE g (interval[vec 0,lift t1] UNION interval[lift t2,vec 1])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                      (g:real^1->real^N) s = g t /\ &0 < drop s /\ drop s < &1
                      ==> s = t`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `simple_path (g:real^1->real^N)` THEN REWRITE_TAC[simple_path] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^1`; `t:real^1`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < drop(s:real^1)` THEN UNDISCH_TAC `drop(s:real^1) < &1` THEN
    ASM_REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[path_image; EXTENSION; IN_DIFF; IN_IMAGE; IN_UNION; IN_INSERT;
                NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC)
        (LABEL_TAC "notb")) THEN
      EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN STRIP_TAC THEN
      ASM_CASES_TAC `drop(t:real^1) <= t1` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `t2 <= drop(t:real^1)` THEN ASM_REWRITE_TAC[] THEN
      USE_THEN "notb" MP_TAC THEN REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC;
        REWRITE_TAC[DE_MORGAN_THM] THEN CONJ_TAC THEN DISCH_TAC THENL
         [USE_THEN "inj" (MP_TAC o SPECL [`t:real^1`; `lift t1`]);
          USE_THEN "inj" (MP_TAC o SPECL [`t:real^1`; `lift t2`])] THEN
        (ANTS_TAC THENL
          [REPEAT CONJ_TAC THENL
            [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
             REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
             ASM_MESON_TAC[];
             ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
           ALL_TAC]) THEN
        DISCH_THEN(MP_TAC o AP_TERM `drop`) THEN REWRITE_TAC[LIFT_DROP] THEN
        ASM_REAL_ARITH_TAC];
      DISCH_THEN(X_CHOOSE_THEN `t:real^1` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "tin"))) THEN
      SUBGOAL_THEN `(t:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
       [USE_THEN "tin" MP_TAC THEN REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL [EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[TAUT `~(p /\ ~q) <=> p ==> q`] THEN
      DISCH_THEN(X_CHOOSE_THEN `t':real^1` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(t':real^1) IN interval[lift t1,lift t2]` THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
      ASM_CASES_TAC `drop(t':real^1) = t1` THENL
       [DISJ1_TAC THEN UNDISCH_TAC `(y:real^N) = g(t':real^1)` THEN
        DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
        ASM_REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP];
        ALL_TAC] THEN
      ASM_CASES_TAC `drop(t':real^1) = t2` THENL
       [DISJ2_TAC THEN UNDISCH_TAC `(y:real^N) = g(t':real^1)` THEN
        DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
        ASM_REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP];
        ALL_TAC] THEN
      USE_THEN "inj" (MP_TAC o SPECL [`t':real^1`; `t:real^1`]) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
          FIRST_ASSUM ACCEPT_TAC;
          UNDISCH_TAC `(y:real^N) = g(t':real^1)` THEN
          UNDISCH_TAC `(y:real^N) = g(t:real^1)` THEN MESON_TAC[];
          ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
        DISCH_THEN SUBST_ALL_TAC THEN USE_THEN "tin" MP_TAC THEN
        REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC]]);;

let MOI_P1M_LOOP_PIECE0 = prove
 (`!(g:real^1->real^N) p x.
     simple_path g /\ pathfinish g = pathstart g /\
     pl_map_on (interval[vec 0,vec 1]) g /\ pathstart g IN p /\
     FINITE p /\ p SUBSET path_image g /\ 2 <= CARD p /\
     x IN path_image g /\ ~(x IN p)
     ==> ?h. arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\
             path_image h SUBSET path_image g /\ x IN path_image h /\
             pathstart h IN p /\ pathfinish h IN p /\
             path_image h INTER p = {pathstart h,pathfinish h} /\
             closed(path_image g DIFF (path_image h DIFF {pathstart h,pathfinish h}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                      (g:real^1->real^N) s = g t /\ &0 < drop s /\ drop s < &1
                      ==> s = t`
  (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `simple_path (g:real^1->real^N)` THEN REWRITE_TAC[simple_path] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^1`; `t:real^1`] o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < drop(s:real^1)` THEN UNDISCH_TAC `drop(s:real^1) < &1` THEN
    ASM_REWRITE_TAC[DROP_VEC] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?t0. t0 IN interval[vec 0,vec 1] /\ (g:real^1->real^N) t0 = x`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN path_image g` THEN REWRITE_TAC[path_image; IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^1->real^N)(vec 0) IN p /\ g(vec 1) IN p` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[pathstart; pathfinish]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < drop t0 /\ drop t0 < &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(t0:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN
    SUBGOAL_THEN `~(t0:real^1 = vec 0) /\ ~(t0 = vec 1)` MP_TAC THENL
     [ASM_MESON_TAC[]; REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `ts = {drop t | t IN interval[vec 0,vec 1] /\ (g:real^1->real^N) t IN p}` THEN
  SUBGOAL_THEN `FINITE(ts:real->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN
    SUBGOAL_THEN `{drop t | t IN interval[vec 0,vec 1] /\ (g:real^1->real^N) t IN p} =
                  IMAGE drop {t | t IN interval[vec 0,vec 1] /\ g t IN p}` SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_IMAGE] THEN MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `(vec 1:real^1) INSERT
                {t | t IN interval[vec 0,vec 1] /\ ~(t = vec 1) /\ (g:real^1->real^N) t IN p}` THEN
    CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN REWRITE_TAC[FINITE_INSERT] THEN
    MP_TAC(ISPECL [`g:real^1->real^N`;
                   `{t | t IN interval[vec 0,vec 1] /\ ~(t = vec 1) /\ (g:real^1->real^N) t IN p}`]
      FINITE_IMAGE_INJ_EQ) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      UNDISCH_TAC `simple_path (g:real^1->real^N)` THEN REWRITE_TAC[simple_path] THEN
      DISCH_THEN(MP_TAC o SPECL [`x':real^1`; `y:real^1`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `p:real^N->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r IN ts ==> &0 <= r /\ r <= &1 /\ ~(r = drop t0)` ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `r:real` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN SUBGOAL_THEN `t:real^1 = t0` SUBST_ALL_TAC THENL
     [ASM_REWRITE_TAC[GSYM DROP_EQ]; ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 IN ts /\ &1 IN ts` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
     [EXISTS_TAC `vec 0:real^1`; EXISTS_TAC `vec 1:real^1`] THEN
    ASM_REWRITE_TAC[DROP_VEC; ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{r | r IN ts /\ r < drop(t0:real^1)}` SUP_FINITE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ts:real->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `&0` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `t1 = sup {r | r IN ts /\ r < drop(t0:real^1)}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `{r | r IN ts /\ drop(t0:real^1) < r}` INF_FINITE) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ts:real->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN EXISTS_TAC `&1` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `t2 = inf {r | r IN ts /\ drop(t0:real^1) < r}` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r. r IN ts ==> r <= t1 \/ t2 <= r` (LABEL_TAC "gap") THENL
   [X_GEN_TAC `r:real` THEN DISCH_TAC THEN
    ASM_CASES_TAC `r < drop(t0:real^1)` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISJ2_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[REAL_ARITH `~(r < t) /\ ~(r = t) ==> t < r`];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= t1 /\ t1 < drop(t0:real^1) /\ drop t0 < t2 /\ t2 <= &1`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(g:real^1->real^N)(lift t1) IN p /\ g(lift t2) IN p` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(t1:real) IN ts` THEN UNDISCH_TAC `(t2:real) IN ts` THEN EXPAND_TAC "ts" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `u2:real^1` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^1` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[LIFT_DROP];
    ALL_TAC] THEN
  SUBGOAL_THEN `lift t1 IN interval[vec 0,vec 1] /\ lift t2 IN interval[vec 0,vec 1]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((g:real^1->real^N)(lift t1) = g(lift t2))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `t1 = &0 /\ t2 = &1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `simple_path (g:real^1->real^N)` THEN REWRITE_TAC[simple_path] THEN
      DISCH_THEN(MP_TAC o SPECL [`lift t1`; `lift t2`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `p SUBSET {(g:real^1->real^N)(vec 0)}` MP_TAC THENL
     [REWRITE_TAC[SUBSET; IN_SING] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
      SUBGOAL_THEN `?t. t IN interval[vec 0,vec 1] /\ (g:real^1->real^N) t = y`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `p SUBSET path_image (g:real^1->real^N)` THEN
        REWRITE_TAC[SUBSET; path_image; IN_IMAGE] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `drop t IN ts` ASSUME_TAC THENL
       [EXPAND_TAC "ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      USE_THEN "gap" (MP_TAC o SPEC `drop t`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
      DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
       [SUBGOAL_THEN `t = vec 0:real^1` SUBST_ALL_TAC THENL
         [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REAL_ARITH_TAC; ASM_MESON_TAC[]];
        SUBGOAL_THEN `t = vec 1:real^1` SUBST_ALL_TAC THENL
         [REWRITE_TAC[GSYM DROP_EQ; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
          ASM_MESON_TAC[pathstart; pathfinish]]];
      DISCH_TAC THEN
      SUBGOAL_THEN `CARD(p:real^N->bool) <= CARD {(g:real^1->real^N)(vec 0)}` MP_TAC THENL
       [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_SING]; ALL_TAC] THEN
      REWRITE_TAC[CARD_SING] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  EXISTS_TAC `subpath (lift t1) (lift t2) (g:real^1->real^N)` THEN
  SUBGOAL_THEN `path_image(subpath (lift t1) (lift t2) (g:real^1->real^N)) =
                IMAGE g (interval[lift t1,lift t2])` SUBST1_TAC THENL
   [MATCH_MP_TAC PATH_IMAGE_SUBPATH THEN REWRITE_TAC[LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  ASM_SIMP_TAC[ARC_SIMPLE_PATH_SUBPATH; MOI_PL2_PL_SUBPATH] THEN
  SUBGOAL_THEN `interval[lift t1,lift t2] SUBSET interval[vec 0,vec 1]` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!t. t IN interval[vec 0,vec 1] /\ t1 < drop t /\ drop t < t2
                    ==> ~((g:real^1->real^N) t IN p)` (LABEL_TAC "nomark") THENL
   [X_GEN_TAC `t:real^1` THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `drop t IN ts` ASSUME_TAC THENL
     [EXPAND_TAC "ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    USE_THEN "gap" (MP_TAC o SPEC `drop t`) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[path_image] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `t0:real^1` THEN
    ASM_REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [ALL_TAC; REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY; IN_INTER; IN_IMAGE] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [EXISTS_TAC `lift t1`; EXISTS_TAC `lift t2`] THEN
      REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC] THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    SUBGOAL_THEN `(t:real^1) IN interval[vec 0,vec 1]` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`(t:real^1) IN interval[lift t1,lift t2]`;
        `interval[lift t1,lift t2] SUBSET interval[vec 0:real^1,vec 1]`] THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(t:real^1) IN interval[lift t1,lift t2]` THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN STRIP_TAC THEN
    ASM_CASES_TAC `drop(t:real^1) = t1` THENL
     [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP];
      ALL_TAC] THEN
    ASM_CASES_TAC `drop(t:real^1) = t2` THENL
     [DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
      ASM_REWRITE_TAC[GSYM DROP_EQ; LIFT_DROP];
      ALL_TAC] THEN
    USE_THEN "nomark" (MP_TAC o SPEC `t:real^1`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(y:real^N) IN p` THEN UNDISCH_TAC `(y:real^N) = g(t:real^1)` THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^1->real^N`; `t1:real`; `t2:real`] MOI_P1M_LOOP_ARC_COMPLEMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
  SIMP_TAC[COMPACT_UNION; COMPACT_INTERVAL] THEN
  MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `simple_path (g:real^1->real^N)` THEN SIMP_TAC[simple_path; path];
    REWRITE_TAC[UNION_SUBSET; SUBSET_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_P1M_LOOP_PIECE = prove
 (`!(g:real^1->real^N) p x.
     simple_path g /\ pathfinish g = pathstart g /\
     pl_map_on (interval[vec 0,vec 1]) g /\
     FINITE p /\ p SUBSET path_image g /\ 2 <= CARD p /\
     x IN path_image g /\ ~(x IN p)
     ==> ?h. arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\
             path_image h SUBSET path_image g /\ x IN path_image h /\
             pathstart h IN p /\ pathfinish h IN p /\
             path_image h INTER p = {pathstart h,pathfinish h} /\
             closed(path_image g DIFF (path_image h DIFF {pathstart h,pathfinish h}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?a. a IN interval[vec 0,vec 1] /\ (g:real^1->real^N) a IN p`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(p:real^N->bool = {})` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `2 <= CARD(p:real^N->bool)` THEN
      ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
    UNDISCH_TAC `p SUBSET path_image (g:real^1->real^N)` THEN
    REWRITE_TAC[SUBSET; path_image; IN_IMAGE] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= drop a /\ drop a <= &1` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(a:real^1) IN interval[vec 0,vec 1]` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image(shiftpath a (g:real^1->real^N)) = path_image g` ASSUME_TAC THENL
   [ASM_SIMP_TAC[PATH_IMAGE_SHIFTPATH]; ALL_TAC] THEN
  MP_TAC(ISPECL [`shiftpath a (g:real^1->real^N)`; `p:real^N->bool`; `x:real^N`]
    MOI_P1M_LOOP_PIECE0) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_SIMP_TAC[SIMPLE_PATH_SHIFTPATH; MOI_PL2_PL_SHIFTPATH; PATHSTART_SHIFTPATH;
                 PATHFINISH_SHIFTPATH];
    DISCH_THEN(fun th -> REWRITE_TAC[th])]);;

(* A PL sub-arc of a PL arc between two of its points; it avoids an end of *)
(* the big arc unless that end is one of the two points.                  *)
let MOI_P1M_SUBARC = prove
 (`!(h:real^1->real^N) a b.
     arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\
     a IN path_image h /\ b IN path_image h /\ ~(a = b)
     ==> ?k. arc k /\ pl_map_on (interval[vec 0,vec 1]) k /\
             pathstart k = a /\ pathfinish k = b /\
             path_image k SUBSET path_image h /\
             (~(a = pathstart h) /\ ~(b = pathstart h)
              ==> ~(pathstart h IN path_image k)) /\
             (~(a = pathfinish h) /\ ~(b = pathfinish h)
              ==> ~(pathfinish h IN path_image k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?s t. s IN interval[vec 0,vec 1] /\ t IN interval[vec 0,vec 1] /\
                      (h:real^1->real^N) s = a /\ h t = b`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(a:real^N) IN path_image h`; `(b:real^N) IN path_image h`] THEN
    REWRITE_TAC[path_image; IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s:real^1 = t)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[s:real^1,t] SUBSET interval[vec 0,vec 1]` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    ASM_REWRITE_TAC[CONVEX_INTERVAL; INSERT_SUBSET; EMPTY_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^1. u IN segment[s,t] /\ (u = vec 0 \/ u = vec 1) ==> u = s \/ u = t`
  (LABEL_TAC "ends") THENL
   [X_GEN_TAC `u:real^1` THEN
    MAP_EVERY UNDISCH_TAC [`(s:real^1) IN interval[vec 0,vec 1]`;
                           `(t:real^1) IN interval[vec 0,vec 1]`] THEN
    REWRITE_TAC[SEGMENT_1] THEN COND_CASES_TAC THEN
    REWRITE_TAC[IN_INTERVAL_1; GSYM DROP_EQ; DROP_VEC] THEN
    UNDISCH_TAC `~(s:real^1 = t)` THEN REWRITE_TAC[GSYM DROP_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!u v:real^1. u IN segment[s,t] /\ v IN interval[vec 0,vec 1] /\
                           (h:real^1->real^N) u = h v ==> u = v` (LABEL_TAC "inj") THENL
   [REPEAT STRIP_TAC THEN UNDISCH_TAC `arc(h:real^1->real^N)` THEN REWRITE_TAC[arc] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `subpath s t (h:real^1->real^N)` THEN
  ASM_SIMP_TAC[ARC_SUBPATH_ARC; MOI_PL2_PL_SUBPATH; PATH_IMAGE_SUBPATH_GEN;
               PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[path_image] THEN MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[pathstart; IN_IMAGE; NOT_EXISTS_THM] THEN STRIP_TAC THEN
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    USE_THEN "inj" (MP_TAC o SPECL [`u:real^1`; `vec 0:real^1`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]; DISCH_TAC] THEN
    USE_THEN "ends" (MP_TAC o SPEC `u:real^1`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]];
    REWRITE_TAC[pathfinish; IN_IMAGE; NOT_EXISTS_THM] THEN STRIP_TAC THEN
    X_GEN_TAC `u:real^1` THEN STRIP_TAC THEN
    USE_THEN "inj" (MP_TAC o SPECL [`u:real^1`; `vec 1:real^1`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL]; DISCH_TAC] THEN
    USE_THEN "ends" (MP_TAC o SPEC `u:real^1`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[]; ASM_MESON_TAC[]]]);;

