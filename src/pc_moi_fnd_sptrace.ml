(* ========================================================================= *)
(* pc_moi_fnd_sptrace: the trace annulus in the split of                    *)
(* MOI_FND_SPLIT_DISK_R3 (Moise 28.19, p.209): the trace of the             *)
(* second-derived neighbourhood of a disk on a closed surface meeting it in *)
(* its rim is an annulus around the rim.  Route: the trace identity and the *)
(* 2D derived neighbourhood of a polygon (pc_moi_fnd_nb2), and the          *)
(* two-sidedness of the band by orientation transfer: the side of the       *)
(* surface where the disk lies, together with the orientation of real^3,    *)
(* orients the vertex stars of the rim coherently, so the band around the   *)
(* rim is not a Moebius band.  Main theorem: SPLIT_TRACE_ANNULUS =          *)
(*   MOI_FSTR_SPLIT_TRACE_COND :                                             *)
(*     |- S4 at N = 3 ==> MOI_FND_SPLIT_TRACE_ANNULUS,                       *)
(* with S4 = MOI_FND_DERIVED_NBHD_POLYGON_2 (terms of pc_moi_fnd_stmt3).     *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt3.ml";;
needs "src/pc_moi_comb.ml";;
needs "src/pc_moi_cone_sides.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_fnd_surfa.ml";;
needs "src/pc_moi_pl1m.ml";;
needs "src/pc_moi_smo_base.ml";;
needs "src/pc_moi_fnd_sgn.ml";;
needs "src/pc_moi_fnd_nb2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The disk side near a rim point: if a disk d (chart f from a closed convex *)
(* set k, rim j the image of the relative frontier) is radially closed      *)
(* toward a rim point x in a ball, and the rim near x consists of full      *)
(* radial segments, then d minus j is connected in that ball.               *)
(* ------------------------------------------------------------------------- *)

let MOI_FSTR_CHART_CONE_CONN = prove
 (`!(f:real^M->real^N) g k d j x r.
     homeomorphism (k,d) (f,g) /\ convex k /\ closed k /\
     j = IMAGE f (relative_frontier k) /\ x IN j /\ &0 < r /\
     (!z s. z IN d /\ z IN ball(x,r) /\ &0 <= s /\ s <= &1 ==> x + s % (z - x) IN d) /\
     (!z s. z IN d /\ z IN ball(x,r) /\ &0 < s /\ s <= &1 /\ x + s % (z - x) IN j
            ==> z IN j)
     ==> connected ((d INTER ball(x,r)) DIFF j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^M->bool) /\
                relative_interior k SUBSET k /\
                (!u. u IN k ==> (u IN relative_frontier k <=> ~(u IN relative_interior k)))`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; RELATIVE_INTERIOR_SUBSET] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* membership in the rim through the chart *)
  SUBGOAL_THEN `!w:real^N. w IN d ==> (w IN j <=> (g:real^N->real^M) w IN relative_frontier k)`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) o
      check (fun th -> is_eq(concl th) && lhs(concl th) = `j:real^N->bool`)) THEN
    REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `u:real^M` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `w:real^N`)) THEN
      SUBGOAL_THEN `(u:real^M) IN k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(g:real^N->real^M) ((f:real^M->real^N) u) = u` SUBST1_TAC THENL
       [ASM_MESON_TAC[]; FIRST_ASSUM ACCEPT_TAC];
      DISCH_TAC THEN EXISTS_TAC `(g:real^N->real^M) w` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN d` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN j` THEN
    FIRST_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) o
      check (fun th -> is_eq(concl th) && lhs(concl th) = `j:real^N->bool`)) THEN
    UNDISCH_TAC `relative_frontier k SUBSET (k:real^M->bool)` THEN
    UNDISCH_TAC `IMAGE (f:real^M->real^N) k = d` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `j:real^N->bool`)) THEN
  SUBGOAL_THEN `(g:real^N->real^M) x IN relative_frontier k` ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^N) IN d`) o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `j:real^N->bool`)) (concl th) &&
      can (find_term ((=) `relative_frontier (k:real^M->bool)`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `y = (g:real^N->real^M) x` THEN
  SUBGOAL_THEN `(f:real^M->real^N) y = x` ASSUME_TAC THENL
   [EXPAND_TAC "y" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^M) IN k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* continuity of f at y and of g at x *)
  SUBGOAL_THEN `?e. &0 < e /\ !u:real^M. u IN k /\ dist(u,y) < e
                                        ==> dist((f:real^M->real^N) u,x) < r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(f:real^M->real^N) continuous_on k` THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `y:real^M`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?h. &0 < h /\ !w:real^N. w IN d /\ dist(w,x) < h
                                        ==> dist((g:real^N->real^M) w,y) < e`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^N->real^M) continuous_on d` THEN
    REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the connected core S near x *)
  ABBREV_TAC `S = IMAGE (f:real^M->real^N) (relative_interior k INTER ball(y,e))` THEN
  SUBGOAL_THEN `connected (S:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `k:real^M->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_INTER THEN
      ASM_SIMP_TAC[CONVEX_RELATIVE_INTERIOR; CONVEX_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:real^N->bool) SUBSET (d INTER ball(x,r)) DIFF j` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_INTER; IN_DIFF; IN_BALL] THEN
    X_GEN_TAC `u:real^M` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(u:real^M) IN k` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `(f:real^M->real^N) u IN d` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      FIRST_X_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME
        `(f:real^M->real^N) u IN d`)]) o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `relative_frontier (k:real^M->bool)`))
            (concl th) && can (find_term ((=) `j:real^N->bool`)) (concl th))) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  (* every point is joined to S by its radial segment *)
  SUBGOAL_THEN
   `!z:real^N. z IN (d INTER ball(x,r)) DIFF j
               ==> segment[x,z] DELETE x SUBSET (d INTER ball(x,r)) DIFF j /\
                   ~((segment[x,z] DELETE x) INTER S = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN REWRITE_TAC[IN_INTER; IN_DIFF; IN_BALL] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(z:real^N = x)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((z:real^N) IN j)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!s. &0 < s /\ s <= &1
                      ==> x + s % (z - x:real^N) IN (d INTER ball(x,r)) DIFF j`
    ASSUME_TAC THENL
     [X_GEN_TAC `s:real` THEN STRIP_TAC THEN
      REWRITE_TAC[IN_INTER; IN_DIFF; IN_BALL] THEN REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
          can (find_term ((=) `&0 <= s`)) (concl th))) THEN
        ASM_REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
        REWRITE_TAC[dist; VECTOR_ARITH `x - (x + s % (z - x)):real^N = --(s % (z - x))`] THEN
        REWRITE_TAC[NORM_NEG; NORM_MUL] THEN
        SUBGOAL_THEN `norm(z - x:real^N) < r` MP_TAC THENL
         [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist]; ALL_TAC] THEN
        SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        MP_TAC(ISPEC `z - x:real^N` NORM_POS_LE) THEN
        UNDISCH_TAC `s <= &1` THEN UNDISCH_TAC `&0 < s` THEN
        POP_ASSUM_LIST(K ALL_TAC) THEN
        REPEAT DISCH_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `&1 * norm(z - x:real^N)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[REAL_MUL_LID]];
        DISCH_TAC THEN UNDISCH_TAC `~((z:real^N) IN j)` THEN REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
          can (find_term ((=) `&0 < s`)) (concl th))) THEN
        EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[IN_BALL]];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DELETE; IN_SEGMENT] THEN X_GEN_TAC `w:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      SUBGOAL_THEN `w:real^N = x + u % (z - x)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(REAL_ARITH `&0 <= u /\ ~(u = &0) ==> &0 < u`) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~(w:real^N = x)` THEN ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    (* a point of the segment close to x *)
    ABBREV_TAC `s = min (&1) (h / (&2 * norm(z - x:real^N)))` THEN
    SUBGOAL_THEN `&0 < norm(z - x:real^N)` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
    SUBGOAL_THEN `&0 < s /\ s <= &1 /\ s * norm(z - x:real^N) < h` STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "s" THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(REAL_ARITH `&0 < a /\ &0 < b ==> &0 < min a b`) THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; MATCH_MP_TAC REAL_LT_DIV THEN ASM_REAL_ARITH_TAC];
        REAL_ARITH_TAC;
        MATCH_MP_TAC REAL_LET_TRANS THEN
        EXISTS_TAC `h / (&2 * norm(z - x:real^N)) * norm(z - x)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC REAL_LE_RMUL THEN CONJ_TAC THENL
           [REAL_ARITH_TAC; REWRITE_TAC[NORM_POS_LE]];
          ASM_SIMP_TAC[REAL_FIELD `&0 < n ==> h / (&2 * n) * n = h / &2`] THEN
          ASM_REAL_ARITH_TAC]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x + s % (z - x:real^N)` THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_DELETE; IN_SEGMENT] THEN CONJ_TAC THENL
       [EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
        REWRITE_TAC[VECTOR_ARITH `x + s % (z - x):real^N = x <=> s % (z - x) = vec 0`] THEN
        ASM_REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    SUBGOAL_THEN `x + s % (z - x:real^N) IN (d INTER ball(x,r)) DIFF j` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_DIFF] THEN STRIP_TAC THEN
    EXPAND_TAC "S" THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `(g:real^N->real^M) (x + s % (z - x))` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INTER; IN_BALL] THEN CONJ_TAC THENL
     [SUBGOAL_THEN `(g:real^N->real^M) (x + s % (z - x)) IN k` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~((g:real^N->real^M) (x + s % (z - x)) IN relative_frontier k)`
      MP_TAC THENL [ASM_MESON_TAC[]; ASM_MESON_TAC[]];
      ONCE_REWRITE_TAC[DIST_SYM] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[dist; VECTOR_ARITH `(x + s % (z - x)) - x:real^N = s % (z - x)`] THEN
      ASM_REWRITE_TAC[NORM_MUL] THEN
      SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  (* the union of the segments with S *)
  ASM_CASES_TAC `(d INTER ball(x,r)) DIFF j:real^N->bool = {}` THEN
  ASM_REWRITE_TAC[CONNECTED_EMPTY] THEN
  SUBGOAL_THEN
   `(d INTER ball(x,r)) DIFF j =
    UNIONS {(segment[x,z] DELETE x) UNION S | z | z IN (d INTER ball(x:real^N,r)) DIFF j}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `w:real^N` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_TAC THEN EXISTS_TAC `(segment[x,w] DELETE x) UNION (S:real^N->bool)` THEN
      CONJ_TAC THENL [EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_UNION; IN_DELETE; ENDS_IN_SEGMENT] THEN DISJ1_TAC THEN
      DISCH_TAC THEN UNDISCH_TAC `(w:real^N) IN (d INTER ball(x,r)) DIFF j` THEN
      ASM_REWRITE_TAC[IN_DIFF];
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      UNDISCH_TAC `(w:real^N) IN t` THEN ASM_REWRITE_TAC[IN_UNION] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(S:real^N->bool) SUBSET (d INTER ball(x,r)) DIFF j` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_UNIONS THEN CONJ_TAC THENL
   [REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONVEX_CONNECTED THEN REWRITE_TAC[CONVEX_SEMIOPEN_SEGMENT];
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(S:real^N->bool = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `~((d INTER ball(x,r)) DIFF j:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N`) THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(S:real^N->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; INTERS_GSPEC; IN_ELIM_THM; IN_UNION] THEN
  MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cones at vertices: a finite complex near a vertex is the cone over its    *)
(* trace on small spheres, which is the radial image of the vertex link.    *)
(* ------------------------------------------------------------------------- *)

let MOI_FSTR_PL_SPHERE1_HOMEO = prove
 (`!b:real^N->bool. pl_sphere 1 b ==> b homeomorphic sphere(vec 0:real^2,&1)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_homeomorphism; LEFT_IMP_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  STRIP_TAC THEN
  MATCH_MP_TAC(ISPECL [`b:real^N->bool`; `relative_frontier(k:real^N->bool)`;
                       `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
  CONJ_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `sphere(vec 0:real^2,&1) = relative_frontier(cball(vec 0,&1))`
  SUBST1_TAC THENL
   [REWRITE_TAC[RELATIVE_FRONTIER_CBALL] THEN CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHIC_RELATIVE_FRONTIERS_CONVEX_BOUNDED_SETS THEN
  REWRITE_TAC[CONVEX_CBALL; BOUNDED_CBALL; AFF_DIM_CBALL; DIMINDEX_2] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_BOUNDED]);;

let MOI_FSTR_VERTEX_CONE = prove
 (`!(c:(real^N->bool)->bool) v.
     FINITE c /\ lf_simplicial_complex c /\ {v} IN c /\
     ~(UNIONS (simplicial_link c v) = {})
     ==> ?r0. &0 < r0 /\
              !r. &0 < r /\ r < r0
                  ==> UNIONS c INTER ball(v,r) =
                      {v + t % (z - v) | t,z | z IN UNIONS c INTER sphere(v,r) /\
                                               &0 <= t /\ t < &1} /\
                      (UNIONS c INTER sphere(v,r)) homeomorphic
                      UNIONS (simplicial_link c v) /\
                      (!x. x IN UNIONS c INTER ball(v,r)
                           ==> ?t. t IN c /\ v IN t /\ x IN t)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_CMB_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `compact (UNIONS (simplicial_link c (v:real^N)))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_SIMP_TAC[MOI_CMB_LINK_FINITE] THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN
    STRIP_TAC THEN
    UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN UNIONS (simplicial_link c v))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `v:real^N`] MOI_CMB_LINK_IN_STAR) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the link is at positive distance from v *)
  SUBGOAL_THEN `&0 < setdist({v:real^N},UNIONS (simplicial_link c v))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE; SETDIST_POS_LE] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[SETDIST_EQ_0_SING] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ABBREV_TAC `dl = setdist({v:real^N},UNIONS (simplicial_link c v))` THEN
  SUBGOAL_THEN `!y:real^N. y IN UNIONS (simplicial_link c v) ==> dl <= dist(v,y)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "dl" THEN MATCH_MP_TAC SETDIST_LE_DIST THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  EXISTS_TAC `min e dl` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  X_GEN_TAC `r:real` THEN STRIP_TAC THEN
  (* points of the star in the ball: v + rho (y - v) with y in the link *)
  SUBGOAL_THEN
   `!x:real^N. x IN UNIONS c /\ dist(v,x) < e /\ ~(x = v)
               ==> ?y rho. y IN UNIONS (simplicial_link c v) /\ &0 < rho /\ rho <= &1 /\
                           x = v + rho % (y - v)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `e:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_CMB_STAR_CONE THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the segment from v to a link point lies in the complex *)
  SUBGOAL_THEN
   `!y:real^N s. y IN UNIONS (simplicial_link c v) /\ &0 <= s /\ s <= &1
                 ==> v + s % (y - v) IN UNIONS c`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`] MOI_CMB_LINK_IN_STAR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(MP_TAC o SPEC `t:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  (* the radial projection of the link onto the sphere *)
  ABBREV_TAC `psi = \y:real^N. v + (r / norm(y - v)) % (y - v)` THEN
  SUBGOAL_THEN
   `!y:real^N. y IN UNIONS (simplicial_link c v)
               ==> &0 < norm(y - v) /\ r < norm(y - v) /\
                   psi y IN UNIONS c INTER sphere(v,r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `r < norm(y - v:real^N)` ASSUME_TAC THENL
     [MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `dl:real` THEN ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[GSYM dist] THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(y - v:real^N)` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_SPHERE] THEN EXPAND_TAC "psi" THEN CONJ_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_SIMP_TAC[REAL_LE_LDIV_EQ; REAL_LE_DIV; REAL_LT_IMP_LE; REAL_MUL_LID];
      REWRITE_TAC[dist; VECTOR_ARITH `v - (v + a % y):real^N = --(a % y)`] THEN
      REWRITE_TAC[NORM_NEG; NORM_MUL; REAL_ABS_DIV; REAL_ABS_NORM] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ] THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [(* the cone description *)
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_BALL; IN_ELIM_THM] THEN EQ_TAC THENL
     [STRIP_TAC THEN ASM_CASES_TAC `x:real^N = v` THENL
       [FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
          is_eq(concl th) && lhs(concl th) = `x:real^N`)) THEN
        UNDISCH_TAC `~(UNIONS (simplicial_link c (v:real^N)) = {})` THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
        MAP_EVERY EXISTS_TAC [`&0`; `(psi:real^N->real^N) y`] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `psi:real^N->real^N`)) (concl th))) THEN
        ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `rho:real`)) (concl th))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `psi:real^N->real^N`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      MAP_EVERY EXISTS_TAC [`(rho * norm(y - v:real^N)) / r`; `(psi:real^N->real^N) y`] THEN
      ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LE_DIV THEN ASM_SIMP_TAC[REAL_LE_MUL; REAL_LT_IMP_LE; NORM_POS_LE];
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID] THEN
        UNDISCH_TAC `dist(v:real^N,x) < r` THEN ASM_REWRITE_TAC[dist] THEN
        REWRITE_TAC[VECTOR_ARITH `v - (v + a % y):real^N = --(a % y)`; NORM_NEG; NORM_MUL] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 < rho ==> abs rho = rho`];
        EXPAND_TAC "psi" THEN ASM_REWRITE_TAC[VECTOR_ADD_SUB; VECTOR_MUL_ASSOC] THEN
        AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        UNDISCH_TAC `&0 < r` THEN UNDISCH_TAC `&0 < norm(y - v:real^N)` THEN
        CONV_TAC REAL_FIELD];
      DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `dist(v:real^N,z) = r` ASSUME_TAC THENL
       [ASM_MESON_TAC[IN_SPHERE]; ALL_TAC] THEN
      CONJ_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `e:real`)) (concl th) &&
          not (can (find_term ((=) `rho:real`)) (concl th)))) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
        REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [ALL_TAC; ASM_REAL_ARITH_TAC] THEN
        UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
        REWRITE_TAC[lf_simplicial_complex] THEN
        DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
        REWRITE_TAC[dist; VECTOR_ARITH `v - (v + a % y):real^N = --(a % y)`] THEN
        REWRITE_TAC[NORM_NEG; NORM_MUL] THEN
        SUBGOAL_THEN `norm(z - v:real^N) = r` SUBST1_TAC THENL
         [ONCE_REWRITE_TAC[NORM_SUB] THEN ASM_REWRITE_TAC[GSYM dist]; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_ARITH `&0 <= t ==> abs t = t`] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[]]];
    (* the radial projection is a homeomorphism from the link *)
    ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    MATCH_MP_TAC HOMEOMORPHIC_COMPACT THEN
    EXISTS_TAC `psi:real^N->real^N` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "psi" THEN MATCH_MP_TAC CONTINUOUS_ON_ADD THEN
      REWRITE_TAC[CONTINUOUS_ON_CONST] THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
      REWRITE_TAC[o_DEF; real_div; LIFT_CMUL] THEN MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN
      MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
        SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
        X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC REAL_LT_IMP_NZ THEN
        ASM_SIMP_TAC[]];
      GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
      REWRITE_TAC[IN_IMAGE] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN ASM_SIMP_TAC[];
        REWRITE_TAC[IN_INTER; IN_SPHERE] THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:real^N` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `rho:real`)) (concl th))) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [ASM_REWRITE_TAC[];
            ASM_REAL_ARITH_TAC;
            DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `dist(v:real^N,v) = r` THEN
            REWRITE_TAC[DIST_REFL] THEN ASM_REAL_ARITH_TAC];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC)) THEN
        EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `psi:real^N->real^N`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        SUBGOAL_THEN `rho * norm(y - v:real^N) = r` ASSUME_TAC THENL
         [UNDISCH_TAC `dist(v:real^N,z) = r` THEN ASM_REWRITE_TAC[dist] THEN
          REWRITE_TAC[VECTOR_ARITH `v - (v + a % y):real^N = --(a % y)`; NORM_NEG; NORM_MUL] THEN
          ASM_SIMP_TAC[REAL_ARITH `&0 < rho ==> abs rho = rho`];
          ALL_TAC] THEN
        EXPAND_TAC "psi" THEN AP_TERM_TAC THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        UNDISCH_TAC `rho * norm(y - v:real^N) = r` THEN
        UNDISCH_TAC `&0 < norm(y - v:real^N)` THEN CONV_TAC REAL_FIELD];
      MAP_EVERY X_GEN_TAC [`y1:real^N`; `y2:real^N`] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y1:real^N`; `y2:real^N`;
                     `r / norm(y1 - v:real^N)`; `r / norm(y2 - v:real^N)`]
        MOI_CMB_CONE_UNIQUE) THEN
      ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(psi:real^N->real^N) y1 = psi y2` THEN EXPAND_TAC "psi" THEN
      REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[] THEN
      CONJ_TAC THEN MATCH_MP_TAC REAL_LT_DIV THEN ASM_SIMP_TAC[]];
    (* points of the ball are in simplices at v *)
    REWRITE_TAC[IN_INTER; IN_BALL] THEN REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `e:real`)) (concl th) &&
      not (can (find_term ((=) `rho:real`)) (concl th)))) THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Open sides: a circle on a round sphere has two open complementary         *)
(* regions, and a cone over such a circle has two open sides in the ball.   *)
(* (The statements of pc_moi_cone_sides plus openness, proved here with the *)
(* lemmas of pc_moi_cone_sides.)                                             *)
(* ------------------------------------------------------------------------- *)

let MOI_FSTR_SPHERE_JORDAN_OPEN = prove
 (`!(q:real^3) r (c:real^3->bool).
     &0 < r /\ c SUBSET sphere(q,r) /\ c homeomorphic sphere(vec 0:real^2,&1)
     ==> ?o1 o2. connected o1 /\ connected o2 /\ ~(o1 = {}) /\ ~(o2 = {}) /\
                 DISJOINT o1 o2 /\ o1 UNION o2 = sphere(q,r) DIFF c /\
                 c SUBSET closure o1 /\ c SUBSET closure o2 /\
                 open_in (subtopology euclidean (sphere(q,r))) o1 /\
                 open_in (subtopology euclidean (sphere(q,r))) o2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?p:real^3. p IN sphere(q,r) /\ ~(p IN c)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(c:real^3->bool) SUBSET s /\ ~(c = s) ==> ?p. p IN s /\ ~(p IN c)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(c:real^3->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_SPHERES_EQ; DIMINDEX_2; DIMINDEX_3; ARITH_EQ] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`q:real^3`; `r:real`; `p:real^3`] MOI_CSD_PUNCTURED_SPHERE_R2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^2` (X_CHOOSE_THEN `g:real^2->real^3`
    ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_UNIV]) THEN
  SUBGOAL_THEN `(c:real^3->bool) SUBSET sphere(q,r) DELETE p` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `d = IMAGE (f:real^3->real^2) c` THEN
  SUBGOAL_THEN `(d:real^2->bool) homeomorphic sphere(vec 0:real^2,&1)` ASSUME_TAC THENL
   [MATCH_MP_TAC(ISPECL [`d:real^2->bool`; `c:real^3->bool`; `sphere(vec 0:real^2,&1)`]
      HOMEOMORPHIC_TRANS) THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
    REWRITE_TAC[homeomorphic] THEN
    MAP_EVERY EXISTS_TAC [`f:real^3->real^2`; `g:real^2->real^3`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`sphere(q:real^3,r) DELETE p`; `(:real^2)`] THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    ALL_TAC] THEN
  MP_TAC(ISPEC `d:real^2->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_REWRITE_TAC[DIMINDEX_2; LE_REFL] THEN STRIP_TAC THEN
  (* the image of the complement of d *)
  SUBGOAL_THEN `IMAGE (g:real^2->real^3) ((:real^2) DIFF d) = (sphere(q,r) DELETE p) DIFF c`
  ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^2) c = d`)) THEN MATCH_MP_TAC MOI_CSD_IMAGE_COMPL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (g:real^2->real^3) d = c` ASSUME_TAC THENL
   [SUBST1_TAC(SYM(ASSUME `IMAGE (f:real^3->real^2) c = d`)) THEN
    UNDISCH_TAC `(c:real^3->bool) SUBSET sphere(q,r) DELETE p` THEN
    UNDISCH_TAC `!x. x IN sphere(q,r) DELETE p ==> (g:real^2->real^3)((f:real^3->real^2) x) = x` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y1 y2. (g:real^2->real^3) y1 = g y2 ==> y1 = y2` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!y. ~((g:real^2->real^3) y = p)` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `IMAGE (g:real^2->real^3) (:real^2) = sphere(q,r) DELETE p` THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIV; IN_DELETE] THEN
    DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* the closure of the image of the inside *)
  SUBGOAL_THEN `closure(inside d) = inside d UNION (d:real^2->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `inside(d:real^2->bool)` CLOSURE_UNION_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact(closure(inside(d:real^2->bool)))` ASSUME_TAC THENL
   [ASM_SIMP_TAC[COMPACT_CLOSURE]; ALL_TAC] THEN
  SUBGOAL_THEN `closure (IMAGE (g:real^2->real^3) (inside d)) =
                IMAGE g (inside d) UNION c` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSURE_MINIMAL THEN CONJ_TAC THENL [REWRITE_TAC[SUBSET_UNION]; ALL_TAC] THEN
      SUBGOAL_THEN `IMAGE (g:real^2->real^3) (inside d) UNION c =
                    IMAGE g (closure(inside d))` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[IMAGE_UNION]; ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      REWRITE_TAC[UNION_SUBSET; CLOSURE_SUBSET] THEN
      SUBGOAL_THEN `c = IMAGE (g:real^2->real^3) (d:real^2->bool)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (g:real^2->real^3) (closure(inside d))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[SUBSET_UNION];
        MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]]];
    ALL_TAC] THEN
  (* p is a limit of the image of the outside *)
  SUBGOAL_THEN `(p:real^3) IN closure (IMAGE (g:real^2->real^3) (outside d))` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `?e. &0 < e /\
                      DISJOINT (ball(p:real^3,e)) (IMAGE (g:real^2->real^3) (outside d))`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `~((p:real^3) IN closure (IMAGE (g:real^2->real^3) (outside d)))` THEN
      REWRITE_TAC[CLOSURE_APPROACHABLE; NOT_FORALL_THM; NOT_IMP; NOT_EXISTS_THM] THEN
      MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN
      REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_BALL; NOT_IN_EMPTY] THEN
      MESON_TAC[DIST_SYM];
      ALL_TAC] THEN
    UNDISCH_TAC `~bounded(outside(d:real^2->bool))` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC BOUNDED_SUBSET THEN
    EXISTS_TAC `IMAGE (f:real^3->real^2) (sphere(q,r) DIFF ball(p,e))` THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `sphere(q:real^3,r) DELETE p` THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_DIFF; IN_DELETE; IN_BALL] THEN
        X_GEN_TAC `x:real^3` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~(dist(p:real^3,p) < e)` THEN ASM_REWRITE_TAC[DIST_REFL];
        MATCH_MP_TAC COMPACT_DIFF THEN REWRITE_TAC[COMPACT_SPHERE; OPEN_BALL]];
      REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN DISCH_TAC THEN
      EXISTS_TAC `(g:real^2->real^3) z` THEN ASM_REWRITE_TAC[IN_DIFF] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (g:real^2->real^3) (:real^2) = sphere(q,r) DELETE p` THEN SET_TAC[];
        UNDISCH_TAC `DISJOINT (ball(p:real^3,e)) (IMAGE (g:real^2->real^3) (outside d))` THEN
        UNDISCH_TAC `(z:real^2) IN outside d` THEN SET_TAC[]]];
    ALL_TAC] THEN
  EXISTS_TAC `IMAGE (g:real^2->real^3) (inside d)` THEN
  EXISTS_TAC `(p:real^3) INSERT IMAGE (g:real^2->real^3) (outside d)` THEN
  REPEAT CONJ_TAC THENL
   [(* connected o1 *)
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV];
    (* connected o2 *)
    SUBGOAL_THEN `connected (IMAGE (g:real^2->real^3) (outside d))` MP_TAC THENL
     [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
      ASM_REWRITE_TAC[SUBSET_UNIV];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP CONNECTED_INSERT th]) THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[IMAGE_EQ_EMPTY];
    REWRITE_TAC[NOT_INSERT_EMPTY];
    (* disjoint *)
    MAP_EVERY UNDISCH_TAC
     [`inside d INTER outside d:real^2->bool = {}`;
      `!y1 y2. (g:real^2->real^3) y1 = g y2 ==> y1 = y2`;
      `!y. ~((g:real^2->real^3) y = p)`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    (* the union *)
    SUBGOAL_THEN `IMAGE (g:real^2->real^3) (inside d) UNION (p INSERT IMAGE g (outside d)) =
                  p INSERT IMAGE g ((:real^2) DIFF d)` SUBST1_TAC THENL
     [REWRITE_TAC[GSYM(ASSUME `inside d UNION outside d = (:real^2) DIFF d`)] THEN
      REWRITE_TAC[IMAGE_UNION] THEN SET_TAC[];
      REWRITE_TAC[ASSUME `IMAGE (g:real^2->real^3) ((:real^2) DIFF d) =
                          (sphere(q,r) DELETE p) DIFF c`] THEN
      MAP_EVERY UNDISCH_TAC [`(p:real^3) IN sphere(q,r)`; `~((p:real^3) IN c)`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[]];
    (* c in the closure of o1 *)
    SUBGOAL_THEN `closure (IMAGE (g:real^2->real^3) (inside d)) = IMAGE g (inside d) UNION c`
    SUBST1_TAC THENL [FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[SUBSET_UNION]];
    (* c in the closure of o2 *)
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure (IMAGE (g:real^2->real^3) (outside d))` THEN CONJ_TAC THENL
     [SUBGOAL_THEN `c = IMAGE (g:real^2->real^3) (d:real^2->bool)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (g:real^2->real^3) (closure(outside d))` THEN CONJ_TAC THENL
       [MATCH_MP_TAC IMAGE_SUBSET THEN
        MP_TAC(ISPEC `outside(d:real^2->bool)` CLOSURE_UNION_FRONTIER) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC IMAGE_CLOSURE_SUBSET THEN REWRITE_TAC[CLOSED_CLOSURE; CLOSURE_SUBSET] THEN
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(:real^2)` THEN
        ASM_REWRITE_TAC[SUBSET_UNIV]];
      MATCH_MP_TAC SUBSET_CLOSURE THEN SET_TAC[]];
    (* o1 open in the sphere *)
    MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `sphere(q:real^3,r) DELETE p` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`f:real^3->real^2`; `(:real^2)`] THEN
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN];
      REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `(:real^3) DELETE p` THEN
      SIMP_TAC[OPEN_DELETE; OPEN_UNIV] THEN SET_TAC[]];
    (* o2 open in the sphere *)
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `(:real^3) DIFF closure (IMAGE (g:real^2->real^3) (inside d))` THEN
    REWRITE_TAC[GSYM closed; CLOSED_CLOSURE] THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (g:real^2->real^3) ((:real^2) DIFF d) = (sphere(q,r) DELETE p) DIFF c`;
      `inside d UNION outside d = (:real^2) DIFF d`;
      `inside d INTER outside d:real^2->bool = {}`;
      `!y1 y2. (g:real^2->real^3) y1 = g y2 ==> y1 = y2`;
      `!y. ~((g:real^2->real^3) y = p)`; `(p:real^3) IN sphere(q,r)`; `~((p:real^3) IN c)`;
      `(c:real^3->bool) SUBSET sphere(q,r)`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[]]);;

let MOI_FSTR_CONE_SIDES_OPEN = prove
 (`!(q:real^3) r c y.
     &0 < r /\ c SUBSET sphere(q,r) /\ c homeomorphic sphere(vec 0:real^2,&1) /\
     y INTER ball(q,r) = {q + t % (z - q) | t,z | z IN c /\ &0 <= t /\ t < &1}
     ==> ?s1 s2. connected s1 /\ connected s2 /\ ~(s1 = {}) /\ ~(s2 = {}) /\
                 DISJOINT s1 s2 /\ ball(q,r) DIFF y = s1 UNION s2 /\
                 y INTER ball(q,r) SUBSET closure s1 /\
                 y INTER ball(q,r) SUBSET closure s2 /\ open s1 /\ open s2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`q:real^3`; `r:real`; `c:real^3->bool`] MOI_FSTR_SPHERE_JORDAN_OPEN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `o1:real^3->bool` (X_CHOOSE_THEN `o2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(c:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(c:real^3->bool) homeomorphic sphere(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* the cones over the two regions *)
  ABBREV_TAC `cone = \u:real^3->bool. {q + t % (z - q) | t,z | z IN u /\ &0 < t /\ t < &1}` THEN
  (* membership in a cone over a part of the sphere *)
  SUBGOAL_THEN
   `!u x. u SUBSET sphere(q,r)
          ==> (x IN (cone:(real^3->bool)->real^3->bool) u <=>
               x IN ball(q,r) /\ ~(x = q) /\
               q + r % (inv(norm(x - q)) % (x - q)) IN u)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "cone" THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(z:real^3) IN sphere(q,r)` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[IN_SPHERE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `norm(z - q:real^3) = r` ASSUME_TAC THENL
       [ASM_MESON_TAC[dist; NORM_SUB]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_BALL; VECTOR_ADD_SUB; NORM_MUL] THEN
      SUBGOAL_THEN `abs t = t` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[dist; VECTOR_ARITH `q - (q + t % (z - q)):real^3 = --(t % (z - q))`] THEN
        ASM_REWRITE_TAC[NORM_NEG; NORM_MUL] THEN
        SUBGOAL_THEN `abs t = t` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        GEN_REWRITE_TAC RAND_CONV [GSYM REAL_MUL_LID] THEN
        MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[VECTOR_ARITH `q + t % (z - q):real^3 = q <=> t % (z - q) = vec 0`] THEN
        REWRITE_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ] THEN
        DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
         [UNDISCH_TAC `&0 < &0` THEN REAL_ARITH_TAC;
          UNDISCH_TAC `norm(q - q:real^3) = r` THEN REWRITE_TAC[VECTOR_SUB_REFL; NORM_0] THEN
          ASM_REAL_ARITH_TAC];
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `q + r % inv(t * r) % t % (z - q):real^3 = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
        REWRITE_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        UNDISCH_TAC `&0 < t` THEN UNDISCH_TAC `&0 < r` THEN CONV_TAC REAL_FIELD];
      STRIP_TAC THEN
      EXISTS_TAC `norm(x - q:real^3) / r` THEN
      EXISTS_TAC `q + r % (inv(norm(x - q)) % (x - q)):real^3` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `&0 < norm(x - q:real^3)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ]; ALL_TAC] THEN
      SUBGOAL_THEN `norm(x - q:real^3) < r` ASSUME_TAC THENL
       [UNDISCH_TAC `(x:real^3) IN ball(q,r)` THEN REWRITE_TAC[IN_BALL; dist] THEN
        MESON_TAC[NORM_SUB];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC REAL_LT_DIV THEN ASM_REWRITE_TAC[];
        ASM_SIMP_TAC[REAL_LT_LDIV_EQ; REAL_MUL_LID];
        REWRITE_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
        X_GEN_TAC `i:num` THEN STRIP_TAC THEN
        UNDISCH_TAC `&0 < norm(x - q:real^3)` THEN UNDISCH_TAC `&0 < r` THEN
        CONV_TAC REAL_FIELD]];
    ALL_TAC] THEN
  (* the radial projection is continuous off q *)
  SUBGOAL_THEN
   `(\x:real^3. q + r % (inv(norm(x - q)) % (x - q))) continuous_on (ball(q,r) DELETE q)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN REWRITE_TAC[CONTINUOUS_ON_CONST] THEN
    MATCH_MP_TAC CONTINUOUS_ON_CMUL THEN MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID] THEN
    REWRITE_TAC[o_DEF] THEN
    MATCH_MP_TAC(REWRITE_RULE[o_DEF] CONTINUOUS_ON_INV) THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_LIFT_NORM_COMPOSE THEN
      SIMP_TAC[CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST; CONTINUOUS_ON_ID];
      REWRITE_TAC[IN_DELETE; NORM_EQ_0; VECTOR_SUB_EQ] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(o1:real^3->bool) SUBSET sphere(q,r) /\ (o2:real^3->bool) SUBSET sphere(q,r)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  (* openness of the cones *)
  SUBGOAL_THEN
   `!u. u SUBSET sphere(q,r) /\ open_in (subtopology euclidean (sphere(q,r))) u
        ==> open ((cone:(real^3->bool)->real^3->bool) u)`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^3->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `open_in (subtopology euclidean (sphere(q,r))) (u:real^3->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(cone:(real^3->bool)->real^3->bool) u =
      {x | x IN ball(q,r) DELETE q /\ q + r % (inv(norm(x - q)) % (x - q)) IN w}`
    SUBST1_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(u:real^3->bool) SUBSET sphere(q,r)`)]) o
        check (fun th -> is_forall(concl th) && can (find_term ((=) `cone:(real^3->bool)->real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM; IN_DELETE; IN_INTER] THEN
      SUBGOAL_THEN `x IN ball(q,r) /\ ~(x = q)
                    ==> q + r % (inv(norm(x - q)) % (x - q)) IN sphere(q:real^3,r)` MP_TAC THENL
       [STRIP_TAC THEN REWRITE_TAC[IN_SPHERE; dist] THEN
        REWRITE_TAC[VECTOR_ARITH `q - (q + a):real^3 = --a`; NORM_NEG; NORM_MUL] THEN
        REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NORM] THEN
        SUBGOAL_THEN `~(norm(x - q:real^3) = &0)` ASSUME_TAC THENL
         [ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ]; ALL_TAC] THEN
        ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
        MESON_TAC[]];
      MATCH_MP_TAC CONTINUOUS_OPEN_PREIMAGE THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[OPEN_DELETE; OPEN_BALL]];
    ALL_TAC] THEN
  EXISTS_TAC `(cone:(real^3->bool)->real^3->bool) o1` THEN
  EXISTS_TAC `(cone:(real^3->bool)->real^3->bool) o2` THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "cone" THEN MATCH_MP_TAC MOI_CSD_CONE_CONNECTED THEN ASM_REWRITE_TAC[];
    EXPAND_TAC "cone" THEN MATCH_MP_TAC MOI_CSD_CONE_CONNECTED THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `~(o1:real^3->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
    EXISTS_TAC `q + inv(&2) % (z - q):real^3` THEN EXPAND_TAC "cone" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`inv(&2)`; `z:real^3`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    UNDISCH_TAC `~(o2:real^3->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
    EXISTS_TAC `q + inv(&2) % (z - q):real^3` THEN EXPAND_TAC "cone" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY EXISTS_TAC [`inv(&2)`; `z:real^3`] THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `x:real^3` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[MATCH_MP th (ASSUME `(o1:real^3->bool) SUBSET sphere(q,r)`);
                                      MATCH_MP th (ASSUME `(o2:real^3->bool) SUBSET sphere(q,r)`)]) o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `cone:(real^3->bool)->real^3->bool`)) (concl th) &&
                       length(fst(strip_forall(concl th))) = 2)) THEN
    UNDISCH_TAC `DISJOINT (o1:real^3->bool) o2` THEN SET_TAC[];
    (* the complement of y in the ball *)
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^3` THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[IN_UNION; MATCH_MP th (ASSUME `(o1:real^3->bool) SUBSET sphere(q,r)`);
                                      MATCH_MP th (ASSUME `(o2:real^3->bool) SUBSET sphere(q,r)`)]) o
      check (fun th -> is_forall(concl th) && can (find_term ((=) `cone:(real^3->bool)->real^3->bool`)) (concl th) &&
                       length(fst(strip_forall(concl th))) = 2)) THEN
    REWRITE_TAC[IN_DIFF] THEN
    ASM_CASES_TAC `(x:real^3) IN ball(q,r)` THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `x:real^3 = q` THEN ASM_REWRITE_TAC[] THENL
     [(* q is in y *)
      SUBGOAL_THEN `(q:real^3) IN y INTER ball(q,r)` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_ELIM_THM] THEN
        UNDISCH_TAC `~(c:real^3->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        DISCH_THEN(X_CHOOSE_TAC `z:real^3`) THEN
        MAP_EVERY EXISTS_TAC [`&0`; `z:real^3`] THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC];
        SIMP_TAC[IN_INTER]];
      ALL_TAC] THEN
    ABBREV_TAC `z = q + r % (inv(norm(x - q)) % (x - q)):real^3` THEN
    SUBGOAL_THEN `(z:real^3) IN sphere(q,r)` ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN REWRITE_TAC[IN_SPHERE; dist] THEN
      REWRITE_TAC[VECTOR_ARITH `q - (q + a):real^3 = --a`; NORM_NEG; NORM_MUL] THEN
      REWRITE_TAC[REAL_ABS_INV; REAL_ABS_NORM] THEN
      SUBGOAL_THEN `~(norm(x - q:real^3) = &0)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ]; ALL_TAC] THEN
      ASM_SIMP_TAC[REAL_MUL_LINV; REAL_MUL_RID] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `x = q + (norm(x - q) / r) % (z - q:real^3)` ASSUME_TAC THENL
     [EXPAND_TAC "z" THEN
      SUBGOAL_THEN `~(norm(x - q:real^3) = &0)` MP_TAC THENL
       [ASM_REWRITE_TAC[NORM_EQ_0; VECTOR_SUB_EQ]; ALL_TAC] THEN
      UNDISCH_TAC `&0 < r` THEN POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN
      REWRITE_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
      X_GEN_TAC `i:num` THEN STRIP_TAC THEN
      UNDISCH_TAC `~(norm(x - q:real^3) = &0)` THEN UNDISCH_TAC `&0 < r` THEN
      CONV_TAC REAL_FIELD;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 < norm(x - q:real^3) / r /\ norm(x - q:real^3) / r < &1`
    STRIP_ASSUME_TAC THENL
     [ASM_SIMP_TAC[REAL_LT_DIV; REAL_LT_LDIV_EQ; REAL_MUL_LID; NORM_POS_LT; VECTOR_SUB_EQ] THEN
      UNDISCH_TAC `(x:real^3) IN ball(q,r)` THEN REWRITE_TAC[IN_BALL; dist] THEN
      MESON_TAC[NORM_SUB];
      ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^3) IN y <=> (z:real^3) IN c` SUBST1_TAC THENL
     [SUBGOAL_THEN `(x:real^3) IN y <=> x IN y INTER ball(q,r)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `t:real` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
        MP_TAC(ISPECL [`q:real^3`; `r:real`; `z:real^3`; `w:real^3`;
                       `norm(x - q:real^3) / r`; `t:real`] MOI_CSD_SPHERE_RAY) THEN
        ANTS_TAC THENL
         [REPEAT CONJ_TAC THENL
           [FIRST_ASSUM ACCEPT_TAC;
            FIRST_ASSUM ACCEPT_TAC;
            UNDISCH_TAC `(w:real^3) IN c` THEN
            UNDISCH_TAC `(c:real^3->bool) SUBSET sphere(q,r)` THEN SET_TAC[];
            MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC;
            FIRST_ASSUM ACCEPT_TAC;
            MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `x:real^3` THEN CONJ_TAC THENL
             [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC]];
          ALL_TAC] THEN
        STRIP_TAC THENL
         [UNDISCH_TAC `&0 < norm(x - q:real^3) / r` THEN
          UNDISCH_TAC `norm(x - q:real^3) / r = &0` THEN REAL_ARITH_TAC;
          ASM_REWRITE_TAC[]];
        DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`norm(x - q:real^3) / r`; `z:real^3`] THEN
        REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        MATCH_MP_TAC REAL_LT_IMP_LE THEN FIRST_ASSUM ACCEPT_TAC];
      ALL_TAC] THEN
    UNDISCH_TAC `(o1:real^3->bool) UNION o2 = sphere(q,r) DIFF c` THEN
    UNDISCH_TAC `(z:real^3) IN sphere(q,r)` THEN SET_TAC[];
    (* y in the closure of the first cone *)
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^3) IN y INTER ball(q,r)` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "cone" THEN
    MATCH_MP_TAC MOI_CSD_CONE_CLOSURE_LEMMA THEN EXISTS_TAC `r:real` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^3) IN y INTER ball(q,r)` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "cone" THEN
    MATCH_MP_TAC MOI_CSD_CONE_CLOSURE_LEMMA THEN EXISTS_TAC `r:real` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The disk side at a rim vertex: near a vertex v of the rim, the surface M *)
(* has two open sides in a small ball, and the disk minus the rim lies in   *)
(* one of them (D).                                                          *)
(* ------------------------------------------------------------------------- *)

(* The rim near v consists of full radial segments. *)
let MOI_FSTR_STAR_RAY = prove
 (`!(c:(real^N->bool)->bool) v.
     FINITE c /\ lf_simplicial_complex c /\ {v} IN c /\
     ~(UNIONS (simplicial_link c v) = {})
     ==> ?r. &0 < r /\
             !z s. dist(v,z) < r /\ &0 < s /\ s <= &1 /\ v + s % (z - v) IN UNIONS c
                   ==> z IN UNIONS c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN UNIONS c` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_CMB_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  (* the link is at positive distance from v *)
  SUBGOAL_THEN `compact (UNIONS (simplicial_link c (v:real^N)))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_SIMP_TAC[MOI_CMB_LINK_FINITE] THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN
    STRIP_TAC THEN
    UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^N) IN UNIONS (simplicial_link c v))` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `v:real^N`] MOI_CMB_LINK_IN_STAR) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 < setdist({v:real^N},UNIONS (simplicial_link c v))` ASSUME_TAC THENL
   [REWRITE_TAC[REAL_LT_LE; SETDIST_POS_LE] THEN
    ONCE_REWRITE_TAC[EQ_SYM_EQ] THEN REWRITE_TAC[SETDIST_EQ_0_SING] THEN
    ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ABBREV_TAC `dl = setdist({v:real^N},UNIONS (simplicial_link c v))` THEN
  EXISTS_TAC `min e dl` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  MAP_EVERY X_GEN_TAC [`z:real^N`; `s:real`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `v + s % (z - v):real^N = v` THENL
   [SUBGOAL_THEN `z:real^N = v` (fun th -> ASM_REWRITE_TAC[th]) THEN
    UNDISCH_TAC `v + s % (z - v):real^N = v` THEN
    REWRITE_TAC[VECTOR_ARITH `v + s % (z - v):real^N = v <=> s % (z - v) = vec 0`] THEN
    ASM_SIMP_TAC[VECTOR_MUL_EQ_0; VECTOR_SUB_EQ; REAL_LT_IMP_NZ];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(z:real^N = v)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(v + s % (v - v):real^N = v)` THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `dist(v:real^N,v + s % (z - v)) < e` ASSUME_TAC THENL
   [REWRITE_TAC[dist; VECTOR_ARITH `v - (v + s % (z - v)):real^N = --(s % (z - v))`] THEN
    REWRITE_TAC[NORM_NEG; NORM_MUL] THEN
    SUBGOAL_THEN `abs s = s` SUBST1_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `&1 * norm(z - v:real^N)` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LE_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LE];
      REWRITE_TAC[REAL_MUL_LID] THEN ONCE_REWRITE_TAC[NORM_SUB] THEN
      ASM_REWRITE_TAC[GSYM dist]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v + s % (z - v):real^N` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `e:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`;
                 `v + s % (z - v):real^N`] MOI_CMB_STAR_CONE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` (X_CHOOSE_THEN `rho:real` STRIP_ASSUME_TAC)) THEN
  (* z lies on the segment from v to the link point y *)
  SUBGOAL_THEN `z = v + (rho / s) % (y - v:real^N)` ASSUME_TAC THENL
   [UNDISCH_TAC `v + s % (z - v):real^N = v + rho % (y - v)` THEN
    UNDISCH_TAC `&0 < s` THEN POP_ASSUM_LIST(K ALL_TAC) THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    UNDISCH_TAC `v + s % (z - v):real^N = v + rho % (y - v)` THEN
    REWRITE_TAC[CART_EQ; VECTOR_ADD_COMPONENT; VECTOR_SUB_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    DISCH_THEN(MP_TAC o SPEC `i:num`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `&0 < s` THEN CONV_TAC REAL_FIELD;
    ALL_TAC] THEN
  SUBGOAL_THEN `dl <= norm(y - v:real^N)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[NORM_SUB] THEN REWRITE_TAC[GSYM dist] THEN
    EXPAND_TAC "dl" THEN MATCH_MP_TAC SETDIST_LE_DIST THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `rho / s <= &1` ASSUME_TAC THENL
   [SUBGOAL_THEN `(rho / s) * norm(y - v:real^N) < dl` MP_TAC THENL
     [SUBGOAL_THEN `(rho / s) * norm(y - v:real^N) = dist(v,z)` SUBST1_TAC THENL
       [ASM_REWRITE_TAC[dist; VECTOR_ARITH `v - (v + a % y):real^N = --(a % y)`] THEN
        REWRITE_TAC[NORM_NEG; NORM_MUL] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
        MATCH_MP_TAC(REAL_ARITH `&0 <= x ==> x = abs x`) THEN
        MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_TAC THEN MATCH_MP_TAC(REAL_ARITH `~(&1 < x) ==> x <= &1`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `&1 * norm(y - v:real^N) < (rho / s) * norm(y - v)` MP_TAC THENL
     [MATCH_MP_TAC REAL_LT_RMUL THEN ASM_REWRITE_TAC[NORM_POS_LT; VECTOR_SUB_EQ] THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`] MOI_CMB_LINK_IN_STAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(MP_TAC o SPEC `t':real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
    MATCH_MP_TAC REAL_LE_DIV THEN ASM_REAL_ARITH_TAC]);;

let MOI_FSTR_VERTEX_SIDES = prove
 (`!(lm:(real^3->bool)->bool) ld lj (k:real^3->bool) (f:real^3->real^3) g v.
     FINITE lm /\ combinatorial_manifold 2 lm /\
     FINITE ld /\ lf_simplicial_complex ld /\ simplicial_subcomplex lj ld /\
     convex k /\ closed k /\ homeomorphism (k,UNIONS ld) (f,g) /\
     UNIONS lj = IMAGE f (relative_frontier k) /\
     UNIONS ld INTER UNIONS lm = UNIONS lj /\
     {v} IN lj /\ {v} IN lm /\ ~(UNIONS (simplicial_link lj v) = {})
     ==> ?r D E. &0 < r /\ open D /\ open E /\ connected D /\ connected E /\
                 DISJOINT D E /\ ball(v,r) DIFF UNIONS lm = D UNION E /\
                 UNIONS lm INTER ball(v,r) SUBSET closure D /\
                 UNIONS lm INTER ball(v,r) SUBSET closure E /\
                 (UNIONS ld INTER ball(v,r)) DIFF UNIONS lj SUBSET D /\
                 (!x. x IN UNIONS lm INTER ball(v,r) ==> ?t. t IN lm /\ v IN t /\ x IN t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `UNIONS (lj:(real^3->bool)->bool)`)) THEN
  SUBGOAL_THEN `lf_simplicial_complex (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (UNIONS (simplicial_link lm (v:real^3)))` ASSUME_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold 2 (lm:(real^3->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (simplicial_link lm (v:real^3)) homeomorphic sphere(vec 0:real^2,&1)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FSTR_PL_SPHERE1_HOMEO]; ALL_TAC] THEN
  SUBGOAL_THEN `~(UNIONS (simplicial_link lm (v:real^3)) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `UNIONS (simplicial_link lm (v:real^3)) homeomorphic sphere(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `v:real^3`] MOI_FSTR_VERTEX_CONE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  (* the disk near v *)
  SUBGOAL_THEN `(lj:(real^3->bool)->bool) SUBSET ld` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN UNIONS ld` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^3}` THEN REWRITE_TAC[IN_SING] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ld:(real^3->bool)->bool`; `v:real^3`] MOI_CMB_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ed:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `FINITE (lj:(real^3->bool)->bool) /\ lf_simplicial_complex lj`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ld:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_FM3_LF_SUBCOMPLEX THEN EXISTS_TAC `ld:(real^3->bool)->bool` THEN
      ASM_MESON_TAC[simplicial_subcomplex]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lj:(real^3->bool)->bool`; `v:real^3`] MOI_FSTR_STAR_RAY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `ej:real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `r = min (r0 / &2) (min ed ej)` THEN
  SUBGOAL_THEN `&0 < r /\ r < r0 /\ r <= ed /\ r <= ej` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `r:real` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `r0:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* the disk side is connected *)
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `k:real^3->bool`;
                 `UNIONS ld:real^3->bool`; `UNIONS lj:real^3->bool`; `v:real^3`; `r:real`]
    MOI_FSTR_CHART_CONE_CONN) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC) THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^3}` THEN ASM_REWRITE_TAC[IN_SING];
      MAP_EVERY X_GEN_TAC [`z:real^3`; `s:real`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `ed:real`)) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(z:real^3) IN ball(v,r)` THEN
        REWRITE_TAC[IN_BALL] THEN ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_CMB_SEGMENT_IN THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `lf_simplicial_complex (ld:(real^3->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o CONJUNCT1) THEN DISCH_THEN(MP_TAC o SPEC `t:real^3->bool`) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
      MAP_EVERY X_GEN_TAC [`z:real^3`; `s:real`] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `ej:real`)) (concl th))) THEN
      EXISTS_TAC `s:real` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN ball(v,r)` THEN REWRITE_TAC[IN_BALL] THEN
      ASM_REAL_ARITH_TAC];
    DISCH_TAC] THEN
  (* the two sides of the surface *)
  MP_TAC(ISPECL [`v:real^3`; `r:real`; `UNIONS lm INTER sphere(v:real^3,r)`;
                 `UNIONS lm:real^3->bool`] MOI_FSTR_CONE_SIDES_OPEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN
    MATCH_MP_TAC(ISPECL [`UNIONS lm INTER sphere(v:real^3,r)`;
                         `UNIONS (simplicial_link lm (v:real^3))`;
                         `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_TRANS) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^3->bool` (X_CHOOSE_THEN `s2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`(UNIONS ld INTER ball(v:real^3,r)) DIFF UNIONS lj`;
                 `s1:real^3->bool`; `s2:real^3->bool`] MOI_FSTR_CONNECTED_IN_ONE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `(s1:real^3->bool) UNION s2`)) THEN
    UNDISCH_TAC `UNIONS ld INTER UNIONS lm = UNIONS (lj:(real^3->bool)->bool)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`r:real`; `s1:real^3->bool`; `s2:real^3->bool`];
    MAP_EVERY EXISTS_TAC [`r:real`; `s2:real^3->bool`; `s1:real^3->bool`]] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[UNION_ACI] THEN
  ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* (O3) agreement of the signs at the two ends of a rim edge.  The disk     *)
(* leaves the rim edge [v,w] into one sector, which is the side D at both   *)
(* ends; the sector of a direction is unchanged by positive scaling and by  *)
(* moving the base point along the edge.                                     *)
(* ------------------------------------------------------------------------- *)

let MOI_FSTR_THIRD = prove
 (`!(p:A) q r v w.
     ~(p = q) /\ ~(p = r) /\ ~(q = r) /\ v IN {p,q,r} /\ w IN {p,q,r} /\ ~(v = w)
     ==> ?x. {p,q,r} = {v,w,x} /\ ~(x = v) /\ ~(x = w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && (lhs(concl th) = `v:A` || lhs(concl th) = `w:A`)))) THEN
  FIRST (map (fun x -> EXISTS_TAC x THEN ASM SET_TAC[]) [`p:A`; `q:A`; `r:A`]));;

(* A triangle of a complex through two vertices v, w is conv{v,w,x}. *)
let MOI_FSTR_TRI_FORM = prove
 (`!(c:(real^N->bool)->bool) t v w.
     simplicial_complex c /\ t IN c /\ aff_dim t = &2 /\ {v} IN c /\ {w} IN c /\
     v IN t /\ w IN t /\ ~(v = w)
     ==> ?x. t = convex hull {v,w,x} /\ ~(x = v) /\ ~(x = w)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `2`] MOI_FSA_VS_SIZE) THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` (X_CHOOSE_THEN `r:real^N`
    STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`p:real^N`; `q:real^N`; `r:real^N`; `v:real^N`; `w:real^N`] MOI_FSTR_THIRD) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `{p:real^N,q,r}`)) THEN
    ASM_MESON_TAC[MOI_FSA_VS_MEM];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`] MOI_FSA_VS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[]);;

(* The vertices of an edge of a complex are vertices of the complex. *)
let MOI_FSTR_EDGE_ENDS = prove
 (`!(c:(real^N->bool)->bool) v w.
     lf_simplicial_complex c /\ segment[v,w] IN c ==> {v} IN c /\ {w} IN c`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `lf_simplicial_complex (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[lf_simplicial_complex] THEN
  DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN DISCH_TAC THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `segment[v:real^N,w]` THEN
  ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

(* The other triangle at an edge of a combinatorial surface. *)
let MOI_FSTR_OTHER_TRI = prove
 (`!(m:(real^3->bool)->bool) v w x.
     FINITE m /\ combinatorial_manifold 2 m /\ segment[v,w] IN m /\ ~(v = w) /\
     convex hull {v,w,x} IN m /\ aff_dim(convex hull {v,w,x}) = &2
     ==> ?x'. ~(x' = x) /\ convex hull {v,w,x'} IN m /\
              aff_dim(convex hull {v,w,x'}) = &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^3->bool)->bool) /\ simplicial_complex m`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FSA_CM_SC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `v:real^3`; `w:real^3`] MOI_FSTR_EDGE_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `S = {t | t IN m /\ aff_dim t = &2 /\ segment[v:real^3,w] SUBSET t}` THEN
  SUBGOAL_THEN `FINITE (S:(real^3->bool)->bool) /\ CARD S = 2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `m:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN EXPAND_TAC "S" THEN SET_TAC[];
      EXPAND_TAC "S" THEN MATCH_MP_TAC MOI_FSA_CM_EDGE2 THEN
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {v:real^3,w,x} IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t:real^3->bool. t IN S /\ ~(t = convex hull {v,w,x})` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    SUBGOAL_THEN `CARD (S:(real^3->bool)->bool) <= CARD {convex hull {v:real^3,w,x}}`
    MP_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN REWRITE_TAC[FINITE_SING; SUBSET; IN_SING] THEN
      ASM_MESON_TAC[];
      ASM_REWRITE_TAC[CARD_SING] THEN ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `(t:real^3->bool) IN S` THEN EXPAND_TAC "S" THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^3->bool)->bool`; `t:real^3->bool`; `v:real^3`; `w:real^3`]
    MOI_FSTR_TRI_FORM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
      is_binary "SUBSET" (concl th) && lhand(concl th) = `segment[v:real^3,w]`)) THEN
    REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `x':real^3` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `t:real^3->bool`)) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
  UNDISCH_TAC `~(convex hull {v:real^3,w,x} = convex hull {v,w,x})` THEN REWRITE_TAC[]);;

(* Points of the disk off its rim accumulate at every rim point. *)
let MOI_FSTR_CHART_ACCUM = prove
 (`!(f:real^M->real^N) g k d y e.
     homeomorphism (k,d) (f,g) /\ convex k /\ closed k /\
     y IN IMAGE f (relative_frontier k) /\ &0 < e
     ==> ?q. q IN d /\ ~(q IN IMAGE f (relative_frontier k)) /\ dist(y,q) < e`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN IMAGE (f:real^M->real^N) (relative_frontier k)` THEN
  REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `y0:real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y0:real^M) IN k` ASSUME_TAC THENL
   [UNDISCH_TAC `(y0:real^M) IN relative_frontier k` THEN
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; IN_DIFF];
    ALL_TAC] THEN
  UNDISCH_TAC `(f:real^M->real^N) continuous_on k` THEN
  REWRITE_TAC[continuous_on] THEN DISCH_THEN(MP_TAC o SPEC `y0:real^M`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `del:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y0:real^M) IN closure(relative_interior k)` MP_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `del:real`) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `x:real^M` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^M) IN k` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  EXISTS_TAC `(f:real^M->real^N) x` THEN REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^M` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^M) IN k` ASSUME_TAC THENL
     [UNDISCH_TAC `(z:real^M) IN relative_frontier k` THEN
      ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; IN_DIFF];
      ALL_TAC] THEN
    SUBGOAL_THEN `x:real^M = z` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(z:real^M) IN relative_frontier k` THEN
    ASM_SIMP_TAC[relative_frontier; CLOSURE_CLOSED; IN_DIFF];
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_SIMP_TAC[]]);;

(* The sector of a direction is unchanged by positive scaling and by       *)
(* adding multiples of the axis.                                              *)
let MOI_FSTR_SEC_SCALE = prove
 (`!(t:real^3) a b w mu s.
     &0 < mu ==> (moi_fstr_sec t a b (mu % w + s % t) <=> moi_fstr_sec t a b w)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fstr_sec] THEN
  REWRITE_TAC[DOT_RADD; DOT_RMUL; CROSS_RADD; CROSS_RMUL; CROSS_REFL; DOT_LADD; DOT_LMUL;
              VECTOR_MUL_RZERO; VECTOR_ADD_RID; DOT_CROSS_SELF; DOT_LZERO;
              REAL_MUL_RZERO; REAL_ADD_RID] THEN
  ASM_SIMP_TAC[REAL_LT_MUL_EQ]);;

let MOI_FSTR_CARD3 = prove
 (`!(a:A) b c. ~(a = b) /\ ~(a = c) /\ ~(b = c) ==> CARD {a,b,c} = 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a:A,b,c} HAS_SIZE 3` MP_TAC THENL
   [CONV_TAC HAS_SIZE_CONV THEN MAP_EVERY EXISTS_TAC [`a:A`; `b:A`; `c:A`] THEN
    ASM_REWRITE_TAC[];
    SIMP_TAC[HAS_SIZE]]);;

(* An ld-triangle at a rim edge: the disk leaves the edge. *)
let MOI_FSTR_RIM_SIMPLEX = prove
 (`!(ld:(real^3->bool)->bool) lj (k:real^3->bool) f g v w y.
     FINITE ld /\ lf_simplicial_complex ld /\ simplicial_subcomplex lj ld /\
     convex k /\ closed k /\ homeomorphism (k,UNIONS ld) (f,g) /\
     UNIONS lj = IMAGE f (relative_frontier k) /\
     segment[v,w] IN lj /\ ~(v = w) /\ y IN segment(v,w)
     ==> ?x. convex hull {v,w,x} SUBSET UNIONS ld /\ aff_dim(convex hull {v,w,x}) = &2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `segment[v:real^3,w] IN ld` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (ld:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_LF_SC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ld:(real^3->bool)->bool`; `v:real^3`; `w:real^3`] MOI_FSTR_EDGE_ENDS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN segment[v,w]` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; SEGMENT_OPEN_SUBSET_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS lj` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS ld` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ld:(real^3->bool)->bool`; `y:real^3`] MOI_CMB_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`f:real^3->real^3`; `g:real^3->real^3`; `k:real^3->bool`;
                 `UNIONS ld:real^3->bool`; `y:real^3`; `e1:real`] MOI_FSTR_CHART_ACCUM) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:real^3` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `e1:real`)) (concl th))) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  (* the simplex s contains the edge, and is not the edge *)
  SUBGOAL_THEN `segment[v:real^3,w] SUBSET s` ASSUME_TAC THENL
   [SUBGOAL_THEN `(segment[v:real^3,w] INTER s) face_of segment[v,w]` ASSUME_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (ld:(real^3->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) INTER b = a ==> a SUBSET b`) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`segment[v:real^3,w] INTER s`; `segment[v:real^3,w]`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(s = segment[v:real^3,w])` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~((q:real^3) IN IMAGE (f:real^3->real^3) (relative_frontier k))` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS lj:real^3->bool`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  (* a third vertex of s *)
  MP_TAC(ISPECL [`ld:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_VS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `s:real^3->bool`)) THEN
  SUBGOAL_THEN `(v:real^3) IN s /\ w IN s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^3) IN moi_fsa_vs s /\ w IN moi_fsa_vs s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_VS_MEM]; ALL_TAC] THEN
  SUBGOAL_THEN `?x:real^3. x IN moi_fsa_vs s /\ ~(x = v) /\ ~(x = w)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    UNDISCH_TAC `~(s = segment[v:real^3,w])` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `s:real^3->bool`
                            then SUBST1_TAC(SYM th) else failwith "no") THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `x:real^3` THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^3->bool` THEN CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `s:real^3->bool`
                              then GEN_REWRITE_TAC RAND_CONV [SYM th] else failwith "no") THEN
      MATCH_MP_TAC HULL_MONO THEN REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]];
    SUBGOAL_THEN `~affine_dependent {v:real^3,w,x}` ASSUME_TAC THENL
     [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN
      EXISTS_TAC `moi_fsa_vs (s:real^3->bool)` THEN
      CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
    MP_TAC(ISPEC `{v:real^3,w,x}` AFF_DIM_AFFINE_INDEPENDENT) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL [`v:real^3`; `w:real^3`; `x:real^3`] MOI_FSTR_CARD3) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      FIRST_ASSUM(ACCEPT_TAC o GSYM);
      DISCH_THEN SUBST1_TAC] THEN
    CONV_TAC INT_REDUCE_CONV]);;

(* Near y in the rim edge, the rim is the edge, so the points of a triangle *)
(* of the disk at the edge just off the edge are off the rim.               *)
let MOI_FSTR_RIM_OFF = prove
 (`!(lj:(real^3->bool)->bool) v w x y.
     lf_simplicial_complex lj /\ (!s. s IN lj ==> aff_dim s <= &1) /\
     segment[v,w] IN lj /\ ~(v = w) /\ y IN segment(v,w) /\
     aff_dim(convex hull {v,w,x}) = &2
     ==> ?h. &0 < h /\ !mu. &0 < mu /\ mu < h ==> ~(y + mu % (x - y) IN UNIONS lj)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN segment[v,w]` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; SEGMENT_OPEN_SUBSET_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS lj` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[v:real^3,w]` THEN
    ASM_MESON_TAC[SUBSET; SEGMENT_OPEN_SUBSET_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lj:(real^3->bool)->bool`; `y:real^3`] MOI_CMB_STAR_NBHD) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `e1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!z:real^3. z IN UNIONS lj /\ dist(y,z) < e1 ==> z IN segment[v,w]`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(segment[v:real^3,w] INTER s) face_of segment[v,w] /\
                  (segment[v,w] INTER s) face_of s`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (lj:(real^3->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[v:real^3,w] INTER s = segment[v,w]` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`segment[v:real^3,w] INTER s`; `segment[v:real^3,w]`]
        FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `s = segment[v:real^3,w]` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`segment[v:real^3,w]`; `s:real^3->bool`] FACE_OF_AFF_DIM_LT) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `lf_simplicial_complex (lj:(real^3->bool)->bool)` THEN
        REWRITE_TAC[lf_simplicial_complex] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^3->bool` o CONJUNCT1) THEN
        ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
        ASM_MESON_TAC[];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s:real^3->bool` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `aff_dim:(real^3->bool)->int`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`&1`; `norm(x - y:real^3)`; `e1:real`] MOI_FSTR_SMALL) THEN
  ASM_REWRITE_TAC[NORM_POS_LE; REAL_LT_01] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `mu:real` THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `y + mu % (x - y) IN segment[v:real^3,w]` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[dist; VECTOR_ARITH `y - (y + mu % x):real^3 = --(mu % x)`] THEN
    REWRITE_TAC[NORM_NEG; NORM_MUL] THEN
    ASM_SIMP_TAC[REAL_ARITH `&0 < mu ==> abs mu = mu`] THEN
    MATCH_MP_TAC REAL_LET_TRANS THEN EXISTS_TAC `h * norm(x - y:real^3)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC REAL_LE_RMUL THEN
    ASM_SIMP_TAC[NORM_POS_LE; REAL_LT_IMP_LE];
    ALL_TAC] THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `(y:real^3) IN segment(v,w)` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `s0:real` STRIP_ASSUME_TAC o CONJUNCT2) THEN
  MP_TAC(ISPECL [`v:real^3`; `w:real^3`; `x:real^3`] MOI_FSTR_TRI_NORMAL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(w - v) cross (x - v:real^3) =
                inv mu % ((w - v) cross ((y + mu % (x - y)) - v))`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `(y + mu % (x - y)) - v:real^3 = (&1 - mu) % (y - v) + mu % (x - v)`
    SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `y - v:real^3 = s0 % (w - v)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[CROSS_RADD; CROSS_RMUL; CROSS_REFL; VECTOR_MUL_RZERO; VECTOR_ADD_LID] THEN
    REWRITE_TAC[VECTOR_MUL_ASSOC] THEN
    ASM_SIMP_TAC[REAL_MUL_LINV; REAL_LT_IMP_NZ; VECTOR_MUL_LID];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y + mu % (x - y)) - v:real^3 = s1 % (w - v)` SUBST1_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `y + mu % (x - y):real^3`)) THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[CROSS_RMUL; CROSS_REFL; VECTOR_MUL_RZERO]);;

(* At a point y of a rim edge near an end u, the sign at u says whether the *)
(* disk leaves the edge into the sector next to the first triangle.         *)
let MOI_FSTR_SG_SIDE_AT = prove
 (`!(lm:(real^3->bool)->bool) ld lj u r D E v w x x' y gx.
     FINITE lm /\ combinatorial_manifold 2 lm /\
     convex hull {v,w,x} IN lm /\ aff_dim(convex hull {v,w,x}) = &2 /\
     convex hull {v,w,x'} IN lm /\ aff_dim(convex hull {v,w,x'}) = &2 /\ ~(x = x') /\
     (u = v \/ u = w) /\ moi_fstr_sides (UNIONS lm) u r D E /\
     (UNIONS ld INTER ball(u,r)) DIFF UNIONS lj SUBSET D /\
     UNIONS ld INTER UNIONS lm = UNIONS lj /\
     y IN segment(v,w) /\ y IN ball(u,r) /\
     convex hull {v,w,gx} SUBSET UNIONS ld /\
     (?h. &0 < h /\ !mu. &0 < mu /\ mu < h ==> ~(y + mu % (gx - y) IN UNIONS lj))
     ==> (moi_fstr_posn D u r (convex hull {v,w,x}) ((w - v) cross (x - v)) <=>
          moi_fstr_sec (w - v) (moi_fstr_perp (w - v) (x - v))
                       (moi_fstr_perp (w - v) (x' - v)) (gx - y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `h:real` STRIP_ASSUME_TAC o check (is_exists o concl)) THEN
  SUBGOAL_THEN `lf_simplicial_complex (lm:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `v:real^3`; `w:real^3`; `x:real^3`;
                 `x':real^3`] MOI_FSTR_EDGE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(u:real^3) IN convex hull {v,w,x}` ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `&0 < r /\ DISJOINT (D:real^3->bool) E` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_fstr_sides]; ALL_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `v:real^3`; `w:real^3`; `x:real^3`;
                 `x':real^3`; `y:real^3`] MOI_FSTR_EDGE_PAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho1:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v:real^3`; `w:real^3`; `x:real^3`; `y:real^3`] MOI_FSTR_PAGE_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ea:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v:real^3`; `w:real^3`; `x':real^3`; `y:real^3`] MOI_FSTR_PAGE_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `ea':real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `rho = min (min rho1 (r - dist(u:real^3,y))) (min ea ea')` THEN
  SUBGOAL_THEN `&0 < rho /\ rho <= ea /\ rho <= ea' /\ ball(y:real^3,rho) SUBSET ball(u,r) /\
                UNIONS lm INTER ball(y,rho) SUBSET
                convex hull {v,w,x} UNION convex hull {v,w,x'}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN ball(u,r)` THEN REWRITE_TAC[IN_BALL] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "rho" THEN ASM_REAL_ARITH_TAC;
      EXPAND_TAC "rho" THEN REAL_ARITH_TAC;
      EXPAND_TAC "rho" THEN REAL_ARITH_TAC;
      REWRITE_TAC[SUBSET; IN_BALL] THEN X_GEN_TAC `z:real^3` THEN
      MP_TAC(ISPECL [`u:real^3`; `y:real^3`; `z:real^3`] DIST_TRIANGLE) THEN
      EXPAND_TAC "rho" THEN REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS lm INTER ball(y:real^3,rho1)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (M:real^3->bool) INTER s SUBSET M INTER t`) THEN
      MATCH_MP_TAC SUBSET_BALL THEN EXPAND_TAC "rho" THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `u:real^3`; `r:real`; `D:real^3->bool`;
                 `E:real^3->bool`; `v:real^3`; `w:real^3`; `x:real^3`; `x':real^3`;
                 `y:real^3`; `rho:real`] MOI_FSTR_SECTOR_SIDES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `u:real^3`; `r:real`; `D:real^3->bool`;
                 `E:real^3->bool`; `v:real^3`; `w:real^3`; `x:real^3`; `x':real^3`;
                 `y:real^3`; `rho:real`] MOI_FSTR_NORMAL_WITNESS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z1:real^3` STRIP_ASSUME_TAC) THEN
  (* the disk point q *)
  MP_TAC(ISPECL [`min h (&1)`; `norm(gx - y:real^3)`; `rho:real`] MOI_FSTR_SMALL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[NORM_POS_LE; REAL_LT_MIN; REAL_LT_01]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real` (STRIP_ASSUME_TAC o REWRITE_RULE[REAL_LT_MIN])) THEN
  ABBREV_TAC `q:real^3 = y + mu % (gx - y)` THEN
  SUBGOAL_THEN `(q:real^3) IN ball(y,rho)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    REWRITE_TAC[IN_BALL; dist; VECTOR_ARITH `y - (y + mu % x):real^3 = --(mu % x)`] THEN
    ASM_SIMP_TAC[NORM_NEG; NORM_MUL; REAL_ARITH `&0 < mu ==> abs mu = mu`];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN convex hull {v,w,gx}` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    REWRITE_TAC[VECTOR_ARITH `y + mu % (gx - y):real^3 = (&1 - mu) % y + mu % gx`] THEN
    MATCH_MP_TAC(REWRITE_RULE[convex] (ISPEC `{v:real^3,w,gx}` CONVEX_CONVEX_HULL)) THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `segment[v:real^3,w] SUBSET convex hull {v,w,gx}` MP_TAC THENL
       [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
        ASM_MESON_TAC[SUBSET; SEGMENT_OPEN_SUBSET_CLOSED]];
      MATCH_MP_TAC HULL_INC THEN SET_TAC[];
      ASM_REAL_ARITH_TAC;
      ASM_REAL_ARITH_TAC;
      REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((q:real^3) IN UNIONS lj)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[IMP_IMP] o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `h:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3) IN D /\ ~(q IN UNIONS lm)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]]; ALL_TAC] THEN
  (* q - y is on neither page *)
  SUBGOAL_THEN
   `~(?s u. &0 <= u /\ q - y = s % (w - v) + u % moi_fstr_perp (w - v) (x - v:real^3))`
  ASSUME_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`s:real`; `uu:real`] THEN
    STRIP_TAC THEN UNDISCH_TAC `~((q:real^3) IN UNIONS lm)` THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `convex hull {v:real^3,w,x}` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `q:real^3 = y + (q - y)` SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `q - y:real^3`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ea:real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `q - y:real^3`)) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(q:real^3) IN ball(y,rho)` THEN REWRITE_TAC[IN_BALL; dist] THEN
    MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~(?s u. &0 <= u /\ q - y = s % (w - v) + u % moi_fstr_perp (w - v) (x' - v:real^3))`
  ASSUME_TAC THENL
   [REWRITE_TAC[NOT_EXISTS_THM] THEN MAP_EVERY X_GEN_TAC [`s:real`; `uu:real`] THEN
    STRIP_TAC THEN UNDISCH_TAC `~((q:real^3) IN UNIONS lm)` THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `convex hull {v:real^3,w,x'}` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `q:real^3 = y + (q - y)` SUBST1_TAC THENL [VECTOR_ARITH_TAC; ALL_TAC] THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `q - y:real^3`)) THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `ea':real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `q - y:real^3`)) THEN
    MATCH_MP_TAC REAL_LTE_TRANS THEN EXISTS_TAC `rho:real` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(q:real^3) IN ball(y,rho)` THEN REWRITE_TAC[IN_BALL; dist] THEN
    MESON_TAC[NORM_SUB];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w - v:real^3`; `moi_fstr_perp (w - v) (x - v:real^3)`;
                 `moi_fstr_perp (w - v) (x' - v:real^3)`; `q - y:real^3`]
    MOI_FSTR_SEC_COVER) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  SUBGOAL_THEN `!a b:real^3. moi_fstr_sec (w - v) a b (gx - y) <=>
                             moi_fstr_sec (w - v) a b (q - y)`
  (fun th -> REWRITE_TAC[th]) THENL
   [REPEAT GEN_TAC THEN
    SUBGOAL_THEN `q - y:real^3 = mu % (gx - y) + &0 % (w - v)` SUBST1_TAC THENL
     [EXPAND_TAC "q" THEN VECTOR_ARITH_TAC; ASM_SIMP_TAC[MOI_FSTR_SEC_SCALE]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th ->
    is_disj(concl th) && is_conj(lhand(concl th)) &&
    is_binary "SUBSET" (lhand(lhand(concl th))))) THEN
  ASM_CASES_TAC
   `moi_fstr_posn D (u:real^3) r (convex hull {v,w,x}) ((w - v) cross (x - v))` THEN
  ASM_CASES_TAC
   `moi_fstr_sec (w - v) (moi_fstr_perp (w - v) (x - v:real^3))
                 (moi_fstr_perp (w - v) (x' - v:real^3)) (q - y)` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* (O3) for a triangle (v,w,x) at a rim edge [v,w]: the signs at v and w agree. *)
let MOI_FSTR_SG_RIM = prove
 (`!(lm:(real^3->bool)->bool) ld lj (k:real^3->bool) (f:real^3->real^3) g v w x
     rv Dv Ev rw Dw Ew.
     FINITE lm /\ combinatorial_manifold 2 lm /\
     FINITE ld /\ lf_simplicial_complex ld /\ simplicial_subcomplex lj ld /\
     (!s. s IN lj ==> aff_dim s <= &1) /\
     convex k /\ closed k /\ homeomorphism (k,UNIONS ld) (f,g) /\
     UNIONS lj = IMAGE f (relative_frontier k) /\
     UNIONS ld INTER UNIONS lm = UNIONS lj /\
     segment[v,w] IN lj /\ segment[v,w] IN lm /\ ~(v = w) /\
     convex hull {v,w,x} IN lm /\ aff_dim(convex hull {v,w,x}) = &2 /\
     moi_fstr_sides (UNIONS lm) v rv Dv Ev /\
     (UNIONS ld INTER ball(v,rv)) DIFF UNIONS lj SUBSET Dv /\
     moi_fstr_sides (UNIONS lm) w rw Dw Ew /\
     (UNIONS ld INTER ball(w,rw)) DIFF UNIONS lj SUBSET Dw
     ==> moi_fstr_sg Dw w rw v w x = moi_fstr_sg Dv v rv v w x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (lj:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBCOMPLEX THEN EXISTS_TAC `ld:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `v:real^3`; `w:real^3`; `x:real^3`]
    MOI_FSTR_OTHER_TRI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x':real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < rv /\ &0 < rw` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_fstr_sides]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v:real^3`; `w:real^3`; `v:real^3`; `rv:real`] MOI_FSTR_SEG_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`v:real^3`; `w:real^3`; `w:real^3`; `rw:real`] MOI_FSTR_SEG_NEAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`ld:(real^3->bool)->bool`; `lj:(real^3->bool)->bool`; `k:real^3->bool`;
                 `f:real^3->real^3`; `g:real^3->real^3`; `v:real^3`; `w:real^3`;
                 `y1:real^3`] MOI_FSTR_RIM_SIMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gx:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`lj:(real^3->bool)->bool`; `v:real^3`; `w:real^3`; `gx:real^3`;
                 `y1:real^3`] MOI_FSTR_RIM_OFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`lj:(real^3->bool)->bool`; `v:real^3`; `w:real^3`; `gx:real^3`;
                 `y2:real^3`] MOI_FSTR_RIM_OFF) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                 `lj:(real^3->bool)->bool`; `v:real^3`; `rv:real`; `Dv:real^3->bool`;
                 `Ev:real^3->bool`; `v:real^3`; `w:real^3`; `x:real^3`; `x':real^3`;
                 `y1:real^3`; `gx:real^3`] MOI_FSTR_SG_SIDE_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                 `lj:(real^3->bool)->bool`; `w:real^3`; `rw:real`; `Dw:real^3->bool`;
                 `Ew:real^3->bool`; `v:real^3`; `w:real^3`; `x:real^3`; `x':real^3`;
                 `y2:real^3`; `gx:real^3`] MOI_FSTR_SG_SIDE_AT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; DISCH_TAC] THEN
  (* the sector of gx is the same from y1 and from y2 *)
  SUBGOAL_THEN
   `moi_fstr_sec (w - v) (moi_fstr_perp (w - v) (x - v:real^3))
                 (moi_fstr_perp (w - v) (x' - v)) (gx - y2) <=>
    moi_fstr_sec (w - v) (moi_fstr_perp (w - v) (x - v:real^3))
                 (moi_fstr_perp (w - v) (x' - v)) (gx - y1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(y1:real^3) IN segment(v,w)` THEN
    UNDISCH_TAC `(y2:real^3) IN segment(v,w)` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `t2:real` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real` STRIP_ASSUME_TAC o CONJUNCT2) THEN
    SUBGOAL_THEN `gx - y2:real^3 = &1 % (gx - y1) + (t1 - t2) % (w - v)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
      SIMP_TAC[MOI_FSTR_SEC_SCALE; REAL_LT_01]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_fstr_sg] THEN ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The half-star labelling around a vertex w of a combinatorial surface.    *)
(* With the triangles at w enumerated cyclically as conv{w,S i,S(i+1)} and  *)
(* a sign at w satisfying (O1) and (O2), the triangles split into the two    *)
(* halves cut out by the edges [w,S 0] and [w,S a]; the labelling is        *)
(* constant across the other edges at w and is read off the sign at the    *)
(* two cutting edges (left of S a -> w -> S 0).                             *)
(* ------------------------------------------------------------------------- *)

let MOI_FSTR_TRI_VERTS = prove
 (`!(cx:(real^N->bool)->bool) a b d u.
     simplicial_complex cx /\ convex hull {a,b,d} IN cx /\
     aff_dim(convex hull {a,b,d}) = &2 /\ {u} IN cx /\ u IN convex hull {a,b,d}
     ==> u = a \/ u = b \/ u = d`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`cx:(real^N->bool)->bool`; `convex hull {a:real^N,b,d}`; `u:real^N`]
    MOI_FSA_VS_MEM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o fst o EQ_IMP_RULE) THEN ANTS_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `d:real^N`] MOI_FSTR_TRI_INDEP) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  ASM_SIMP_TAC[MOI_FSA_VS_HULL] THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]);;

(* The sign is constant along the cyclic enumeration. *)
let MOI_FSTR_HS_CONST = prove
 (`!(cx:(real^N->bool)->bool) (sg:real^N->real^N->real^N->real) w n (S:num->real^N).
     3 <= n /\ S n = S 0 /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. i < n ==> convex hull {w, S i, S(SUC i)} IN cx /\
                    aff_dim(convex hull {w, S i, S(SUC i)}) = &2) /\
     (!a b d. convex hull {a,b,d} IN cx /\ aff_dim(convex hull {a,b,d}) = &2 /\
              w IN {a,b,d}
              ==> (sg a b d = &1 \/ sg a b d = -- &1) /\
                  sg b a d = --(sg a b d) /\ sg a d b = --(sg a b d)) /\
     (!a b d d'. w IN {a,b} /\ ~(d = d') /\
                 convex hull {a,b,d} IN cx /\ aff_dim(convex hull {a,b,d}) = &2 /\
                 convex hull {a,b,d'} IN cx /\ aff_dim(convex hull {a,b,d'}) = &2
                 ==> sg a b d' = --(sg a b d))
     ==> !i. i < n ==> sg w (S i) (S(SUC i)) = sg w (S 0) (S 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN INDUCT_TAC THENL
   [REWRITE_TAC[ONE]; ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    can (find_term ((=) `sg:real^N->real^N->real^N->real`)) (concl th))) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
  SUBGOAL_THEN `convex hull {w,S(SUC i),S i} = convex hull {w:real^N,S i,S(SUC i)}`
  ASSUME_TAC THENL [AP_TERM_TAC THEN SET_TAC[]; ALL_TAC] THEN
  MAP_EVERY (fun j -> FIRST_ASSUM(MP_TAC o SPEC j o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; STRIP_TAC]) [`i:num`; `SUC i`] THEN
  SUBGOAL_THEN `~((S:num->real^N) i = S(SUC(SUC i)))` ASSUME_TAC THENL
   [DISCH_TAC THEN ASM_CASES_TAC `SUC(SUC i) < n` THENL
     [SUBGOAL_THEN `i = SUC(SUC i)` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ARITH_TAC];
      SUBGOAL_THEN `SUC(SUC i) = n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `i = 0` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        REPEAT CONJ_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC; ASM_MESON_TAC[]];
        ASM_ARITH_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:real^N`; `(S:num->real^N)(SUC i)`; `(S:num->real^N) i`;
                 `(S:num->real^N)(SUC(SUC i))`]
    (ASSUME `!a b d d'. w IN {a,b} /\ ~(d = d') /\
                 convex hull {a,b,d} IN cx /\ aff_dim(convex hull {a,b,d}) = &2 /\
                 convex hull {a,b,d'} IN cx /\ aff_dim(convex hull {a,b,d'}) = &2
                 ==> (sg:real^N->real^N->real^N->real) a b d' = --(sg a b d)`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`w:real^N`; `(S:num->real^N) i`; `(S:num->real^N)(SUC i)`]
    (ASSUME `!a b d. convex hull {a,b,d} IN cx /\ aff_dim(convex hull {a,b,d}) = &2 /\
              w IN {a,b,d}
              ==> ((sg:real^N->real^N->real^N->real) a b d = &1 \/ sg a b d = -- &1) /\
                  sg b a d = --(sg a b d) /\ sg a d b = --(sg a b d)`)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; STRIP_TAC] THEN
  ASM_REWRITE_TAC[REAL_NEG_NEG]);;

(* Index bookkeeping for a cyclic enumeration with S n = S 0. *)
let MOI_FSTR_HS_IDX = prove
 (`!(S:num->A) n k m.
     S n = S 0 /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     k <= n /\ m < n /\ S k = S m
     ==> k = m \/ (k = n /\ m = 0)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `k:num = n` THENL
   [DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ASM_MESON_TAC[]];
    DISJ1_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* The triangles of the enumeration are pairwise distinct. *)
let MOI_FSTR_HS_DISTINCT = prove
 (`!(cx:(real^N->bool)->bool) w n (S:num->real^N).
     3 <= n /\ S n = S 0 /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. i < n ==> convex hull {w, S i, S(SUC i)} IN cx /\
                    aff_dim(convex hull {w, S i, S(SUC i)}) = &2)
     ==> !i j. i < n /\ j < n /\
               convex hull {w, S i, S(SUC i)} = convex hull {w, S j, S(SUC j)}
               ==> i = j`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
  MAP_EVERY (fun k -> FIRST_ASSUM(MP_TAC o SPEC k o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`w:real^N`; mk_comb(`S:num->real^N`,k);
                   mk_comb(`S:num->real^N`,mk_comb(`SUC`,k))] MOI_FSTR_TRI_INDEP) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC]) [`i:num`; `j:num`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `{w:real^N,S i,S(SUC i)} = {w,S j,S(SUC j)}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `{w:real^N,S i,S(SUC i)}` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    MP_TAC(ISPEC `{w:real^N,S j,S(SUC j)}` EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((S:num->real^N) i = S j)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(S:num->real^N) i = S(SUC j) /\ S j = S(SUC i)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o AP_TERM `(IN) ((S:num->real^N) i)` o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `{w:real^N,S i,S(SUC i)}`));
      FIRST_X_ASSUM(MP_TAC o AP_TERM `(IN) ((S:num->real^N) j)` o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `{w:real^N,S i,S(SUC i)}`))] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:num->real^N`; `n:num`; `SUC j`; `i:num`] MOI_FSTR_HS_IDX) THEN
  MP_TAC(ISPECL [`S:num->real^N`; `n:num`; `SUC i`; `j:num`] MOI_FSTR_HS_IDX) THEN
  ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC);;

(* The half-star labelling. *)
let MOI_FSTR_HALFSTAR = prove
 (`!(cx:(real^N->bool)->bool) (sg:real^N->real^N->real^N->real) w n (S:num->real^N) a.
     FINITE cx /\ combinatorial_manifold 2 cx /\ {w} IN cx /\
     3 <= n /\ S n = S 0 /\ (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     (!i. i < n ==> convex hull {w, S i, S(SUC i)} IN cx /\
                    aff_dim(convex hull {w, S i, S(SUC i)}) = &2) /\
     (!t. t IN cx /\ aff_dim t = &2 /\ w IN t
          ==> ?i. i < n /\ t = convex hull {w, S i, S(SUC i)}) /\
     (!a b d. convex hull {a,b,d} IN cx /\ aff_dim(convex hull {a,b,d}) = &2 /\
              w IN {a,b,d}
              ==> (sg a b d = &1 \/ sg a b d = -- &1) /\
                  sg b a d = --(sg a b d) /\ sg a d b = --(sg a b d)) /\
     (!a b d d'. w IN {a,b} /\ ~(d = d') /\
                 convex hull {a,b,d} IN cx /\ aff_dim(convex hull {a,b,d}) = &2 /\
                 convex hull {a,b,d'} IN cx /\ aff_dim(convex hull {a,b,d'}) = &2
                 ==> sg a b d' = --(sg a b d)) /\
     0 < a /\ a < n
     ==> ?left:(real^N->bool)->bool.
           (!t t' u. t IN cx /\ aff_dim t = &2 /\ w IN t /\
                     t' IN cx /\ aff_dim t' = &2 /\ w IN t' /\
                     {u} IN cx /\ u IN t /\ u IN t' /\
                     ~(u = w) /\ ~(u = S 0) /\ ~(u = S a)
                     ==> (left t <=> left t')) /\
           (!x. convex hull {w, S 0, x} IN cx /\ aff_dim(convex hull {w, S 0, x}) = &2
                ==> (left(convex hull {w, S 0, x}) <=> sg w (S 0) x = &1)) /\
           (!x. convex hull {w, S a, x} IN cx /\ aff_dim(convex hull {w, S a, x}) = &2
                ==> (left(convex hull {w, S a, x}) <=> sg (S a) w x = &1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (cx:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cx:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`; `w:real^N`;
                 `n:num`; `S:num->real^N`] MOI_FSTR_HS_CONST) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`cx:(real^N->bool)->bool`; `w:real^N`; `n:num`; `S:num->real^N`]
    MOI_FSTR_HS_DISTINCT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  (* facts on the triangles *)
  SUBGOAL_THEN
   `!k. k < n ==> {(S:num->real^N) k} IN cx /\ {S(SUC k)} IN cx /\
                  ~(w = S k) /\ ~(w = S(SUC k)) /\ ~(S k = S(SUC k))`
  ASSUME_TAC THENL
   [X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `k:num` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`w:real^N`; `(S:num->real^N) k`; `(S:num->real^N)(SUC k)`]
      MOI_FSTR_TRI_INDEP) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`cx:(real^N->bool)->bool`; `convex hull {w:real^N,S k,S(SUC k)}`]
      MOI_FSA_VS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_fsa_vs (convex hull {w:real^N,S k,S(SUC k)}) = {w,S k,S(SUC k)}`
    SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_FSA_VS_HULL THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    STRIP_TAC THEN CONJ_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  ABBREV_TAC `eps = (sg:real^N->real^N->real^N->real) w (S 0) (S 1)` THEN
  SUBGOAL_THEN `eps = &1 \/ eps = -- &1` ASSUME_TAC THENL
   [EXPAND_TAC "eps" THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N`; `(S:num->real^N) 0`; `(S:num->real^N) 1`] o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_INSERT] THEN REWRITE_TAC[ONE] THEN
      FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th))) THEN
      ASM_ARITH_TAC;
      SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i. i < n ==> ((?k. k < a /\ convex hull {w,S i,S(SUC i)} =
                                 convex hull {w:real^N,S k,S(SUC k)}) <=> i < a)`
  ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `i:num = k` (fun th -> ASM_REWRITE_TAC[th]) THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun tm -> try fst(dest_const tm) = "hull" with _ -> false))
            (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      DISCH_TAC THEN EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `\t:real^N->bool. (?i. i < a /\ t = convex hull {w, S i, S(SUC i)}) <=>
                                eps = &1` THEN
  REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* (i) the labelling is constant across the other edges at w *)
    MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `t':real^N->bool`; `u:real^N`] THEN STRIP_TAC THEN
    MAP_EVERY (fun (tt,ii) ->
      FIRST_ASSUM(MP_TAC o SPEC tt o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        is_exists(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN ii STRIP_ASSUME_TAC)])
      [`t:real^N->bool`,`i:num`; `t':real^N->bool`,`j:num`] THEN
    REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
      (lhs(concl th) = `t:real^N->bool` || lhs(concl th) = `t':real^N->bool`)))) THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `a:num`)) (concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "hull" with _ -> false)) (concl th) &&
        is_imp(snd(strip_forall(concl th))) &&
        is_iff(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `a:num`)) (concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "hull" with _ -> false)) (concl th) &&
        is_imp(snd(strip_forall(concl th))) &&
        is_iff(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    MATCH_MP_TAC(TAUT `(p <=> q) ==> ((p <=> r) <=> (q <=> r))`) THEN
    SUBGOAL_THEN
     `!k. k < n /\ (u:real^N) IN convex hull {w,S k,S(SUC k)}
          ==> ?p. p < n /\ (p = k \/ p = SUC k) /\ u = S p`
    ASSUME_TAC THENL
     [X_GEN_TAC `k:num` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`cx:(real^N->bool)->bool`; `w:real^N`; `(S:num->real^N) k`;
                     `(S:num->real^N)(SUC k)`; `u:real^N`] MOI_FSTR_TRI_VERTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
         [EXISTS_TAC `k:num` THEN ASM_REWRITE_TAC[];
          ASM_CASES_TAC `SUC k = n` THENL
           [UNDISCH_TAC `~((u:real^N) = S 0)` THEN ASM_MESON_TAC[];
            EXISTS_TAC `SUC k` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `p:num` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `j:num`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `q:num` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)))] THEN
    SUBGOAL_THEN `p:num = q` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        not (can (find_term (fun tm -> try fst(dest_const tm) = "hull" with _ -> false))
                 (concl th)))) THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(p:num = a)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_ARITH_TAC;
    (* (ii) at the edge [w,S 0] *)
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `convex hull {w:real^N,S 0,x}` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      is_exists(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(S:num->real^N) 0 = S i \/ S 0 = S(SUC i)` MP_TAC THENL
     [MP_TAC(ISPECL [`cx:(real^N->bool)->bool`; `w:real^N`; `(S:num->real^N) i`;
                     `(S:num->real^N)(SUC i)`; `(S:num->real^N) 0`] MOI_FSTR_TRI_VERTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[ARITH_RULE `3 <= n ==> 0 < n`];
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
            lhs(concl th) = `convex hull {w:real^N,S 0,x}`)) THEN
          MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
        ASM_MESON_TAC[ARITH_RULE `3 <= n ==> 0 < n`]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
        lhs(concl th) = `convex hull {w:real^N,S 0,x}`
      then SUBST1_TAC th THEN ASSUME_TAC th else failwith "no") THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `a:num`)) (concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "hull" with _ -> false)) (concl th) &&
        is_imp(snd(strip_forall(concl th))) &&
        is_iff(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    STRIP_TAC THENL
     [(* S 0 = S i: i = 0 and x = S 1 *)
      SUBGOAL_THEN `i = 0` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
          not (can (find_term (fun tm -> try fst(dest_const tm) = "hull" with _ -> false))
                   (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `x:real^N = S 1` SUBST1_TAC THENL
       [MATCH_MP_TAC MOI_FSTR_TRI_EQ THEN
        MAP_EVERY EXISTS_TAC [`w:real^N`; `(S:num->real^N) 0`] THEN
        ASM_REWRITE_TAC[GSYM ONE];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      (* S 0 = S(SUC i): SUC i = n and x = S i *)
      MP_TAC(ISPECL [`S:num->real^N`; `n:num`; `SUC i`; `0`] MOI_FSTR_HS_IDX) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[NOT_SUC] THEN DISCH_TAC THEN
      SUBGOAL_THEN `~(i:num < a)` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `convex hull {w,S i,S(SUC i)} = convex hull {w:real^N,S 0,S i}`
      ASSUME_TAC THENL
       [UNDISCH_TAC `(S:num->real^N) 0 = S(SUC i)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        AP_TERM_TAC THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `x:real^N = (S:num->real^N) i` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC MOI_FSTR_TRI_EQ THEN
        MAP_EVERY EXISTS_TAC [`w:real^N`; `(S:num->real^N) 0`] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `eps:real`)) (concl th))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(S:num->real^N) 0 = S(SUC i)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N`; `(S:num->real^N) i`; `(S:num->real^N) 0`] o
        check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_INSERT] THEN
        SUBGOAL_THEN `convex hull {w,S i,S 0} = convex hull {w:real^N,S 0,S i}`
        SUBST1_TAC THENL [AP_TERM_TAC THEN SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(STRIP_ASSUME_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC];
    (* (iii) at the edge [w,S a] *)
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    FIRST_ASSUM(MP_TAC o SPEC `convex hull {w:real^N,(S:num->real^N) a,x}` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      is_exists(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term ((=) `aff_dim:(real^N->bool)->int`)) (concl th))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    SUBGOAL_THEN `(S:num->real^N) a = S i \/ S a = S(SUC i)` MP_TAC THENL
     [MP_TAC(ISPECL [`cx:(real^N->bool)->bool`; `w:real^N`; `(S:num->real^N) i`;
                     `(S:num->real^N)(SUC i)`; `(S:num->real^N) a`] MOI_FSTR_TRI_VERTS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[];
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
            lhs(concl th) = `convex hull {w:real^N,(S:num->real^N) a,x}`)) THEN
          MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
        ASM_MESON_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
        lhs(concl th) = `convex hull {w:real^N,(S:num->real^N) a,x}`
      then SUBST1_TAC th THEN ASSUME_TAC th else failwith "no") THEN
    FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `a:num`)) (concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "hull" with _ -> false)) (concl th) &&
        is_imp(snd(strip_forall(concl th))) &&
        is_iff(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_THEN(fun th -> REWRITE_TAC[th])] THEN
    STRIP_TAC THENL
     [(* S a = S i: i = a and x = S(SUC a) *)
      SUBGOAL_THEN `i:num = a` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
          not (can (find_term (fun tm -> try fst(dest_const tm) = "hull" with _ -> false))
                   (concl th)))) THEN
        ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[LT_REFL] THEN
      SUBGOAL_THEN `x:real^N = (S:num->real^N)(SUC a)` SUBST1_TAC THENL
       [MATCH_MP_TAC MOI_FSTR_TRI_EQ THEN
        MAP_EVERY EXISTS_TAC [`w:real^N`; `(S:num->real^N) a`] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:num` o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `eps:real`)) (concl th))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N`; `(S:num->real^N) a`;
                                    `(S:num->real^N)(SUC a)`] o
        check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      (* S a = S(SUC i): SUC i = a and x = S i *)
      MP_TAC(ISPECL [`S:num->real^N`; `n:num`; `SUC i`; `a:num`] MOI_FSTR_HS_IDX) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; DISCH_TAC] THEN
      SUBGOAL_THEN `SUC i = a` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `i:num < a` (fun th -> REWRITE_TAC[th]) THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `convex hull {w,S i,S(SUC i)} = convex hull {w:real^N,S a,S i}`
      ASSUME_TAC THENL
       [UNDISCH_TAC `(S:num->real^N) a = S(SUC i)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        AP_TERM_TAC THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `x:real^N = (S:num->real^N) i` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC MOI_FSTR_TRI_EQ THEN
        MAP_EVERY EXISTS_TAC [`w:real^N`; `(S:num->real^N) a`] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `eps:real`)) (concl th))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      UNDISCH_TAC `(S:num->real^N) a = S(SUC i)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      DISCH_TAC THEN
      FIRST_ASSUM(MP_TAC o SPECL [`w:real^N`; `(S:num->real^N) i`; `(S:num->real^N) a`] o
        check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_INSERT] THEN
        SUBGOAL_THEN `convex hull {w,S i,S a} = convex hull {w:real^N,(S:num->real^N) a,S i}`
        SUBST1_TAC THENL [AP_TERM_TAC THEN SET_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT2 o CONJUNCT2) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`w:real^N`; `(S:num->real^N) a`; `(S:num->real^N) i`] o
        check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_INSERT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(ASSUME_TAC o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[REAL_NEG_NEG]]]);;

(* ------------------------------------------------------------------------- *)
(* The half-star labelling at a vertex w with two marked neighbours p, q,   *)
(* from the cyclic structure of the link of w (MOI_FN2_ROT of nb2).          *)
(* ------------------------------------------------------------------------- *)

let MOI_FSTR_VERTEX_HALF = prove
 (`!(cx:(real^N->bool)->bool) (sg:real^N->real^N->real^N->real) w p q.
     FINITE cx /\ combinatorial_manifold 2 cx /\ {w} IN cx /\
     segment[w,p] IN cx /\ segment[w,q] IN cx /\
     ~(p = w) /\ ~(q = w) /\ ~(p = q) /\
     (!a b d. convex hull {a,b,d} IN cx /\ aff_dim(convex hull {a,b,d}) = &2 /\
              w IN {a,b,d}
              ==> (sg a b d = &1 \/ sg a b d = -- &1) /\
                  sg b a d = --(sg a b d) /\ sg a d b = --(sg a b d)) /\
     (!a b d d'. w IN {a,b} /\ ~(d = d') /\
                 convex hull {a,b,d} IN cx /\ aff_dim(convex hull {a,b,d}) = &2 /\
                 convex hull {a,b,d'} IN cx /\ aff_dim(convex hull {a,b,d'}) = &2
                 ==> sg a b d' = --(sg a b d))
     ==> ?left:(real^N->bool)->bool.
           (!t t' u. t IN cx /\ aff_dim t = &2 /\ w IN t /\
                     t' IN cx /\ aff_dim t' = &2 /\ w IN t' /\
                     {u} IN cx /\ u IN t /\ u IN t' /\
                     ~(u = w) /\ ~(u = q) /\ ~(u = p)
                     ==> (left t <=> left t')) /\
           (!x. convex hull {w, q, x} IN cx /\ aff_dim(convex hull {w, q, x}) = &2
                ==> (left(convex hull {w, q, x}) <=> sg w q x = &1)) /\
           (!x. convex hull {w, p, x} IN cx /\ aff_dim(convex hull {w, p, x}) = &2
                ==> (left(convex hull {w, p, x}) <=> sg p w x = &1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (cx:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cx:(real^N->bool)->bool`; `w:real^N`] MOI_FN2_ROT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `U:num->real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fn2_kcyc] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "moi_fn2_kcyc" with _ -> false)) THEN
  (* p and q are link vertices *)
  SUBGOAL_THEN `!z:real^N. segment[w,z] IN cx /\ ~(z = w)
                           ==> {z} IN simplicial_link cx w`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM; IN_SING] THEN
    MP_TAC(ISPECL [`cx:(real^N->bool)->bool`; `w:real^N`; `z:real^N`] MOI_FSTR_EDGE_ENDS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `segment[w:real^N,z]` THEN
    ASM_REWRITE_TAC[ENDS_IN_SEGMENT; FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN `?iq. iq < d /\ q = (U:num->real^N) iq` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      is_imp(snd(strip_forall(concl th))) &&
      can (find_term (fun tm -> try fst(dest_const tm) = "simplicial_link" with _ -> false))
          (concl th) &&
      is_exists(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?ip. ip < d /\ p = (U:num->real^N) ip` STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      is_imp(snd(strip_forall(concl th))) &&
      can (find_term (fun tm -> try fst(dest_const tm) = "simplicial_link" with _ -> false))
          (concl th) &&
      is_exists(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:num`; `U:num->real^N`; `iq:num`; `ip:num`] MOI_FN2_CYC_REP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC)] THEN
  SUBGOAL_THEN `~(r = 0)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(p:real^N = q)` THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cx:(real^N->bool)->bool`; `sg:real^N->real^N->real^N->real`; `w:real^N`;
                 `d:num`; `\i. (U:num->real^N)(iq + i)`; `r:num`] MOI_FSTR_HALFSTAR) THEN
  REWRITE_TAC[ADD_CLAUSES] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST
     [FIRST_ASSUM ACCEPT_TAC;
      (* injectivity of the rotated enumeration *)
      MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      DISJ_CASES_TAC(ARITH_RULE `i:num <= j \/ j <= i`) THENL
       [MP_TAC(ISPECL [`d:num`; `U:num->real^N`; `iq + i:num`; `j - i:num`]
          MOI_FN2_CYC_INJ_WINDOW) THEN
        ASM_SIMP_TAC[ARITH_RULE `i <= j ==> (iq + i) + (j - i) = iq + j:num`];
        MP_TAC(ISPECL [`d:num`; `U:num->real^N`; `iq + j:num`; `i - j:num`]
          MOI_FN2_CYC_INJ_WINDOW) THEN
        ASM_SIMP_TAC[ARITH_RULE `j <= i ==> (iq + j) + (i - j) = iq + i:num`]] THEN
      (ANTS_TAC THENL
        [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ASM_ARITH_TAC]; ASM_ARITH_TAC]);
      (* the rotated triangles *)
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `iq + i:num` o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun tm -> try fst(dest_const tm) = "affine_dependent"
                                  with _ -> false)) (concl th))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
      MP_TAC(ISPECL [`w:real^N`; `(U:num->real^N)(iq + i)`; `(U:num->real^N)(SUC(iq + i))`]
        MOI_FSTR_CARD3) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC_ALL THEN
          EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[]];
        DISCH_THEN SUBST1_TAC THEN CONV_TAC INT_REDUCE_CONV];
      (* every triangle at w is a rotated one *)
      X_GEN_TAC `tr:real^N->bool` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `tr:real^N->bool` o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        is_imp(snd(strip_forall(concl th))) &&
        is_exists(snd(dest_imp(snd(strip_forall(concl th))))) &&
        type_of(fst(dest_forall(concl th))) = `:real^N->bool` &&
        not (can (find_term (fun tm -> try fst(dest_const tm) = "simplicial_link"
                                       with _ -> false)) (concl th)))) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`d:num`; `U:num->real^N`; `iq:num`; `j:num`] MOI_FN2_CYC_REP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r':num` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(U:num->real^N)(SUC j) = U(SUC(iq + r'))` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_FN2_CYC_SUC_EQ THEN EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `r':num` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM(fun th -> ACCEPT_TAC(SPEC `iq:num` th));
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U:num->real^N)(iq + r) = p /\ U iq = q` (fun th -> REWRITE_TAC[th]) THEN
  ASM_MESON_TAC[]);;

(* Labellings at all vertices of the cycle k (enumerated by Q). *)
let MOI_FSTR_TS_LABELS = prove
 (`!(c:(real^N->bool)->bool) k (sg:real^N->real^N->real^N->real^N->real) n Q.
     FINITE c /\ combinatorial_manifold 2 c /\ simplicial_subcomplex k c /\
     moi_fn2_kcyc k n Q /\
     (!w a b d. {w} IN k /\ convex hull {a,b,d} IN c /\
                aff_dim(convex hull {a,b,d}) = &2 /\ w IN {a,b,d}
                ==> (sg w a b d = &1 \/ sg w a b d = -- &1) /\
                    sg w b a d = --(sg w a b d) /\ sg w a d b = --(sg w a b d)) /\
     (!w a b d d'. {w} IN k /\ w IN {a,b} /\ ~(d = d') /\
                   convex hull {a,b,d} IN c /\ aff_dim(convex hull {a,b,d}) = &2 /\
                   convex hull {a,b,d'} IN c /\ aff_dim(convex hull {a,b,d'}) = &2
                   ==> sg w a b d' = --(sg w a b d))
     ==> ?LEFT:num->(real^N->bool)->bool.
           !i. i < n ==>
             (!t t' u. t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                       t' IN c /\ aff_dim t' = &2 /\ Q i IN t' /\
                       {u} IN c /\ u IN t /\ u IN t' /\
                       ~(u = Q i) /\ ~(u = Q(SUC i)) /\ ~(u = Q(i + n - 1))
                       ==> (LEFT i t <=> LEFT i t')) /\
             (!x. convex hull {Q i, Q(SUC i), x} IN c /\
                  aff_dim(convex hull {Q i, Q(SUC i), x}) = &2
                  ==> (LEFT i (convex hull {Q i, Q(SUC i), x}) <=>
                       sg (Q i) (Q i) (Q(SUC i)) x = &1)) /\
             (!x. convex hull {Q i, Q(i + n - 1), x} IN c /\
                  aff_dim(convex hull {Q i, Q(i + n - 1), x}) = &2
                  ==> (LEFT i (convex hull {Q i, Q(i + n - 1), x}) <=>
                       sg (Q i) (Q(i + n - 1)) (Q i) x = &1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fn2_kcyc] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "moi_fn2_kcyc" with _ -> false)) THEN
  SUBGOAL_THEN `(k:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  REWRITE_TAC[GSYM SKOLEM_THM; GSYM RIGHT_IMP_EXISTS_THM] THEN
  X_GEN_TAC `i:num` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(Q:num->real^N)(SUC(i + n - 1)) = Q i` ASSUME_TAC THENL
   [SUBGOAL_THEN `SUC(i + n - 1) = i + n` SUBST1_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(sg:real^N->real^N->real^N->real^N->real) ((Q:num->real^N) i)`;
                 `(Q:num->real^N) i`; `(Q:num->real^N)(i + n - 1)`; `(Q:num->real^N)(SUC i)`]
    MOI_FSTR_VERTEX_HALF) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [(* the vertex *)
    ASM SET_TAC[];
    (* the edge to the previous vertex *)
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `(i:num) + n - 1` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      is_conj(snd(strip_forall(concl th))) &&
      can (find_term (fun tm -> try fst(dest_const tm) = "closed_segment" with _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    (* the edge to the next vertex *)
    FIRST_X_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      is_conj(snd(strip_forall(concl th))) &&
      can (find_term (fun tm -> try fst(dest_const tm) = "closed_segment" with _ -> false))
          (concl th))) THEN
    ASM SET_TAC[];
    (* the neighbours are distinct from w and from each other *)
    MP_TAC(ISPECL [`n:num`; `Q:num->real^N`; `(i:num) + n - 1`] MOI_FN2_CYC_NEQ_SUC_ALL) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`n:num`; `Q:num->real^N`; `i:num`] MOI_FN2_CYC_NEQ_SUC_ALL) THEN
    ASM_MESON_TAC[];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`n:num`; `Q:num->real^N`; `(i:num) + n - 1`; `2`] MOI_FN2_CYC_INJ_WINDOW) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((i:num) + n - 1) + 2 = SUC i + n` SUBST1_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    (* (O1) and (O2) at the vertex *)
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    REPEAT GEN_TAC THEN STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;

(* Two triangles through w sharing a further point x share an edge [w,u] through x. *)
let MOI_FSTR_COMMON_EDGE = prove
 (`!(cx:(real^N->bool)->bool) t t' w x.
     simplicial_complex cx /\ t IN cx /\ t' IN cx /\ aff_dim t = &2 /\ aff_dim t' = &2 /\
     ~(t = t') /\ {w} IN cx /\ w IN t /\ w IN t' /\ x IN t /\ x IN t' /\ ~(x = w)
     ==> ?u. {u} IN cx /\ ~(u = w) /\ u IN t /\ u IN t' /\ x IN segment[w,u]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t INTER t':real^N->bool) face_of t /\ (t INTER t') face_of t' /\
                t INTER t' IN cx`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (cx:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(t INTER t':real^N->bool) < &2` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `aff_dim(t:real^N->bool)`)) THEN
    MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (cx:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
      DISCH_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) face_of t'` ASSUME_TAC THENL
       [UNDISCH_TAC `(t INTER t':real^N->bool) face_of t'` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`t:real^N->bool`; `t':real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
      ASM_REWRITE_TAC[INT_LT_REFL] THEN
      UNDISCH_TAC `simplicial_complex (cx:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `t':real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`cx:(real^N->bool)->bool`; `t INTER t':real^N->bool`] MOI_FSA_VS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `V = moi_fsa_vs(t INTER t':real^N->bool)` THEN
  SUBGOAL_THEN `(w:real^N) IN V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    MP_TAC(ISPECL [`cx:(real^N->bool)->bool`; `t INTER t':real^N->bool`; `w:real^N`]
      MOI_FSA_VS_MEM) THEN
    ASM_REWRITE_TAC[IN_INTER];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(V:real^N->bool) = 2` ASSUME_TAC THENL
   [SUBGOAL_THEN `~(CARD(V:real^N->bool) = 1)` MP_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `V = {w:real^N}` ASSUME_TAC THENL
       [MATCH_MP_TAC(GSYM CARD_SUBSET_EQ) THEN ASM_REWRITE_TAC[CARD_SING] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `~(x:real^N = w)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^N) IN convex hull V` MP_TAC THENL
       [FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
           lhs(concl th) = `t INTER t':real^N->bool`
         then SUBST1_TAC(SYM th) else failwith "no") THEN ASM_REWRITE_TAC[IN_INTER];
        ASM_REWRITE_TAC[CONVEX_HULL_SING; IN_SING]];
      SUBGOAL_THEN `1 <= CARD(V:real^N->bool)` MP_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `~(n = 0) ==> 1 <= n`) THEN
        ASM_SIMP_TAC[CARD_EQ_0] THEN ASM SET_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `&(CARD(V:real^N->bool)) = aff_dim(t INTER t':real^N->bool) + &1` THEN
      UNDISCH_TAC `aff_dim(t INTER t':real^N->bool) < &2` THEN
      SPEC_TAC(`aff_dim(t INTER t':real^N->bool)`,`dd:int`) THEN
      SPEC_TAC(`CARD(V:real^N->bool)`,`cc:num`) THEN
      REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_EQ] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u:real^N. ~(u = w) /\ V = {w,u}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `CARD(V:real^N->bool) = 2` THEN
    SUBGOAL_THEN `FINITE(V:real^N->bool)` MP_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IMP_IMP; GSYM HAS_SIZE] THEN CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `a1:real^N` (X_CHOOSE_THEN `a2:real^N` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `(w:real^N) IN V` THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `a2:real^N` THEN ASM SET_TAC[];
      EXISTS_TAC `a1:real^N` THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `u:real^N` THEN
  SUBGOAL_THEN `t INTER t' = segment[w:real^N,u]` ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> if is_eq(concl th) &&
       lhs(concl th) = `t INTER t':real^N->bool`
     then SUBST1_TAC th else failwith "no") THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_INSERT];
    FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `(u:real^N) IN t INTER t'` MP_TAC THENL
     [ASM_REWRITE_TAC[ENDS_IN_SEGMENT; GSYM SEGMENT_CONVEX_HULL]; SET_TAC[]];
    SUBGOAL_THEN `(u:real^N) IN t INTER t'` MP_TAC THENL
     [ASM_REWRITE_TAC[ENDS_IN_SEGMENT; GSYM SEGMENT_CONVEX_HULL]; SET_TAC[]];
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `segment[w:real^N,u]`)) THEN
    ASM_REWRITE_TAC[IN_INTER]]);;

(* A triangle meeting the relative interior of a triangle is that triangle. *)
let MOI_FSTR_RELINT_UNIQUE = prove
 (`!(cx:(real^N->bool)->bool) t t0 x.
     simplicial_complex cx /\ t IN cx /\ t0 IN cx /\ aff_dim t = &2 /\ aff_dim t0 = &2 /\
     x IN t /\ x IN relative_interior t0
     ==> t = t0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN t0` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(t INTER t0:real^N->bool) face_of t /\ (t INTER t0) face_of t0`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (cx:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `t INTER t0:real^N->bool = t0` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t INTER t0:real^N->bool`; `t0:real^N->bool`]
      FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t0:real^N->bool`; `t:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (cx:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CONVEX];
      UNDISCH_TAC `(t INTER t0:real^N->bool) face_of t` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `~(t:real^N->bool = t0)` THEN MESON_TAC[]];
    ASM_REWRITE_TAC[INT_LT_REFL]]);;

(* A point of the dual segment of a k-edge off |k| is interior to a triangle at the edge. *)
let MOI_FSTR_DUAL_POINT = prove
 (`!(c:(real^N->bool)->bool) k e x.
     FINITE c /\ combinatorial_manifold 2 c /\ simplicial_subcomplex k c /\
     (!s. s IN k ==> aff_dim s <= &1) /\ e IN k /\ aff_dim e = &1 /\
     x IN moi_fn2_dual c e /\ ~(x IN UNIONS k)
     ==> ?t0. t0 IN c /\ aff_dim t0 = &2 /\ e SUBSET t0 /\ x IN relative_interior t0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(e:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `k:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FN2_DUAL_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `~(x:real^N = simplex_barycentre e)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((x:real^N) IN UNIONS k)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_fn2_dual c e INTER UNIONS k = {simplex_barycentre (e:real^N->bool)}` THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FN2_DUAL_EDGE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `t1 IN c /\ aff_dim t1 = &2 /\ (e:real^N->bool) SUBSET t1 /\
                t2 IN c /\ aff_dim t2 = &2 /\ e SUBSET t2`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `{t1:real^N->bool,t2}`)) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* each barycentre segment minus b(e) is in the relative interior *)
  SUBGOAL_THEN
   `!t:real^N->bool. t IN c /\ aff_dim t = &2 /\ e SUBSET t /\
                     x IN segment[simplex_barycentre e,simplex_barycentre t]
                     ==> x IN relative_interior t`
  ASSUME_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?nn. nn simplex (t:real^N->bool)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `t:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?ne. ne simplex (e:real^N->bool)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(t:real^N->bool = {}) /\ ~(e:real^N->bool = {})` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
      RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
      FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `-- &1:int`)) THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`nn:int`; `t:real^N->bool`] SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`ne:int`; `e:real^N->bool`] MOI_BAR_SIMPLEX_BARYCENTRE_IN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    ASM_CASES_TAC `x:real^N = simplex_barycentre t` THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN segment(simplex_barycentre t,simplex_barycentre e)`
    MP_TAC THENL
     [REWRITE_TAC[open_segment] THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_INSERT; NOT_IN_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex (t:real^N->bool) /\ closure t = t` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC SIMPLEX_IMP_CONVEX THEN EXISTS_TAC `nn:int` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CLOSURE_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC SIMPLEX_IMP_COMPACT THEN EXISTS_TAC `nn:int` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SPEC_TAC(`x:real^N`,`z:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e:real^N->bool) SUBSET t` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN moi_fn2_dual c e` THEN ASM_REWRITE_TAC[IN_UNION] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `t1:real^N->bool`; EXISTS_TAC `t2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

(* The labellings at the two ends of a k-edge agree on the triangles at it (O3). *)
let MOI_FSTR_TS_CONSIST = prove
 (`!(c:(real^N->bool)->bool) k (sg:real^N->real^N->real^N->real^N->real) n Q
     (LEFT:num->(real^N->bool)->bool) i j x.
     moi_fn2_kcyc k n Q /\
     (!v w x. segment[v,w] IN k /\ ~(v = w) /\ convex hull {v,w,x} IN c /\
              aff_dim(convex hull {v,w,x}) = &2 ==> sg w v w x = sg v v w x) /\
     (!i. i < n ==>
          (!x. convex hull {Q i, Q(SUC i), x} IN c /\
               aff_dim(convex hull {Q i, Q(SUC i), x}) = &2
               ==> (LEFT i (convex hull {Q i, Q(SUC i), x}) <=>
                    sg (Q i) (Q i) (Q(SUC i)) x = &1)) /\
          (!x. convex hull {Q i, Q(i + n - 1), x} IN c /\
               aff_dim(convex hull {Q i, Q(i + n - 1), x}) = &2
               ==> (LEFT i (convex hull {Q i, Q(i + n - 1), x}) <=>
                    sg (Q i) (Q(i + n - 1)) (Q i) x = &1))) /\
     i < n /\ j < n /\ Q j = Q(SUC i) /\
     convex hull {Q i, Q(SUC i), x} IN c /\ aff_dim(convex hull {Q i, Q(SUC i), x}) = &2
     ==> (LEFT j (convex hull {Q i, Q(SUC i), x}) <=>
          LEFT i (convex hull {Q i, Q(SUC i), x}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fn2_kcyc] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "moi_fn2_kcyc" with _ -> false)) THEN
  SUBGOAL_THEN `(Q:num->real^N)((j:num) + n - 1) = Q i` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FN2_CYC_PRE_EQ THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `SUC((j:num) + n - 1) = j + n` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {(Q:num->real^N) i, Q(SUC i), x} = convex hull {Q j, Q((j:num) + n - 1), x}`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN SET_TAC[]; ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `j:num` o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
    can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT2) THEN
  FIRST_ASSUM(MP_TAC o SPEC `i:num` o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
    can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N` o CONJUNCT1) THEN
  SUBGOAL_THEN
   `convex hull {(Q:num->real^N) j, Q((j:num) + n - 1), x} = convex hull {Q i, Q(SUC i), x}`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`n:num`; `Q:num->real^N`; `i:num`] MOI_FN2_CYC_NEQ_SUC_ALL) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Two-sidedness: with coherent signs (O1)-(O3) on the triangles of bsd m   *)
(* at the vertices of the cycle bsd l, the derived neighbourhood minus the  *)
(* polygon splits into the closed parts on the two sides.                   *)
(* ------------------------------------------------------------------------- *)

let MOI_FSTR_STAR_CLOSED = prove
 (`!(c:(real^N->bool)->bool) w.
     moi_bar_complex c /\ FINITE c /\ {w} IN c
     ==> closed (UNIONS (moi_fm3_cstar (barycentric_subdivision c) w))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (c:(real^N->bool)->bool)`; `w:real^N`]
    MOI_FM3_CSTAR) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FMB_SC_LF THEN REWRITE_TAC[MOI_BAR_SIMPLICIAL_COMPLEX] THEN
      ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; MOI_BAR_SUBDIVISION_COMPLEX];
      MATCH_MP_TAC MOI_FRN_SING_IN_BARY THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FSA_SC_FACTS o CONJUNCT1) THEN STRIP_TAC THEN
  MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
  ASM_SIMP_TAC[]);;

(* The barycentre of a triangle at a k-edge lies in the triangle, off |k|. *)
let MOI_FSTR_BARY_OFF = prove
 (`!(c:(real^N->bool)->bool) k e t.
     FINITE c /\ combinatorial_manifold 2 c /\ simplicial_subcomplex k c /\
     (!s. s IN k ==> aff_dim s <= &1) /\ e IN k /\ aff_dim e = &1 /\
     t IN c /\ aff_dim t = &2 /\ e SUBSET t /\ simplex_barycentre t IN moi_fn2_dual c e
     ==> simplex_barycentre t IN t /\ ~(simplex_barycentre t IN UNIONS k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?nn. nn simplex (t:real^N->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `t:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?ne. ne simplex (e:real^N->bool)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(t:real^N->bool = {}) /\ ~(e:real^N->bool = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `-- &1:int`)) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`nn:int`; `t:real^N->bool`] SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `k:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FN2_DUAL_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (t:real^N->bool) = simplex_barycentre e` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`ne:int`; `e:real^N->bool`] MOI_BAR_SIMPLEX_BARYCENTRE_IN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) face_of t` ASSUME_TAC THENL
   [SUBGOAL_THEN `(e INTER t:real^N->bool) face_of t` MP_TAC THENL
     [UNDISCH_TAC `simplicial_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
      SUBGOAL_THEN `e INTER t:real^N->bool = e` (fun th -> REWRITE_TAC[th]) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real^N->bool`; `t:real^N->bool`] FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim(t:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM SET_TAC[]);;

(* Points of two different stars: the triangles through them coincide and *)
(* the labellings agree on them.                                            *)
let MOI_FSTR_TS_CROSS = prove
 (`!(c:(real^N->bool)->bool) k (sg:real^N->real^N->real^N->real^N->real) n Q
     (LEFT:num->(real^N->bool)->bool) i j x t t'.
     FINITE c /\ combinatorial_manifold 2 c /\ simplicial_subcomplex k c /\
     (!s. s IN k ==> aff_dim s <= &1) /\ moi_fn2_kcyc k n Q /\
     (!i j. i < j /\ j < n /\ ~(j = SUC i) /\ ~(i = 0 /\ j = n - 1)
            ==> UNIONS (moi_fm3_cstar (barycentric_subdivision c) (Q i)) INTER
                UNIONS (moi_fm3_cstar (barycentric_subdivision c) (Q j)) = {}) /\
     (!i. i < n
          ==> UNIONS (moi_fm3_cstar (barycentric_subdivision c) (Q i)) INTER
              UNIONS (moi_fm3_cstar (barycentric_subdivision c) (Q(SUC i))) =
              moi_fn2_dual c (segment[Q i,Q(SUC i)])) /\
     (!v w x. segment[v,w] IN k /\ ~(v = w) /\ convex hull {v,w,x} IN c /\
              aff_dim(convex hull {v,w,x}) = &2 ==> sg w v w x = sg v v w x) /\
     (!i. i < n ==>
          (!x. convex hull {Q i, Q(SUC i), x} IN c /\
               aff_dim(convex hull {Q i, Q(SUC i), x}) = &2
               ==> (LEFT i (convex hull {Q i, Q(SUC i), x}) <=>
                    sg (Q i) (Q i) (Q(SUC i)) x = &1)) /\
          (!x. convex hull {Q i, Q(i + n - 1), x} IN c /\
               aff_dim(convex hull {Q i, Q(i + n - 1), x}) = &2
               ==> (LEFT i (convex hull {Q i, Q(i + n - 1), x}) <=>
                    sg (Q i) (Q(i + n - 1)) (Q i) x = &1))) /\
     i < n /\ j < n /\ ~(i = j) /\
     x IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) (Q i)) /\
     x IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) (Q j)) /\
     ~(x IN UNIONS k) /\
     t IN c /\ aff_dim t = &2 /\ x IN t /\ t' IN c /\ aff_dim t' = &2 /\ x IN t'
     ==> t = t' /\ (LEFT i t <=> LEFT j t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fn2_kcyc] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "moi_fn2_kcyc" with _ -> false)) THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
  SUBGOAL_THEN `(k:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  (* the generic adjacent case: x lies on the dual of the k-edge at a *)
  SUBGOAL_THEN
   `!a b. a < n /\ b < n /\ (Q:num->real^N) b = Q(SUC a) /\
          x IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) (Q a)) /\
          x IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) (Q(SUC a)))
          ==> (t:real^N->bool) = t' /\
              ((LEFT:num->(real^N->bool)->bool) a t <=> LEFT b t)`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:num`; `b:num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN moi_fn2_dual c (segment[Q a,Q(SUC a)])` ASSUME_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 1 &&
          can (find_term (fun tm -> try fst(dest_const tm) = "moi_fn2_dual" with _ -> false))
              (concl th)
        then MP_TAC(SPEC `a:num` th) else failwith "no") THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((Q:num->real^N) a = Q(SUC a))` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC_ALL THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                   `segment[(Q:num->real^N) a,Q(SUC a)]`; `x:real^N`] MOI_FSTR_DUAL_POINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[AFF_DIM_SEGMENT]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `t:real^N->bool = t0 /\ t':real^N->bool = t0` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOI_FSTR_RELINT_UNIQUE THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t0:real^N->bool`; `(Q:num->real^N) a`;
                   `(Q:num->real^N)(SUC a)`] MOI_FSTR_TRI_FORM) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
       [FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          is_binary "SUBSET" (concl th) && lhand(concl th) = `k:(real^N->bool)->bool`)) THEN
        ASM_REWRITE_TAC[];
        FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          is_binary "SUBSET" (concl th) && lhand(concl th) = `k:(real^N->bool)->bool`)) THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          is_binary "SUBSET" (concl th) &&
          lhand(concl th) = `segment[(Q:num->real^N) a,Q(SUC a)]`)) THEN
        REWRITE_TAC[ENDS_IN_SEGMENT];
        FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
          is_binary "SUBSET" (concl th) &&
          lhand(concl th) = `segment[(Q:num->real^N) a,Q(SUC a)]`)) THEN
        REWRITE_TAC[ENDS_IN_SEGMENT]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `t0:real^N->bool`)) THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_FSTR_TS_CONSIST THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                          `sg:real^N->real^N->real^N->real^N->real`; `n:num`] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `convex hull {(Q:num->real^N) a,Q(SUC a),x0}`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Q:num->real^N) n = Q 0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FN2_CYC_N THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `SUC(n - 1) = n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  (* the empty intersections of non-adjacent stars *)
  SUBGOAL_THEN
   `!p q. p < q /\ q < n /\ ~(q = SUC p) /\ ~(p = 0 /\ q = n - 1) /\
          (x:real^N) IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) (Q p)) /\
          x IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) (Q q))
          ==> F`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`p:num`; `q:num`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun tm -> try fst(dest_const tm) = "moi_fm3_cstar" with _ -> false))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISJ_CASES_TAC(ARITH_RULE `i < j \/ j < (i:num) \/ i = j`) THENL
   [ASM_CASES_TAC `j = SUC i` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`i:num`; `j:num`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `i = 0 /\ j = n - 1` THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n - 1`; `0`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        ASM_ARITH_TAC;
        MESON_TAC[]];
      ASM_MESON_TAC[]];
    FIRST_X_ASSUM(DISJ_CASES_TAC) THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
    ASM_CASES_TAC `i = SUC j` THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`j:num`; `i:num`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `j = 0 /\ i = n - 1` THENL
     [FIRST_X_ASSUM(CONJUNCTS_THEN SUBST_ALL_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`n - 1`; `0`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th))) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        ASM_ARITH_TAC;
        MESON_TAC[]];
      ASM_MESON_TAC[]]]);;

let MOI_FSTR_TWO_SIDED = prove
 (`!(m:(real^N->bool)->bool) l (sg:real^N->real^N->real^N->real^N->real).
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\
     (!w a b d. {w} IN barycentric_subdivision l /\
                convex hull {a,b,d} IN barycentric_subdivision m /\
                aff_dim(convex hull {a,b,d}) = &2 /\ w IN {a,b,d}
                ==> (sg w a b d = &1 \/ sg w a b d = -- &1) /\
                    sg w b a d = --(sg w a b d) /\ sg w a d b = --(sg w a b d)) /\
     (!w a b d d'. {w} IN barycentric_subdivision l /\ w IN {a,b} /\ ~(d = d') /\
                   convex hull {a,b,d} IN barycentric_subdivision m /\
                   aff_dim(convex hull {a,b,d}) = &2 /\
                   convex hull {a,b,d'} IN barycentric_subdivision m /\
                   aff_dim(convex hull {a,b,d'}) = &2
                   ==> sg w a b d' = --(sg w a b d)) /\
     (!v w x. segment[v,w] IN barycentric_subdivision l /\ ~(v = w) /\
              convex hull {v,w,x} IN barycentric_subdivision m /\
              aff_dim(convex hull {v,w,x}) = &2
              ==> sg w v w x = sg v v w x)
     ==> ~connected (derived_nbhd m l DIFF UNIONS l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPEC `barycentric_subdivision (l:(real^N->bool)->bool)` MOI_FN2_KCYC_EXISTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `Q:num->real^N` ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_NBHD_STARS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `n:num`;
                 `Q:num->real^N`] MOI_FN2_KSTARS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                 `barycentric_subdivision (l:(real^N->bool)->bool)`;
                 `sg:real^N->real^N->real^N->real^N->real`; `n:num`; `Q:num->real^N`]
    MOI_FSTR_TS_LABELS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `LEFT:num->(real^N->bool)->bool`) THEN
  ABBREV_TAC `c = barycentric_subdivision (m:(real^N->bool)->bool)` THEN
  ABBREV_TAC `k = barycentric_subdivision (l:(real^N->bool)->bool)` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `UNIONS (l:(real^N->bool)->bool)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o REWRITE_RULE[moi_fn2_kcyc] o check (fun th ->
    try fst(dest_const(fst(strip_comb(concl th)))) = "moi_fn2_kcyc" with _ -> false)) THEN
  ABBREV_TAC
   `L = UNIONS {UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i)) INTER
                UNIONS {t | t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                            (LEFT:num->(real^N->bool)->bool) i t} | i | i < n}` THEN
  ABBREV_TAC
   `R = UNIONS {UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i)) INTER
                UNIONS {t | t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                            ~(LEFT:num->(real^N->bool)->bool) i t} | i | i < n}` THEN
  SUBGOAL_THEN `derived_nbhd m l = (L:real^N->bool) UNION R` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> if is_eq(concl th) &&
       lhs(concl th) = `derived_nbhd (m:(real^N->bool)->bool) l`
     then SUBST1_TAC th else failwith "no") THEN
    MAP_EVERY EXPAND_TAC ["L"; "R"] THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_UNION; IN_UNIONS; IN_ELIM_THM; IN_INTER] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `s:real^N->bool`)) THEN
      FIRST_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        type_of(fst(dest_forall(concl th))) = `:real^N` &&
        is_exists(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
      ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `w:real^N`)) THEN
      UNDISCH_TAC `(x:real^N) IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i))` THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(Q:num->real^N) i`; `s0:real^N->bool`]
        MOI_FN2_CSTAR_IN_SIMPLEX) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t0:real^N->bool`] MOI_FSA_CM_PURE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `(LEFT:num->(real^N->bool)->bool) i t` THENL
       [DISJ1_TAC THEN
        EXISTS_TAC `UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i)) INTER
                    UNIONS {t | t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                                (LEFT:num->(real^N->bool)->bool) i t}`;
        DISJ2_TAC THEN
        EXISTS_TAC `UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i)) INTER
                    UNIONS {t | t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                                ~(LEFT:num->(real^N->bool)->bool) i t}`] THEN
      (CONJ_TAC THENL [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
      (CONJ_TAC THENL [EXISTS_TAC `s0:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      STRIP_TAC THEN
      (EXISTS_TAC `UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i))` THEN
       CONJ_TAC THENL
        [EXISTS_TAC `(Q:num->real^N) i` THEN ASM_REWRITE_TAC[];
         FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
           lhs(concl th) = `t:real^N->bool`)) THEN
         ASM SET_TAC[]])];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(L:real^N->bool) /\ closed(R:real^N->bool)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FSA_SC_FACTS) THEN
    SUBGOAL_THEN `(k:(real^N->bool)->bool) SUBSET c` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["L"; "R"] THEN CONJ_TAC THEN
    (MATCH_MP_TAC CLOSED_UNIONS THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN SIMP_TAC[FINITE_IMAGE; FINITE_NUMSEG_LT] THEN
    REWRITE_TAC[FORALL_IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    MATCH_MP_TAC CLOSED_INTER THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FSTR_STAR_CLOSED THEN
      REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      FIRST_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET] o check (fun th ->
        is_binary "SUBSET" (concl th) && lhand(concl th) = `k:(real^N->bool)->bool`)) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
        CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SET_TAC[]];
        REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        FIRST_ASSUM(MP_TAC o SPEC `t:real^N->bool` o check (fun th ->
          is_forall(concl th) && can (find_term (fun tm ->
            try fst(dest_const tm) = "compact" with _ -> false)) (concl th))) THEN
        ASM_SIMP_TAC[]]]);
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(!x. x IN L <=>
         ?i. i < n /\
             x IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i)) /\
             ?t. (t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                  (LEFT:num->(real^N->bool)->bool) i t) /\ x IN t) /\
    (!x. x IN R <=>
         ?i. i < n /\
             x IN UNIONS (moi_fm3_cstar (barycentric_subdivision c) ((Q:num->real^N) i)) /\
             ?t. (t IN c /\ aff_dim t = &2 /\ Q i IN t /\
                  ~(LEFT:num->(real^N->bool)->bool) i t) /\ x IN t)`
  (CONJUNCTS_THEN2 (LABEL_TAC "Lc") (LABEL_TAC "Rc")) THENL
   [MAP_EVERY EXPAND_TAC ["L"; "R"] THEN
    REWRITE_TAC[IN_UNIONS; EXISTS_IN_GSPEC; IN_INTER; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(L:real^N->bool) INTER R SUBSET UNIONS k` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
    USE_THEN "Lc" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "Rc" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC))))
      (X_CHOOSE_THEN `j:num` (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC))))) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    ASM_CASES_TAC `i:num = j` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool) /\ {(Q:num->real^N) j} IN c`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL [ASM_MESON_TAC[MOI_FSA_CM_SC]; ALL_TAC] THEN
        SUBGOAL_THEN `(k:(real^N->bool)->bool) SUBSET c` MP_TAC THENL
         [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(t:real^N->bool = t')` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `~(x:real^N = (Q:num->real^N) j)` ASSUME_TAC THENL
       [DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((Q:num->real^N) j IN UNIONS k)` THEN REWRITE_TAC[IN_UNIONS] THEN
        EXISTS_TAC `{(Q:num->real^N) j}` THEN ASM_REWRITE_TAC[IN_SING];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `t':real^N->bool`;
                     `(Q:num->real^N) j`; `x:real^N`] MOI_FSTR_COMMON_EDGE) THEN
      ANTS_TAC THENL
       [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC); ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `~((u:real^N) = Q(SUC j)) /\ ~(u = Q(j + n - 1))` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `~((x:real^N) IN UNIONS k)` THEN REWRITE_TAC[IN_UNIONS] THENL
         [EXISTS_TAC `segment[(Q:num->real^N) j,Q(SUC j)]` THEN ASM_REWRITE_TAC[];
          EXISTS_TAC `segment[(Q:num->real^N)(j + n - 1),Q(SUC(j + n - 1))]` THEN
          ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `SUC(j + n - 1) = j + n` SUBST1_TAC THENL
           [ASM_ARITH_TAC; ASM_REWRITE_TAC[]] THEN
          ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `j:num` o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th) &&
        is_conj(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(MP_TAC o SPECL [`t:real^N->bool`; `t':real^N->bool`; `u:real^N`] o
        CONJUNCT1) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                     `sg:real^N->real^N->real^N->real^N->real`; `n:num`; `Q:num->real^N`;
                     `LEFT:num->(real^N->bool)->bool`; `i:num`; `j:num`; `x:real^N`;
                     `t:real^N->bool`; `t':real^N->bool`] MOI_FSTR_TS_CROSS) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
        GEN_TAC THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `i':num` o check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 1 &&
          can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        STRIP_TAC THEN ASM_MESON_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((L:real^N->bool) DIFF UNIONS k = {}) /\ ~((R:real^N->bool) DIFF UNIONS k = {})`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool) /\ (k:(real^N->bool)->bool) SUBSET c`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FSA_CM_SC; simplicial_subcomplex]; ALL_TAC] THEN
    SUBGOAL_THEN `segment[(Q:num->real^N) 0,Q 1] IN k /\ ~(Q 0 = Q 1) /\ {Q 0} IN k`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[ONE] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC_ALL THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `e = segment[(Q:num->real^N) 0,Q 1]` THEN
    SUBGOAL_THEN `(e:real^N->bool) IN c /\ aff_dim e = &1` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM SET_TAC[]; EXPAND_TAC "e" THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FN2_DUAL_EDGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `t1 IN c /\ aff_dim t1 = &2 /\ (e:real^N->bool) SUBSET t1 /\
                  t2 IN c /\ aff_dim t2 = &2 /\ e SUBSET t2`
    STRIP_ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq(concl th) &&
        rand(concl th) = `{t1:real^N->bool,t2}`)) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      ALL_TAC] THEN
    (* the two barycentres lie in the star of Q 0, off the polygon *)
    SUBGOAL_THEN
     `!t:real^N->bool. t IN c /\ aff_dim t = &2 /\ e SUBSET t /\
                       simplex_barycentre t IN moi_fn2_dual c e
                       ==> simplex_barycentre t IN t /\ ~(simplex_barycentre t IN UNIONS k) /\
                           simplex_barycentre t IN
                           UNIONS (moi_fm3_cstar (barycentric_subdivision c) (Q 0))`
    ASSUME_TAC THENL
     [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `k:(real^N->bool)->bool`; `e:real^N->bool`;
                     `t:real^N->bool`] MOI_FSTR_BARY_OFF) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun tm -> try fst(dest_const tm) = "moi_fn2_dual" with _ -> false))
            (concl th))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM ONE] THEN
      FIRST_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `e:real^N->bool`
                            then REWRITE_TAC[th] else failwith "no") THEN
      DISCH_THEN(MP_TAC o AP_TERM `(IN) (simplex_barycentre (t:real^N->bool))`) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `simplex_barycentre t1 IN moi_fn2_dual c (e:real^N->bool) /\
                  simplex_barycentre t2 IN moi_fn2_dual c e`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_UNION; ENDS_IN_SEGMENT]; ALL_TAC] THEN
    (* exactly one of the two triangles is on the left *)
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t1:real^N->bool`; `(Q:num->real^N) 0`;
                   `(Q:num->real^N) 1`] MOI_FSTR_TRI_FORM) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t2:real^N->bool`; `(Q:num->real^N) 0`;
                   `(Q:num->real^N) 1`] MOI_FSTR_TRI_FORM) THEN
    SUBGOAL_THEN `{(Q:num->real^N) 0} IN c /\ {Q 1} IN c /\ Q 0 IN e /\ Q 1 IN e`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "e" THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(Q:num->real^N) 0`; `(Q:num->real^N) 1`]
        MOI_FSTR_EDGE_ENDS) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_FMB_SC_LF; SUBSET]; SIMP_TAC[]];
      ALL_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x2:real^N` STRIP_ASSUME_TAC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(x1:real^N = x2)` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `~(t1:real^N->bool = t2)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "simplex_barycentre"
                                  with _ -> false)) (concl th) &&
        can (find_term (fun tm -> try fst(dest_const tm) = "moi_fm3_cstar"
                                  with _ -> false)) (concl th)
      then MP_TAC(SPEC `t1:real^N->bool` th) THEN MP_TAC(SPEC `t2:real^N->bool` th)
      else failwith "no") THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    (* the signs of the two triangles at [Q 0,Q 1] *)
    SUBGOAL_THEN
     `((LEFT:num->(real^N->bool)->bool) 0 t1 <=>
       (sg:real^N->real^N->real^N->real^N->real) (Q 0) (Q 0) (Q 1) x1 = &1) /\
      (LEFT 0 t2 <=> sg (Q 0) (Q 0) (Q 1) x2 = &1)`
    STRIP_ASSUME_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPEC `0` o check (fun th -> is_forall(concl th) &&
        length(fst(strip_forall(concl th))) = 1 &&
        can (find_term ((=) `LEFT:num->(real^N->bool)->bool`)) (concl th) &&
        is_conj(snd(dest_imp(snd(strip_forall(concl th))))))) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[GSYM ONE] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      DISCH_THEN(fun th -> MP_TAC(SPEC `x1:real^N` th) THEN MP_TAC(SPEC `x2:real^N` th)) THEN
      SUBGOAL_THEN `convex hull {(Q:num->real^N) 0,Q 1,x1} = t1 /\
                    convex hull {(Q:num->real^N) 0,Q 1,x2} = t2`
      (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `(sg:real^N->real^N->real^N->real^N->real) (Q 0) (Q 0) (Q 1) x2 =
      --(sg (Q 0) (Q 0) (Q 1) x1) /\
      (sg (Q 0) (Q 0) (Q 1) x1 = &1 \/ sg (Q 0) (Q 0) (Q 1) x1 = -- &1)`
    (CONJUNCTS_THEN ASSUME_TAC) THENL
     [CONJ_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          length(fst(strip_forall(concl th))) = 5)) THEN
        REWRITE_TAC[IN_INSERT] THEN
        SUBGOAL_THEN `convex hull {(Q:num->real^N) 0,Q 1,x1} = t1 /\
                      convex hull {(Q:num->real^N) 0,Q 1,x2} = t2`
        (fun th -> REWRITE_TAC[th]) THENL
         [CONJ_TAC THEN CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPECL [`(Q:num->real^N) 0`; `(Q:num->real^N) 0`;
                                      `(Q:num->real^N) 1`; `x1:real^N`] o
          check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 4)) THEN
        REWRITE_TAC[IN_INSERT] THEN
        SUBGOAL_THEN `convex hull {(Q:num->real^N) 0,Q 1,x1} = t1` SUBST1_TAC THENL
         [CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `((LEFT:num->(real^N->bool)->bool) 0 t1 <=> ~LEFT 0 t2)` ASSUME_TAC THENL
     [MAP_EVERY (fun tm -> FIRST_ASSUM(fun th -> if concl th = tm then REWRITE_TAC[th]
                                                  else failwith "no"))
       [`(LEFT:num->(real^N->bool)->bool) 0 t1 <=>
         (sg:real^N->real^N->real^N->real^N->real) (Q 0) (Q 0) (Q 1) x1 = &1`;
        `(LEFT:num->(real^N->bool)->bool) 0 t2 <=>
         (sg:real^N->real^N->real^N->real^N->real) (Q 0) (Q 0) (Q 1) x2 = &1`;
        `(sg:real^N->real^N->real^N->real^N->real) (Q 0) (Q 0) (Q 1) x2 =
         --(sg (Q 0) (Q 0) (Q 1) x1)`] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST1_TAC o check (fun th ->
        is_disj(concl th) && can (find_term ((=) `x1:real^N`)) (concl th))) THEN
      CONV_TAC REAL_RAT_REDUCE_CONV;
      ALL_TAC] THEN
    SUBGOAL_THEN `(Q:num->real^N) 0 IN t1 /\ Q 0 IN t2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      FIRST_ASSUM(fun th -> if is_binary "SUBSET" (concl th) &&
          lhand(concl th) = `e:real^N->bool` then
          MATCH_MP_TAC(REWRITE_RULE[SUBSET] th) else failwith "no") THEN
      FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    USE_THEN "Lc" (fun th -> REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; th]) THEN
    USE_THEN "Rc" (fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `(LEFT:num->(real^N->bool)->bool) 0 t1` THENL
     [CONJ_TAC THENL
       [EXISTS_TAC `simplex_barycentre(t1:real^N->bool)` THEN
        CONJ_TAC THENL [EXISTS_TAC `0` THEN REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC;
          EXISTS_TAC `t1:real^N->bool` THEN REPEAT CONJ_TAC THEN
          FIRST_ASSUM ACCEPT_TAC];
         FIRST_ASSUM ACCEPT_TAC];
        EXISTS_TAC `simplex_barycentre(t2:real^N->bool)` THEN
        CONJ_TAC THENL [EXISTS_TAC `0` THEN REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC;
          EXISTS_TAC `t2:real^N->bool` THEN REPEAT CONJ_TAC THEN
          TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_MESON_TAC[]];
         FIRST_ASSUM ACCEPT_TAC]];
      CONJ_TAC THENL
       [EXISTS_TAC `simplex_barycentre(t2:real^N->bool)` THEN
        CONJ_TAC THENL [EXISTS_TAC `0` THEN REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC;
          EXISTS_TAC `t2:real^N->bool` THEN REPEAT CONJ_TAC THEN
          TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_MESON_TAC[]];
         FIRST_ASSUM ACCEPT_TAC];
        EXISTS_TAC `simplex_barycentre(t1:real^N->bool)` THEN
        CONJ_TAC THENL [EXISTS_TAC `0` THEN REPEAT CONJ_TAC THENL
         [ASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC;
          EXISTS_TAC `t1:real^N->bool` THEN REPEAT CONJ_TAC THEN
          FIRST_ASSUM ACCEPT_TAC];
         FIRST_ASSUM ACCEPT_TAC]]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
    rand(concl th) = `(L:real^N->bool) UNION R`)) THEN
  REWRITE_TAC[CONNECTED_CLOSED_IN_EQ] THEN
  MAP_EVERY EXISTS_TAC [`(L:real^N->bool) DIFF UNIONS k`; `(R:real^N->bool) DIFF UNIONS k`] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(L:real^N->bool) DIFF UNIONS k = ((L UNION R) DIFF UNIONS k) INTER L`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN FIRST_ASSUM ACCEPT_TAC;
    SUBGOAL_THEN `(R:real^N->bool) DIFF UNIONS k = ((L UNION R) DIFF UNIONS k) INTER R`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN FIRST_ASSUM ACCEPT_TAC;
    SET_TAC[];
    UNDISCH_TAC `(L:real^N->bool) INTER R SUBSET UNIONS k` THEN SET_TAC[];
    FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Assembly of the trace annulus theorem. The rim of the disk is a PL        *)
(* circle, the first derived complexes carry the sides of the surface at the *)
(* rim vertices, the signs O1-O3 exist, so the trace of N on the surface     *)
(* minus the rim is not connected, and the band of S4 is the annulus.        *)
(* ------------------------------------------------------------------------- *)

(* The boundary of a 2-cell is a PL circle (as MOI_SCX_CELL_SPHERE of       *)
(* pc_moi_sch3_cvx, outside this load closure; here j is polyhedral).       *)
let MOI_FSTR_RIM_SPHERE = prove
 (`!(d:real^N->bool) j. pl_cell_with_boundary 2 d j /\ pl_polyhedron j ==> pl_sphere 1 j`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[pl_cell_with_boundary; pl_sphere; ARITH_RULE `1 + 1 = 2`] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC))))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; STRIP_TAC] THEN
  SUBGOAL_THEN `relative_frontier k SUBSET (k:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_homeomorphism (k:real^N->bool,d:real^N->bool) (f:real^N->real^N,g:real^N->real^N)` THEN
  REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `IMAGE (f:real^N->real^N) (relative_frontier k) SUBSET d` ASSUME_TAC THENL
   [UNDISCH_TAC `homeomorphism (k:real^N->bool,d:real^N->bool) (f:real^N->real^N,g:real^N->real^N)` THEN
    REWRITE_TAC[homeomorphism] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `d:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON];
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `d:real^N->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON]]);;

(* A vertex of degree two in a 1-dimensional complex has a nonempty link. *)
let MOI_FSTR_DEG_LINK = prove
 (`!(k:(real^N->bool)->bool) v.
     simplicial_complex k /\ {v} IN k /\
     CARD {e | e IN k /\ aff_dim e = &1 /\ v IN e} = 2
     ==> ~(UNIONS (simplicial_link k v) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~({e | e IN k /\ aff_dim e = &1 /\ (v:real^N) IN e} = {})` MP_TAC THENL
   [DISCH_THEN(fun th ->
      UNDISCH_TAC `CARD {e | e IN k /\ aff_dim e = &1 /\ (v:real^N) IN e} = 2` THEN
      REWRITE_TAC[th; CARD_CLAUSES]) THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?n. n simplex (e:real^N->bool)` (X_CHOOSE_TAC `n:int`) THENL
   [UNDISCH_TAC `simplicial_complex (k:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `e:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
  UNDISCH_TAC `&1 simplex (e:real^N->bool)` THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(c:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD (c:real^N->bool)):int = &1 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `?x:real^N. (x = a \/ x = b) /\ ~(x = v)`
  (X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN ASSUME_TAC)) THENL
   [ASM_CASES_TAC `a:real^N = v` THENL
     [EXISTS_TAC `b:real^N` THEN ASM_MESON_TAC[];
      EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{x:real^N} face_of e` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[FACE_OF_SING; GSYM SEGMENT_CONVEX_HULL; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
  EXISTS_TAC `x:real^N` THEN EXISTS_TAC `{x:real^N}` THEN
  REWRITE_TAC[IN_SING] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_complex (k:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* The basic facts on the disk, the surface and the rim. *)
let MOI_FSTR_RIM_BASE = prove
 (`!(t:(real^N->bool)->bool) ld lm.
     FINITE t /\ lf_simplicial_complex t /\
     simplicial_subcomplex ld t /\ simplicial_subcomplex lm t /\
     combinatorial_manifold 2 lm /\
     pl_cell_with_boundary 2 (UNIONS ld) (UNIONS ld INTER UNIONS lm)
     ==> FINITE ld /\ FINITE lm /\ lf_simplicial_complex ld /\ lf_simplicial_complex lm /\
         simplicial_subcomplex (ld INTER lm) lm /\
         UNIONS (ld INTER lm) = UNIONS ld INTER UNIONS lm /\
         pl_sphere 1 (UNIONS (ld INTER lm))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(ld:(real^N->bool)->bool) SUBSET t /\ lm SUBSET t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (ld:(real^N->bool)->bool) /\ FINITE (lm:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `ld:(real^N->bool)->bool`;
                 `lm:(real^N->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SUBCOMPLEX];
    ASM_MESON_TAC[combinatorial_manifold];
    ASM_MESON_TAC[MOI_FN2_SUBCOMPLEX_INTER];
    MATCH_MP_TAC MOI_FSTR_RIM_SPHERE THEN EXISTS_TAC `UNIONS ld:real^N->bool` THEN
    ASM_REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `(ld:(real^N->bool)->bool) INTER lm` THEN
    ASM_SIMP_TAC[FINITE_INTER; IN_INTER] THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; MESON_TAC[SIMPLEX_IMP_POLYTOPE]]]);;

(* The first derived complexes of the surface, the disk and the rim. *)
let MOI_FSTR_DISK_CONTEXT = prove
 (`!(t:(real^N->bool)->bool) ld lm.
     FINITE t /\ lf_simplicial_complex t /\
     simplicial_subcomplex ld t /\ simplicial_subcomplex lm t /\
     combinatorial_manifold 2 lm /\
     pl_cell_with_boundary 2 (UNIONS ld) (UNIONS ld INTER UNIONS lm)
     ==> FINITE (barycentric_subdivision lm) /\
         combinatorial_manifold 2 (barycentric_subdivision lm) /\
         FINITE (barycentric_subdivision ld) /\
         lf_simplicial_complex (barycentric_subdivision ld) /\
         simplicial_subcomplex (barycentric_subdivision (ld INTER lm))
                               (barycentric_subdivision ld) /\
         barycentric_subdivision (ld INTER lm) SUBSET barycentric_subdivision lm /\
         (!s. s IN barycentric_subdivision (ld INTER lm) ==> aff_dim s <= &1) /\
         UNIONS (barycentric_subdivision ld) INTER UNIONS (barycentric_subdivision lm) =
         UNIONS (barycentric_subdivision (ld INTER lm)) /\
         (!v. {v} IN barycentric_subdivision (ld INTER lm)
              ==> ~(UNIONS (simplicial_link (barycentric_subdivision (ld INTER lm)) v) = {})) /\
         (?(k:real^N->bool) (f:real^N->real^N) (g:real^N->real^N). convex k /\ closed k /\
                  homeomorphism (k,UNIONS (barycentric_subdivision ld)) (f,g) /\
                  UNIONS (barycentric_subdivision (ld INTER lm)) =
                  IMAGE f (relative_frontier k))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `ld:(real^N->bool)->bool`;
                 `lm:(real^N->bool)->bool`] MOI_FSTR_RIM_BASE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`lm:(real^N->bool)->bool`; `(ld:(real^N->bool)->bool) INTER lm`]
    MOI_FN2_CONTEXT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `simplicial_subcomplex (barycentric_subdivision ((ld:(real^N->bool)->bool) INTER lm))
                                      (barycentric_subdivision ld)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `ld:(real^N->bool)->bool`;
                   `lm:(real^N->bool)->bool`] MOI_FN2_TRACE_SETUP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `barycentric_subdivision (ld:(real^N->bool)->bool)`;
                   `barycentric_subdivision (lm:(real^N->bool)->bool)`]
      MOI_FN2_SUBCOMPLEX_INTER) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (barycentric_subdivision (ld:(real^N->bool)->bool)) = UNIONS ld /\
                UNIONS (barycentric_subdivision (lm:(real^N->bool)->bool)) = UNIONS lm`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC UNIONS_BARYCENTRIC_SUBDIVISION THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC MOI_BAR_SUBDIVISION_FINITE THEN FIRST_ASSUM ACCEPT_TAC;
    MATCH_MP_TAC BARYCENTRIC_SUBDIVISION_LF THEN FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    ASM_MESON_TAC[simplicial_subcomplex];
    FIRST_ASSUM ACCEPT_TAC;
    ASM_REWRITE_TAC[];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FSTR_DEG_LINK THEN
    ASM_SIMP_TAC[];
    UNDISCH_TAC `pl_cell_with_boundary 2 (UNIONS ld) (UNIONS ld INTER UNIONS (lm:(real^N->bool)->bool))` THEN
    REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_CLOSED]]);;

(* The signs O1-O3 of the two-sidedness lemma exist for the first derived  *)
(* complexes of the surface and the rim: at each rim vertex take the sides *)
(* of the surface in a small ball, with the disk side first.               *)
let MOI_FSTR_SIGNS = prove
 (`!(t:(real^3->bool)->bool) ld lm.
     FINITE t /\ lf_simplicial_complex t /\
     simplicial_subcomplex ld t /\ simplicial_subcomplex lm t /\
     combinatorial_manifold 2 lm /\
     pl_cell_with_boundary 2 (UNIONS ld) (UNIONS ld INTER UNIONS lm)
     ==> ?sg:real^3->real^3->real^3->real^3->real.
          (!w a b d. {w} IN barycentric_subdivision (ld INTER lm) /\
                     convex hull {a,b,d} IN barycentric_subdivision lm /\
                     aff_dim(convex hull {a,b,d}) = &2 /\ w IN {a,b,d}
                     ==> (sg w a b d = &1 \/ sg w a b d = -- &1) /\
                         sg w b a d = --(sg w a b d) /\ sg w a d b = --(sg w a b d)) /\
          (!w a b d d'. {w} IN barycentric_subdivision (ld INTER lm) /\ w IN {a,b} /\
                        ~(d = d') /\
                        convex hull {a,b,d} IN barycentric_subdivision lm /\
                        aff_dim(convex hull {a,b,d}) = &2 /\
                        convex hull {a,b,d'} IN barycentric_subdivision lm /\
                        aff_dim(convex hull {a,b,d'}) = &2
                        ==> sg w a b d' = --(sg w a b d)) /\
          (!v w x. segment[v,w] IN barycentric_subdivision (ld INTER lm) /\ ~(v = w) /\
                   convex hull {v,w,x} IN barycentric_subdivision lm /\
                   aff_dim(convex hull {v,w,x}) = &2
                   ==> sg w v w x = sg v v w x)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FSTR_DISK_CONTEXT) THEN
  ABBREV_TAC `c = barycentric_subdivision (lm:(real^3->bool)->bool)` THEN
  ABBREV_TAC `dd = barycentric_subdivision (ld:(real^3->bool)->bool)` THEN
  ABBREV_TAC `kk = barycentric_subdivision ((ld:(real^3->bool)->bool) INTER lm)` THEN
  STRIP_TAC THEN
  (* the sides at the rim vertices, the disk side first *)
  SUBGOAL_THEN
   `!w:real^3. ?r D E. {w} IN kk
        ==> moi_fstr_sides (UNIONS c) w r D E /\
            (UNIONS dd INTER ball(w,r)) DIFF UNIONS kk SUBSET D`
  MP_TAC THENL
   [X_GEN_TAC `w:real^3` THEN
    ASM_CASES_TAC `{w:real^3} IN kk` THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    REWRITE_TAC[ASSUME `{w:real^3} IN kk`] THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `dd:(real^3->bool)->bool`;
                   `kk:(real^3->bool)->bool`; `k:real^3->bool`; `f:real^3->real^3`;
                   `g:real^3->real^3`; `w:real^3`] MOI_FSTR_VERTEX_SIDES) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `D:real^3->bool`
      (X_CHOOSE_THEN `E:real^3->bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`r:real`; `D:real^3->bool`; `E:real^3->bool`] THEN
    REWRITE_TAC[moi_fstr_sides] THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `rr:real^3->real` (X_CHOOSE_THEN `DS:real^3->real^3->bool`
    (X_CHOOSE_THEN `ES:real^3->real^3->bool` (LABEL_TAC "vsides")))) THEN
  EXISTS_TAC `\w a b d. moi_fstr_sg ((DS:real^3->real^3->bool) w) w ((rr:real^3->real) w)
                                    (a:real^3) b d` THEN
  BETA_TAC THEN REPEAT CONJ_TAC THENL
   [(* O1 *)
    MAP_EVERY X_GEN_TAC [`w:real^3`; `a:real^3`; `b:real^3`; `d:real^3`] THEN STRIP_TAC THEN
    USE_THEN "vsides" (MP_TAC o SPEC `w:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w:real^3`; `(rr:real^3->real) w`;
                   `(DS:real^3->real^3->bool) w`; `(ES:real^3->real^3->bool) w`;
                   `a:real^3`; `b:real^3`; `d:real^3`] MOI_FSTR_SG_SWAP) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MATCH_MP_TAC HULL_INC THEN FIRST_ASSUM ACCEPT_TAC;
      SIMP_TAC[]];
    (* O2 *)
    MAP_EVERY X_GEN_TAC [`w:real^3`; `a:real^3`; `b:real^3`; `d:real^3`; `d':real^3`] THEN
    STRIP_TAC THEN
    USE_THEN "vsides" (MP_TAC o SPEC `w:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `w:real^3`; `(rr:real^3->real) w`;
                   `(DS:real^3->real^3->bool) w`; `(ES:real^3->real^3->bool) w`;
                   `a:real^3`; `b:real^3`; `d:real^3`; `d':real^3`] MOI_FSTR_SG_EDGE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      UNDISCH_TAC `(w:real^3) IN {a,b}` THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
      SIMP_TAC[]];
    (* O3 *)
    MAP_EVERY X_GEN_TAC [`v:real^3`; `w:real^3`; `x:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `{v:real^3} IN kk /\ {w} IN kk` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      UNDISCH_TAC `simplicial_subcomplex (kk:(real^3->bool)->bool) dd` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      EXISTS_TAC `segment[v:real^3,w]` THEN
      ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      ALL_TAC] THEN
    USE_THEN "vsides" (MP_TAC o SPEC `v:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    USE_THEN "vsides" (MP_TAC o SPEC `w:real^3`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `dd:(real^3->bool)->bool`;
                   `kk:(real^3->bool)->bool`; `k:real^3->bool`; `f:real^3->real^3`;
                   `g:real^3->real^3`; `v:real^3`; `w:real^3`; `x:real^3`;
                   `(rr:real^3->real) v`; `(DS:real^3->real^3->bool) v`;
                   `(ES:real^3->real^3->bool) v`;
                   `(rr:real^3->real) w`; `(DS:real^3->real^3->bool) w`;
                   `(ES:real^3->real^3->bool) w`] MOI_FSTR_SG_RIM) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN ASM_MESON_TAC[SUBSET];
      SIMP_TAC[]]]);;

(* The trace of N on the surface minus the rim is not connected. *)
let MOI_FSTR_TRACE_NOT_CONNECTED = prove
 (`!(t:(real^3->bool)->bool) ld lm.
     FINITE t /\ lf_simplicial_complex t /\
     simplicial_subcomplex ld t /\ simplicial_subcomplex lm t /\
     combinatorial_manifold 2 lm /\
     pl_cell_with_boundary 2 (UNIONS ld) (UNIONS ld INTER UNIONS lm)
     ==> ~connected (derived_nbhd lm (ld INTER lm) DIFF UNIONS (ld INTER lm))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(fun th -> STRIP_ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(MATCH_MP MOI_FSTR_RIM_BASE th) THEN
    X_CHOOSE_THEN `sg:real^3->real^3->real^3->real^3->real` STRIP_ASSUME_TAC
      (MATCH_MP MOI_FSTR_SIGNS th)) THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `(ld:(real^3->bool)->bool) INTER lm`;
                 `sg:real^3->real^3->real^3->real^3->real`] MOI_FSTR_TWO_SIDED) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]]);;

(* The trace annulus theorem, with S4 (MOI_FND_DERIVED_NBHD_POLYGON_2 at     *)
(* N = 3) as the antecedent.                                                 *)
let MOI_FSTR_SPLIT_TRACE_COND = prove
 (mk_imp(inst [`:3`,`:N`] MOI_FND_DERIVED_NBHD_POLYGON_2, MOI_FND_SPLIT_TRACE_ANNULUS),
  DISCH_THEN(LABEL_TAC "S4") THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                       `lm:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`] MOI_FSTR_RIM_BASE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `ld:(real^3->bool)->bool`;
                 `lm:(real^3->bool)->bool`] MOI_FN2_DERIVED_TRACE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> REWRITE_TAC[GSYM(CONJUNCT1 th); CONJUNCT2 th]) THEN
  USE_THEN "S4" (MP_TAC o SPECL [`lm:(real^3->bool)->bool`;
                                 `(ld:(real^3->bool)->bool) INTER lm`]) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `FINITE (components (derived_nbhd lm (ld INTER lm) DIFF
                                    UNIONS ((ld:(real^3->bool)->bool) INTER lm)))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `(ld:(real^3->bool)->bool) INTER lm`]
      MOI_FN2_COMPONENTS_NL) THEN
    ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; DISCH_THEN SUBST1_TAC] THEN
    ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `barycentric_subdivision (lm:(real^3->bool)->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_SUBDIVISION_FINITE THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_frn_vp] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~connected (derived_nbhd lm (ld INTER lm) DIFF
                            UNIONS ((ld:(real^3->bool)->bool) INTER lm))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FSTR_TRACE_NOT_CONNECTED THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (components (derived_frontier lm ((ld:(real^3->bool)->bool) INTER lm))) = 2`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `~(CARD (components (derived_nbhd lm (ld INTER lm) DIFF
                                      UNIONS ((ld:(real^3->bool)->bool) INTER lm))) = 1)`
    MP_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `components (derived_nbhd lm (ld INTER lm) DIFF
                                UNIONS ((ld:(real^3->bool)->bool) INTER lm)) HAS_SIZE 1`
      MP_TAC THENL [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
      CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
      REWRITE_TAC[COMPONENTS_EQ_SING_EXISTS] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM(MP_TAC o check (is_disj o concl)) THEN
    FIRST_ASSUM(MP_TAC o check (fun th -> let c = concl th in is_eq c &&
      (try fst(dest_const(rator(lhs c))) = "CARD" &&
           fst(dest_const(rator(rhs c))) = "CARD" with Failure _ -> false))) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    can (find_term (fun u -> is_const u && fst(dest_const u) = "pl_annulus_with_ends"))
        (concl th))) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j1:real^3->bool` (X_CHOOSE_THEN `j2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`j1:real^3->bool`; `j2:real^3->bool`] THEN
  REPEAT CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
     rhs(concl th) = `(j1:real^3->bool) UNION j2`)) THEN
  MP_TAC(ISPECL [`lm:(real^3->bool)->bool`; `(ld:(real^3->bool)->bool) INTER lm`]
    DERIVED_NBHD_BASIC) THEN
  ANTS_TAC THENL [CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; STRIP_TAC] THEN
  REWRITE_TAC[derived_frontier; frontier_of] THEN
  MP_TAC(ISPECL [`subtopology euclidean (UNIONS (lm:(real^3->bool)->bool))`;
                 `derived_nbhd lm ((ld:(real^3->bool)->bool) INTER lm)`] INTERIOR_OF_SUBSET) THEN
  UNDISCH_TAC `UNIONS ((ld:(real^3->bool)->bool) INTER lm) SUBSET
               (subtopology euclidean (UNIONS lm)) interior_of (derived_nbhd lm (ld INTER lm))` THEN
  SET_TAC[]);;

let SPLIT_TRACE_ANNULUS = MOI_FSTR_SPLIT_TRACE_COND;;

