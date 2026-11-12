(* ========================================================================= *)
(* pc_moi_s34_tvarc: the vertex arcs of a trace component, for s34_fdisk.    *)
(* If a trace component J of the face ball of s meets the rims in three      *)
(* points (Lemma 11), then J INTER f1(C_u) is the PL arc of J between its    *)
(* two rim points at u, for each vertex u of s.                              *)
(* ========================================================================= *)

needs "src/pc_moi_s34_trace.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The meet of a trace component with a vertex ball.                         *)
(* ------------------------------------------------------------------------- *)

(* If J is the union of an arc K in A_u and two pieces in other A's, and    *)
(* the rim points of J outside K miss C_u, then J INTER C_u = K.            *)
let MOI_S4T_ARC_IS_MEET = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3
    j u x1 x2 k k1 k2 pa pb pc.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     u IN {v1,v2,v3} /\ x1 IN {v1,v2,v3} /\ x2 IN {v1,v2,v3} /\
     ~(x1 = u) /\ ~(x2 = u) /\
     j = k UNION k1 UNION k2 /\
     k SUBSET IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) /\
     k1 SUBSET IMAGE f1 (moi_s34_vb tt kk x1 INTER moi_s34_bd tt kk) /\
     k2 SUBSET IMAGE f1 (moi_s34_vb tt kk x2 INTER moi_s34_bd tt kk) /\
     j INTER moi_s34_rims tt kk f1 SUBSET {pa,pb,pc} /\
     pa IN k /\ pb IN k /\ ~(pc IN IMAGE f1 (moi_s34_vb tt kk u))
     ==> j INTER IMAGE f1 (moi_s34_vb tt kk u) = k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY (fun x ->
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                   x; `u:real^N`] MOI_S4T_TRI_PAIR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC])
   [`x1:real^N`; `x2:real^N`] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) SUBSET
                IMAGE f1 (moi_s34_vb tt kk u)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `j:real^3->bool`)) THEN
  MAP_EVERY UNDISCH_TAC
   [`k SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`;
    `k1 SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x1 INTER moi_s34_bd tt kk)`;
    `k2 SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x2 INTER moi_s34_bd tt kk)`;
    `(k UNION k1 UNION k2) INTER moi_s34_rims tt kk (f1:real^N->real^3) SUBSET {pa,pb,pc}`;
    `(pa:real^3) IN k`; `(pb:real^3) IN k`;
    `~((pc:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u))`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) SUBSET
     IMAGE f1 (moi_s34_vb tt kk u)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x1 INTER moi_s34_bd tt kk) INTER
     IMAGE f1 (moi_s34_vb tt kk u) =
     IMAGE f1 (moi_s34_vb tt kk x1 INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x2 INTER moi_s34_bd tt kk) INTER
     IMAGE f1 (moi_s34_vb tt kk u) =
     IMAGE f1 (moi_s34_vb tt kk x2 INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3)
       (moi_s34_vb tt kk x1 INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)
     SUBSET moi_s34_rims tt kk f1`;
    `IMAGE (f1:real^N->real^3)
       (moi_s34_vb tt kk x2 INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)
     SUBSET moi_s34_rims tt kk f1`] THEN
  POP_ASSUM_LIST(K ALL_TAC) THEN
  MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
   [`IMAGE (f1:real^N->real^3)
       (moi_s34_vb tt kk x1 INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`, `R1:real^3->bool`;
    `IMAGE (f1:real^N->real^3)
       (moi_s34_vb tt kk x2 INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`, `R2:real^3->bool`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`, `AU:real^3->bool`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x1 INTER moi_s34_bd tt kk)`, `A1:real^3->bool`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x2 INTER moi_s34_bd tt kk)`, `A2:real^3->bool`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u)`, `CU:real^3->bool`;
    `moi_s34_rims tt kk (f1:real^N->real^3)`, `RR:real^3->bool`] THEN
  SET_TAC[]);;

(* Three pairwise different 2-subsets of a 3-set cannot share a point. *)
let MOI_S4T_NOT_ALL_CONTAIN = prove
 (`!(v1:A) v2 v3 e0 e1 e2 z.
     ~(v1 = v2) /\ ~(v1 = v3) /\ ~(v2 = v3) /\
     (e0 = {v1,v2} \/ e0 = {v1,v3} \/ e0 = {v2,v3}) /\
     (e1 = {v1,v2} \/ e1 = {v1,v3} \/ e1 = {v2,v3}) /\
     (e2 = {v1,v2} \/ e2 = {v1,v3} \/ e2 = {v2,v3}) /\
     ~(e0 = e1) /\ ~(e1 = e2) /\ ~(e0 = e2) /\
     z IN e0 /\ z IN e1 /\ z IN e2
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REPEAT(FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && is_var(lhs(concl th)) &&
    not (lhs(concl th) = `z:A`)))) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> moi_s4l_has "INSERT" th))) THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (is_neg o concl))) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]);;

(* One vertex: J INTER C_u is the PL arc K of J between its two rim points  *)
(* at u, and these are the meets of J with the two disks at u.              *)
let MOI_S4T_VERTEX_ARC_CASE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3
    j l x y u w1 w2 pc.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     simple_path l /\ pl_map_on (interval[vec 0,vec 1]) l /\
     &0 <= x /\ x < y /\ y <= &1 /\ ~(l(lift x) = l(lift y)) /\
     u IN {v1,v2,v3} /\ w1 IN {v1,v2,v3} /\ w2 IN {v1,v2,v3} /\
     ~(u = w1) /\ ~(u = w2) /\ ~(w1 = w2) /\
     IMAGE l (interval[lift x,lift y]) SUBSET
     IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) /\
     l(lift x) IN IMAGE f1 (moi_s34_vb tt kk w1) /\
     l(lift y) IN IMAGE f1 (moi_s34_vb tt kk w2) /\
     j INTER IMAGE f1 (moi_s34_vb tt kk u) = IMAGE l (interval[lift x,lift y]) /\
     j INTER moi_s34_rims tt kk f1 SUBSET {l(lift x),l(lift y),pc} /\
     ~(pc IN IMAGE f1 (moi_s34_vb tt kk u))
     ==> pl_cell_with_boundary 1 (j INTER IMAGE f1 (moi_s34_vb tt kk u))
           (UNIONS {j INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                    g IN moi_s34_simp kk (&1) /\ u IN g /\ g SUBSET s})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4T_TRI_TRACE) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `moi_s34_trace tt kk (f1:real^N->real^3)
                       ((cb:(real^N->bool)->real^3->bool) s)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4t_tri]) THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [MATCH_MP_TAC IN_COMPONENTS_SUBSET THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `lift x IN interval[vec 0,vec 1] /\ lift y IN interval[vec 0,vec 1] /\
                lift x IN interval[lift x,lift y] /\ lift y IN interval[lift x,lift y]`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) SUBSET
                IMAGE f1 (moi_s34_vb tt kk u)` ASSUME_TAC THENL
   [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(l:real^1->real^3)(lift x) IN IMAGE l (interval[lift x,lift y]) /\
                l(lift y) IN IMAGE l (interval[lift x,lift y])` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `convex(s:real^N->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
      MOI_S4L_TRI_FORM) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[CONVEX_CONVEX_HULL];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. w IN {v1,v2,v3} ==> {w:real^N} IN kk /\ w IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN s /\ {x} IN kk} = {v1:real^N,v2,v3}` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `UNIONS {j INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g) | g |
            g IN moi_s34_simp kk (&1) /\ u IN g /\ g SUBSET s} =
    {(l:real^1->real^3)(lift x),l(lift y)}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `q:real^3` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `t:real^3->bool`)) THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u':real^N` (X_CHOOSE_THEN `w':real^N` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(u':real^N) IN {v1,v2,v3} /\ (w':real^N) IN {v1,v2,v3} /\
                    (u = u' \/ u = w')`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
       [REPEAT CONJ_TAC THENL
         [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
            rand(concl th) = `{v1:real^N,v2,v3}`)) THEN
          REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(g:real^N->bool) SUBSET s` THEN ASM_REWRITE_TAC[] THEN
          MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
          FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
            rand(concl th) = `{v1:real^N,v2,v3}`)) THEN
          REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(g:real^N->bool) SUBSET s` THEN ASM_REWRITE_TAC[] THEN
          MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
          SUBGOAL_THEN `(u:real^N) IN {v | v IN g /\ {v} IN kk}` MP_TAC THENL
           [REWRITE_TAC[IN_ELIM_THM] THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
          ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
        ALL_TAC] THEN
      SUBGOAL_THEN `?w:real^N. w IN {v1,v2,v3} /\ ~(u = w) /\
                    moi_s34_sd tt kk g = moi_s34_vb tt kk u INTER moi_s34_vb tt kk w`
      STRIP_ASSUME_TAC THENL
       [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (fun th ->
          is_disj(concl th) && vfree_in `u':real^N` (concl th))) THENL
         [EXISTS_TAC `w':real^N` THEN ASM_REWRITE_TAC[];
          EXISTS_TAC `u':real^N` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
          FIRST [UNDISCH_TAC `~(u':real^N = w')` THEN MESON_TAC[]; SET_TAC[]]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                     `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                     `u:real^N`; `w:real^N`] MOI_S4T_TRI_PAIR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      UNDISCH_TAC `(q:real^3) IN j INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)` THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
        vfree_in `w:real^N` (concl th) && moi_s4l_has "moi_s34_sd" th)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        rand(concl th) = `IMAGE (f1:real^N->real^3)
                            (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w)`)) THEN
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(q:real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_S4T_TRI_MEET_RIMS THEN
        MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
          `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
          `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
          `u:real^N`; `w:real^N`] THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `!a. (q:real^3) IN a /\ a SUBSET b ==> q IN b`) THEN
        EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `j INTER moi_s34_rims tt kk (f1:real^N->real^3) SUBSET
                   {(l:real^1->real^3)(lift x),l(lift y),pc}` THEN
      REWRITE_TAC[SUBSET; IN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `q:real^3`) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((pc:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u))` THEN
      UNDISCH_TAC `(q:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u)` THEN
      UNDISCH_TAC `(q:real^3) = pc` THEN MESON_TAC[];
      SUBGOAL_THEN
       `!w0 p0. w0 IN {v1,v2,v3} /\ ~(u = w0) /\ (p0:real^3) IN j /\
                p0 IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) /\
                p0 IN IMAGE f1 (moi_s34_vb tt kk w0)
                ==> ?t. (?g. (g IN moi_s34_simp kk (&1) /\ u IN g /\ g SUBSET s) /\
                             t = j INTER IMAGE f1 (moi_s34_sd tt kk g)) /\ p0 IN t`
      ASSUME_TAC THENL
       [REPEAT GEN_TAC THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                       `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                       `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                       `u:real^N`; `w0:real^N`] MOI_S4T_TRI_PAIR) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `u:real^N`; `w0:real^N`] MOI_S4L_EDGE_SD) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `~(u:real^N = w0)` THEN MESON_TAC[];
          STRIP_TAC] THEN
        EXISTS_TAC `j INTER IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[u,w0]))` THEN
        CONJ_TAC THENL
         [EXISTS_TAC `segment[u:real^N,w0]` THEN REWRITE_TAC[ENDS_IN_SEGMENT] THEN
          ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN ASM_SIMP_TAC[];
          FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
            lhs(concl th) = `moi_s34_sd tt kk (segment[u:real^N,w0])`)) THEN
          FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
            rand(concl th) = `IMAGE (f1:real^N->real^3)
                                (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w0)`)) THEN
          ASM_REWRITE_TAC[IN_INTER]];
        ALL_TAC] THEN
      SUBGOAL_THEN `!p. (p:real^3) IN IMAGE (l:real^1->real^3) (interval[lift x,lift y])
                        ==> p IN j /\ p IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u)`
      ASSUME_TAC THENL
       [UNDISCH_TAC `j INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) =
                     IMAGE (l:real^1->real^3) (interval[lift x,lift y])` THEN
        SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
       [EXISTS_TAC `w1:real^N`; EXISTS_TAC `w2:real^N`] THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `subpath (lift x) (lift y) (l:real^1->real^3)` MOI_S4O_ARC_CELL) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC ARC_SIMPLE_PATH_SUBPATH THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_PL2_PL_SUBPATH THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[PATHSTART_SUBPATH; PATHFINISH_SUBPATH] THEN
  SUBGOAL_THEN `path_image (subpath (lift x) (lift y) (l:real^1->real^3)) =
                IMAGE l (interval[lift x,lift y])` SUBST1_TAC THENL
   [MATCH_MP_TAC PATH_IMAGE_SUBPATH THEN REWRITE_TAC[LIFT_DROP] THEN
    ASM_REAL_ARITH_TAC;
    REWRITE_TAC[]]);;


(* ------------------------------------------------------------------------- *)
(* The meet of a trace component with a vertex ball is a 1-cell whose ends   *)
(* are the meets with the two disks at the vertex (for s34_fdisk).           *)
(* ------------------------------------------------------------------------- *)

(* Three different elements of a 3-set are all of it. *)
let MOI_S4T_THREE_OF_THREE = prove
 (`!(v1:A) v2 v3 a0 a1 a2 u.
     a0 IN {v1,v2,v3} /\ a1 IN {v1,v2,v3} /\ a2 IN {v1,v2,v3} /\
     ~(a0 = a1) /\ ~(a0 = a2) /\ ~(a1 = a2) /\ u IN {v1,v2,v3}
     ==> u = a0 \/ u = a1 \/ u = a2`,
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT GEN_TAC THEN
  moi_s4t_vcases [`a0:A`; `a1:A`; `a2:A`; `u:A`] THEN REWRITE_TAC[]);;

(* One gap [x,y] of a trace loop l lying in A_u, the rest of J in the other *)
(* two A's: J INTER C_u is that arc, with the two disk meets as its ends.   *)
let MOI_S4T_VERTEX_GAP = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3
    j l x y u w1 w2 x1 x2 k1 k2 pc.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     simple_path l /\ pl_map_on (interval[vec 0,vec 1]) l /\
     &0 <= x /\ x < y /\ y <= &1 /\ ~(l(lift x) = l(lift y)) /\
     u IN {v1,v2,v3} /\ w1 IN {v1,v2,v3} /\ w2 IN {v1,v2,v3} /\
     ~(u = w1) /\ ~(u = w2) /\ ~(w1 = w2) /\
     IMAGE l (interval[lift x,lift y]) SUBSET
     IMAGE f1 (moi_s34_vb tt kk u INTER moi_s34_bd tt kk) /\
     l(lift x) IN IMAGE f1 (moi_s34_vb tt kk w1) /\
     l(lift y) IN IMAGE f1 (moi_s34_vb tt kk w2) /\
     x1 IN {v1,v2,v3} /\ x2 IN {v1,v2,v3} /\ ~(x1 = u) /\ ~(x2 = u) /\
     j = IMAGE l (interval[lift x,lift y]) UNION k1 UNION k2 /\
     k1 SUBSET IMAGE f1 (moi_s34_vb tt kk x1 INTER moi_s34_bd tt kk) /\
     k2 SUBSET IMAGE f1 (moi_s34_vb tt kk x2 INTER moi_s34_bd tt kk) /\
     j INTER moi_s34_rims tt kk f1 SUBSET {l(lift x),l(lift y),pc} /\
     ~(pc IN IMAGE f1 (moi_s34_vb tt kk u))
     ==> pl_cell_with_boundary 1 (j INTER IMAGE f1 (moi_s34_vb tt kk u))
           (UNIONS {j INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                    g IN moi_s34_simp kk (&1) /\ u IN g /\ g SUBSET s})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`; `u:real^N`; `x1:real^N`; `x2:real^N`;
                 `IMAGE (l:real^1->real^3) (interval[lift x,lift y])`;
                 `k1:real^3->bool`; `k2:real^3->bool`;
                 `(l:real^1->real^3)(lift x)`; `(l:real^1->real^3)(lift y)`;
                 `pc:real^3`] MOI_S4T_ARC_IS_MEET) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN
    REWRITE_TAC[IN_INTERVAL_1; LIFT_DROP] THEN ASM_REAL_ARITH_TAC;
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`; `l:real^1->real^3`; `x:real`; `y:real`;
                 `u:real^N`; `w1:real^N`; `w2:real^N`; `pc:real^3`]
    MOI_S4T_VERTEX_ARC_CASE) THEN
  ANTS_TAC THENL [REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC; REWRITE_TAC[]]);;

(* One case of the main lemma: the vertex u is the vertex of the gap [x,y]. *)
let moi_s4t_vgap_tac x y u w1 w2 x1 x2 k1 k2 pc =
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`; `l:real^1->real^3`; x; y; u; w1; w2; x1; x2;
                 k1; k2; pc] MOI_S4T_VERTEX_GAP) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    TRY(MATCH_ACCEPT_TAC REAL_LE_REFL) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
    USE_THEN "jb" (fun th -> REWRITE_TAC[th]) THEN REWRITE_TAC[UNION_ACI];
    REWRITE_TAC[]];;

(* Lemma 11 at a vertex (for s34_fdisk): if a trace component J of s has   *)
(* three rim points, then for each vertex u of s, J INTER C_u is a 1-cell  *)
(* whose boundary is the union of the meets of J with the two disks at u.  *)
let MOI_S4T_COMP_VERTEX_ARC = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v1 v2 v3 j u.
     moi_s4t_tri tt kk h ep f1 car cb s v1 v2 v3 /\
     (!s v j. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\
              j IN components (moi_s34_trace tt kk f1 (cb s))
              ==> ~(j SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk))) /\
     (!s v g a aa. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\ g IN moi_s34_simp kk (&1) /\
                   pl_cell_with_boundary 1 a aa /\
                   a SUBSET moi_s34_trace tt kk f1 (cb s) /\
                   a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                   aa SUBSET IMAGE f1 (moi_s34_sd tt kk g) /\
                   a INTER moi_s34_rims tt kk f1 = aa
                   ==> F) /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     CARD (j INTER moi_s34_rims tt kk f1) = 3 /\ u IN {v1,v2,v3}
     ==> pl_cell_with_boundary 1 (j INTER IMAGE f1 (moi_s34_vb tt kk u))
           (UNIONS {j INTER IMAGE f1 (moi_s34_sd tt kk g) | g |
                    g IN moi_s34_simp kk (&1) /\ u IN g /\ g SUBSET s})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`] MOI_S4T_COMP_RIMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `j:real^3->bool`] MOI_S4T_COMP_LOOP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `CARD (j INTER moi_s34_rims tt kk (f1:real^N->real^3)) = 3` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `l:real^1->real^3` STRIP_ASSUME_TAC)] THEN
  MP_TAC(ISPECL [`l:real^1->real^3`; `j INTER moi_s34_rims tt kk (f1:real^N->real^3)`]
    MOI_S4T_TIMES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
    REWRITE_TAC[IN_INTER; PATHSTART_IN_PATH_IMAGE] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INTER_SUBSET];
    STRIP_TAC] THEN
  MP_TAC(ISPEC `{t | &0 <= t /\ t <= &1 /\
                     (l:real^1->real^3)(lift t) IN j INTER moi_s34_rims tt kk
                     (f1:real^N->real^3)}` MOI_S4T_FOUR_TIMES) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [SIMP_TAC[IN_ELIM_THM]; ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC)) THEN
  (* the three gaps and their vertex data *)
  MAP_EVERY (fun (x,y,(a,b,c)) ->
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                   `j:real^3->bool`; `l:real^1->real^3`; x; y] MOI_S4T_GAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN a (X_CHOOSE_THEN b (X_CHOOSE_THEN c STRIP_ASSUME_TAC))))
   [`&0`, `r1:real`, (`a0:real^N`, `b0:real^N`, `c0:real^N`);
    `r1:real`, `r2:real`, (`a1:real^N`, `b1:real^N`, `c1:real^N`);
    `r2:real`, `&1`, (`a2:real^N`, `b2:real^N`, `c2:real^N`)] THEN
  SUBGOAL_THEN `(l:real^1->real^3)(lift(&1)) = l(lift(&0))` ASSUME_TAC THENL
   [UNDISCH_TAC `pathfinish (l:real^1->real^3) = pathstart l` THEN
    REWRITE_TAC[pathstart; pathfinish; LIFT_NUM];
    ALL_TAC] THEN
  ABBREV_TAC `ee = \q. {x | x IN {v1:real^N,v2,v3} /\
                            q IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x)}` THEN
  SUBGOAL_THEN
   `!q u0 w0. u0 IN {v1,v2,v3} /\ w0 IN {v1,v2,v3} /\ ~(u0:real^N = w0) /\
              q IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u0) /\
              q IN IMAGE f1 (moi_s34_vb tt kk w0)
              ==> ee q = {u0,w0}`
  (LABEL_TAC "ee") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ee" THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4T_EDGE_SET THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
      `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
      `s:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q z. z IN {v1,v2,v3} /\ (q:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk z)
          ==> z IN ee q`
  (LABEL_TAC "eein") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "ee" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the edge sets of the three rim points *)
  SUBGOAL_THEN
   `ee ((l:real^1->real^3)(lift(&0))) = {a0:real^N,b0} /\ ee (l(lift(&0))) = {a2,c2} /\
    ee (l(lift r1)) = {a0,c0} /\ ee (l(lift r1)) = {a1,b1} /\
    ee (l(lift r2)) = {a1,c1} /\ ee (l(lift r2)) = {a2,b2}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN USE_THEN "ee" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `(l:real^1->real^3)(lift(&1))`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{a0:real^N,c0} = {a1,b1} /\ {a0:real^N,b0} = {a2,c2} /\
                {a1:real^N,c1} = {a2,b2}` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift r1)) = {a1,b1}`;
      UNDISCH_TAC `(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift(&0))) = {a2,c2}`;
      UNDISCH_TAC `(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift r2)) = {a2,b2}`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b c:real^N. ~(a = b) /\ ~(a = c) /\ ~(b = c) ==> ~({a,b} = {a,c})`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
    SUBGOAL_THEN `(b:real^N) IN {a,c}` MP_TAC THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INSERT];
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~({a0:real^N,b0} = {a0,c0}) /\ ~({a0:real^N,c0} = {a1,c1}) /\
                ~({a0:real^N,b0} = {a1,c1})` STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ALL_TAC;
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `{a0:real^N,c0}`));
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `{a0:real^N,b0}`)) THEN
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `{a1:real^N,c1}`))] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV SYM_CONV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4t_tri] o
    check (moi_s4l_has "moi_s4t_tri")) THEN
  (* no vertex lies on all three edge sets *)
  SUBGOAL_THEN `!z:real^N. z IN {a0,b0} /\ z IN {a0,c0} /\ z IN {a1,c1} ==> F`
  (LABEL_TAC "nac") THENL
   [X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`v1:real^N`; `v2:real^N`; `v3:real^N`; `{a0:real^N,b0}`;
                   `{a0:real^N,c0}`; `{a1:real^N,c1}`; `z:real^N`]
      MOI_S4T_NOT_ALL_CONTAIN) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
      MATCH_MP_TAC MOI_S4T_PAIR_CASES THEN REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      REWRITE_TAC[]];
    ALL_TAC] THEN
  (* so the three gap vertices are different *)
  SUBGOAL_THEN `~(a0:real^N = a1) /\ ~(a1:real^N = a0) /\ ~(a0:real^N = a2) /\
                ~(a2:real^N = a0) /\ ~(a1:real^N = a2) /\ ~(a2:real^N = a1)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(a0:real^N = a1) /\ ~(a0:real^N = a2) /\ ~(a1:real^N = a2)`
    MP_TAC THENL
     [REPEAT CONJ_TAC THEN DISCH_TAC THENL
       [USE_THEN "nac" (MP_TAC o SPEC `a0:real^N`) THEN
        UNDISCH_TAC `a0:real^N = a1` THEN POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
        USE_THEN "nac" (MP_TAC o SPEC `a0:real^N`) THEN
        MAP_EVERY UNDISCH_TAC [`{a1:real^N,c1} = {a2,b2}`; `a0:real^N = a2`] THEN
        POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
        USE_THEN "nac" (MP_TAC o SPEC `a1:real^N`) THEN
        MAP_EVERY UNDISCH_TAC [`{a0:real^N,c0} = {a1,b1}`; `{a0:real^N,b0} = {a2,c2}`;
                               `a1:real^N = a2`] THEN
        POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[]];
      MESON_TAC[]];
    ALL_TAC] THEN
  (* the third rim point of a gap is not in the ball of the gap vertex *)
  SUBGOAL_THEN
   `~((l:real^1->real^3)(lift r2) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk a0)) /\
    ~(l(lift(&0)) IN IMAGE f1 (moi_s34_vb tt kk a1)) /\
    ~(l(lift r1) IN IMAGE f1 (moi_s34_vb tt kk a2))`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THENL
     [USE_THEN "eein" (MP_TAC o SPECL [`(l:real^1->real^3)(lift r2)`; `a0:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "nac" (MP_TAC o SPEC `a0:real^N`) THEN
      UNDISCH_TAC `(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift r2)) = {a1,c1}` THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      SPEC_TAC(`(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift r2))`,
               `e:real^N->bool`) THEN
      SET_TAC[];
      USE_THEN "eein" (MP_TAC o SPECL [`(l:real^1->real^3)(lift(&0))`; `a1:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "nac" (MP_TAC o SPEC `a1:real^N`) THEN
      MAP_EVERY UNDISCH_TAC
       [`(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift(&0))) = {a0,b0}`;
        `{a0:real^N,c0} = {a1,b1}`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      SPEC_TAC(`(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift(&0)))`,
               `e:real^N->bool`) THEN
      SET_TAC[];
      USE_THEN "eein" (MP_TAC o SPECL [`(l:real^1->real^3)(lift r1)`; `a2:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      USE_THEN "nac" (MP_TAC o SPEC `a2:real^N`) THEN
      MAP_EVERY UNDISCH_TAC
       [`(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift r1)) = {a0,c0}`;
        `{a0:real^N,b0} = {a2,c2}`; `{a1:real^N,c1} = {a2,b2}`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      SPEC_TAC(`(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift r1))`,
               `e:real^N->bool`) THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* consecutive rim points are different *)
  SUBGOAL_THEN `~((l:real^1->real^3)(lift(&0)) = l(lift r1)) /\ ~(l(lift r1) = l(lift r2)) /\
                ~(l(lift r2) = l(lift(&1)))` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift(&0))) = {a0,b0}`;
      `(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift r1)) = {a0,c0}`;
      `(ee:real^3->real^N->bool) ((l:real^1->real^3)(lift r2)) = {a1,c1}`;
      `(l:real^1->real^3)(lift(&1)) = l(lift(&0))`;
      `~({a0:real^N,b0} = {a0,c0})`; `~({a0:real^N,c0} = {a1,c1})`;
      `~({a0:real^N,b0} = {a1,c1})`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`{a0:real^N,b0}`, `e0:real^N->bool`; `{a0:real^N,c0}`, `e1:real^N->bool`;
      `{a1:real^N,c1}`, `e2:real^N->bool`] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  (* the rim points of J are the three gap ends *)
  SUBGOAL_THEN `j INTER moi_s34_rims tt kk (f1:real^N->real^3) SUBSET
                {(l:real^1->real^3)(lift(&0)),l(lift r1),l(lift r2)}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT1 o GEN_REWRITE_RULE I [IN_INTER] o
      check (fun th -> concl th = `(q:real^3) IN j INTER moi_s34_rims tt kk
                                     (f1:real^N->real^3)`)) THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
    REWRITE_TAC[path_image; IN_IMAGE] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `drop t IN {t | &0 <= t /\ t <= &1 /\
                   (l:real^1->real^3)(lift t) IN j INTER moi_s34_rims tt kk
                   (f1:real^N->real^3)}` MP_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM; LIFT_DROP] THEN
      UNDISCH_TAC `(t:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `q:real^3`)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `{&0,r1,r2,&1}`)) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN (fun th ->
      SUBST_ALL_TAC(REWRITE_RULE[LIFT_DROP] (AP_TERM `lift` th)))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `j INTER moi_s34_rims tt kk (f1:real^N->real^3) SUBSET
                {(l:real^1->real^3)(lift r1),l(lift r2),l(lift(&0))} /\
                j INTER moi_s34_rims tt kk f1 SUBSET {l(lift r2),l(lift(&1)),l(lift r1)}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(l:real^1->real^3)(lift(&1)) = l(lift(&0))` THEN
    UNDISCH_TAC `j INTER moi_s34_rims tt kk (f1:real^N->real^3) SUBSET
                 {(l:real^1->real^3)(lift(&0)),l(lift r1),l(lift r2)}` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`j INTER moi_s34_rims tt kk (f1:real^N->real^3)`, `d:real^3->bool`;
      `(l:real^1->real^3)(lift(&0))`, `p0:real^3`;
      `(l:real^1->real^3)(lift r1)`, `p1:real^3`;
      `(l:real^1->real^3)(lift r2)`, `p2:real^3`;
      `(l:real^1->real^3)(lift(&1))`, `p3:real^3`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= r1 /\ r1 <= &1 /\ &0 <= r2 /\ r2 <= &1` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`&0 < r1`; `r1 < r2`; `r2 < &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* J is the union of the three gap arcs *)
  SUBGOAL_THEN `path_image (l:real^1->real^3) =
                IMAGE l (interval[lift(&0),lift r1]) UNION
                IMAGE l (interval[lift r1,lift r2]) UNION
                IMAGE l (interval[lift r2,lift(&1)])` (LABEL_TAC "jb") THENL
   [REWRITE_TAC[path_image; GSYM IMAGE_UNION] THEN AP_TERM_TAC THEN
    REWRITE_TAC[EXTENSION; IN_UNION; IN_INTERVAL_1; LIFT_DROP; DROP_VEC] THEN
    X_GEN_TAC `t:real^1` THEN
    MAP_EVERY UNDISCH_TAC [`&0 < r1`; `r1 < r2`; `r2 < &1`] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  (* u is one of the three gap vertices *)
  MP_TAC(ISPECL [`v1:real^N`; `v2:real^N`; `v3:real^N`; `a0:real^N`; `a1:real^N`;
                 `a2:real^N`; `u:real^N`] MOI_S4T_THREE_OF_THREE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN SUBST_ALL_TAC) THENL
   [moi_s4t_vgap_tac `&0` `r1:real` `a0:real^N` `b0:real^N` `c0:real^N`
      `a1:real^N` `a2:real^N`
      `IMAGE (l:real^1->real^3) (interval[lift r1,lift r2])`
      `IMAGE (l:real^1->real^3) (interval[lift r2,lift(&1)])`
      `(l:real^1->real^3)(lift r2)`;
    moi_s4t_vgap_tac `r1:real` `r2:real` `a1:real^N` `b1:real^N` `c1:real^N`
      `a0:real^N` `a2:real^N`
      `IMAGE (l:real^1->real^3) (interval[lift(&0),lift r1])`
      `IMAGE (l:real^1->real^3) (interval[lift r2,lift(&1)])`
      `(l:real^1->real^3)(lift(&0))`;
    moi_s4t_vgap_tac `r2:real` `&1` `a2:real^N` `b2:real^N` `c2:real^N`
      `a0:real^N` `a1:real^N`
      `IMAGE (l:real^1->real^3) (interval[lift(&0),lift r1])`
      `IMAGE (l:real^1->real^3) (interval[lift r1,lift r2])`
      `(l:real^1->real^3)(lift r1)`]);;

