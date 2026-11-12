(* ========================================================================= *)
(* pc_moi_s34_l910: Moise Sec 34, Lemmas 9-10, pp.243-244.  Main theorem     *)
(* L910 : |- MOI_S34_L910 (pc_moi_s34_stmt.ml), by a sphere route on the     *)
(* frontier of each vertex ball, with no use of MOI_FND_GRAPH_TUBE_HOLES.    *)
(* Infrastructure in pc_moi_s34_tinf (Sec 34 tube and traces) and          *)
(* pc_moi_pl1m (PL 1-manifolds).                                           *)
(* ========================================================================= *)

needs "src/pc_moi_s34_tinf.ml";;
needs "src/pc_moi_sch3_s2.ml";;
needs "src/pc_moi_sch3_free.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Link conditions.  A vertex property that agrees along the                 *)
(* edges avoiding w is constant on the vertices other than w, when the      *)
(* polyhedron of the (finite) complex minus w is connected.  Applied to the  *)
(* link of a vertex v of kk: the graph of the edges at v (adjacent through   *)
(* triangles at v) is connected, also after deleting one edge.              *)
(* ------------------------------------------------------------------------- *)

let MOI_S4L_SIMPLEX_EDGE_FACE = prove
 (`!t a b:real^N.
     (?n. n simplex t) /\ a extreme_point_of t /\ b extreme_point_of t
     ==> segment[a,b] face_of t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `c:real^N->bool`
    STRIP_ASSUME_TAC)) MP_TAC) THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT;
               FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  STRIP_TAC THEN EXISTS_TAC `{a:real^N,b}` THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL; INSERT_SUBSET; EMPTY_SUBSET]);;

let MOI_S4L_SIMPLEX_COMMON_VERTEX = prove
 (`!L t1 t2 (x:real^N) w.
     simplicial_complex L /\ t1 IN L /\ t2 IN L /\ x IN t1 /\ x IN t2 /\ ~(x = w)
     ==> ?a. a extreme_point_of t1 /\ a extreme_point_of t2 /\ ~(a = w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t1 INTER t2) face_of (t1:real^N->bool) /\ (t1 INTER t2) face_of t2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex(L:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?c:real^N->bool. ~affine_dependent c /\ t1 = convex hull c`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex(L:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex; simplex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?c':real^N->bool. c' SUBSET c /\ t1 INTER t2 = convex hull c'`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull c'` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^N. a IN c' /\ ~(a = w)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(s SUBSET {w:real^N}) ==> ?a. a IN s /\ ~(a = w)`) THEN
    DISCH_TAC THEN
    MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `c':real^N->bool`; `{w:real^N}`]
      HULL_MONO) THEN
    ASM_REWRITE_TAC[CONVEX_HULL_SING] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) extreme_point_of (t1 INTER t2)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c':real^N->bool`; `a:real^N`]
      EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[EXTREME_POINT_OF_FACE]);;

let MOI_S4L_COMPLEX_PUNCTURED_CONST = prove
 (`!(L:(real^N->bool)->bool) (P:real^N->bool) w.
     simplicial_complex L /\ connected (UNIONS L DELETE w) /\
     (!a b. segment[a,b] IN L /\ ~(a = w) /\ ~(b = w) ==> (P a <=> P b))
     ==> !a b. {a} IN L /\ {b} IN L /\ ~(a = w) /\ ~(b = w) ==> (P a <=> P b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!t a b:real^N. t IN L /\ a extreme_point_of t /\ b extreme_point_of t /\
                               ~(a = w) /\ ~(b = w) ==> (P a <=> P b)`
  (LABEL_TAC "same") THENL
   [REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `simplicial_complex(L:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "face_of")) (concl th) &&
      not (can (find_term (fun t -> is_const t && fst(dest_const t) = "INTER")) (concl th)))) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4L_SIMPLEX_EDGE_FACE THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `e1 = UNIONS {t | t IN L /\
                     !a:real^N. a extreme_point_of t /\ ~(a = w) ==> P a}` THEN
  ABBREV_TAC `e2 = UNIONS {t | t IN L /\
                     !a:real^N. a extreme_point_of t /\ ~(a = w) ==> ~P a}` THEN
  SUBGOAL_THEN `closed(e1:real^N->bool) /\ closed(e2:real^N->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN CONJ_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    (CONJ_TAC THENL
      [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
       CONJ_TAC THENL [ASM_MESON_TAC[simplicial_complex]; SET_TAC[]];
       ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CLOSED]]);
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS L DELETE (w:real^N) SUBSET e1 UNION e2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    ASM_CASES_TAC `!a:real^N. a extreme_point_of t /\ ~(a = w) ==> P a` THENL
     [DISJ1_TAC THEN EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC o
        REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
      X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
      USE_THEN "same" (MP_TAC o SPECL [`t:real^N->bool`; `a:real^N`; `b:real^N`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `e1 INTER e2 INTER (UNIONS L DELETE (w:real^N)) = {}` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN
    REWRITE_TAC[EXTENSION; NOT_IN_EMPTY; IN_INTER; IN_DELETE; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t1:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `t2:real^N->bool` STRIP_ASSUME_TAC)
        STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t1:real^N->bool`; `t2:real^N->bool`;
                   `x:real^N`; `w:real^N`] MOI_S4L_SIMPLEX_COMMON_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `e1 INTER (UNIONS L DELETE (w:real^N)) = {} \/
                e2 INTER (UNIONS L DELETE w) = {}` MP_TAC THENL
   [UNDISCH_TAC `connected (UNIONS L DELETE (w:real^N))` THEN
    REWRITE_TAC[CONNECTED_CLOSED] THEN
    DISCH_THEN(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`] o
      REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^N. {a} IN L /\ ~(a = w)
                ==> (P a ==> a IN e1 INTER (UNIONS L DELETE w)) /\
                    (~P a ==> a IN e2 INTER (UNIONS L DELETE w))` ASSUME_TAC THENL
   [X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
    MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN
    REWRITE_TAC[IN_INTER; IN_DELETE; IN_UNIONS; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?t:real^N->bool. t IN L /\ a IN t` (fun th -> REWRITE_TAC[th]) THENL
     [EXISTS_TAC `{a:real^N}` THEN ASM_REWRITE_TAC[IN_SING]; ALL_TAC] THEN
    REWRITE_TAC[EXTREME_POINT_OF_SING] THEN CONJ_TAC THEN DISCH_TAC THEN
    EXISTS_TAC `{a:real^N}` THEN ASM_SIMP_TAC[IN_SING; EXTREME_POINT_OF_SING];
    ALL_TAC] THEN
  STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `(P:real^N->bool) a` THEN ASM_CASES_TAC `(P:real^N->bool) b` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S4L_HOMEO_PUNCTURED = prove
 (`!d s (f:real^N->real^N) g w.
     homeomorphism (d,s) (f,g) /\ connected d /\ (!x. connected(d DELETE x))
     ==> connected(s DELETE w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(w:real^N) IN s` THENL
   [SUBGOAL_THEN `s DELETE (w:real^N) = IMAGE (f:real^N->real^N) (d DELETE (g:real^N->real^N) w)`
    SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `d:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_SIMP_TAC[SET_RULE `~((w:real^N) IN s) ==> s DELETE w = s`] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && is_comb(lhs(concl th)) &&
      fst(dest_const(fst(strip_comb(lhs(concl th))))) = "IMAGE" &&
      rand(lhs(concl th)) = `d:real^N->bool`)) THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[]]);;

let MOI_S4L_PL_SB2_PUNCTURED = prove
 (`!s w:real^N. pl_sphere 2 s \/ pl_ball 2 s ==> connected(s DELETE w)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_sphere; pl_ball; pl_homeomorphism] THEN
  CONV_TAC NUM_REDUCE_CONV THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S4L_HOMEO_PUNCTURED THENL
   [MAP_EVERY EXISTS_TAC [`relative_frontier k:real^N->bool`; `f:real^N->real^N`;
                          `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `convex(k:real^N->bool) /\ bounded k /\ aff_dim k = &3`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED;
                    AFF_DIM_SIMPLEX];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    X_GEN_TAC `x:real^N` THEN ASM_CASES_TAC `(x:real^N) IN relative_frontier k` THENL
     [MP_TAC(ISPECL [`k:real^N->bool`; `(:real^2)`; `x:real^N`]
        HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN) THEN
      ASM_REWRITE_TAC[AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_2] THEN
      CONV_TAC INT_REDUCE_CONV THEN
      DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_CONNECTEDNESS) THEN
      REWRITE_TAC[CONNECTED_UNIV];
      ASM_SIMP_TAC[SET_RULE `~((w:real^N) IN s) ==> s DELETE w = s`] THEN
      MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `convex(k:real^N->bool) /\ aff_dim k = &2` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; AFF_DIM_SIMPLEX]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONVEX_CONNECTED; CONNECTED_PUNCTURED_CONVEX; INT_ARITH `~(&2:int = &1)`]]);;

(* The graph of the edges of kk at a vertex v, adjacent through triangles   *)
(* at v, minus the edge to w: a property agreeing along such triangles is   *)
(* constant on the remaining edges at v.  (w may be any point; w = v gives *)
(* the plain connectivity used for Lemma 9.)                               *)
let MOI_S4L_LINK_EDGE_CONST = prove
 (`!kk (v:real^N) w (P:real^N->bool).
     combinatorial_manifold_with_boundary 3 kk /\ {v} IN kk /\
     (!a b. ~(a = v) /\ ~(b = v) /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
            convex hull {v,a,b} IN kk /\ aff_dim(convex hull {v,a,b}) = &2
            ==> (P a <=> P b))
     ==> !a b. segment[v,a] IN kk /\ segment[v,b] IN kk /\ ~(a = v) /\ ~(b = v) /\
               ~(a = w) /\ ~(b = w) ==> (P a <=> P b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex(kk:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  MP_TAC(ISPECL [`simplicial_link kk (v:real^N)`; `P:real^N->bool`; `w:real^N`]
    MOI_S4L_COMPLEX_PUNCTURED_CONST) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LINK_SC];
      MATCH_MP_TAC MOI_S4L_PL_SB2_PUNCTURED THEN
      UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (kk:(real^N->bool)->bool)` THEN
      REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_MESON_TAC[];
      MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
      ASM_CASES_TAC `a:real^N = b` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`; `segment[a:real^N,b]`]
        MOI_FM3_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `convex hull ((v:real^N) INSERT segment[a,b]) = convex hull {v,a,b}`
      ASSUME_TAC THENL
       [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
        ONCE_REWRITE_TAC[SET_RULE `(v:real^N) INSERT s = {v} UNION s`] THEN
        REWRITE_TAC[GSYM HULL_UNION_RIGHT] THEN AP_TERM_TAC THEN SET_TAC[];
        ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[ENDS_IN_SEGMENT];
        ASM_MESON_TAC[ENDS_IN_SEGMENT];
        UNDISCH_TAC `convex hull ((v:real^N) INSERT segment[a,b]) IN kk` THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `aff_dim (convex hull ((v:real^N) INSERT segment[a,b])) =
                     aff_dim (segment[a,b]) + &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN INT_ARITH_TAC]];
    ALL_TAC] THEN
  DISCH_TAC THEN MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!c:real^N. segment[v,c] IN kk /\ ~(c = v)
                           ==> {c} IN simplicial_link kk v`
  (fun th -> ASM_MESON_TAC[th]) THEN
  X_GEN_TAC `c:real^N` THEN STRIP_TAC THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM; IN_SING] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex(kk:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    EXISTS_TAC `segment[v:real^N,c]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    EXISTS_TAC `segment[v:real^N,c]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT; ENDS_IN_SEGMENT]]);;

(* ------------------------------------------------------------------------- *)
(* The sphere Sigma_v = frontier C_v and the open part of A_v.               *)
(* ------------------------------------------------------------------------- *)

let MOI_S4L_EDGE_SD = prove
 (`!(tt:(real^N->bool)->bool) kk v w.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk
     ==> segment[v,w] IN moi_s34_simp kk (&1) /\ {w} IN kk /\
         moi_s34_sd tt kk (segment[v,w]) =
         moi_s34_vb tt kk v INTER moi_s34_vb tt kk w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_TUBE_TUBE) THEN
  SUBGOAL_THEN `{w:real^N} IN kk` ASSUME_TAC THENL
   [UNDISCH_TAC `lf_simplicial_complex(kk:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    EXISTS_TAC `segment[v:real^N,w]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM; AFF_DIM_SEGMENT] THEN
  REWRITE_TAC[moi_s34_sd] THEN
  SUBGOAL_THEN `{moi_s34_vb tt kk x | x | x IN segment[v,w] /\ {x} IN kk} =
                {moi_s34_vb tt kk (v:real^N), moi_s34_vb tt kk w}` SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `q:real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `x:real^N`; `segment[v:real^N,w]`]
        MOI_S4L_LF_VERTEX_EXTREME) THEN
      ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN ASM_MESON_TAC[];
      STRIP_TAC THEN ASM_MESON_TAC[ENDS_IN_SEGMENT]];
    REWRITE_TAC[INTERS_INSERT; INTERS_0; INTER_UNIV]]);;

let MOI_S4L_LOCAL_AV = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     x IN IMAGE f1 (moi_s34_vb tt kk v) /\
     (!w. {w} IN kk /\ ~(w = v) ==> ~(x IN IMAGE f1 (moi_s34_vb tt kk w)))
     ==> ?oo. open oo /\ x IN oo /\
             IMAGE f1 (moi_s34_bd tt kk) INTER oo SUBSET
             IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN car {v:real^N}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u0. open u0 /\ (x:real^3) IN u0 /\
                     FINITE {q:real^N->bool | q IN kk /\ ~(q = {}) /\
                                              ~((car:(real^N->bool)->real^3->bool) q INTER u0 = {})}`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
    REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `car {v:real^N}:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  ABBREV_TAC `zs = UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u) | u |
                           {u} IN kk /\ ~(u = v) /\
                           ~((car:(real^N->bool)->real^3->bool) {u} INTER u0 = {})}` THEN
  SUBGOAL_THEN `closed(zs:real^3->bool) /\ ~((x:real^3) IN zs)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "zs" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `IMAGE (CHOICE:(real^N->bool)->real^N)
                      {q | q IN kk /\ ~(q = {}) /\
                           ~((car:(real^N->bool)->real^3->bool) q INTER u0 = {})}` THEN
        ASM_SIMP_TAC[FINITE_IMAGE] THEN
        REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_IMAGE] THEN X_GEN_TAC `u:real^N` THEN
        STRIP_TAC THEN EXISTS_TAC `{u:real^N}` THEN
        ASM_REWRITE_TAC[MOI_S4L_CHOICE_SING; NOT_INSERT_EMPTY];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        ASM_MESON_TAC[MOI_S4L_AV_BASIC]];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `t:real^3->bool` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      UNDISCH_TAC `(x:real^3) IN t` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `u0 DIFF (zs:real^3->bool)` THEN
  ASM_SIMP_TAC[OPEN_DIFF; IN_DIFF] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF] THEN X_GEN_TAC `y:real^3` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?u:real^N. {u} IN kk /\
                  (y:real^3) IN IMAGE (f1:real^N->real^3)
                                  (moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN UNIONS {IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) | v | {v} IN kk}` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = v` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN zs` (fun th -> ASM_MESON_TAC[th]) THEN
  EXPAND_TAC "zs" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk u)` THEN CONJ_TAC THENL
   [EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `u:real^N`] MOI_S4L_AV_BASIC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]];
    ASM SET_TAC[]]);;

let MOI_S4L_AV_NO_OTHER = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v w x.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     {v} IN kk /\ {w} IN kk /\ ~(w = v) /\
     x IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
     x IN IMAGE f1 (moi_s34_vb tt kk w)
     ==> segment[v,w] IN kk /\
         x IN IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
         x IN moi_s34_rims tt kk f1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE) THEN
  SUBGOAL_THEN `moi_s34_vb tt kk (v:real^N) SUBSET moi_s34_nb tt kk /\
                moi_s34_vb tt kk (w:real^N) SUBSET moi_s34_nb tt kk`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,w] IN kk` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^N`; `w:real^N`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "closed_segment")) (concl th) &&
      can (find_term ((=) `f1:real^N->real^3`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)` THEN
    UNDISCH_TAC `(x:real^3) IN IMAGE (f1:real^N->real^3)
                   (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk =
                  (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER moi_s34_vb tt kk (w:real^N)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (f1:real^N->real^3)
                    ((moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER moi_s34_vb tt kk w) =
                  IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) INTER
                  IMAGE f1 (moi_s34_vb tt kk w)` SUBST1_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_nb")) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "closed_segment"))
               (concl th)))) THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `moi_s34_vb tt kk (v:real^N) SUBSET moi_s34_nb tt kk` THEN SET_TAC[];
        FIRST_ASSUM ACCEPT_TAC];
      ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`; `w:real^N`]
    MOI_S4L_EDGE_SD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[moi_s34_rims; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `IMAGE (f1:real^N->real^3)
                (moi_s34_sd tt kk (segment[v,w]) INTER moi_s34_bd tt kk)` THEN
  CONJ_TAC THENL [EXISTS_TAC `segment[v:real^N,w]` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[INTER_ASSOC] THEN ASM_REWRITE_TAC[]);;

let MOI_S4L_SIGMA = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk
     ==> pl_sphere 2 (frontier (IMAGE f1 (moi_s34_vb tt kk v))) /\
         frontier (IMAGE f1 (moi_s34_vb tt kk v)) =
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) UNION
         UNIONS {IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) | w |
                 ~(w = v) /\ segment[v,w] IN kk} /\
         (!w. ~(w = v) /\ segment[v,w] IN kk
              ==> {w} IN kk /\
                  pl_cell_with_boundary 2
                    (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w))
                    (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                               moi_s34_bd tt kk)) /\
                  IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
                  IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) =
                  IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                            moi_s34_bd tt kk)) /\
         (!w w'. ~(w = v) /\ ~(w' = v) /\ ~(w = w') /\
                 segment[v,w] IN kk /\ segment[v,w'] IN kk
                 ==> IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
                     IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w') = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_AV_BASIC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE) THEN
  SUBGOAL_THEN `!w. ~(w = v) /\ segment[v:real^N,w] IN kk
                    ==> segment[v,w] IN moi_s34_simp kk (&1) /\ {w} IN kk /\
                        moi_s34_sd tt kk (segment[v,w]) =
                        moi_s34_vb tt kk v INTER moi_s34_vb tt kk w`
  (LABEL_TAC "esd") THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S4L_EDGE_SD THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4L_BALL_FRONTIER_SPHERE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `g:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(g:real^N->bool) IN kk` ASSUME_TAC THENL
       [UNDISCH_TAC `(g:real^N->bool) IN moi_s34_simp kk (&1)` THEN
        SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(v:real^N) = u \/ v = w` MP_TAC THENL
       [UNDISCH_TAC `{x | x IN g /\ {x} IN kk} = {u:real^N,w}` THEN
        REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        is_eq(concl th) && lhs(concl th) = `g:real^N->bool`)) THEN
      STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
       [EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
        EXISTS_TAC `u:real^N` THEN ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
        ASM_REWRITE_TAC[] THEN REWRITE_TAC[INTER_COMM]];
      X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `segment[v:real^N,w]` THEN
      USE_THEN "esd" (MP_TAC o SPEC `w:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    USE_THEN "esd" (MP_TAC o SPEC `w:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_s34_frame tt kk h ep (f1:real^N->real^3) car` THEN
      REWRITE_TAC[moi_s34_frame] THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `segment[v:real^N,w]` o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_cell_with_boundary"))
          (concl th))) THEN
      ASM_REWRITE_TAC[INTER_ASSOC];
      SUBGOAL_THEN `moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk =
                    (moi_s34_vb tt kk v INTER moi_s34_vb tt kk (w:real^N)) INTER
                    (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` SUBST1_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      CONV_TAC SYM_CONV THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s34_nb")) (concl th) &&
        not (can (find_term (fun t -> is_const t && fst(dest_const t) = "closed_segment"))
               (concl th)))) THEN
      SUBGOAL_THEN `moi_s34_vb tt kk (v:real^N) SUBSET moi_s34_nb tt kk` MP_TAC THENL
       [ASM_MESON_TAC[]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`w:real^N`; `w':real^N`] THEN STRIP_TAC THEN
    USE_THEN "esd" (MP_TAC o SPEC `w:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    USE_THEN "esd" (MP_TAC o SPEC `w':real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`v:real^N`; `w:real^N`; `w':real^N`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 3 &&
      can (find_term ((=) `f1:real^N->real^3`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_vb tt kk v INTER moi_s34_vb tt kk (w:real^N)`;
                   `moi_s34_vb tt kk (w:real^N)`] IMAGE_SUBSET) THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_vb tt kk v INTER moi_s34_vb tt kk (w':real^N)`;
                   `moi_s34_vb tt kk (w':real^N)`] IMAGE_SUBSET) THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_vb tt kk v INTER moi_s34_vb tt kk (w:real^N)`;
                   `moi_s34_vb tt kk (v:real^N)`] IMAGE_SUBSET) THEN
    REWRITE_TAC[INTER_SUBSET] THEN SET_TAC[]);;

(* A trace component inside A_v misses all rims (two-sidedness at rim     *)
(* points of the edges at v; triple intersections for the other edges).   *)
let MOI_S4L_COMP_MISS_RIMS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car s c v j.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     s IN moi_s34_simp kk (&2) /\ moi_s34_fb1 tt kk h f1 car s c /\ {v} IN kk /\
     j IN components (moi_s34_trace tt kk f1 c) /\
     j SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
     ==> DISJOINT j (moi_s34_rims tt kk f1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)` THEN
  REWRITE_TAC[moi_s34_rims; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(g:real^N->bool) IN kk` ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^N->bool) IN moi_s34_simp kk (&1)` THEN
    SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN q` THEN ASM_REWRITE_TAC[INTER_ASSOC]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s34_trace tt kk f1 c /\
                y IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET];
      MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`;
                     `moi_s34_vb tt kk (v:real^N)`] IMAGE_SUBSET) THEN
      REWRITE_TAC[INTER_SUBSET] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  (* the two-sided case at an edge of v *)
  SUBGOAL_THEN `!w':real^N. ~(w' = v) /\ segment[v,w'] IN kk /\
                  (y:real^3) IN IMAGE (f1:real^N->real^3)
                     (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w' INTER moi_s34_bd tt kk)
                  ==> F` (LABEL_TAC "two") THENL
   [X_GEN_TAC `w':real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                   `c:real^3->bool`; `v:real^N`; `w':real^N`; `y:real^3`; `&1`]
      MOI_S4L_CROSS_SIDES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `y':real^3`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(k:real^3->bool) SUBSET j` ASSUME_TAC THENL
     [MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
      EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3) c` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `y:real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~((y':real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`;
                   `moi_s34_vb tt kk (v:real^N)`] IMAGE_SUBSET) THEN
    REWRITE_TAC[INTER_SUBSET] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = v` THENL
   [USE_THEN "two" (MP_TAC o SPEC `w:real^N`) THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    UNDISCH_TAC `(g:real^N->bool) IN kk` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `w:real^N = v` THENL
   [USE_THEN "two" (MP_TAC o SPEC `u:real^N`) THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk u INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    UNDISCH_TAC `(g:real^N->bool) IN kk` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[SEGMENT_SYM] THEN
    REWRITE_TAC[SET_RULE `(a:real^N->bool) INTER b INTER c = b INTER a INTER c`] THEN
    MESON_TAC[SEGMENT_SYM];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMG_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `u:real^N`; `w:real^N`] o CONJUNCT1 o
    CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f1:real^N->real^3`;
                 `moi_s34_vb tt kk (u:real^N) INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk`;
                 `moi_s34_vb tt kk (u:real^N)`] IMAGE_SUBSET) THEN
  MP_TAC(ISPECL [`f1:real^N->real^3`;
                 `moi_s34_vb tt kk (u:real^N) INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk`;
                 `moi_s34_vb tt kk (w:real^N)`] IMAGE_SUBSET) THEN
  REWRITE_TAC[INTER_SUBSET; SET_RULE `(a:real^N->bool) INTER b INTER c SUBSET b`] THEN
  ASM SET_TAC[]);;

(* The splitting disks of two edges of a triangle tau at v lie on the same *)
(* side of a separating set b0 of Sigma_v that the broken lines of tau     *)
(* avoid.                                                                  *)
let MOI_S4L_SAME_SIDE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car tau ct v a b u1 u2 b0.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     tau IN moi_s34_simp kk (&2) /\ moi_s34_fb1 tt kk h f1 car tau ct /\
     {x | x IN tau /\ {x} IN kk} = {v,a,b} /\ ~(v = a) /\ ~(v = b) /\ ~(a = b) /\
     segment[v,a] IN kk /\ segment[v,b] IN kk /\ segment[a,b] IN kk /\
     closed u1 /\ closed u2 /\
     u1 UNION u2 = frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\ u1 INTER u2 = b0 /\
     DISJOINT b0 (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a)) /\
     DISJOINT b0 (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b)) /\
     (!z. connected z /\
          z SUBSET (moi_s34_trace tt kk f1 ct INTER
                    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)) UNION
                   IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a INTER
                             moi_s34_bd tt kk) UNION
                   IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b INTER
                             moi_s34_bd tt kk) /\
          ~(z INTER IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a INTER
                              moi_s34_bd tt kk) = {})
          ==> DISJOINT z b0)
     ==> (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a) SUBSET u1 <=>
          IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b) SUBSET u1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `tau:real^N->bool`; `ct:real^3->bool`;
                 `v:real^N`; `a:real^N`; `b:real^N`] MOI_S4L_BROKEN_LINE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{v:real^N} IN kk` ASSUME_TAC THENL
   [UNDISCH_TAC `{x | x IN tau /\ {x} IN kk} = {v:real^N,a,b}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `sg = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))` THEN
  ABBREV_TAC `da = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a)` THEN
  ABBREV_TAC `db = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b)` THEN
  ABBREV_TAC `ra = IMAGE (f1:real^N->real^3)
                 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `rb = IMAGE (f1:real^N->real^3)
                 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b INTER moi_s34_bd tt kk)` THEN
  ABBREV_TAC `av = IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
  SUBGOAL_THEN `connected(da:real^3->bool) /\ ra SUBSET da /\ ~(da = {}) /\
                connected(db:real^3->bool) /\ rb SUBSET db /\ ~(db = {}) /\
                da SUBSET sg /\ db SUBSET sg /\ ra SUBSET sg /\ rb SUBSET sg /\
                av SUBSET sg`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `a:real^N` th) THEN MP_TAC(SPEC `b:real^N` th)) o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_cell_with_boundary"))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO) ASSUME_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO) ASSUME_TAC)) THEN
    ASM_SIMP_TAC[PATH_CONNECTED_IMP_CONNECTED] THEN
    SUBGOAL_THEN `(da:real^3->bool) SUBSET sg /\ (db:real^3->bool) SUBSET sg /\ av SUBSET sg`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `sg = (av:real^3->bool) UNION
         UNIONS {IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) | w |
                 ~(w = v) /\ segment[v,w] IN kk}` THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
      REPEAT CONJ_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
      TRY(DISJ1_TAC THEN FIRST_ASSUM ACCEPT_TAC) THEN DISJ2_TAC THENL
       [EXISTS_TAC `da:real^3->bool`; EXISTS_TAC `db:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THENL
       [EXISTS_TAC `a:real^N`; EXISTS_TAC `b:real^N`] THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected((da UNION z) UNION (db:real^3->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_UNION THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONNECTED_UNION THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (z:real^3->bool) b0` ASSUME_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(da UNION z) UNION (db:real^3->bool)`; `u1:real^3->bool`;
                 `u2:real^3->bool`; `b0:real^3->bool`] MOI_SFR_CONNECTED_SIDE) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [UNDISCH_TAC `(u1:real^3->bool) UNION u2 = sg` THEN DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `(z:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3) ct INTER
                     av UNION ra UNION rb` THEN
      MAP_EVERY UNDISCH_TAC [`(da:real^3->bool) SUBSET sg`; `(db:real^3->bool) SUBSET sg`;
        `(ra:real^3->bool) SUBSET sg`; `(rb:real^3->bool) SUBSET sg`;
        `(av:real^3->bool) SUBSET sg`] THEN SET_TAC[];
      MAP_EVERY UNDISCH_TAC [`DISJOINT (z:real^3->bool) b0`;
        `DISJOINT (b0:real^3->bool) da`; `DISJOINT (b0:real^3->bool) db`] THEN SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC [`(u1:real^3->bool) INTER u2 = b0`;
    `DISJOINT (b0:real^3->bool) da`; `DISJOINT (b0:real^3->bool) db`;
    `~(da:real^3->bool = {})`; `~(db:real^3->bool = {})`] THEN
  SET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 9 (p.243): a trace component in A_v bounds a disk in A_v missing   *)
(* every splitting disk (sides of the sphere Sigma_v, broken lines, link     *)
(* connectivity); an innermost such disk is an Operation 1 witness.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4L_CLOPEN_MISS = prove
 (`!t r j z:real^N->bool.
     closed t /\ FINITE(components t) /\ j IN components t /\ closed r /\
     DISJOINT j r /\ connected z /\ z SUBSET t UNION r /\ ~(z SUBSET j)
     ==> DISJOINT z j`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `k0 = UNIONS (components t DELETE j) UNION (r:real^N->bool)` THEN
  SUBGOAL_THEN `closed(j:real^N->bool) /\ closed(k0:real^N->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[CLOSED_COMPONENTS]; ALL_TAC] THEN
    EXPAND_TAC "k0" THEN MATCH_MP_TAC CLOSED_UNION THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_DELETE; IN_DELETE] THEN
    ASM_MESON_TAC[CLOSED_COMPONENTS];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^N->bool) SUBSET j UNION k0` ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN
    MP_TAC(ISPEC `t:real^N->bool` UNIONS_COMPONENTS) THEN
    UNDISCH_TAC `(z:real^N->bool) SUBSET t UNION r` THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_DELETE; EXTENSION] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^N->bool) INTER k0 = {}` ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNION; IN_UNIONS; IN_DELETE; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
     [ASM_MESON_TAC[COMPONENTS_NONOVERLAP; IN_INTER; NOT_IN_EMPTY];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`z:real^N->bool`; `j:real^N->bool`; `k0:real^N->bool`; `{}:real^N->bool`]
    MOI_SFR_CONNECTED_SIDE) THEN
  ASM_REWRITE_TAC[INTER_EMPTY] THEN ASM SET_TAC[]);;

let MOI_S4L_LINK_TRI = prove
 (`!(tt:(real^N->bool)->bool) kk v a b.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(a = v) /\ ~(b = v) /\ ~(a = b) /\
     convex hull {v,a,b} IN kk /\ aff_dim(convex hull {v,a,b}) = &2
     ==> convex hull {v,a,b} IN moi_s34_simp kk (&2) /\
         {x | x IN convex hull {v,a,b} /\ {x} IN kk} = {v,a,b} /\
         segment[v,a] IN kk /\ segment[v,b] IN kk /\ segment[a,b] IN kk /\
         {a} IN kk /\ {b} IN kk`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_TUBE_TUBE) THEN
  SUBGOAL_THEN `CARD {v:real^N,a,b} = 3` ASSUME_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {v:real^N,a,b}` ASSUME_TAC THENL
   [REWRITE_TAC[AFFINE_INDEPENDENT_IFF_CARD; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(convex hull {v:real^N,a,b}) = &2` THEN
    REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN DISCH_THEN SUBST1_TAC THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `!c. c SUBSET {v:real^N,a,b} ==> convex hull c IN kk` (LABEL_TAC "faces") THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `lf_simplicial_complex(kk:(real^N->bool)->bool)` THEN
    REWRITE_TAC[lf_simplicial_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    EXISTS_TAC `convex hull {v:real^N,a,b}` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[v:real^N,a] IN kk /\ segment[v,b] IN kk /\ segment[a,b] IN kk /\
                {a} IN kk /\ {b} IN kk` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REPEAT CONJ_TAC THENL
     [USE_THEN "faces" (MP_TAC o SPEC `{v:real^N,a}`);
      USE_THEN "faces" (MP_TAC o SPEC `{v:real^N,b}`);
      USE_THEN "faces" (MP_TAC o SPEC `{a:real^N,b}`);
      USE_THEN "faces" (MP_TAC o SPEC `{a:real^N}`);
      USE_THEN "faces" (MP_TAC o SPEC `{b:real^N}`)] THEN
    REWRITE_TAC[CONVEX_HULL_SING] THEN DISCH_THEN MATCH_MP_TAC THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[moi_s34_simp; IN_ELIM_THM] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `x:real^N` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `x:real^N`; `convex hull {v:real^N,a,b}`]
      MOI_S4L_LF_VERTEX_EXTREME) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN SET_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]]);;

let MOI_S4L_RIM_IN_RIMS = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) v w.
     moi_s34_tube tt kk /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk
     ==> IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)
         SUBSET moi_s34_rims tt kk f1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `v:real^N`; `w:real^N`]
    MOI_S4L_EDGE_SD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  REWRITE_TAC[moi_s34_rims; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  EXISTS_TAC `IMAGE (f1:real^N->real^3)
                (moi_s34_sd tt kk (segment[v,w]) INTER moi_s34_bd tt kk)` THEN
  CONJ_TAC THENL [EXISTS_TAC `segment[v:real^N,w]` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[INTER_ASSOC]);;

(* With a separator b0 = u1 INTER u2 of Sigma_v avoided by the splitting     *)
(* disks and by the broken lines of the triangles at v avoiding w, all       *)
(* splitting disks at v other than the one to w lie on one side.             *)
let MOI_S4L_SIDES_AGREE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb v w u1 u2 b0.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ {v} IN kk /\
     closed u1 /\ closed u2 /\
     u1 UNION u2 = frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\ u1 INTER u2 = b0 /\
     (!a. ~(a = v) /\ ~(a = w) /\ segment[v,a] IN kk
          ==> DISJOINT b0 (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a))) /\
     (!a b z. ~(a = v) /\ ~(b = v) /\ ~(a = b) /\ ~(a = w) /\ ~(b = w) /\
              convex hull {v,a,b} IN kk /\ aff_dim(convex hull {v,a,b}) = &2 /\
              connected z /\
              z SUBSET (moi_s34_trace tt kk f1 (cb (convex hull {v,a,b})) INTER
                        IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)) UNION
                       IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a INTER
                                 moi_s34_bd tt kk) UNION
                       IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b INTER
                                 moi_s34_bd tt kk) /\
              ~(z INTER IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a INTER
                                  moi_s34_bd tt kk) = {})
              ==> DISJOINT z b0)
     ==> !a b. segment[v,a] IN kk /\ segment[v,b] IN kk /\ ~(a = v) /\ ~(b = v) /\
               ~(a = w) /\ ~(b = w)
               ==> (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a) SUBSET u1 <=>
                    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b) SUBSET u1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`kk:(real^N->bool)->bool`; `v:real^N`; `w:real^N`;
                 `\a. IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a)
                      SUBSET u1`] MOI_S4L_LINK_EDGE_CONST) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  CONJ_TAC THENL [ASM_MESON_TAC[moi_s34_tube]; ASM_REWRITE_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `v:real^N`; `a:real^N`; `b:real^N`] MOI_S4L_LINK_TRI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC MOI_S4L_SAME_SIDE THEN
  MAP_EVERY EXISTS_TAC [
    `h:real^N->real^3`; `ep:real^N->real`; `car:(real^N->bool)->real^3->bool`;
    `convex hull {v:real^N,a,b}`; `(cb:(real^N->bool)->real^3->bool) (convex hull {v,a,b})`;
    `u2:real^3->bool`; `b0:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `moi_s34_fbinv tt kk h (f1:real^N->real^3) car cb` THEN
    REWRITE_TAC[moi_s34_fbinv] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[];
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1)) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N`; `b:real^N`; `z:real^3->bool`] o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4L_CLEAN_SIDE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v e e' b0.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     e UNION e' = frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\ e INTER e' = b0 /\
     (!w. ~(w = v) /\ segment[v,w] IN kk
          ==> IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) SUBSET e' /\
              DISJOINT b0 (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)))
     ==> e SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
         (!g. g IN moi_s34_simp kk (&1)
              ==> DISJOINT e (IMAGE f1 (moi_s34_sd tt kk g)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. ~(w = v) /\ segment[v:real^N,w] IN kk
                    ==> DISJOINT (e:real^3->bool)
                          (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w))`
  (LABEL_TAC "dis") THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(e:real^3->bool) INTER e' = b0` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(e:real^3->bool) SUBSET
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(e:real^3->bool) SUBSET frontier (IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk v))` MP_TAC THENL
     [UNDISCH_TAC `(e:real^3->bool) UNION e' = frontier (IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk v))` THEN SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
      is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier")) (lhs(concl th)))) THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    USE_THEN "dis" (MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `g:real^N->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(g:real^N->bool) IN kk` ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^N->bool) IN moi_s34_simp kk (&1)` THEN
    SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_CASES_TAC `(v:real^N) IN g` THENL
   [SUBGOAL_THEN `(v:real^N) = u \/ v = w` MP_TAC THENL
     [UNDISCH_TAC `{x | x IN g /\ {x} IN kk} = {u:real^N,w}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `g:real^N->bool`)) THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [USE_THEN "dis" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      USE_THEN "dis" (MP_TAC o SPEC `u:real^N`) THEN
      ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[INTER_COMM]];
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMG_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`g:real^N->bool`; `v:real^N`] o CONJUNCT1 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`;
                   `moi_s34_vb tt kk (v:real^N)`] IMAGE_SUBSET) THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    UNDISCH_TAC `(e:real^3->bool) SUBSET
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    SET_TAC[]]);;

(* Lemma 9, first half: a trace component j of the face ball of s lying in *)
(* A_v bounds a disk e in A_v that meets no splitting disk.               *)
let MOI_S4L_L9_CLEAN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v j.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\ {v} IN kk /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     j SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)
     ==> ?e e'. pl_cell_with_boundary 2 e j /\ closed e /\ closed e' /\
                e UNION e' = frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\ e INTER e' = j /\
                e SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                (!g. g IN moi_s34_simp kk (&1)
                     ==> DISJOINT e (IMAGE f1 (moi_s34_sd tt kk g)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s (cb s)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_fbinv tt kk h (f1:real^N->real^3) car cb` THEN
    REWRITE_TAC[moi_s34_fbinv] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_S4L_TRI_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^N` (X_CHOOSE_THEN `p2:real^N` (X_CHOOSE_THEN `p3:real^N`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `s:real^N->bool`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `(cb:(real^N->bool)->real^3->bool) s`;
                 `p1:real^N`; `p2:real^N`; `p3:real^N`] MOI_S4L_TRACE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && is_comb(lhs(concl th)) &&
    is_const(fst(strip_comb(lhs(concl th)))) &&
    fst(dest_const(fst(strip_comb(lhs(concl th))))) = "moi_s34_trace")) THEN
  SUBGOAL_THEN `pl_sphere 1 (j:real^3->bool)` ASSUME_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && moi_s4l_has "pl_sphere" th)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `(cb:(real^N->bool)->real^3->bool) s`; `v:real^N`; `j:real^3->bool`]
    MOI_S4L_COMP_MISS_RIMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!w. ~(w = v) /\ segment[v:real^N,w] IN kk
        ==> IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) SUBSET
            frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\
            DISJOINT j (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)) /\
            connected (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)) /\
            ~(IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) = {})`
  (LABEL_TAC "nbr") THENL
   [X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "pl_cell_with_boundary"))
        (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO) THEN
    REPEAT CONJ_TAC THENL
     [ALL_TAC; ALL_TAC; ASM_SIMP_TAC[PATH_CONNECTED_IMP_CONNECTED];
      UNDISCH_TAC `~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)
                     DIFF IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                                    moi_s34_bd tt kk) = {})` THEN SET_TAC[]] THENL
     [FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_eq(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier")) (lhs(concl th))))
      THEN REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `f1:real^N->real^3`; `v:real^N`; `w:real^N`] MOI_S4L_RIM_IN_RIMS) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!a r rr. DISJOINT (j:real^3->bool) rr /\ j SUBSET a /\
                                      d INTER a = r /\ r SUBSET rr ==> DISJOINT j d`) THEN
      MAP_EVERY EXISTS_TAC
       [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
        `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                                    moi_s34_bd tt kk)`;
        `moi_s34_rims tt kk (f1:real^N->real^3)`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET frontier (IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v))` ASSUME_TAC THENL
   [FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
      is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier")) (lhs(concl th))))
    THEN MATCH_MP_TAC(SET_RULE `!j a b:real^3->bool. j SUBSET a ==> j SUBSET a UNION b`) THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier")) (lhs(concl th)))) THEN
  MP_TAC(ISPECL [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
                 `j:real^3->bool`] SPHERE_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `closed(d1:real^3->bool) /\ closed(d2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `d1:real^3->bool`; `j:real^3->bool`] MOI_S4L_PL_CELL_FACTS) THEN
    MP_TAC(ISPECL [`2`; `d2:real^3->bool`; `j:real^3->bool`] MOI_S4L_PL_CELL_FACTS) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  (* the splitting disks at v all lie on one side of j *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `v:real^N`; `d1:real^3->bool`; `d2:real^3->bool`;
                 `j:real^3->bool`] MOI_S4L_SIDES_AGREE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `a:real^N` THEN STRIP_TAC THEN
      USE_THEN "nbr" (MP_TAC o SPEC `a:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `z:real^3->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `v:real^N`; `a:real^N`; `b:real^N`] MOI_S4L_LINK_TRI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN
     `DISJOINT (j:real^3->bool) (IMAGE (f1:real^N->real^3)
        (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a INTER moi_s34_bd tt kk)) /\
      DISJOINT j (IMAGE f1
        (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b INTER moi_s34_bd tt kk)) /\
      compact (IMAGE f1
        (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a INTER moi_s34_bd tt kk)) /\
      compact (IMAGE f1
        (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b INTER moi_s34_bd tt kk))`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `f1:real^N->real^3`; `v:real^N`; `a:real^N`] MOI_S4L_RIM_IN_RIMS) THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `f1:real^N->real^3`; `v:real^N`; `b:real^N`] MOI_S4L_RIM_IN_RIMS) THEN
      ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `!rr. DISJOINT (j:real^3->bool) rr /\ r SUBSET rr
                                    ==> DISJOINT j r`) THEN
        EXISTS_TAC `moi_s34_rims tt kk (f1:real^N->real^3)` THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC(SET_RULE `!rr. DISJOINT (j:real^3->bool) rr /\ r SUBSET rr
                                    ==> DISJOINT j r`) THEN
        EXISTS_TAC `moi_s34_rims tt kk (f1:real^N->real^3)` THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `a:real^N` o check (fun th ->
          is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
          moi_s4l_has "pl_cell_with_boundary" th)) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS o CONJUNCT1 o CONJUNCT2) THEN
        SIMP_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPEC `b:real^N` o check (fun th ->
          is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
          moi_s4l_has "pl_cell_with_boundary" th)) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        DISCH_THEN(MP_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS o CONJUNCT1 o CONJUNCT2) THEN
        SIMP_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `convex hull {v:real^N,a,b} = s` THENL
     [MATCH_MP_TAC MOI_S4L_CLOPEN_MISS THEN
      MAP_EVERY EXISTS_TAC
       [`moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`;
        `IMAGE (f1:real^N->real^3)
           (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a INTER moi_s34_bd tt kk) UNION
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b INTER moi_s34_bd tt kk)`] THEN
      REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
        FIRST_ASSUM ACCEPT_TAC;
        FIRST_ASSUM ACCEPT_TAC;
        ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CLOSED_UNION];
        MATCH_MP_TAC(SET_RULE `DISJOINT (j:real^3->bool) a /\ DISJOINT j b
                               ==> DISJOINT j (a UNION b)`) THEN
        ASM_REWRITE_TAC[];
        FIRST_ASSUM ACCEPT_TAC;
        UNDISCH_TAC `convex hull {v:real^N,a,b} = s` THEN DISCH_THEN SUBST_ALL_TAC THEN
        MATCH_MP_TAC(SET_RULE `!a. (z:real^3->bool) SUBSET (t INTER a) UNION ra UNION rb
                               ==> z SUBSET t UNION ra UNION rb`) THEN
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
        FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC(SET_RULE `!ra. ~((z:real^3->bool) INTER ra = {}) /\ DISJOINT j ra
                               ==> ~(z SUBSET j)`) THEN
        EXISTS_TAC `IMAGE (f1:real^N->real^3)
            (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a INTER moi_s34_bd tt kk)` THEN
        ASM_REWRITE_TAC[]];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                     `s:real^N->bool`; `convex hull {v:real^N,a,b}`] MOI_S4L_TRACES_DISJ) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
      SUBGOAL_THEN `(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                     ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
       [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE
       `!t t' a ra rb. z SUBSET (t' INTER a) UNION ra UNION rb /\ j SUBSET t /\
                       t INTER t' = {} /\ DISJOINT j ra /\ DISJOINT j rb
                       ==> DISJOINT (z:real^3->bool) j`) THEN
      MAP_EVERY EXISTS_TAC
       [`moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`;
        `moi_s34_trace tt kk (f1:real^N->real^3)
           ((cb:(real^N->bool)->real^3->bool) (convex hull {v:real^N,a,b}))`;
        `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
        `IMAGE (f1:real^N->real^3)
           (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a INTER moi_s34_bd tt kk)`;
        `IMAGE (f1:real^N->real^3)
           (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b INTER moi_s34_bd tt kk)`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(LABEL_TAC "agree")] THEN
  ASM_CASES_TAC `?a:real^N. ~(a = v) /\ segment[v,a] IN kk /\
                  IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a)
                  SUBSET d1` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `a0:real^N` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`d2:real^3->bool`; `d1:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_S4L_CLEAN_SIDE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
      `car:(real^N->bool)->real^3->bool`; `d1:real^3->bool`; `j:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
      ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN CONJ_TAC THENL
       [USE_THEN "agree" (MP_TAC o SPECL [`w:real^N`; `a0:real^N`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
        USE_THEN "nbr" (MP_TAC o SPEC `w:real^N`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]];
    MAP_EVERY EXISTS_TAC [`d1:real^3->bool`; `d2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S4L_CLEAN_SIDE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
      `car:(real^N->bool)->real^3->bool`; `d2:real^3->bool`; `j:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN
    USE_THEN "nbr" (MP_TAC o SPEC `w:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`;
                   `d1:real^3->bool`; `d2:real^3->bool`; `j:real^3->bool`]
      MOI_SFR_CONNECTED_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `DISJOINT (j:real^3->bool) (IMAGE (f1:real^N->real^3)
                     (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w))` THEN SET_TAC[];
      ASM_MESON_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 9, second half: innermost clean disks.                              *)
(* ------------------------------------------------------------------------- *)

(* A connected subset k of M = f1(Bd N) meeting a clean side e of a curve b *)
(* in Sigma_v and missing b lies in e (near e DIFF b, M is A_v).           *)
let MOI_S4L_COMP_INSIDE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v e e' b k.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     closed e /\ closed e' /\
     e UNION e' = frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\ e INTER e' = b /\
     e SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
     DISJOINT (e DIFF b) (moi_s34_rims tt kk f1) /\
     connected k /\ k SUBSET IMAGE f1 (moi_s34_bd tt kk) /\ DISJOINT k b /\
     ~(k INTER e = {})
     ==> k SUBSET e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
                e UNION e'` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SUBSET_UNION]; ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier")) (lhs(concl th)))) THEN
  UNDISCH_TAC `connected(k:real^3->bool)` THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `k INTER (e:real^3->bool)`) THEN
  ANTS_TAC THENL
   [ALL_TAC; UNDISCH_TAC `~((k:real^3->bool) INTER e = {})` THEN SET_TAC[]] THEN
  ASM_SIMP_TAC[CLOSED_IN_CLOSED_INTER] THEN
  ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `x:real^3` THEN
  REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((x:real^3) IN b) /\ ~(x IN e') /\ ~(x IN moi_s34_rims tt kk f1) /\
                x IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`DISJOINT (k:real^3->bool) b`; `(e:real^3->bool) INTER e' = b`;
      `DISJOINT ((e:real^3->bool) DIFF b) (moi_s34_rims tt kk (f1:real^N->real^3))`;
      `(e:real^3->bool) SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
      `(x:real^3) IN k`; `(x:real^3) IN e`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`; `x:real^3`]
    MOI_S4L_LOCAL_AV) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MP_TAC(ISPECL [`f1:real^N->real^3`;
                     `moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`;
                     `moi_s34_vb tt kk (v:real^N)`] IMAGE_SUBSET) THEN
      REWRITE_TAC[INTER_SUBSET] THEN ASM SET_TAC[];
      X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `v:real^N`; `w:real^N`; `x:real^3`]
        MOI_S4L_AV_NO_OTHER) THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k INTER (oo INTER ((:real^3) DIFF e'))` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN MATCH_MP_TAC OPEN_INTER THEN
    ASM_REWRITE_TAC[GSYM closed];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_UNIV] THEN
  MAP_EVERY UNDISCH_TAC
   [`(k:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk) INTER oo SUBSET
     IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
     e UNION e'`] THEN
  SET_TAC[]);;

let MOI_S4L_TRACE_COMP_FACTS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ s IN moi_s34_simp kk (&2)
     ==> moi_s34_fb1 tt kk h f1 car s (cb s) /\
         compact (moi_s34_trace tt kk f1 (cb s)) /\
         FINITE (components (moi_s34_trace tt kk f1 (cb s))) /\
         (!k. k IN components (moi_s34_trace tt kk f1 (cb s)) ==> pl_sphere 1 k) /\
         compact (cb s) /\ frontier (cb s) SUBSET cb s /\
         moi_s34_trace tt kk f1 (cb s) SUBSET cb s /\
         moi_s34_trace tt kk f1 (cb s) SUBSET IMAGE f1 (moi_s34_bd tt kk)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s (cb s)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s34_fbinv tt kk h (f1:real^N->real^3) car cb` THEN
    REWRITE_TAC[moi_s34_fbinv] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`; `s:real^N->bool`]
    MOI_S4L_TRI_FORM) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^N` (X_CHOOSE_THEN `p2:real^N` (X_CHOOSE_THEN `p3:real^N`
    STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `s:real^N->bool`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `(cb:(real^N->bool)->real^3->bool) s`;
                 `p1:real^N`; `p2:real^N`; `p3:real^N`] MOI_S4L_TRACE_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) && is_comb(lhs(concl th)) &&
    is_const(fst(strip_comb(lhs(concl th)))) &&
    fst(dest_const(fst(strip_comb(lhs(concl th))))) = "moi_s34_trace")) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s34_trace; INTER_SUBSET] THEN
  MATCH_MP_TAC(SET_RULE `f SUBSET c ==> f INTER m SUBSET (c:real^3->bool)`) THEN
  ASM_REWRITE_TAC[]);;

let MOI_S4L_TRACE_AT_V = prove
 (`!(tt:(real^N->bool)->bool) kk h (f1:real^N->real^3) car s c v k.
     moi_s34_fb1 tt kk h f1 car s c /\ {v} IN kk /\
     k SUBSET moi_s34_trace tt kk f1 c /\ k SUBSET IMAGE f1 (moi_s34_vb tt kk v) /\
     ~(k = {})
     ==> v IN s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s c` THEN
  REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N` o check (fun th ->
    is_forall(concl th) && moi_s4l_has "DISJOINT" th)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `compact(c:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S4L_PL_BALL_COMPACT]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier(c:real^3->bool) SUBSET c` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(k:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3) c`;
    `(k:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`;
    `~(k:real^3->bool = {})`; `frontier(c:real^3->bool) SUBSET c`] THEN
  REWRITE_TAC[moi_s34_trace] THEN SET_TAC[]);;

let moi_s4l_cand = new_definition
 `moi_s4l_cand (tt:(real^N->bool)->bool) kk (f1:real^N->real^3) cb v s j e e' <=>
    s IN moi_s34_simp kk (&2) /\ j IN components (moi_s34_trace tt kk f1 (cb s)) /\
    pl_cell_with_boundary 2 e j /\ closed e /\ closed e' /\
    e UNION e' = frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\ e INTER e' = j /\
    e SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
    (!g. g IN moi_s34_simp kk (&1) ==> DISJOINT e (IMAGE f1 (moi_s34_sd tt kk g)))`;;

let MOI_S4L_FAMILY_FINITE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ {v} IN kk
     ==> FINITE (UNIONS {components (moi_s34_trace tt kk f1 (cb s)) | s |
                         s IN moi_s34_simp kk (&2) /\ v IN s})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_TUBE_TUBE) THEN
  REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t:real^N->bool | t IN kk /\ v IN t}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_STAR_FINITE THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN MESON_TAC[]];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
    ASM_SIMP_TAC[]]);;

(* A trace component k inside the open part of a clean disk e bounds a      *)
(* clean disk e1 inside e, which does not contain the boundary j of e.     *)
let MOI_S4L_SMALLER = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb v s j e e' s1 k.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ {v} IN kk /\
     moi_s4l_cand tt kk f1 cb v s j e e' /\
     s1 IN moi_s34_simp kk (&2) /\ k IN components (moi_s34_trace tt kk f1 (cb s1)) /\
     k SUBSET e DIFF j
     ==> ?e1 e1'. moi_s4l_cand tt kk f1 cb v s1 k e1 e1' /\ e1 SUBSET e /\
                  ~(j SUBSET e1)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4l_cand] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s1:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (k:real^3->bool) /\ ~(k = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && moi_s4l_has "pl_sphere" th)) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier")) (lhs(concl th)))) THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET frontier (IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v))` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(k:real^3->bool) SUBSET e DIFF j`;
      `(e:real^3->bool) UNION e' = frontier (IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
                 `k:real^3->bool`] SPHERE_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `connected (j:real^3->bool) /\ ~(j = {}) /\ j SUBSET e` STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
      moi_s4l_has "pl_cell_with_boundary" th && rand(concl th) = `j:real^3->bool`)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u u'. pl_cell_with_boundary 2 u k /\ pl_cell_with_boundary 2 u' k /\
           u UNION u' = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) /\
           u INTER u' = k /\ j SUBSET u'
           ==> ?e1 e1'. (s1 IN moi_s34_simp kk (&2) /\
                         k IN components (moi_s34_trace tt kk f1 (cb s1)) /\
                         pl_cell_with_boundary 2 e1 k /\ closed e1 /\ closed e1' /\
                         e1 UNION e1' = frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\
                         e1 INTER e1' = k /\
                         e1 SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                         (!g. g IN moi_s34_simp kk (&1)
                              ==> DISJOINT e1 (IMAGE f1 (moi_s34_sd tt kk g)))) /\
                        e1 SUBSET e /\ ~(j SUBSET e1)`
  (LABEL_TAC "side") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `u':real^3->bool`] THEN
    MP_TAC(ISPECL [`2`; `u:real^3->bool`; `k:real^3->bool`] MOI_S4L_PL_CELL_FACTS) THEN
    MP_TAC(ISPECL [`2`; `u':real^3->bool`; `k:real^3->bool`] MOI_S4L_PL_CELL_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN STRIP_ASSUME_TAC THEN DISCH_THEN STRIP_ASSUME_TAC THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
      moi_s4l_has "pl_cell_with_boundary" th &&
      rand(rator(concl th)) = `u:real^3->bool`)) THEN
    SUBGOAL_THEN `(u:real^3->bool) SUBSET e` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`(u:real^3->bool) DIFF k`; `e:real^3->bool`; `e':real^3->bool`;
                     `j:real^3->bool`] MOI_SFR_CONNECTED_SIDE) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`(k:real^3->bool) SUBSET e DIFF j`; `(j:real^3->bool) SUBSET u'`;
          `(u:real^3->bool) INTER u' = k`;
          `(u:real^3->bool) UNION u' = frontier (IMAGE (f1:real^N->real^3)
             (moi_s34_vb tt kk v))`;
          `(e:real^3->bool) UNION e' = frontier (IMAGE (f1:real^N->real^3)
             (moi_s34_vb tt kk v))`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `closure((u:real^3->bool) DIFF k)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(u:real^3->bool) SUBSET e'` ASSUME_TAC THENL
         [MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `closure((u:real^3->bool) DIFF k)` THEN ASM_REWRITE_TAC[] THEN
          MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [`(k:real^3->bool) SUBSET e DIFF j`; `(u:real^3->bool) SUBSET e'`;
          `(e:real^3->bool) INTER e' = j`; `(u:real^3->bool) INTER u' = k`;
          `~(k:real^3->bool = {})`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
      ASM SET_TAC[];
      X_GEN_TAC `g:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!e. DISJOINT e d /\ (u:real^3->bool) SUBSET e
                             ==> DISJOINT u d`) THEN
      EXISTS_TAC `e:real^3->bool` THEN ASM_SIMP_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`(k:real^3->bool) SUBSET e DIFF j`; `(j:real^3->bool) SUBSET u'`;
        `(u:real^3->bool) INTER u' = k`; `~(j:real^3->bool = {})`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`j:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`;
                 `k:real^3->bool`] MOI_SFR_CONNECTED_SIDE) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`2`; `d1:real^3->bool`; `k:real^3->bool`] MOI_S4L_PL_CELL_FACTS) THEN
    MP_TAC(ISPECL [`2`; `d2:real^3->bool`; `k:real^3->bool`] MOI_S4L_PL_CELL_FACTS) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN REPEAT DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC
     [`(k:real^3->bool) SUBSET e DIFF j`; `(j:real^3->bool) SUBSET e`;
      `(d1:real^3->bool) UNION d2 = frontier (IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v))`;
      `(e:real^3->bool) UNION e' = frontier (IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [USE_THEN "side" (MP_TAC o SPECL [`d2:real^3->bool`; `d1:real^3->bool`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]];
      SIMP_TAC[]];
    USE_THEN "side" (MP_TAC o SPECL [`d1:real^3->bool`; `d2:real^3->bool`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]]]);;

let MOI_S4L_CLEAN_NO_RIMS = prove
 (`!(tt:(real^N->bool)->bool) kk (f1:real^N->real^3) e.
     (!g. g IN moi_s34_simp kk (&1) ==> DISJOINT e (IMAGE f1 (moi_s34_sd tt kk g)))
     ==> DISJOINT e (moi_s34_rims tt kk f1)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  REWRITE_TAC[moi_s34_rims; DISJOINT; EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM;
              NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `g:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_sd tt kk (g:real^N->bool) INTER moi_s34_bd tt kk`;
                 `moi_s34_sd tt kk (g:real^N->bool)`] IMAGE_SUBSET) THEN
  REWRITE_TAC[INTER_SUBSET] THEN
  MAP_EVERY UNDISCH_TAC [`(y:real^3) IN e`; `(y:real^3) IN t`] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* An innermost clean disk: no trace point in its open part. *)
let MOI_S4L_L9_MIN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb v s0 j0 e0 e0'.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ {v} IN kk /\
     moi_s4l_cand tt kk f1 cb v s0 j0 e0 e0'
     ==> ?s j e e'. moi_s4l_cand tt kk f1 cb v s j e e' /\
                    !s1. s1 IN moi_s34_simp kk (&2)
                         ==> DISJOINT (e DIFF j) (moi_s34_trace tt kk f1 (cb s1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `ff = UNIONS {components (moi_s34_trace tt kk (f1:real^N->real^3)
                                         ((cb:(real^N->bool)->real^3->bool) s)) | s |
                           s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s}` THEN
  SUBGOAL_THEN `FINITE (ff:(real^3->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ff" THEN MATCH_MP_TAC MOI_S4L_FAMILY_FINITE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\n. ?s j e e'. moi_s4l_cand tt kk (f1:real^N->real^3) cb (v:real^N) s j e e' /\
                    CARD {k | k IN ff /\ k SUBSET e} = n` num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`CARD {k | k IN ff /\ (k:real^3->bool) SUBSET e0}`;
      `s0:real^N->bool`; `j0:real^3->bool`; `e0:real^3->bool`; `e0':real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `j:real^3->bool`
      (X_CHOOSE_THEN `e:real^3->bool` (X_CHOOSE_THEN `e':real^3->bool` STRIP_ASSUME_TAC))))
    (LABEL_TAC "min"))) THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `j:real^3->bool`; `e:real^3->bool`;
                        `e':real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s1:real^N->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s4l_cand tt kk (f1:real^N->real^3) cb v s j e e'` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[moi_s4l_cand] th)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s1:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ABBREV_TAC `k = connected_component (moi_s34_trace tt kk (f1:real^N->real^3)
                    ((cb:(real^N->bool)->real^3->bool) s1)) y` THEN
  SUBGOAL_THEN `(k:real^3->bool) IN components (moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s1)) /\
                y IN k /\ connected k /\
                k SUBSET moi_s34_trace tt kk f1 (cb s1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "k" THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS];
      REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT];
      REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (k:real^3->bool) j` ASSUME_TAC THENL
   [ASM_CASES_TAC `s1:real^N->bool = s` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      MP_TAC(ISPECL [`moi_s34_trace tt kk (f1:real^N->real^3)
                       ((cb:(real^N->bool)->real^3->bool) s)`;
                     `k:real^3->bool`; `j:real^3->bool`] COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[DISJOINT] THEN DISCH_THEN SUBST1_TAC THEN
      DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                     `s:real^N->bool`; `s1:real^N->bool`] MOI_S4L_TRACES_DISJ) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`(k:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
          ((cb:(real^N->bool)->real^3->bool) s1)`;
        `(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
          ((cb:(real^N->bool)->real^3->bool) s)`;
        `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s) INTER
         moi_s34_trace tt kk f1 (cb s1) = {}`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET e` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4L_COMP_INSIDE THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
      `car:(real^N->bool)->real^3->bool`; `v:real^N`; `e':real^3->bool`; `j:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `DISJOINT (e:real^3->bool) r ==> DISJOINT (e DIFF j) r`) THEN
      MATCH_MP_TAC MOI_S4L_CLEAN_NO_RIMS THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3)
                    ((cb:(real^N->bool)->real^3->bool) s1)` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(y:real^3) IN k` THEN UNDISCH_TAC `(y:real^3) IN e` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `s:real^N->bool`; `j:real^3->bool`; `e:real^3->bool`;
                 `e':real^3->bool`; `s1:real^N->bool`; `k:real^3->bool`] MOI_S4L_SMALLER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(k:real^3->bool) SUBSET e` THEN UNDISCH_TAC `DISJOINT (k:real^3->bool) j` THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^3->bool` (X_CHOOSE_THEN `e1':real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  USE_THEN "min" (MP_TAC o SPEC `CARD {k' | k' IN ff /\ (k':real^3->bool) SUBSET e1}`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `k:real^3->bool`; `e1:real^3->bool`;
                          `e1':real^3->bool`] THEN
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `CARD {k | k IN ff /\ (k:real^3->bool) SUBSET e} = n` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CARD_PSUBSET THEN CONJ_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `ff:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]] THEN
  REWRITE_TAC[PSUBSET; SUBSET; IN_ELIM_THM; EXTENSION] THEN CONJ_TAC THENL
   [X_GEN_TAC `k':real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    DISCH_THEN(MP_TAC o SPEC `j:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(j:real^3->bool) IN ff` (fun th -> REWRITE_TAC[th]) THENL
     [EXPAND_TAC "ff" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `components (moi_s34_trace tt kk (f1:real^N->real^3)
                    ((cb:(real^N->bool)->real^3->bool) s))` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_S4L_TRACE_AT_V THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
        `h:real^N->real^3`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
        `(cb:(real^N->bool)->real^3->bool) s`; `j:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`f1:real^N->real^3`;
                       `moi_s34_vb tt kk (v:real^N) INTER moi_s34_bd tt kk`;
                       `moi_s34_vb tt kk (v:real^N)`] IMAGE_SUBSET) THEN
        REWRITE_TAC[INTER_SUBSET] THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
          moi_s4l_has "pl_cell_with_boundary" th && rand(concl th) = `j:real^3->bool`)) THEN
        MAP_EVERY UNDISCH_TAC
         [`(j:real^3->bool) SUBSET e`;
          `(e:real^3->bool) SUBSET IMAGE (f1:real^N->real^3)
             (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`] THEN
        SET_TAC[];
        ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]];
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
        moi_s4l_has "pl_cell_with_boundary" th && rand(concl th) = `j:real^3->bool`)) THEN
      REWRITE_TAC[GSYM SUBSET] THEN ASM_REWRITE_TAC[]]]);;

(* Lemma 9 (p.243): with Operation 1 impossible, no trace component lies in *)
(* one A_v.                                                               *)
let MOI_S4L_L9 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\
     (!s. s IN moi_s34_simp kk (&2) ==> ~moi_s34_op1 tt kk f1 cb s)
     ==> !s v j. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\
                 j IN components (moi_s34_trace tt kk f1 (cb s))
                 ==> ~(j SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v:real^N`; `j:real^3->bool`] MOI_S4L_L9_CLEAN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^3->bool` (X_CHOOSE_THEN `e0':real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `s:real^N->bool`; `j:real^3->bool`; `e0:real^3->bool`;
                 `e0':real^3->bool`] MOI_S4L_L9_MIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[moi_s4l_cand]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s1:real^N->bool` (X_CHOOSE_THEN `j1:real^3->bool`
    (X_CHOOSE_THEN `e:real^3->bool` (X_CHOOSE_THEN `e':real^3->bool`
      (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[moi_s4l_cand])
                       (LABEL_TAC "empty")))))) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s1:real^N->bool` o check (fun th ->
    is_forall(concl th) && moi_s4l_has "moi_s34_op1" th)) THEN
  ASM_REWRITE_TAC[moi_s34_op1] THEN
  MAP_EVERY EXISTS_TAC [`v:real^N`; `e:real^3->bool`; `j1:real^3->bool`] THEN
  REWRITE_TAC[moi_s34_op1w] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s1:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
    moi_s4l_has "pl_cell_with_boundary" th && rand(concl th) = `j1:real^3->bool`)) THEN
  SUBGOAL_THEN `(e:real^3->bool) SUBSET IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j1:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s1)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "empty" (MP_TAC o SPEC `s1:real^N->bool`) THEN
    ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!m. DISJOINT (e DIFF j) (f INTER m) /\ j SUBSET f INTER m /\
                               j SUBSET e /\ e SUBSET m ==> (e:real^3->bool) INTER f = j`) THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
    REWRITE_TAC[GSYM moi_s34_trace] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `s':real^N->bool` THEN STRIP_TAC THEN
  USE_THEN "empty" (MP_TAC o SPEC `s':real^N->bool`) THEN
  ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s':real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `(e:real^3->bool) DIFF j1 SUBSET (cb:(real^N->bool)->real^3->bool) s'`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`(e:real^3->bool) DIFF j1`;
                   `(cb:(real^N->bool)->real^3->bool) s'`] CONNECTED_INTER_FRONTIER) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `((e:real^3->bool) DIFF j1) INTER frontier ((cb:(real^N->bool)->real^3->bool) s') = {}`
    (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC(SET_RULE `!m. DISJOINT (e DIFF j) (f INTER m) /\ e SUBSET m
                               ==> ((e:real^3->bool) DIFF j) INTER f = {}`) THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)` THEN
      REWRITE_TAC[GSYM moi_s34_trace] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~DISJOINT ((e:real^3->bool) DIFF j1) ((cb:(real^N->bool)->real^3->bool) s')` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j1:real^3->bool) SUBSET (cb:(real^N->bool)->real^3->bool) s'` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `e:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `closure((e:real^3->bool) DIFF j1)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s1:real^N->bool`; `s':real^N->bool`] MOI_S4L_TRACES_DISJ) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `~(j1:real^3->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY]; ALL_TAC] THEN
  MP_TAC(SET_RULE
   `!j t c c' m:real^3->bool. j SUBSET c' /\ j SUBSET t /\ t SUBSET c /\ t SUBSET m /\
                 c INTER c' INTER m = {} /\ ~(j = {}) ==> F`) THEN
  DISCH_THEN(MP_TAC o SPECL
   [`j1:real^3->bool`;
    `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s1)`;
    `(cb:(real^N->bool)->real^3->bool) s1`; `(cb:(real^N->bool)->real^3->bool) s'`;
    `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`]) THEN
  ASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Arcs and circles (generic, for Lemma 10).                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S4L_ARC_INTERIOR_CONNECTED = prove
 (`!h:real^1->real^N.
     arc h ==> connected (path_image h DIFF {pathstart h,pathfinish h})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `path_image h DIFF {pathstart h,pathfinish h} =
                IMAGE (h:real^1->real^N) (interval(vec 0,vec 1))` SUBST1_TAC THENL
   [REWRITE_TAC[path_image; pathstart; pathfinish; EXTENSION; IN_DIFF; IN_IMAGE;
                IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) MP_TAC) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[OPEN_CLOSED_INTERVAL_1; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(t:real^1) IN interval(vec 0,vec 1)` THEN
      REWRITE_TAC[OPEN_CLOSED_INTERVAL_1; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
      STRIP_TAC THEN CONJ_TAC THENL [EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `arc(h:real^1->real^N)` THEN REWRITE_TAC[arc] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      ASM_MESON_TAC[ENDS_IN_UNIT_INTERVAL]];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN
    UNDISCH_TAC `arc(h:real^1->real^N)` THEN SIMP_TAC[arc; path]]);;

let MOI_S4L_ARC_SAME_ENDS = prove
 (`!h k:real^1->real^N.
     arc h /\ arc k /\ path_image k SUBSET path_image h /\
     {pathstart k,pathfinish k} = {pathstart h,pathfinish h}
     ==> path_image k = path_image h`,
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[GSYM SUBSET_ANTISYM_EQ] THEN
  FIRST_ASSUM(X_CHOOSE_THEN `hi:real^N->real^1` STRIP_ASSUME_TAC o
    MATCH_MP HOMEOMORPHISM_ARC o check (fun th -> concl th = `arc(h:real^1->real^N)`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `connected(IMAGE (hi:real^N->real^1) (path_image (k:real^1->real^N)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `path_image (h:real^1->real^N)` THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
      MATCH_MP_TAC PATH_CONNECTED_PATH_IMAGE THEN ASM_SIMP_TAC[ARC_IMP_PATH]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(pathstart h:real^N) IN path_image k /\ (pathfinish h:real^N) IN path_image k`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^1->real^N` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `k:real^1->real^N` PATHFINISH_IN_PATH_IMAGE) THEN
    UNDISCH_TAC `{pathstart k:real^N,pathfinish k} = {pathstart h,pathfinish h}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interval[vec 0:real^1,vec 1] SUBSET
                IMAGE (hi:real^N->real^1) (path_image (k:real^1->real^N))` ASSUME_TAC THENL
   [UNDISCH_TAC `connected(IMAGE (hi:real^N->real^1) (path_image (k:real^1->real^N)))` THEN
    REWRITE_TAC[GSYM IS_INTERVAL_CONNECTED_1; IS_INTERVAL_1] THEN DISCH_TAC THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `t:real^1` THEN
    REWRITE_TAC[IN_INTERVAL_1; DROP_VEC] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY EXISTS_TAC [`vec 0:real^1`; `vec 1:real^1`] THEN
    ASM_REWRITE_TAC[DROP_VEC; IN_IMAGE] THEN CONJ_TAC THENL
     [EXISTS_TAC `pathstart h:real^N`; EXISTS_TAC `pathfinish h:real^N`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[pathstart; pathfinish] THEN
    CONV_TAC SYM_CONV THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[ENDS_IN_UNIT_INTERVAL];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(hi:real^N->real^1) y IN IMAGE hi (path_image (k:real^1->real^N))` MP_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!s. s SUBSET t /\ (x:real^1) IN s ==> x IN t`) THEN
    EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[IN_IMAGE] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(z:real^N) IN path_image h` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[]]);;

let MOI_S4L_LOOP_PUNCTURED_CONNECTED = prove
 (`!(g:real^1->real^N) r.
     simple_path g /\ pathfinish g = pathstart g /\ r IN path_image g
     ==> connected(path_image g DELETE r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?a. a IN interval[vec 0,vec 1] /\ (g:real^1->real^N) a = r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(r:real^N) IN path_image g` THEN REWRITE_TAC[path_image; IN_IMAGE] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?g':real^1->real^N. simple_path g' /\ path_image g' = path_image g /\
                  g'(vec 0) = r /\ g'(vec 1) = r`
  STRIP_ASSUME_TAC THENL
   [EXISTS_TAC `shiftpath a (g:real^1->real^N)` THEN
    SUBGOAL_THEN `&0 <= drop a /\ drop a <= &1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(a:real^1) IN interval[vec 0,vec 1]` THEN
      REWRITE_TAC[IN_INTERVAL_1; DROP_VEC];
      ALL_TAC] THEN
    ASM_SIMP_TAC[SIMPLE_PATH_SHIFTPATH; PATH_IMAGE_SHIFTPATH] THEN
    MP_TAC(ISPECL [`a:real^1`; `g:real^1->real^N`] PATHSTART_SHIFTPATH) THEN
    MP_TAC(ISPECL [`a:real^1`; `g:real^1->real^N`] PATHFINISH_SHIFTPATH) THEN
    RULE_ASSUM_TAC(REWRITE_RULE[pathstart; pathfinish]) THEN
    ASM_REWRITE_TAC[pathstart; pathfinish] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image g DELETE (r:real^N) = IMAGE (g':real^1->real^N) (interval(vec 0,vec 1))`
  SUBST1_TAC THENL
   [UNDISCH_TAC `path_image (g':real^1->real^N) = path_image g` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[path_image; EXTENSION; IN_DELETE; IN_IMAGE] THEN
    X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[OPEN_CLOSED_INTERVAL_1; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[];
      DISCH_THEN(X_CHOOSE_THEN `t:real^1` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(t:real^1) IN interval(vec 0,vec 1)` THEN
      REWRITE_TAC[OPEN_CLOSED_INTERVAL_1; IN_DIFF; IN_INSERT; NOT_IN_EMPTY] THEN
      STRIP_TAC THEN CONJ_TAC THENL [EXISTS_TAC `t:real^1` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `simple_path(g':real^1->real^N)` THEN REWRITE_TAC[simple_path] THEN
      DISCH_THEN(MP_TAC o SPECL [`t:real^1`; `vec 0:real^1`] o CONJUNCT2) THEN
      ASM_REWRITE_TAC[ENDS_IN_UNIT_INTERVAL] THEN ASM_MESON_TAC[]];
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN REWRITE_TAC[CONNECTED_INTERVAL] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `interval[vec 0:real^1,vec 1]` THEN
    REWRITE_TAC[INTERVAL_OPEN_SUBSET_CLOSED] THEN
    UNDISCH_TAC `simple_path(g':real^1->real^N)` THEN SIMP_TAC[simple_path; path]]);;

let MOI_S4L_CELL1_PL_ARC = prove
 (`!a aa:real^N->bool.
     pl_cell_with_boundary 1 a aa
     ==> ?h. arc h /\ pl_map_on (interval[vec 0,vec 1]) h /\ path_image h = a /\
             aa = {pathstart h,pathfinish h}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_PL2_SIMPLEX_1]) THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` (X_CHOOSE_THEN `x1:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  EXISTS_TAC `(f:real^N->real^N) o linepath(x0,x1)` THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC ARC_CONTINUOUS_IMAGE THEN ASM_SIMP_TAC[ARC_LINEPATH; PATH_IMAGE_LINEPATH] THEN
    ASM_MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `segment[x0:real^N,x1]` THEN
    ASM_SIMP_TAC[MOI_PL2_PL_LINEPATH; MOI_PL2_LOCALLY_POLYHEDRAL_INTERVAL] THEN
    REWRITE_TAC[GSYM path_image; PATH_IMAGE_LINEPATH; SUBSET_REFL];
    ASM_REWRITE_TAC[PATH_IMAGE_COMPOSE; PATH_IMAGE_LINEPATH];
    ASM_SIMP_TAC[MOI_S4O_RF_SEGMENT; PATHSTART_COMPOSE; PATHFINISH_COMPOSE;
                 PATHSTART_LINEPATH; PATHFINISH_LINEPATH] THEN
    REWRITE_TAC[IMAGE_CLAUSES]]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 10 (p.243): trace circles meet the rims in at least two points, the *)
(* clean side of a returning arc, innermost returning arcs.                   *)
(* ------------------------------------------------------------------------- *)

(* A trace circle never meets the rims in exactly one point (two-sidedness). *)
let MOI_S4L_TRACE_RIMS_NOT_SING = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s j r.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ s IN moi_s34_simp kk (&2) /\
     j IN components (moi_s34_trace tt kk f1 (cb s)) /\
     j INTER moi_s34_rims tt kk f1 = {r}
     ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(r:real^3) IN j /\ r IN moi_s34_rims tt kk (f1:real^N->real^3)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(j:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3) = {r}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(j:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s)` ASSUME_TAC THENL
   [ASM_MESON_TAC[IN_COMPONENTS_SUBSET]; ALL_TAC] THEN
  UNDISCH_TAC `(r:real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)` THEN
  REWRITE_TAC[moi_s34_rims; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(g:real^N->bool) IN kk` ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^N->bool) IN moi_s34_simp kk (&1)` THEN
    SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(r:real^3) IN IMAGE (f1:real^N->real^3)
      (moi_s34_vb tt kk x INTER moi_s34_vb tt kk z INTER moi_s34_bd tt kk) /\
    r IN IMAGE f1 (moi_s34_vb tt kk z INTER moi_s34_vb tt kk x INTER moi_s34_bd tt kk) /\
    segment[x:real^N,z] IN kk /\ segment[z,x] IN kk`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(r:real^3) IN q` THEN ASM_REWRITE_TAC[INTER_ASSOC] THEN
    REWRITE_TAC[SET_RULE `(a:real^N->bool) INTER b INTER c = b INTER a INTER c`] THEN
    SIMP_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `(g:real^N->bool) IN kk` THEN ASM_REWRITE_TAC[] THEN
    MESON_TAC[SEGMENT_SYM];
    ALL_TAC] THEN
  (* the two sides at r *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `(cb:(real^N->bool)->real^3->bool) s`; `x:real^N`; `z:real^N`; `r:real^3`;
                 `&1`] MOI_S4L_CROSS_SIDES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_01; IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k1:real^3->bool` (X_CHOOSE_THEN `y1:real^3`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `s:real^N->bool`;
                 `(cb:(real^N->bool)->real^3->bool) s`; `z:real^N`; `x:real^N`; `r:real^3`;
                 `&1`] MOI_S4L_CROSS_SIDES) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[REAL_LT_01; IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k2:real^3->bool` (X_CHOOSE_THEN `y2:real^3`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(k1:real^3->bool) SUBSET j /\ (k2:real^3->bool) SUBSET j`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s)` THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `r:real^3` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* j minus r is connected *)
  SUBGOAL_THEN `connected((j:real^3->bool) DELETE r)` ASSUME_TAC THENL
   [SUBGOAL_THEN `pl_sphere 1 (j:real^3->bool)` MP_TAC THENL
     [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && moi_s4l_has "pl_sphere" th)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `gam:real^1->real^3` STRIP_ASSUME_TAC o
      MATCH_MP MOI_S4O_CIRCLE_LOOP) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `j:real^3->bool`)) THEN
    MATCH_MP_TAC MOI_S4L_LOOP_PUNCTURED_CONNECTED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the part of j DELETE r in C_x is clopen *)
  UNDISCH_TAC `connected((j:real^3->bool) DELETE r)` THEN REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC
    `((j:real^3->bool) DELETE r) INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x)`) THEN
  SUBGOAL_THEN
   `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x INTER moi_s34_bd tt kk) SUBSET
    IMAGE f1 (moi_s34_vb tt kk x) /\
    IMAGE (f1:real^N->real^3)
      (moi_s34_vb tt kk x INTER moi_s34_vb tt kk z INTER moi_s34_bd tt kk) SUBSET
    IMAGE f1 (moi_s34_vb tt kk x) /\
    IMAGE (f1:real^N->real^3)
      (moi_s34_vb tt kk x INTER moi_s34_vb tt kk z INTER moi_s34_bd tt kk) SUBSET
    IMAGE f1 (moi_s34_vb tt kk z)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[NOT_IMP; DE_MORGAN_THM] THEN REPEAT CONJ_TAC THENL
   [ONCE_REWRITE_TAC[OPEN_IN_SUBOPEN] THEN X_GEN_TAC `y:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_DELETE] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk x INTER moi_s34_bd tt kk) /\
                  ~(y IN moi_s34_rims tt kk f1)` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                       `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                       `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_GRAPH_TUBE) THEN
        SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x INTER moi_s34_bd tt kk) =
                      IMAGE f1 (moi_s34_vb tt kk x) INTER IMAGE f1 (moi_s34_bd tt kk)`
        SUBST1_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
            moi_s4l_has "moi_s34_nb" th &&
            not (moi_s4l_has "closed_segment" th))) THEN
          CONJ_TAC THENL
           [FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
              is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
              moi_s4l_has "pl_cell_with_boundary" th && moi_s4l_has "moi_s34_nb" th)) THEN
            ANTS_TAC THENL [FIRST_ASSUM ACCEPT_TAC; SIMP_TAC[]];
            FIRST_ASSUM ACCEPT_TAC];
          ALL_TAC] THEN
        REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
        MATCH_MP_TAC(SET_RULE `!j t. (y:real^3) IN j /\ j SUBSET t /\ t SUBSET m
                               ==> y IN m`) THEN
        MAP_EVERY EXISTS_TAC
         [`j:real^3->bool`; `moi_s34_trace tt kk (f1:real^N->real^3)
                               ((cb:(real^N->bool)->real^3->bool) s)`] THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC(SET_RULE `!j. (y:real^3) IN j /\ ~(y = r) /\ j INTER rr = {r}
                               ==> ~(y IN rr)`) THEN
        EXISTS_TAC `j:real^3->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `x:real^N`; `y:real^3`]
      MOI_S4L_LOCAL_AV) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `w:real^N` THEN STRIP_TAC THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `x:real^N`; `w:real^N`; `y:real^3`]
        MOI_S4L_AV_NO_OTHER) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `oo:real^3->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `((j:real^3->bool) DELETE r) INTER oo` THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_INTER; IN_DELETE] THEN
    MATCH_MP_TAC(SET_RULE
     `!t m a. j SUBSET t /\ t SUBSET m /\ m INTER oo SUBSET a /\ a SUBSET cx
              ==> ((j:real^3->bool) DELETE r) INTER oo SUBSET (j DELETE r) INTER cx`) THEN
    MAP_EVERY EXISTS_TAC
     [`moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x INTER moi_s34_bd tt kk)`] THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC CLOSED_IN_CLOSED_INTER THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    ASM_MESON_TAC[MOI_S4L_AV_BASIC];
    MATCH_MP_TAC(SET_RULE
     `!y2 k ax cz. k SUBSET j /\ (y2:real^3) IN k /\ y2 IN ax /\ ax SUBSET cx /\
                   ~(y2 IN cz) /\ r IN cz ==> ~((j DELETE r) INTER cx = {})`) THEN
    MAP_EVERY EXISTS_TAC
     [`y2:real^3`; `k2:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x INTER moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk z)`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC(SET_RULE
     `!y1 k. k SUBSET j /\ (y1:real^3) IN k /\ ~(y1 IN cx) /\ r IN cx
             ==> ~((j DELETE r) INTER cx = j DELETE r)`) THEN
    MAP_EVERY EXISTS_TAC [`y1:real^3`; `k1:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 10: the clean side of a returning arc.                              *)
(* ------------------------------------------------------------------------- *)

let MOI_S4L_L10_DISJ = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car v w x a.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     ~(w = v) /\ segment[v,w] IN kk /\ ~(x = v) /\ ~(x = w) /\ segment[v,x] IN kk /\
     a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
     a INTER moi_s34_rims tt kk f1 SUBSET
     IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)
     ==> DISJOINT a (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x)) /\
         DISJOINT (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w))
                  (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `DISJOINT (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w))
                  (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x))` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      moi_s4l_has "INTER" th)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM((fun th -> MP_TAC(SPEC `x:real^N` th) THEN MP_TAC(SPEC `w:real^N` th)) o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      moi_s4l_has "pl_cell_with_boundary" th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
    (STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS) ASSUME_TAC)) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `f1:real^N->real^3`; `v:real^N`; `x:real^N`] MOI_S4L_RIM_IN_RIMS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `!av rvx rr rvw dvw. a SUBSET av /\ dvx INTER av = rvx /\ rvx SUBSET rr /\
                         a INTER rr SUBSET rvw /\ rvw SUBSET dvw /\ DISJOINT dvw dvx
                         ==> DISJOINT (a:real^3->bool) dvx`) THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3)
       (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x INTER moi_s34_bd tt kk)`;
    `moi_s34_rims tt kk (f1:real^N->real^3)`;
    `IMAGE (f1:real^N->real^3)
       (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`;
    `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`] THEN
  ASM_REWRITE_TAC[]);;

(* Returning-arc candidates at v for the edge vw: a PL arc ha of the trace   *)
(* of s in A_v with ends on rim_vw and no other rim point, a PL arc hg of    *)
(* rim_vw with the same ends, and a clean side e of the circle ha UNION hg.  *)
let moi_s4l_rcand = new_definition
 `moi_s4l_rcand (tt:(real^N->bool)->bool) kk (f1:real^N->real^3) cb v w s
                (ha:real^1->real^3) (hg:real^1->real^3) e e' <=>
    s IN moi_s34_simp kk (&2) /\ ~(w = v) /\ segment[v,w] IN kk /\
    arc ha /\ pl_map_on (interval[vec 0,vec 1]) ha /\
    arc hg /\ pl_map_on (interval[vec 0,vec 1]) hg /\
    pathstart hg = pathstart ha /\ pathfinish hg = pathfinish ha /\
    path_image ha SUBSET moi_s34_trace tt kk f1 (cb s) /\
    path_image ha SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
    path_image ha INTER moi_s34_rims tt kk f1 = {pathstart ha,pathfinish ha} /\
    path_image hg SUBSET
    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
    path_image ha INTER path_image hg = {pathstart ha,pathfinish ha} /\
    pl_cell_with_boundary 2 e (path_image ha UNION path_image hg) /\
    pl_cell_with_boundary 2 e' (path_image ha UNION path_image hg) /\
    closed e /\ closed e' /\
    e UNION e' = frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\
    e INTER e' = path_image ha UNION path_image hg /\
    e SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
    e INTER IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) = path_image hg /\
    (!x. ~(x = v) /\ ~(x = w) /\ segment[v,x] IN kk
         ==> DISJOINT e (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x))) /\
    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) SUBSET e'`;;

(* A side u of ha UNION hg that misses the splitting disks at v other than *)
(* D_vw, whose other side contains D_vw, is a returning-arc candidate.     *)
let MOI_S4L_L10_SIDE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb v w s ha hg u u'.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     s IN moi_s34_simp kk (&2) /\ ~(w = v) /\ segment[v,w] IN kk /\
     arc ha /\ pl_map_on (interval[vec 0,vec 1]) ha /\
     arc hg /\ pl_map_on (interval[vec 0,vec 1]) hg /\
     pathstart hg = pathstart ha /\ pathfinish hg = pathfinish ha /\
     path_image ha SUBSET moi_s34_trace tt kk f1 (cb s) /\
     path_image ha SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
     path_image ha INTER moi_s34_rims tt kk f1 = {pathstart ha,pathfinish ha} /\
     path_image hg SUBSET
     IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
     path_image ha INTER path_image hg = {pathstart ha,pathfinish ha} /\
     pl_cell_with_boundary 2 u (path_image ha UNION path_image hg) /\
     pl_cell_with_boundary 2 u' (path_image ha UNION path_image hg) /\
     u UNION u' = frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\
     u INTER u' = path_image ha UNION path_image hg /\
     IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) SUBSET u' /\
     (!x. ~(x = v) /\ ~(x = w) /\ segment[v,x] IN kk
          ==> IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x) SUBSET u')
     ==> moi_s4l_rcand tt kk f1 cb v w s ha hg u u'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s4l_rcand] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN
   `!x. ~(x = v) /\ ~(x = w) /\ segment[v:real^N,x] IN kk
        ==> DISJOINT (path_image ha UNION path_image hg)
                     (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x))`
  (LABEL_TAC "cdis") THENL
   [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `v:real^N`; `w:real^N`; `x:real^N`;
                   `path_image (ha:real^1->real^3)`] MOI_S4L_L10_DISJ) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `path_image (hg:real^1->real^3)` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `hg:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
      MP_TAC(ISPEC `hg:real^1->real^3` PATHFINISH_IN_PATH_IMAGE) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!dvw. DISJOINT (a:real^3->bool) d /\ b SUBSET dvw /\
                                 DISJOINT dvw d ==> DISJOINT (a UNION b) d`) THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x. ~(x = v) /\ ~(x = w) /\ segment[v:real^N,x] IN kk
                    ==> DISJOINT u (IMAGE (f1:real^N->real^3)
                          (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x))`
  (LABEL_TAC "udis") THENL
   [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    USE_THEN "cdis" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      not(moi_s4l_has "pl_cell_with_boundary" th) && moi_s4l_has "SUBSET" th &&
      not(moi_s4l_has "DISJOINT" th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!u' c. u INTER u' = c /\ d SUBSET u' /\ DISJOINT c d
                           ==> DISJOINT (u:real^3->bool) d`) THEN
    MAP_EVERY EXISTS_TAC [`u':real^3->bool`;
                          `path_image (ha:real^1->real^3) UNION path_image hg`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `u INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) =
    path_image (hg:real^1->real^3)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!rvw av a u'. u INTER u' = a UNION b /\ d SUBSET u' /\ b SUBSET u /\ b SUBSET d /\
                    a SUBSET av /\ d INTER av = rvw /\ a INTER rvw SUBSET b
                    ==> (u:real^3->bool) INTER d = b`) THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
      `path_image (ha:real^1->real^3)`; `u':real^3->bool`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MP_TAC(ISPECL [`2`; `u:real^3->bool`; `path_image (ha:real^1->real^3) UNION
                       path_image (hg:real^1->real^3)`] MOI_S4L_PL_CELL_FACTS) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3)
                    (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        moi_s4l_has "pl_cell_with_boundary" th)) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MATCH_MP_TAC(SET_RULE `!rr e. a INTER rr = e /\ e SUBSET b /\ r SUBSET rr
                             ==> (a:real^3->bool) INTER r SUBSET b`) THEN
      MAP_EVERY EXISTS_TAC [`moi_s34_rims tt kk (f1:real^N->real^3)`;
                            `{pathstart ha:real^3,pathfinish ha}`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `hg:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
        MP_TAC(ISPEC `hg:real^1->real^3` PATHFINISH_IN_PATH_IMAGE) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        MATCH_MP_TAC MOI_S4L_RIM_IN_RIMS THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `closed(u:real^3->bool) /\ closed(u':real^3->bool)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `u:real^3->bool`; `path_image (ha:real^1->real^3) UNION
                     path_image (hg:real^1->real^3)`] MOI_S4L_PL_CELL_FACTS) THEN
    MP_TAC(ISPECL [`2`; `u':real^3->bool`; `path_image (ha:real^1->real^3) UNION
                     path_image (hg:real^1->real^3)`] MOI_S4L_PL_CELL_FACTS) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  (* u lies in A_v *)
  SUBGOAL_THEN `(u:real^3->bool) SUBSET frontier (IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v))` MP_TAC THENL
   [UNDISCH_TAC `(u:real^3->bool) UNION u' = frontier (IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v))` THEN SET_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
    is_eq(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier")) (lhs(concl th)))) THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN MP_TAC) THENL [SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  ASM_CASES_TAC `x:real^N = w` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!t d b r. (y:real^3) IN t /\ t = d /\ y IN u /\ u INTER d = b /\ b SUBSET r /\
                r SUBSET av ==> y IN av`) THEN
    MAP_EVERY EXISTS_TAC
     [`t:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`;
      `path_image (hg:real^1->real^3)`;
      `IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    USE_THEN "udis" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!t d. (y:real^3) IN t /\ t = d /\ y IN u /\ DISJOINT u d ==> y IN av`) THEN
    MAP_EVERY EXISTS_TAC
     [`t:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x)`] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S4L_SPLIT_ORIENT = prove
 (`!sg c d1 d2 x:real^3->bool.
     pl_cell_with_boundary 2 d1 c /\ pl_cell_with_boundary 2 d2 c /\
     d1 UNION d2 = sg /\ d1 INTER d2 = c /\
     connected x /\ x SUBSET sg /\ DISJOINT x c
     ==> ?u u'. pl_cell_with_boundary 2 u c /\ pl_cell_with_boundary 2 u' c /\
                u UNION u' = sg /\ u INTER u' = c /\ x SUBSET u'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`x:real^3->bool`; `d1:real^3->bool`; `d2:real^3->bool`; `c:real^3->bool`]
    MOI_SFR_CONNECTED_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`2`; `d1:real^3->bool`; `c:real^3->bool`] MOI_S4L_PL_CELL_FACTS) THEN
    MP_TAC(ISPECL [`2`; `d2:real^3->bool`; `c:real^3->bool`] MOI_S4L_PL_CELL_FACTS) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN REPEAT DISCH_TAC THEN
    UNDISCH_TAC `DISJOINT (x:real^3->bool) c` THEN SET_TAC[];
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`d2:real^3->bool`; `d1:real^3->bool`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]];
      MAP_EVERY EXISTS_TAC [`d1:real^3->bool`; `d2:real^3->bool`] THEN
      ASM_REWRITE_TAC[]]]);;

let MOI_S4L_L10_THETA = prove
 (`!sg a g1 g2 e1 e1' e2 e2' (p:real^3) q z.
     closed e1 /\ closed e2 /\ closed e2' /\
     e1 UNION e1' = sg /\ e1 INTER e1' = a UNION g1 /\
     e2 UNION e2' = sg /\ e2 INTER e2' = a UNION g2 /\
     connected (e1 DIFF (a UNION g1)) /\ e1 SUBSET closure (e1 DIFF (a UNION g1)) /\
     g2 SUBSET e1' /\ g1 SUBSET e2' /\
     a INTER g1 = {p,q} /\ g1 INTER g2 = {p,q} /\
     z IN g1 /\ ~(z = p) /\ ~(z = q)
     ==> e1 DIFF (a UNION g1) SUBSET e2' DIFF (a UNION g2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`e1 DIFF (a UNION g1):real^3->bool`; `e2:real^3->bool`; `e2':real^3->bool`;
                 `a UNION g2:real^3->bool`] MOI_SFR_CONNECTED_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(e1:real^3->bool) UNION e1' = sg`; `(e1:real^3->bool) INTER e1' = a UNION g1`;
      `(e2:real^3->bool) UNION e2' = sg`; `(g2:real^3->bool) SUBSET e1'`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `(e1:real^3->bool) SUBSET e2` ASSUME_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `closure((e1:real^3->bool) DIFF (a UNION g1))` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(e1:real^3->bool) SUBSET e2`; `(e1:real^3->bool) INTER e1' = a UNION g1`;
      `(e2:real^3->bool) INTER e2' = a UNION g2`; `(g1:real^3->bool) SUBSET e2'`;
      `(a:real^3->bool) INTER g1 = {p,q}`; `(g1:real^3->bool) INTER g2 = {p,q}`;
      `(z:real^3) IN g1`; `~((z:real^3) = p)`; `~((z:real^3) = q)`] THEN
    SET_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`(e1:real^3->bool) DIFF (a UNION g1) SUBSET e2'`;
      `(e1:real^3->bool) UNION e1' = sg`; `(e1:real^3->bool) INTER e1' = a UNION g1`;
      `(g2:real^3->bool) SUBSET e1'`] THEN
    SET_TAC[]]);;

(* Lemma 10, first half: a returning arc ha (ends on rim_vw, no other rim    *)
(* point) has a clean side: a returning-arc candidate.                      *)
let MOI_S4L_L10_CLEAN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb s v w ha.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\
     s IN moi_s34_simp kk (&2) /\ {v} IN kk /\ ~(w = v) /\ segment[v,w] IN kk /\
     arc ha /\ pl_map_on (interval[vec 0,vec 1]) ha /\
     path_image ha SUBSET moi_s34_trace tt kk f1 (cb s) /\
     path_image ha SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
     path_image ha INTER moi_s34_rims tt kk f1 = {pathstart ha,pathfinish ha} /\
     pathstart ha IN
     IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
     pathfinish ha IN
     IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)
     ==> ?hg e e'. moi_s4l_rcand tt kk f1 cb v w s ha hg e e'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
    moi_s4l_has "pl_cell_with_boundary" th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
    moi_s4l_has "pl_cell_with_boundary" th &&
    not (is_forall(concl th)))) THEN
  SUBGOAL_THEN `pl_sphere 1 (IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4O_CELL_SPHERE THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)` THEN
    CONV_TAC NUM_REDUCE_CONV THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `gam:real^1->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4O_CIRCLE_LOOP) THEN
  SUBGOAL_THEN `~(pathstart ha:real^3 = pathfinish ha)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ARC_DISTINCT_ENDS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`gam:real^1->real^3`; `pathstart ha:real^3`; `pathfinish ha:real^3`]
    MOI_SFR_LOOP_SPLIT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a1:real^1->real^3` (X_CHOOSE_THEN `a2:real^1->real^3`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `p = pathstart (ha:real^1->real^3)` THEN
  ABBREV_TAC `q = pathfinish (ha:real^1->real^3)` THEN
  SUBGOAL_THEN
   `IMAGE (f1:real^N->real^3)
      (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) SUBSET
    moi_s34_rims tt kk f1 /\
    (!x. ~(x = v) /\ segment[v:real^N,x] IN kk
         ==> IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x) SUBSET
             frontier (IMAGE f1 (moi_s34_vb tt kk v))) /\
    IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
    frontier (IMAGE f1 (moi_s34_vb tt kk v)) /\
    IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) SUBSET
    IMAGE f1 (moi_s34_vb tt kk w)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4L_RIM_IN_RIMS THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_eq(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier"))
          (lhs(concl th)))) THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN DISJ2_TAC THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x)` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
        is_eq(concl th) &&
        can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier"))
          (lhs(concl th)))) THEN
      REWRITE_TAC[SUBSET_UNION];
      MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier")) (lhs(concl th)))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN s` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S4L_TRACE_AT_V THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `h:real^N->real^3`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
      `(cb:(real^N->bool)->real^3->bool) s`; `{p:real^3}`] THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `ha:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `path_image (ha:real^1->real^3) SUBSET
                   moi_s34_trace tt kk (f1:real^N->real^3)
                     ((cb:(real^N->bool)->real^3->bool) s)` THEN
      SET_TAC[];
      MATCH_MP_TAC(SET_RULE `!r d. (p:real^3) IN r /\ r SUBSET d /\ d SUBSET c ==> p IN c`) THEN
      MAP_EVERY EXISTS_TAC
       [`IMAGE (f1:real^N->real^3)
           (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`;
        `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `path_image (a1:real^1->real^3) SUBSET
    IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
    path_image (a2:real^1->real^3) SUBSET
    IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
    path_image (ha:real^1->real^3) INTER path_image a1 = {p,q} /\
    path_image (ha:real^1->real^3) INTER path_image a2 = {p,q}`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!gam rims. a1 UNION a2 = gam /\ gam = rim /\ ha INTER rims = {p,q} /\
                 rim SUBSET rims /\ (p:real^3) IN ha /\ q IN ha /\ p IN a1 /\ q IN a1 /\
                 p IN a2 /\ q IN a2
                 ==> a1 SUBSET rim /\ a2 SUBSET rim /\ ha INTER a1 = {p,q} /\
                     ha INTER a2 = {p,q}`) THEN
    MAP_EVERY EXISTS_TAC [`path_image (gam:real^1->real^3)`;
                          `moi_s34_rims tt kk (f1:real^N->real^3)`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
     [MP_TAC(ISPEC `ha:real^1->real^3` PATHSTART_IN_PATH_IMAGE);
      MP_TAC(ISPEC `ha:real^1->real^3` PATHFINISH_IN_PATH_IMAGE);
      MP_TAC(ISPEC `a1:real^1->real^3` PATHSTART_IN_PATH_IMAGE);
      MP_TAC(ISPEC `a1:real^1->real^3` PATHFINISH_IN_PATH_IMAGE);
      MP_TAC(ISPEC `a2:real^1->real^3` PATHSTART_IN_PATH_IMAGE);
      MP_TAC(ISPEC `a2:real^1->real^3` PATHFINISH_IN_PATH_IMAGE)] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e e'. pl_cell_with_boundary 2 e (path_image (ha:real^1->real^3) UNION path_image (a1:real^1->real^3)) /\
           pl_cell_with_boundary 2 e' (path_image ha UNION path_image (a1:real^1->real^3)) /\
           e UNION e' = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) /\
           e INTER e' = path_image ha UNION path_image (a1:real^1->real^3) /\
           IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) SUBSET e' /\
           closed e /\ closed e' /\
           connected (e DIFF (path_image ha UNION path_image (a1:real^1->real^3))) /\
           e SUBSET closure (e DIFF (path_image ha UNION path_image (a1:real^1->real^3)))`
  (X_CHOOSE_THEN `e1:real^3->bool` (X_CHOOSE_THEN `e1':real^3->bool` STRIP_ASSUME_TAC)) THENL
   [MP_TAC(ISPECL [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
                   `path_image (ha:real^1->real^3) UNION path_image (a1:real^1->real^3)`] SPHERE_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SLV_ARCS_SPHERE THEN ASM_REWRITE_TAC[DIMINDEX_3; ARITH];
        MATCH_MP_TAC(SET_RULE `!av r d. ha SUBSET av /\ av SUBSET sg /\ b SUBSET r /\
                                        r SUBSET d /\ d SUBSET sg
                                        ==> (ha:real^3->bool) UNION b SUBSET sg`) THEN
        MAP_EVERY EXISTS_TAC
         [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
          `IMAGE (f1:real^N->real^3)
             (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`;
          `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`] THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
                   `path_image (ha:real^1->real^3) UNION path_image (a1:real^1->real^3)`;
                   `d1:real^3->bool`; `d2:real^3->bool`;
                   `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) DIFF
                    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                              moi_s34_bd tt kk)`] MOI_S4L_SPLIT_ORIENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `d SUBSET sg ==> d DIFF r SUBSET (sg:real^3->bool)`) THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC(SET_RULE `!av. ha SUBSET av /\ d INTER av = r /\ b SUBSET r
                               ==> DISJOINT (d DIFF r) ((ha:real^3->bool) UNION b)`) THEN
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `u':real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `u':real^3->bool`] THEN
    MP_TAC(ISPECL [`2`; `u:real^3->bool`; `path_image (ha:real^1->real^3) UNION path_image (a1:real^1->real^3)`]
      MOI_S4L_PL_CELL_FACTS) THEN
    MP_TAC(ISPECL [`2`; `u':real^3->bool`; `path_image (ha:real^1->real^3) UNION path_image (a1:real^1->real^3)`]
      MOI_S4L_PL_CELL_FACTS) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
      moi_s4l_has "pl_cell_with_boundary" th &&
      rand(rator(concl th)) = `u:real^3->bool`)) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)
                  DIFF IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                                 moi_s34_bd tt kk))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?e e'. pl_cell_with_boundary 2 e (path_image (ha:real^1->real^3) UNION path_image (a2:real^1->real^3)) /\
           pl_cell_with_boundary 2 e' (path_image ha UNION path_image (a2:real^1->real^3)) /\
           e UNION e' = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) /\
           e INTER e' = path_image ha UNION path_image (a2:real^1->real^3) /\
           IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) SUBSET e' /\
           closed e /\ closed e' /\
           connected (e DIFF (path_image ha UNION path_image (a2:real^1->real^3))) /\
           e SUBSET closure (e DIFF (path_image ha UNION path_image (a2:real^1->real^3)))`
  (X_CHOOSE_THEN `e2:real^3->bool` (X_CHOOSE_THEN `e2':real^3->bool` STRIP_ASSUME_TAC)) THENL
   [MP_TAC(ISPECL [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
                   `path_image (ha:real^1->real^3) UNION path_image (a2:real^1->real^3)`] SPHERE_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SLV_ARCS_SPHERE THEN ASM_REWRITE_TAC[DIMINDEX_3; ARITH];
        MATCH_MP_TAC(SET_RULE `!av r d. ha SUBSET av /\ av SUBSET sg /\ b SUBSET r /\
                                        r SUBSET d /\ d SUBSET sg
                                        ==> (ha:real^3->bool) UNION b SUBSET sg`) THEN
        MAP_EVERY EXISTS_TAC
         [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
          `IMAGE (f1:real^N->real^3)
             (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`;
          `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`] THEN
        ASM_SIMP_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
                   `path_image (ha:real^1->real^3) UNION path_image (a2:real^1->real^3)`;
                   `d1:real^3->bool`; `d2:real^3->bool`;
                   `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) DIFF
                    IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                              moi_s34_bd tt kk)`] MOI_S4L_SPLIT_ORIENT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE `d SUBSET sg ==> d DIFF r SUBSET (sg:real^3->bool)`) THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC(SET_RULE `!av. ha SUBSET av /\ d INTER av = r /\ b SUBSET r
                               ==> DISJOINT (d DIFF r) ((ha:real^3->bool) UNION b)`) THEN
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `u':real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `u':real^3->bool`] THEN
    MP_TAC(ISPECL [`2`; `u:real^3->bool`; `path_image (ha:real^1->real^3) UNION path_image (a2:real^1->real^3)`]
      MOI_S4L_PL_CELL_FACTS) THEN
    MP_TAC(ISPECL [`2`; `u':real^3->bool`; `path_image (ha:real^1->real^3) UNION path_image (a2:real^1->real^3)`]
      MOI_S4L_PL_CELL_FACTS) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
      moi_s4l_has "pl_cell_with_boundary" th &&
      rand(rator(concl th)) = `u:real^3->bool`)) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN REPEAT DISCH_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)
                  DIFF IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                                 moi_s34_bd tt kk))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  (* the other splitting disks at v avoid both circles *)
  SUBGOAL_THEN
   `!x. ~(x = v) /\ ~(x = w) /\ segment[v:real^N,x] IN kk
        ==> DISJOINT (path_image (ha:real^1->real^3))
              (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x)) /\
            DISJOINT (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w))
              (IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x))`
  (LABEL_TAC "odis") THENL
   [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S4L_L10_DISJ THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    UNDISCH_TAC `pathstart (ha:real^1->real^3) IN
      IMAGE (f1:real^N->real^3)
        (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    UNDISCH_TAC `pathfinish (ha:real^1->real^3) IN
      IMAGE (f1:real^N->real^3)
        (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x b. ~(x = v) /\ ~(x = w) /\ segment[v:real^N,x] IN kk /\ (b = a1 \/ b = a2)
          ==> DISJOINT (path_image (ha:real^1->real^3) UNION path_image b)
                (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x))`
  (LABEL_TAC "cdis") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    USE_THEN "odis" (MP_TAC o SPEC `x:real^N`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(SET_RULE `!r d. DISJOINT a dx /\ b SUBSET r /\ r SUBSET d /\ DISJOINT d dx
                           ==> DISJOINT ((a:real^3->bool) UNION b) dx`) THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* splitting disks other than D_vw lie on one side of the first circle *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `e1:real^3->bool`; `e1':real^3->bool`;
                 `path_image (ha:real^1->real^3) UNION path_image (a1:real^1->real^3)`]
    MOI_S4L_SIDES_AGREE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      USE_THEN "cdis" (MP_TAC o SPECL [`x:real^N`; `a1:real^1->real^3`]) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`; `z:real^3->bool`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `v:real^N`; `a:real^N`; `b:real^N`] MOI_S4L_LINK_TRI) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `~((w:real^N) IN convex hull {v,a,b})` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `{x | x IN convex hull {v:real^N,a,b} /\ {x} IN kk} = {v,a,b}` THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(convex hull {v:real^N,a,b} = s)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((w:real^N) IN convex hull {v,a,b})` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`; `convex hull {v:real^N,a,b}`] MOI_S4L_TRACES_DISJ) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `convex hull {v:real^N,a,b}`] MOI_S4L_TRACE_COMP_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    SUBGOAL_THEN `DISJOINT ((cb:(real^N->bool)->real^3->bool) (convex hull {v,a,b}))
                    (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w))` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_s34_fb1 tt kk h (f1:real^N->real^3) car (convex hull {v:real^N,a,b})
                    ((cb:(real^N->bool)->real^3->bool) (convex hull {v,a,b}))` THEN
      REWRITE_TAC[moi_s34_fb1] THEN STRIP_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "odis" (MP_TAC o SPEC `a:real^N`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    USE_THEN "odis" (MP_TAC o SPEC `b:real^N`) THEN
    (ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC]) THEN
    MATCH_MP_TAC(SET_RULE
     `!t ts ct av rva rvb cw dva dvb dvw rw.
        z SUBSET (t INTER av) UNION rva UNION rvb /\ ha SUBSET ts /\ ts INTER t = {} /\
        t SUBSET ct /\ DISJOINT ct cw /\ a1 SUBSET rw /\ rw SUBSET dvw /\ dvw SUBSET cw /\
        rva SUBSET dva /\ rvb SUBSET dvb /\ DISJOINT ha dva /\ DISJOINT ha dvb /\
        DISJOINT dvw dva /\ DISJOINT dvw dvb
        ==> DISJOINT (z:real^3->bool) (ha UNION a1)`) THEN
    MAP_EVERY EXISTS_TAC
     [`moi_s34_trace tt kk (f1:real^N->real^3)
         ((cb:(real^N->bool)->real^3->bool) (convex hull {v:real^N,a,b}))`;
      `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`;
      `(cb:(real^N->bool)->real^3->bool) (convex hull {v:real^N,a,b})`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a INTER moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b INTER moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk w)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk a)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk b)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`;
      `IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`] THEN
    ASM_REWRITE_TAC[] THEN
    CONJ_TAC THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    DISCH_THEN(LABEL_TAC "agree")] THEN
  SUBGOAL_THEN
   `!b. b = a1 \/ b = a2
        ==> path_image (b:real^1->real^3) SUBSET
            IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`
  (LABEL_TAC "bsub") THENL
   [GEN_TAC THEN DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?x:real^N. ~(x = v) /\ ~(x = w) /\ segment[v,x] IN kk /\
               IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x)
               SUBSET e1` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPEC `a1:real^1->real^3` MOI_SFR_ARC_MIDPOINT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
                   `path_image (ha:real^1->real^3)`; `path_image (a1:real^1->real^3)`;
                   `path_image (a2:real^1->real^3)`; `e1:real^3->bool`; `e1':real^3->bool`;
                   `e2:real^3->bool`; `e2':real^3->bool`; `p:real^3`; `q:real^3`; `z:real^3`]
      MOI_S4L_L10_THETA) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "bsub" MATCH_MP_TAC THEN REWRITE_TAC[];
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "bsub" MATCH_MP_TAC THEN REWRITE_TAC[];
        UNDISCH_TAC `~((z:real^3) = pathstart a1)` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `~((z:real^3) = pathfinish a1)` THEN ASM_REWRITE_TAC[]];
      DISCH_TAC] THEN
    MAP_EVERY EXISTS_TAC [`a2:real^1->real^3`; `e2:real^3->bool`; `e2':real^3->bool`] THEN
    MATCH_MP_TAC MOI_S4L_L10_SIDE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    USE_THEN "agree" (MP_TAC o SPECL [`x:real^N`; `x0:real^N`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[] THEN DISCH_TAC] THEN
    USE_THEN "cdis" (MP_TAC o SPECL [`x:real^N`; `a1:real^1->real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC(SET_RULE
     `!c e2. d SUBSET e1 /\ DISJOINT c d /\ e1 DIFF c SUBSET e2' DIFF e2
             ==> (d:real^3->bool) SUBSET e2'`) THEN
    MAP_EVERY EXISTS_TAC
     [`path_image (ha:real^1->real^3) UNION path_image (a1:real^1->real^3)`;
      `path_image (ha:real^1->real^3) UNION path_image (a2:real^1->real^3)`] THEN
    ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`a1:real^1->real^3`; `e1:real^3->bool`; `e1':real^3->bool`] THEN
    MATCH_MP_TAC MOI_S4L_L10_SIDE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    USE_THEN "cdis" (MP_TAC o SPECL [`x:real^N`; `a1:real^1->real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o REWRITE_RULE[NOT_EXISTS_THM]) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x)`;
                   `e1:real^3->bool`; `e1':real^3->bool`;
                   `path_image (ha:real^1->real^3) UNION path_image (a1:real^1->real^3)`]
      MOI_SFR_CONNECTED_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        moi_s4l_has "pl_cell_with_boundary" th)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
      FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL_FACTS o check (fun th ->
        moi_s4l_has "pl_cell_with_boundary" th && not(is_forall(concl th)) &&
        can (find_term ((=) `x:real^N`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        UNDISCH_TAC `DISJOINT (path_image (ha:real^1->real^3) UNION path_image a1)
                       (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x))` THEN
        SET_TAC[]];
      ASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 10, second half: innermost returning arcs.                          *)
(* ------------------------------------------------------------------------- *)

let MOI_S4L_RIMPTS_FINITE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb v.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ {v} IN kk
     ==> FINITE (UNIONS {frontier (cb s) INTER moi_s34_rims tt kk f1 | s |
                         s IN moi_s34_simp kk (&2) /\ v IN s})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_TUBE_TUBE) THEN
  REWRITE_TAC[FINITE_UNIONS] THEN CONJ_TAC THENL
   [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t:real^N->bool | t IN kk /\ v IN t}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_STAR_FINITE THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `{v:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
      REWRITE_TAC[SUBSET; IN_ELIM_THM; moi_s34_simp] THEN MESON_TAC[]];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    UNDISCH_TAC `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s
                   ((cb:(real^N->bool)->real^3->bool) s)` THEN
    SIMP_TAC[moi_s34_fb1]]);;

(* In a returning-arc candidate, e meets the rims only along hg. *)
let MOI_S4L_RCAND_RIMS = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb v w s ha hg e e'.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\ {v} IN kk /\
     moi_s4l_rcand tt kk f1 cb v w s ha hg e e'
     ==> e INTER moi_s34_rims tt kk f1 SUBSET path_image hg`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s4l_rcand] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET; IN_INTER; moi_s34_rims; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `q:real^3->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(g:real^N->bool) IN kk` ASSUME_TAC THENL
   [UNDISCH_TAC `(g:real^N->bool) IN moi_s34_simp kk (&1)` THEN
    SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!e a. (y:real^3) IN e /\ e SUBSET a /\ a SUBSET c ==> y IN c`) THEN
    MAP_EVERY EXISTS_TAC
     [`e:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x INTER moi_s34_vb tt kk z)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!r. (y:real^3) IN r /\ r SUBSET c ==> y IN c`) THEN
    EXISTS_TAC `q:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    ALL_TAC] THEN
  (* v must be a vertex of g *)
  SUBGOAL_THEN `(v:real^N) = x \/ v = z` MP_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMG_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `x:real^N`; `z:real^N`] o CONJUNCT1 o
      CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_vb tt kk (x:real^N) INTER moi_s34_vb tt kk z`;
                   `moi_s34_vb tt kk (x:real^N)`] IMAGE_SUBSET) THEN
    MP_TAC(ISPECL [`f1:real^N->real^3`; `moi_s34_vb tt kk (x:real^N) INTER moi_s34_vb tt kk z`;
                   `moi_s34_vb tt kk (z:real^N)`] IMAGE_SUBSET) THEN
    REWRITE_TAC[INTER_SUBSET] THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`;
      `(y:real^3) IN IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x INTER moi_s34_vb tt kk z)`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,u) -> SPEC_TAC(t,u))
     [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x INTER moi_s34_vb tt kk z)`,`D:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`,`CV:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk x)`,`CX:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk z)`,`CZ:real^3->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* the edge at v *)
  DISCH_TAC THEN
  SUBGOAL_THEN `?u:real^N. ~(u = v) /\ segment[v,u] IN kk /\
                  q = IMAGE (f1:real^N->real^3)
                        (moi_s34_vb tt kk v INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
     [EXISTS_TAC `z:real^N` THEN
      UNDISCH_TAC `(g:real^N->bool) IN kk` THEN
      UNDISCH_TAC `q = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
      ASM_REWRITE_TAC[INTER_ASSOC] THEN SIMP_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
      UNDISCH_TAC `~(x:real^N = z)` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `x:real^N` THEN
      UNDISCH_TAC `(g:real^N->bool) IN kk` THEN
      UNDISCH_TAC `q = IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g INTER moi_s34_bd tt kk)` THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
      CONJ_TAC THENL [ONCE_REWRITE_TAC[SEGMENT_SYM] THEN FIRST_ASSUM ACCEPT_TAC;
                      AP_TERM_TAC THEN SET_TAC[]]];
    ALL_TAC] THEN
  ASM_CASES_TAC `u:real^N = w` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC(SET_RULE `!d r. (y:real^3) IN e /\ y IN q /\ q = r /\ r SUBSET d /\
                                 e INTER d = b ==> y IN b`) THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`;
      `IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N` o check (fun th ->
      is_forall(concl th) && moi_s4l_has "DISJOINT" th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MATCH_MP_TAC(SET_RULE `!d r. (y:real^3) IN e /\ y IN q /\ q = r /\ r SUBSET d /\
                                 DISJOINT e d ==> F`) THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk u)`;
      `IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v INTER moi_s34_vb tt kk u INTER moi_s34_bd tt kk)`] THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]]);;

let MOI_S4L_CARD_GE2 = prove
 (`!s:A->bool. FINITE s /\ ~(s = {}) /\ (!x. ~(s = {x})) ==> 2 <= CARD s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC(ARITH_RULE `~(n = 0) /\ ~(n = 1) ==> 2 <= n`) THEN
  CONJ_TAC THENL [ASM_MESON_TAC[CARD_EQ_0]; DISCH_TAC] THEN
  SUBGOAL_THEN `(s:A->bool) HAS_SIZE (SUC 0)` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE; ONE]; ALL_TAC] THEN
  REWRITE_TAC[HAS_SIZE_CLAUSES] THEN ASM_MESON_TAC[]);;

(* An inner trace point y of a returning-arc candidate lies on a trace arc  *)
(* h2 inside e with ends on hg, no other rim point, interior missing the    *)
(* boundary circle, and ends different from those of ha (given Lemma 9).    *)
let MOI_S4L_L10_PIECE = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb v w s ha hg e e' s1 y.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ {v} IN kk /\
     (!s v j. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\
              j IN components (moi_s34_trace tt kk f1 (cb s))
              ==> ~(j SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk))) /\
     moi_s4l_rcand tt kk f1 cb v w s ha hg e e' /\
     s1 IN moi_s34_simp kk (&2) /\ y IN moi_s34_trace tt kk f1 (cb s1) /\ y IN e /\
     ~(y IN path_image ha UNION path_image hg)
     ==> ?h2. arc h2 /\ pl_map_on (interval[vec 0,vec 1]) h2 /\
              path_image h2 SUBSET moi_s34_trace tt kk f1 (cb s1) /\
              path_image h2 SUBSET e /\
              path_image h2 INTER moi_s34_rims tt kk f1 = {pathstart h2,pathfinish h2} /\
              pathstart h2 IN path_image hg /\ pathfinish h2 IN path_image hg /\
              ~({pathstart h2,pathfinish h2} = {pathstart ha,pathfinish ha}) /\
              DISJOINT (path_image h2 DIFF {pathstart h2,pathfinish h2})
                       (path_image ha UNION path_image hg)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4l_rcand]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `s:real^N->bool`; `ha:real^1->real^3`;
                 `hg:real^1->real^3`; `e:real^3->bool`; `e':real^3->bool`] MOI_S4L_RCAND_RIMS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s1:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `DISJOINT ((e:real^3->bool) DIFF (path_image ha UNION path_image hg))
                  (moi_s34_rims tt kk (f1:real^N->real^3))` ASSUME_TAC THENL
   [UNDISCH_TAC `(e:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3) SUBSET
                 path_image (hg:real^1->real^3)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^3) IN moi_s34_rims tt kk (f1:real^N->real^3))` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT ((e:real^3->bool) DIFF (path_image ha UNION path_image hg))
                  (moi_s34_rims tt kk (f1:real^N->real^3))` THEN
    UNDISCH_TAC `(y:real^3) IN e` THEN
    UNDISCH_TAC `~((y:real^3) IN path_image ha UNION path_image hg)` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `jj = connected_component (moi_s34_trace tt kk (f1:real^N->real^3)
                     ((cb:(real^N->bool)->real^3->bool) s1)) y` THEN
  SUBGOAL_THEN `(jj:real^3->bool) IN components (moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s1)) /\
                y IN jj /\ connected jj /\
                jj SUBSET moi_s34_trace tt kk f1 (cb s1)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "jj" THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[CONNECTED_COMPONENT_IN_COMPONENTS];
      REWRITE_TAC[IN] THEN REWRITE_TAC[CONNECTED_COMPONENT_REFL_EQ] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT];
      REWRITE_TAC[CONNECTED_COMPONENT_SUBSET]];
    ALL_TAC] THEN
  (* the component through ha *)
  SUBGOAL_THEN
   `jj INTER path_image (ha:real^1->real^3) = {} \/
    (s1:real^N->bool) = s /\ path_image ha SUBSET jj`
  ASSUME_TAC THENL
   [ASM_CASES_TAC `jj INTER path_image (ha:real^1->real^3) = {}` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(s1:real^N->bool) = s` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                     `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                     `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                     `s:real^N->bool`; `s1:real^N->bool`] MOI_S4L_TRACES_DISJ) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`~(jj INTER path_image (ha:real^1->real^3) = {})`;
        `(jj:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
           ((cb:(real^N->bool)->real^3->bool) s1)`;
        `path_image (ha:real^1->real^3) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
           ((cb:(real^N->bool)->real^3->bool) s)`;
        `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s) INTER
         moi_s34_trace tt kk f1 (cb s1) = {}`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)` THEN
    ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC PATH_CONNECTED_IMP_CONNECTED THEN
    MATCH_MP_TAC PATH_CONNECTED_PATH_IMAGE THEN ASM_SIMP_TAC[ARC_IMP_PATH];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (hg:real^1->real^3) SUBSET moi_s34_rims tt kk (f1:real^N->real^3)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4L_RIM_IN_RIMS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pathstart (ha:real^1->real^3) IN moi_s34_rims tt kk (f1:real^N->real^3) /\
                pathfinish ha IN moi_s34_rims tt kk f1 /\
                pathstart ha IN path_image ha /\ pathfinish ha IN path_image ha`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[PATHSTART_IN_PATH_IMAGE; PATHFINISH_IN_PATH_IMAGE] THEN
    UNDISCH_TAC `path_image (ha:real^1->real^3) INTER moi_s34_rims tt kk (f1:real^N->real^3) =
                 {pathstart ha,pathfinish ha}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE ((jj:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `frontier ((cb:(real^N->bool)->real^3->bool) s1) INTER
                moi_s34_rims tt kk (f1:real^N->real^3)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_s34_fb1 tt kk h (f1:real^N->real^3) car s1
                     ((cb:(real^N->bool)->real^3->bool) s1)` THEN
      SIMP_TAC[moi_s34_fb1];
      UNDISCH_TAC `(jj:real^3->bool) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                     ((cb:(real^N->bool)->real^3->bool) s1)` THEN
      REWRITE_TAC[moi_s34_trace] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((jj:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3) = {})`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `DISJOINT (jj:real^3->bool) (path_image ha UNION path_image hg)`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
       [MAP_EVERY UNDISCH_TAC
         [`jj INTER path_image (ha:real^1->real^3) = {}`;
          `(jj:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3) = {}`;
          `path_image (hg:real^1->real^3) SUBSET moi_s34_rims tt kk (f1:real^N->real^3)`] THEN
        SET_TAC[];
        FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
        MAP_EVERY UNDISCH_TAC
         [`(jj:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3) = {}`;
          `path_image (ha:real^1->real^3) SUBSET jj`;
          `pathstart (ha:real^1->real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)`;
          `pathstart (ha:real^1->real^3) IN path_image ha`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(jj:real^3->bool) SUBSET e` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4L_COMP_INSIDE THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
        `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
        `car:(real^N->bool)->real^3->bool`; `v:real^N`; `e':real^3->bool`;
        `path_image (ha:real^1->real^3) UNION path_image hg`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3)
                      ((cb:(real^N->bool)->real^3->bool) s1)` THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(y:real^3) IN jj` THEN UNDISCH_TAC `(y:real^3) IN e` THEN SET_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`s1:real^N->bool`; `v:real^N`; `jj:real^3->bool`] o
      check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3 &&
                       moi_s4l_has "components" th)) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `e:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. ~((jj:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3) = {r})`
  ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S4L_TRACE_RIMS_NOT_SING THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
      `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
      `s1:real^N->bool`; `jj:real^3->bool`; `r:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (jj:real^3->bool)` MP_TAC THENL
   [FIRST_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && moi_s4l_has "pl_sphere" th)) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `gj:real^1->real^3` STRIP_ASSUME_TAC o
    MATCH_MP MOI_S4O_CIRCLE_LOOP) THEN
  MP_TAC(ISPECL [`gj:real^1->real^3`;
                 `(jj:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3)`;
                 `y:real^3`] MOI_P1M_LOOP_PIECE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[INTER_SUBSET; IN_INTER] THEN
    MATCH_MP_TAC MOI_S4L_CARD_GE2 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real^1->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `h2:real^1->real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `path_image (h2:real^1->real^3) INTER moi_s34_rims tt kk (f1:real^N->real^3) =
                {pathstart h2,pathfinish h2}` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`path_image (h2:real^1->real^3) SUBSET jj`;
      `path_image (h2:real^1->real^3) INTER jj INTER moi_s34_rims tt kk (f1:real^N->real^3) =
       {pathstart h2,pathfinish h2}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `path_image (h2:real^1->real^3) SUBSET moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s1)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `jj:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(y:real^3) IN path_image h2 DIFF {pathstart h2,pathfinish h2}` ASSUME_TAC THENL
   [UNDISCH_TAC `~((y:real^3) IN moi_s34_rims tt kk (f1:real^N->real^3))` THEN
    UNDISCH_TAC `(y:real^3) IN path_image h2` THEN
    UNDISCH_TAC `path_image (h2:real^1->real^3) INTER moi_s34_rims tt kk (f1:real^N->real^3) =
                 {pathstart h2,pathfinish h2}` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (path_image h2 DIFF {pathstart h2,pathfinish h2}) (path_image (ha:real^1->real^3)) /\
    ((s1:real^N->bool) = s /\ path_image ha SUBSET jj
     ==> ?k. arc k /\ path_image ha UNION path_image k = jj /\
             {pathstart k,pathfinish k} = {pathstart ha,pathfinish ha} /\
             path_image (h2:real^1->real^3) SUBSET path_image k)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THENL
     [CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`jj INTER path_image (ha:real^1->real^3) = {}`;
          `path_image (h2:real^1->real^3) SUBSET jj`] THEN SET_TAC[];
        STRIP_TAC THEN
        UNDISCH_TAC `jj INTER path_image (ha:real^1->real^3) = {}` THEN
        UNDISCH_TAC `path_image (ha:real^1->real^3) SUBSET jj` THEN
        UNDISCH_TAC `pathstart (ha:real^1->real^3) IN path_image ha` THEN SET_TAC[]];
      FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
      MP_TAC(ISPECL [`gj:real^1->real^3`; `ha:real^1->real^3`] MOI_PL2_ARC_IN_LOOP) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `k:real^1->real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `path_image (h2:real^1->real^3) DIFF {pathstart h2,pathfinish h2}
                    SUBSET path_image (k:real^1->real^3)` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`path_image (h2:real^1->real^3) DIFF {pathstart h2,pathfinish h2}`;
                       `path_image (ha:real^1->real^3)`; `path_image (k:real^1->real^3)`;
                       `{pathstart ha:real^3,pathfinish ha}`] MOI_SFR_CONNECTED_SIDE) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[MOI_S4L_ARC_INTERIOR_CONNECTED; CLOSED_PATH_IMAGE; ARC_IMP_PATH] THEN
          CONJ_TAC THENL
           [MAP_EVERY UNDISCH_TAC
             [`path_image (h2:real^1->real^3) SUBSET jj`;
              `path_image (ha:real^1->real^3) UNION path_image k = path_image gj`;
              `path_image (gj:real^1->real^3) = jj`] THEN SET_TAC[];
            MAP_EVERY UNDISCH_TAC
             [`path_image (h2:real^1->real^3) INTER jj INTER moi_s34_rims tt kk (f1:real^N->real^3) =
               {pathstart h2,pathfinish h2}`;
              `path_image (ha:real^1->real^3) SUBSET jj`;
              `pathstart (ha:real^1->real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)`;
              `pathfinish (ha:real^1->real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)`;
              `pathstart (ha:real^1->real^3) IN path_image ha`;
              `pathfinish (ha:real^1->real^3) IN path_image ha`] THEN
            SET_TAC[]];
          ALL_TAC] THEN
        STRIP_TAC THEN
        UNDISCH_TAC `(y:real^3) IN path_image h2 DIFF {pathstart h2,pathfinish h2}` THEN
        UNDISCH_TAC `~((y:real^3) IN path_image ha UNION path_image hg)` THEN
        UNDISCH_TAC `path_image (h2:real^1->real^3) DIFF {pathstart h2,pathfinish h2}
                     SUBSET path_image (ha:real^1->real^3)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`path_image (h2:real^1->real^3) DIFF {pathstart h2,pathfinish h2}
           SUBSET path_image (k:real^1->real^3)`;
          `path_image (ha:real^1->real^3) INTER path_image k = {pathstart ha,pathfinish ha}`;
          `path_image (h2:real^1->real^3) INTER jj INTER moi_s34_rims tt kk (f1:real^N->real^3) =
           {pathstart h2,pathfinish h2}`;
          `path_image (ha:real^1->real^3) SUBSET jj`;
          `pathstart (ha:real^1->real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)`;
          `pathfinish (ha:real^1->real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)`;
          `pathstart (ha:real^1->real^3) IN path_image ha`;
          `pathfinish (ha:real^1->real^3) IN path_image ha`] THEN
        SET_TAC[];
        DISCH_TAC THEN EXISTS_TAC `k:real^1->real^3` THEN ASM_REWRITE_TAC[] THEN
        CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `closure(path_image (h2:real^1->real^3) DIFF {pathstart h2,pathfinish h2})` THEN
        CONJ_TAC THENL
         [ASM_SIMP_TAC[MOI_SFR_ARC_CLOSURE_DIFF; FINITE_INSERT; FINITE_EMPTY; SUBSET_REFL];
          MATCH_MP_TAC CLOSURE_MINIMAL THEN
          ASM_SIMP_TAC[CLOSED_PATH_IMAGE; ARC_IMP_PATH]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (path_image h2 DIFF {pathstart h2,pathfinish h2})
                  (path_image (ha:real^1->real^3) UNION path_image hg)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`DISJOINT (path_image h2 DIFF {pathstart h2,pathfinish h2}) (path_image (ha:real^1->real^3))`;
      `path_image (h2:real^1->real^3) INTER moi_s34_rims tt kk (f1:real^N->real^3) =
       {pathstart h2,pathfinish h2}`;
      `path_image (hg:real^1->real^3) SUBSET moi_s34_rims tt kk (f1:real^N->real^3)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (h2:real^1->real^3) SUBSET e` ASSUME_TAC THENL
   [SUBGOAL_THEN `path_image h2 DIFF {pathstart h2,pathfinish h2} SUBSET (e:real^3->bool)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S4L_COMP_INSIDE THEN
      MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
        `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
        `car:(real^N->bool)->real^3->bool`; `v:real^N`; `e':real^3->bool`;
        `path_image (ha:real^1->real^3) UNION path_image hg`] THEN
      ASM_SIMP_TAC[MOI_S4L_ARC_INTERIOR_CONNECTED] THEN CONJ_TAC THENL
       [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `jj:real^3->bool` THEN
        CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC SUBSET_TRANS THEN
        EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3)
                      ((cb:(real^N->bool)->real^3->bool) s1)` THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(y:real^3) IN path_image h2 DIFF {pathstart h2,pathfinish h2}` THEN
        UNDISCH_TAC `(y:real^3) IN e` THEN SET_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure(path_image (h2:real^1->real^3) DIFF {pathstart h2,pathfinish h2})` THEN
    CONJ_TAC THENL
     [ASM_SIMP_TAC[MOI_SFR_ARC_CLOSURE_DIFF; FINITE_INSERT; FINITE_EMPTY; SUBSET_REFL];
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pathstart (h2:real^1->real^3) IN path_image hg /\ pathfinish h2 IN path_image hg`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `h2:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `h2:real^1->real^3` PATHFINISH_IN_PATH_IMAGE) THEN
    MAP_EVERY UNDISCH_TAC
     [`path_image (h2:real^1->real^3) SUBSET e`;
      `path_image (h2:real^1->real^3) INTER moi_s34_rims tt kk (f1:real^N->real^3) =
       {pathstart h2,pathfinish h2}`;
      `(e:real^3->bool) INTER moi_s34_rims tt kk (f1:real^N->real^3) SUBSET
       path_image (hg:real^1->real^3)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  (* both ends of ha: then jj is ha UNION h2, a trace circle in A_v *)
  SUBGOAL_THEN `(s1:real^N->bool) = s /\ path_image (ha:real^1->real^3) SUBSET jj`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `jj INTER path_image (ha:real^1->real^3) = {}` THEN
    MP_TAC(ISPEC `h2:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
    MAP_EVERY UNDISCH_TAC
     [`{pathstart h2:real^3,pathfinish h2} = {pathstart ha,pathfinish ha}`;
      `path_image (h2:real^1->real^3) SUBSET jj`;
      `pathstart (ha:real^1->real^3) IN path_image ha`;
      `pathfinish (ha:real^1->real^3) IN path_image ha`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th) &&
    moi_s4l_has "arc" th)) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^1->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`k:real^1->real^3`; `h2:real^1->real^3`] MOI_S4L_ARC_SAME_ENDS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`s1:real^N->bool`; `v:real^N`; `jj:real^3->bool`] o
    check (fun th -> is_forall(concl th) && length(fst(strip_forall(concl th))) = 3 &&
                     moi_s4l_has "components" th)) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `path_image (ha:real^1->real^3) UNION path_image k = jj` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  MAP_EVERY UNDISCH_TAC
   [`path_image (h2:real^1->real^3) = path_image (k:real^1->real^3)`;
    `path_image (h2:real^1->real^3) SUBSET e`;
    `path_image (ha:real^1->real^3) SUBSET
     IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
    `(e:real^3->bool) SUBSET
     IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`] THEN
  SET_TAC[]);;

(* The trace arc h2 of an inner point and the sub-arc of hg between its   *)
(* ends bound a smaller candidate inside e, missing a trace-rim point of e. *)
let MOI_S4L_L10_INNER = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb v w s ha hg e e' s1 h2.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ {v} IN kk /\
     moi_s4l_rcand tt kk f1 cb v w s ha hg e e' /\ s1 IN moi_s34_simp kk (&2) /\
     arc h2 /\ pl_map_on (interval[vec 0,vec 1]) h2 /\
     path_image h2 SUBSET moi_s34_trace tt kk f1 (cb s1) /\ path_image h2 SUBSET e /\
     path_image h2 INTER moi_s34_rims tt kk f1 = {pathstart h2,pathfinish h2} /\
     pathstart h2 IN path_image hg /\ pathfinish h2 IN path_image hg /\
     ~({pathstart h2,pathfinish h2} = {pathstart ha,pathfinish ha}) /\
     DISJOINT (path_image h2 DIFF {pathstart h2,pathfinish h2})
              (path_image ha UNION path_image hg)
     ==> ?hg2 e2 e2'. moi_s4l_rcand tt kk f1 cb v w s1 h2 hg2 e2 e2' /\ e2 SUBSET e /\
                      ?t. t IN frontier (cb s) INTER moi_s34_rims tt kk f1 /\ t IN e /\
                          ~(t IN e2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s4l_rcand]) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
    moi_s4l_has "pl_cell_with_boundary" th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
    moi_s4l_has "pl_cell_with_boundary" th && not (is_forall(concl th)) &&
    can (find_term ((=) `w:real^N`)) (concl th))) THEN
  SUBGOAL_THEN
   `!x. ~(x = v) /\ segment[v:real^N,x] IN kk
        ==> IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x) SUBSET
            frontier (IMAGE f1 (moi_s34_vb tt kk v))`
  (LABEL_TAC "dsub") THENL
   [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    FIRST_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
      is_eq(concl th) &&
      can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier")) (lhs(concl th)))) THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN DISJ2_TAC THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th ->
    is_eq(concl th) &&
    can (find_term (fun t -> is_const t && fst(dest_const t) = "frontier")) (lhs(concl th)))) THEN
  (* the sub-arc of hg between the ends of h2 *)
  SUBGOAL_THEN `~(pathstart h2:real^3 = pathfinish h2)` ASSUME_TAC THENL
   [ASM_MESON_TAC[ARC_DISTINCT_ENDS]; ALL_TAC] THEN
  MP_TAC(ISPECL [`hg:real^1->real^3`; `pathstart h2:real^3`; `pathfinish h2:real^3`]
    MOI_P1M_SUBARC) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^1->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `path_image (h2:real^1->real^3) INTER path_image (k:real^1->real^3) =
                {pathstart h2,pathfinish h2}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `k:real^1->real^3` PATHFINISH_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `h2:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `h2:real^1->real^3` PATHFINISH_IN_PATH_IMAGE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE
     `!hg r rims. (b:real^3->bool) SUBSET hg /\ hg SUBSET r /\ r SUBSET rims /\
                  a INTER rims = {p,q}
                  ==> q IN a ==> p IN a ==> q IN b ==> p IN b ==> a INTER b = {p,q}`) THEN
    MAP_EVERY EXISTS_TAC
     [`path_image (hg:real^1->real^3)`;
      `IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`;
      `moi_s34_rims tt kk (f1:real^N->real^3)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S4L_RIM_IN_RIMS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (hg:real^1->real^3) SUBSET e` ASSUME_TAC THENL
   [UNDISCH_TAC `e INTER IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) =
                 path_image (hg:real^1->real^3)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) DIFF
              IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk))
             (path_image (h2:real^1->real^3) UNION path_image k)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!av e hg. a SUBSET e /\ e SUBSET av /\ d INTER av = r /\ b SUBSET hg /\ hg SUBSET r
                ==> DISJOINT (d DIFF r) ((a:real^3->bool) UNION b)`) THEN
    MAP_EVERY EXISTS_TAC
     [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
      `e:real^3->bool`; `path_image (hg:real^1->real^3)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?u u'. pl_cell_with_boundary 2 u (path_image (h2:real^1->real^3) UNION path_image k) /\
           pl_cell_with_boundary 2 u' (path_image h2 UNION path_image k) /\
           u UNION u' = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)) /\
           u INTER u' = path_image h2 UNION path_image k /\
           IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) DIFF
           IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)
           SUBSET u'`
  (X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `u':real^3->bool` STRIP_ASSUME_TAC)) THENL
   [MP_TAC(ISPECL [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
                   `path_image (h2:real^1->real^3) UNION path_image k`] SPHERE_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SLV_ARCS_SPHERE THEN ASM_REWRITE_TAC[DIMINDEX_3; ARITH];
        MAP_EVERY UNDISCH_TAC
         [`path_image (h2:real^1->real^3) SUBSET e`;
          `path_image (k:real^1->real^3) SUBSET path_image hg`;
          `path_image (hg:real^1->real^3) SUBSET e`;
          `(e:real^3->bool) UNION e' = frontier (IMAGE (f1:real^N->real^3)
             (moi_s34_vb tt kk v))`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real^3->bool` (X_CHOOSE_THEN `d2:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MATCH_MP_TAC MOI_S4L_SPLIT_ORIENT THEN
    MAP_EVERY EXISTS_TAC [`d1:real^3->bool`; `d2:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `d SUBSET sg ==> d DIFF r SUBSET (sg:real^3->bool)`) THEN
    USE_THEN "dsub" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed(u:real^3->bool) /\ closed(u':real^3->bool) /\
                (u:real^3->bool) SUBSET closure (u DIFF (path_image h2 UNION path_image k))`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`2`; `u:real^3->bool`; `path_image (h2:real^1->real^3) UNION path_image k`]
      MOI_S4L_PL_CELL_FACTS) THEN
    MP_TAC(ISPECL [`2`; `u':real^3->bool`; `path_image (h2:real^1->real^3) UNION path_image k`]
      MOI_S4L_PL_CELL_FACTS) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
      moi_s4l_has "pl_cell_with_boundary" th &&
      rand(rator(concl th)) = `u:real^3->bool`)) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) SUBSET u'`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)
                  DIFF IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER
                                 moi_s34_bd tt kk))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the open part of e' lies on the D side of the new circle *)
  SUBGOAL_THEN `e' DIFF (path_image ha UNION path_image hg) SUBSET (u':real^3->bool)`
  ASSUME_TAC THENL
   [FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S4L_PL_CELL2_TOPO o check (fun th ->
      moi_s4l_has "pl_cell_with_boundary" th &&
      rand(rator(concl th)) = `e':real^3->bool`)) THEN
    MP_TAC(ISPECL [`e' DIFF (path_image ha UNION path_image hg):real^3->bool`;
                   `u:real^3->bool`; `u':real^3->bool`;
                   `path_image (h2:real^1->real^3) UNION path_image k`]
      MOI_SFR_CONNECTED_SIDE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`(e:real^3->bool) UNION e' = frontier (IMAGE (f1:real^N->real^3)
           (moi_s34_vb tt kk v))`;
        `(e:real^3->bool) INTER e' = path_image ha UNION path_image hg`;
        `path_image (h2:real^1->real^3) SUBSET e`;
        `path_image (k:real^1->real^3) SUBSET path_image hg`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_TAC) THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
    SUBGOAL_THEN
     `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) DIFF
      IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) SUBSET
      e' DIFF (path_image ha UNION path_image hg)` MP_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!av. d SUBSET e' /\ ha SUBSET av /\ d INTER av = r /\ hg SUBSET r
             ==> d DIFF r SUBSET e' DIFF ((ha:real^3->bool) UNION hg)`) THEN
      EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`e' DIFF (path_image ha UNION path_image hg) SUBSET (u:real^3->bool)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) DIFF
       IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)
       SUBSET u'`;
      `(u:real^3->bool) INTER u' = path_image h2 UNION path_image k`;
      `DISJOINT (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) DIFF
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk))
         (path_image (h2:real^1->real^3) UNION path_image k)`;
      `~(IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) DIFF
         IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) = {})`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) DIFF
       IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`,
      `ID:real^3->bool`;
      `e' DIFF (path_image ha UNION path_image hg):real^3->bool`, `EO:real^3->bool`;
      `path_image (h2:real^1->real^3) UNION path_image k`, `C2:real^3->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^3->bool) SUBSET e` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `closure ((u:real^3->bool) DIFF (path_image h2 UNION path_image k))` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`e' DIFF (path_image ha UNION path_image hg) SUBSET (u':real^3->bool)`;
      `(u:real^3->bool) INTER u' = path_image h2 UNION path_image k`;
      `(u:real^3->bool) UNION u' = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
      `(e:real^3->bool) UNION e' = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
      `(e:real^3->bool) INTER e' = path_image ha UNION path_image hg`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`, `SG:real^3->bool`;
      `path_image (h2:real^1->real^3) UNION path_image k`, `C2:real^3->bool`;
      `path_image (ha:real^1->real^3) UNION path_image hg`, `C1:real^3->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`k:real^1->real^3`; `u:real^3->bool`; `u':real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4L_L10_SIDE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`path_image (h2:real^1->real^3) SUBSET e`;
        `(e:real^3->bool) SUBSET IMAGE (f1:real^N->real^3)
           (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`] THEN SET_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `path_image (hg:real^1->real^3)` THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
        is_forall(concl th) && moi_s4l_has "DISJOINT" th &&
        length(fst(strip_forall(concl th))) = 1)) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      USE_THEN "dsub" (MP_TAC o SPEC `x:real^N`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`e' DIFF (path_image ha UNION path_image hg) SUBSET (u':real^3->bool)`;
        `(e:real^3->bool) UNION e' = frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`;
        `(e:real^3->bool) INTER e' = path_image ha UNION path_image hg`;
        `DISJOINT e (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x))`;
        `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x) SUBSET
         frontier (IMAGE f1 (moi_s34_vb tt kk v))`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
       [`frontier (IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v))`, `SG:real^3->bool`;
        `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk x)`,
        `DX:real^3->bool`;
        `path_image (ha:real^1->real^3) UNION path_image hg`, `C1:real^3->bool`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* a trace-rim end of ha outside the new disk *)
  SUBGOAL_THEN `~(pathstart ha:real^3 = pathfinish ha)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `ha:real^1->real^3` ARC_DISTINCT_ENDS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?t:real^3. (t = pathstart ha \/ t = pathfinish ha) /\
                           ~(pathstart h2 = t) /\ ~(pathfinish h2 = t)`
  (X_CHOOSE_THEN `t:real^3` (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC)) THENL
   [MAP_EVERY UNDISCH_TAC
     [`~(pathstart ha:real^3 = pathfinish ha)`;
      `~({pathstart h2:real^3,pathfinish h2} = {pathstart ha,pathfinish ha})`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`pathstart (ha:real^1->real^3)`, `p:real^3`;
      `pathfinish (ha:real^1->real^3)`, `q:real^3`;
      `pathstart (h2:real^1->real^3)`, `p2:real^3`;
      `pathfinish (h2:real^1->real^3)`, `q2:real^3`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `t:real^3` THEN
  SUBGOAL_THEN `(t:real^3) IN path_image ha /\ t IN path_image hg /\
                t IN moi_s34_rims tt kk (f1:real^N->real^3)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`path_image (ha:real^1->real^3) INTER moi_s34_rims tt kk (f1:real^N->real^3) =
       {pathstart ha,pathfinish ha}`;
      `path_image (ha:real^1->real^3) INTER path_image hg = {pathstart ha,pathfinish ha}`;
      `(t:real^3) = pathstart ha \/ t = pathfinish ha`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`moi_s34_rims tt kk (f1:real^N->real^3)`, `RR:real^3->bool`;
      `path_image (ha:real^1->real^3)`, `A:real^3->bool`;
      `path_image (hg:real^1->real^3)`, `G:real^3->bool`;
      `pathstart (ha:real^1->real^3)`, `p:real^3`;
      `pathfinish (ha:real^1->real^3)`, `q:real^3`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `!a t. (x:real^3) IN a /\ a SUBSET t /\ t SUBSET f ==> x IN f`) THEN
    MAP_EVERY EXISTS_TAC
     [`path_image (ha:real^1->real^3)`;
      `moi_s34_trace tt kk (f1:real^N->real^3) ((cb:(real^N->bool)->real^3->bool) s)`] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s34_trace; INTER_SUBSET];
    UNDISCH_TAC `(e:real^3->bool) INTER e' = path_image ha UNION path_image hg` THEN
    UNDISCH_TAC `(t:real^3) IN path_image ha` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
    SUBGOAL_THEN `~((t:real^3) IN path_image h2)` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`path_image (h2:real^1->real^3) INTER moi_s34_rims tt kk (f1:real^N->real^3) =
         {pathstart h2,pathfinish h2}`;
        `(t:real^3) IN moi_s34_rims tt kk (f1:real^N->real^3)`;
        `~(pathstart h2:real^3 = t)`; `~(pathfinish h2:real^3 = t)`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN
      MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
       [`moi_s34_rims tt kk (f1:real^N->real^3)`, `RR:real^3->bool`;
        `path_image (h2:real^1->real^3)`, `A:real^3->bool`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((t:real^3) IN path_image k)` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`(t:real^3) = pathstart ha \/ t = pathfinish ha`;
        `~(pathstart h2:real^3 = t)`; `~(pathfinish h2:real^3 = t)`;
        `pathstart hg:real^3 = pathstart ha`; `pathfinish hg:real^3 = pathfinish ha`;
        `~(pathstart h2:real^3 = pathstart hg) /\ ~(pathfinish h2 = pathstart hg)
         ==> ~(pathstart hg IN path_image k)`;
        `~(pathstart h2:real^3 = pathfinish hg) /\ ~(pathfinish h2 = pathfinish hg)
         ==> ~(pathfinish hg IN path_image k)`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(t:real^3) IN u'` ASSUME_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!b r d. (t:real^3) IN b /\ b SUBSET r /\ r SUBSET d /\ d SUBSET u'
                             ==> t IN u'`) THEN
      MAP_EVERY EXISTS_TAC
       [`path_image (hg:real^1->real^3)`;
        `IMAGE (f1:real^N->real^3)
           (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`;
        `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`] THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(u:real^3->bool) INTER u' = path_image h2 UNION path_image k` THEN
    MAP_EVERY UNDISCH_TAC
     [`~((t:real^3) IN path_image h2)`; `~((t:real^3) IN path_image k)`;
      `(t:real^3) IN u'`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Lemma 10, conclusion: the innermost returning arc gives Operation 2.      *)
(* ------------------------------------------------------------------------- *)

(* An innermost candidate: no trace point inside its disk off the circle.   *)
let MOI_S4L_L10_MIN = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb v w s0 ha0 hg0 e0 e0'.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\ {v} IN kk /\
     (!s v j. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\
              j IN components (moi_s34_trace tt kk f1 (cb s))
              ==> ~(j SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk))) /\
     moi_s4l_rcand tt kk f1 cb v w s0 ha0 hg0 e0 e0'
     ==> ?s ha hg e e'. moi_s4l_rcand tt kk f1 cb v w s ha hg e e' /\
                        !s1. s1 IN moi_s34_simp kk (&2)
                             ==> DISJOINT (e DIFF (path_image ha UNION path_image hg))
                                          (moi_s34_trace tt kk f1 (cb s1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `pp = UNIONS {frontier ((cb:(real^N->bool)->real^3->bool) s) INTER
                           moi_s34_rims tt kk (f1:real^N->real^3) | s |
                           s IN moi_s34_simp kk (&2) /\ (v:real^N) IN s}` THEN
  SUBGOAL_THEN `FINITE (pp:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "pp" THEN MATCH_MP_TAC MOI_S4L_RIMPTS_FINITE THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `\n. ?s ha hg e e'. moi_s4l_rcand tt kk (f1:real^N->real^3) cb (v:real^N) w
                                     s ha hg e e' /\
                                   CARD ((pp:real^3->bool) INTER e) = n` num_WOP) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`CARD ((pp:real^3->bool) INTER e0)`;
      `s0:real^N->bool`; `ha0:real^1->real^3`; `hg0:real^1->real^3`; `e0:real^3->bool`;
      `e0':real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s:real^N->bool` (X_CHOOSE_THEN `ha:real^1->real^3`
      (X_CHOOSE_THEN `hg:real^1->real^3` (X_CHOOSE_THEN `e:real^3->bool`
        (X_CHOOSE_THEN `e':real^3->bool` STRIP_ASSUME_TAC)))))
    (LABEL_TAC "min"))) THEN
  MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `ha:real^1->real^3`; `hg:real^1->real^3`;
                        `e:real^3->bool`; `e':real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s1:real^N->bool` THEN DISCH_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_DIFF; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  (* v is a vertex of s, so the trace-rim points of cb s count in pp *)
  SUBGOAL_THEN `(v:real^N) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s4l_rcand tt kk (f1:real^N->real^3) cb v w s ha hg e e'` THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[moi_s4l_rcand]) THEN
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                   `s:real^N->bool`] MOI_S4L_TRACE_COMP_FACTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC MOI_S4L_TRACE_AT_V THEN
    MAP_EVERY EXISTS_TAC [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
      `h:real^N->real^3`; `f1:real^N->real^3`; `car:(real^N->bool)->real^3->bool`;
      `(cb:(real^N->bool)->real^3->bool) s`; `path_image (ha:real^1->real^3)`] THEN
    ASM_REWRITE_TAC[PATH_IMAGE_NONEMPTY] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `s:real^N->bool`; `ha:real^1->real^3`;
                 `hg:real^1->real^3`; `e:real^3->bool`; `e':real^3->bool`;
                 `s1:real^N->bool`; `y:real^3`] MOI_S4L_L10_PIECE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `h2:real^1->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `s:real^N->bool`; `ha:real^1->real^3`;
                 `hg:real^1->real^3`; `e:real^3->bool`; `e':real^3->bool`;
                 `s1:real^N->bool`; `h2:real^1->real^3`] MOI_S4L_L10_INNER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hg2:real^1->real^3` (X_CHOOSE_THEN `e2:real^3->bool`
    (X_CHOOSE_THEN `e2':real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `t:real^3` STRIP_ASSUME_TAC)))))) THEN
  SUBGOAL_THEN `(t:real^3) IN pp` ASSUME_TAC THENL
   [EXPAND_TAC "pp" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `frontier ((cb:(real^N->bool)->real^3->bool) s) INTER
                moi_s34_rims tt kk (f1:real^N->real^3)` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s4l_rcand tt kk (f1:real^N->real^3) cb v w s ha hg e e'` THEN
    SIMP_TAC[moi_s4l_rcand];
    ALL_TAC] THEN
  USE_THEN "min" (MP_TAC o SPEC `CARD ((pp:real^3->bool) INTER e2)`) THEN
  REWRITE_TAC[NOT_IMP] THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY EXISTS_TAC [`s1:real^N->bool`; `h2:real^1->real^3`; `hg2:real^1->real^3`;
                          `e2:real^3->bool`; `e2':real^3->bool`] THEN
    ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `CARD ((pp:real^3->bool) INTER e) = n` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC CARD_PSUBSET THEN
  ASM_SIMP_TAC[FINITE_INTER] THEN REWRITE_TAC[PSUBSET] THEN CONJ_TAC THENL
   [UNDISCH_TAC `(e2:real^3->bool) SUBSET e` THEN SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER] THEN DISCH_THEN(MP_TAC o SPEC `t:real^3`) THEN
    ASM_REWRITE_TAC[]]);;

(* Lemma 10 (p.243): with Operations 1 and 2 impossible, no arc of a trace *)
(* in one A_v returns to the rim it starts on.                             *)
let MOI_S4L_L10 = prove
 (`!(tt:(real^N->bool)->bool) kk h ep (f1:real^N->real^3) car cb.
     moi_s34_tube tt kk /\ moi_s34_frame tt kk h ep f1 car /\
     moi_s34_fbinv tt kk h f1 car cb /\
     (!s. s IN moi_s34_simp kk (&2)
          ==> ~moi_s34_op1 tt kk f1 cb s /\ ~moi_s34_op2 tt kk f1 cb s)
     ==> !s v g a aa. s IN moi_s34_simp kk (&2) /\ {v} IN kk /\
                      g IN moi_s34_simp kk (&1) /\
                      pl_cell_with_boundary 1 a aa /\
                      a SUBSET moi_s34_trace tt kk f1 (cb s) /\
                      a SUBSET IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) /\
                      aa SUBSET IMAGE f1 (moi_s34_sd tt kk g) /\
                      a INTER moi_s34_rims tt kk f1 = aa
                      ==> F`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`]
    MOI_S4L_L9) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; DISCH_TAC] THEN
  (* the arc a as a PL arc ha *)
  FIRST_X_ASSUM(X_CHOOSE_THEN `ha:real^1->real^3`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (SUBST_ALL_TAC o SYM) SUBST_ALL_TAC))) o
    MATCH_MP MOI_S4L_CELL1_PL_ARC) THEN
  (* v is a vertex of g *)
  SUBGOAL_THEN `(v:real^N) IN g` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`] MOI_S4L_IMAGES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`g:real^N->bool`; `v:real^N`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      moi_s4l_has "moi_s34_sd" th && moi_s4l_has "moi_s34_vb" th)) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
                  IMAGE f1 (moi_s34_vb tt kk v)` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPEC `ha:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
    MAP_EVERY UNDISCH_TAC
     [`{pathstart ha:real^3,pathfinish ha} SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`;
      `path_image (ha:real^1->real^3) SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`, `AV:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v)`, `CV:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk g)`, `DG:real^3->bool`;
      `path_image (ha:real^1->real^3)`, `A:real^3->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* so g is an edge segment[v,w] *)
  SUBGOAL_THEN `?w:real^N. ~(w = v) /\ segment[v,w] IN kk /\ g = segment[v,w]`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `g:real^N->bool`] MOI_S4L_EDGE_VERTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(g:real^N->bool) IN kk` ASSUME_TAC THENL
     [UNDISCH_TAC `(g:real^N->bool) IN moi_s34_simp kk (&1)` THEN
      SIMP_TAC[moi_s34_simp; IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `(v:real^N) = u1 \/ v = u2` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`{x | x IN g /\ {x} IN kk} = {u1:real^N,u2}`; `(v:real^N) IN g`; `{v:real^N} IN kk`] THEN
      POP_ASSUM_LIST(K ALL_TAC) THEN SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC
     [`(v:real^N) = u1 \/ v = u2`; `~(u1:real^N = u2)`; `(g:real^N->bool) = segment[u1,u2]`;
      `(g:real^N->bool) IN kk`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN MESON_TAC[SEGMENT_SYM];
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `g:real^N->bool`)) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `v:real^N`; `w:real^N`] MOI_S4L_EDGE_SD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `v:real^N`] MOI_S4L_SIGMA) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N` o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
    moi_s4l_has "pl_cell_with_boundary" th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `{pathstart ha:real^3,pathfinish ha} SUBSET
                IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `{pathstart ha:real^3,pathfinish ha} SUBSET
                 IMAGE (f1:real^N->real^3) (moi_s34_sd tt kk (segment[v,w]))` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* the ends of ha lie on rim_vw *)
  SUBGOAL_THEN
   `pathstart ha IN IMAGE (f1:real^N->real^3)
      (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk) /\
    pathfinish ha IN IMAGE (f1:real^N->real^3)
      (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `ha:real^1->real^3` PATHSTART_IN_PATH_IMAGE) THEN
    MP_TAC(ISPEC `ha:real^1->real^3` PATHFINISH_IN_PATH_IMAGE) THEN
    MAP_EVERY UNDISCH_TAC
     [`{pathstart ha:real^3,pathfinish ha} SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`;
      `path_image (ha:real^1->real^3) SUBSET
       IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w) INTER
       IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) =
       IMAGE f1 (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`, `RV:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w)`, `DV:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`, `AV:real^3->bool`;
      `path_image (ha:real^1->real^3)`, `A:real^3->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  (* a candidate, then an innermost one *)
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `s:real^N->bool`; `v:real^N`; `w:real^N`; `ha:real^1->real^3`]
    MOI_S4L_L10_CLEAN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `hg:real^1->real^3` (X_CHOOSE_THEN `e:real^3->bool`
    (X_CHOOSE_THEN `e':real^3->bool` ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                 `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                 `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`;
                 `v:real^N`; `w:real^N`; `s:real^N->bool`; `ha:real^1->real^3`;
                 `hg:real^1->real^3`; `e:real^3->bool`; `e':real^3->bool`]
    MOI_S4L_L10_MIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `s2:real^N->bool` (X_CHOOSE_THEN `ha2:real^1->real^3`
    (X_CHOOSE_THEN `hg2:real^1->real^3` (X_CHOOSE_THEN `e2:real^3->bool`
      (X_CHOOSE_THEN `e2':real^3->bool` (CONJUNCTS_THEN2
        (STRIP_ASSUME_TAC o REWRITE_RULE[moi_s4l_rcand]) (LABEL_TAC "inn"))))))) THEN
  (* the Operation 2 witness *)
  SUBGOAL_THEN `pl_cell_with_boundary 1 (path_image (ha2:real^1->real^3))
                  {pathstart ha2,pathfinish ha2} /\
                pl_cell_with_boundary 1 (path_image (hg2:real^1->real^3))
                  {pathstart ha2,pathfinish ha2}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S4O_ARC_CELL THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `hg2:real^1->real^3` MOI_S4O_ARC_CELL) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `path_image (ha2:real^1->real^3) SUBSET
                frontier ((cb:(real^N->bool)->real^3->bool) s2)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `moi_s34_trace tt kk (f1:real^N->real^3)
                  ((cb:(real^N->bool)->real^3->bool) s2)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_s34_trace; INTER_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `{pathstart ha2:real^3,pathfinish ha2} SUBSET
                IMAGE (f1:real^N->real^3)
                  (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`
  ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`path_image (ha2:real^1->real^3) INTER path_image hg2 = {pathstart ha2,pathfinish ha2}`;
      `path_image (hg2:real^1->real^3) SUBSET IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`] THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`IMAGE (f1:real^N->real^3)
         (moi_s34_vb tt kk v INTER moi_s34_vb tt kk w INTER moi_s34_bd tt kk)`, `RV:real^3->bool`;
      `path_image (ha2:real^1->real^3)`, `A:real^3->bool`;
      `path_image (hg2:real^1->real^3)`, `G:real^3->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s3. s3 IN moi_s34_simp kk (&2)
         ==> DISJOINT (e2 DIFF (path_image ha2 UNION path_image hg2))
                      (frontier ((cb:(real^N->bool)->real^3->bool) s3))`
  ASSUME_TAC THENL
   [X_GEN_TAC `s3:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "inn" (MP_TAC o SPEC `s3:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_s34_trace] THEN
    SUBGOAL_THEN `IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk) SUBSET
                  IMAGE f1 (moi_s34_bd tt kk)` MP_TAC THENL
     [MATCH_MP_TAC IMAGE_SUBSET THEN REWRITE_TAC[INTER_SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `(e2:real^3->bool) SUBSET
                 IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)` THEN
    POP_ASSUM_LIST(K ALL_TAC) THEN
    MAP_EVERY (fun (t,x) -> SPEC_TAC(t,x))
     [`IMAGE (f1:real^N->real^3) (moi_s34_vb tt kk v INTER moi_s34_bd tt kk)`, `AV:real^3->bool`;
      `IMAGE (f1:real^N->real^3) (moi_s34_bd tt kk)`, `M:real^3->bool`;
      `frontier ((cb:(real^N->bool)->real^3->bool) s3)`, `FS:real^3->bool`;
      `path_image (ha2:real^1->real^3) UNION path_image hg2`, `C:real^3->bool`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s2:real^N->bool` o check (fun th ->
    moi_s4l_has "moi_s34_op2" th)) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `q ==> ~p /\ ~q ==> F`) THEN
  REWRITE_TAC[moi_s34_op2] THEN
  MAP_EVERY EXISTS_TAC
   [`v:real^N`; `segment[v:real^N,w]`; `path_image (ha2:real^1->real^3)`;
    `path_image (hg2:real^1->real^3)`; `{pathstart ha2:real^3,pathfinish ha2}`;
    `e2:real^3->bool`; `path_image (ha2:real^1->real^3) UNION path_image hg2`] THEN
  ASM_REWRITE_TAC[INTER_ASSOC]);;

(* The main theorem L910: Lemmas 9 and 10 of Sec 34 (p.243). *)
let L910 = prove
 (MOI_S34_L910,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s34_l910] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S4L_L9 THEN
    MAP_EVERY EXISTS_TAC [`h:real^N->real^3`; `ep:real^N->real`;
                          `car:(real^N->bool)->real^3->bool`] THEN
    ASM_SIMP_TAC[];
    MP_TAC(ISPECL [`tt:(real^N->bool)->bool`; `kk:(real^N->bool)->bool`;
                   `h:real^N->real^3`; `ep:real^N->real`; `f1:real^N->real^3`;
                   `car:(real^N->bool)->real^3->bool`; `cb:(real^N->bool)->real^3->bool`]
      MOI_S4L_L10) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; REWRITE_TAC[]]]);;

