(* ========================================================================= *)
(* pc_moi_s33_msides: the two sides of Bd N and Bd X, the per-vertex data   *)
(* (degree, neighbours, charts of the pieces, rims and traces) and the      *)
(* pieces A_v, A'_v (finite, compact, covering, local neighbourhoods) used  *)
(* by Moise 33.1 Lemma 13 (pc_moi_s33_match).  Main theorems                *)
(* MOI_S3MS_SIDES, MOI_S3MS_VDATA and MOI_S3MS_PCS (the statements used in  *)
(* pc_moi_s33_match as MOI_S3MT_SIDES_TERM, MOI_S3MT_VDATA_STMT and         *)
(* MOI_S3MT_PCS_STMT).                                                      *)
(* ========================================================================= *)

needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_plmap.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_fnd_tubeb.ml";;
needs "src/pc_moi_fnd_tubed.ml";;
needs "src/pc_moi_fnd_tubeh.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* M1. Facts from the hypotheses: the tube data of moi_s33_hd, endpoints of *)
(* edges, and the two sides of a regular closed set in real^3.              *)
(* ------------------------------------------------------------------------- *)

let MOI_S3MS_HD_FACTS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c
     ==> FINITE t /\ graph_in_complex t l /\ FINITE l /\ l SUBSET t /\
         lf_simplicial_complex t /\ simplicial_subcomplex l t /\
         (!s f. s IN l /\ f face_of s ==> f IN l)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_hd; moi_s33_tube] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_subcomplex]) THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[FINITE_SUBSET]);;

let MOI_S3MS_EDGE_ENDS = prove
 (`!(l:(real^3->bool)->bool) u v.
     (!s f. s IN l /\ f face_of s ==> f IN l) /\ segment[u,v] IN l
     ==> {u} IN l /\ {v} IN l`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `segment[u:real^3,v]` THEN
  ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

let MOI_S3MS_TWO_SIDES = prove
 (`!(s:real^3->bool) b.
     closed s /\ closure (interior s) = s /\ frontier s = b
     ==> ?ee. open (interior s) /\ open ee /\ DISJOINT (interior s) ee /\
              interior s UNION ee = (:real^3) DIFF b /\
              frontier (interior s) = b /\ frontier ee = b`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN EXISTS_TAC `(:real^3) DIFF s` THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[OPEN_INTERIOR; FRONTIER_COMPLEMENT] THEN
  ASM_REWRITE_TAC[GSYM closed] THEN
  MP_TAC(ISPEC `s:real^3->bool` INTERIOR_SUBSET) THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    ASM_SIMP_TAC[frontier; CLOSURE_CLOSED] THEN ASM SET_TAC[];
    REWRITE_TAC[frontier; INTERIOR_INTERIOR] THEN ASM_SIMP_TAC[CLOSURE_CLOSED]]);;

let MOI_S3MS_COMPLEX_COMPACT = prove
 (`!x:(real^3->bool)->bool.
     FINITE x /\ combinatorial_manifold_with_boundary 3 x ==> compact (UNIONS x)`,
  REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
  REPEAT STRIP_TAC THEN MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]);;

let MOI_S3MS_SEG_NE = prove
 (`!v a b:real^3. ~(a = v) /\ ~(a = b) ==> ~(segment[v,a] = segment[v,b])`,
  REWRITE_TAC[SEGMENT_EQ] THEN SET_TAC[]);;

let MOI_S3MS_FINITE_VERTS = prove
 (`!l:(real^3->bool)->bool. FINITE l ==> FINITE {v | {v} IN l}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\v:real^3. {v}`; `l:(real^3->bool)->bool`] FINITE_IMAGE_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_SING] THEN MESON_TAC[]);;

let MOI_S3MS_CELL_COMPACT = prove
 (`!n (s:real^3->bool) b. pl_cell_with_boundary n s b ==> compact s`,
  REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:real^3->bool`; `s:real^3->bool`] HOMEOMORPHIC_COMPACTNESS) THEN
  ANTS_TAC THENL [REWRITE_TAC[homeomorphic] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_MESON_TAC[SIMPLEX_IMP_COMPACT]);;

(* A local neighbourhood of a rim: the complement of the other pieces.     *)

let MOI_S3MS_NBHD = prove
 (`!(Q:real^3->bool) (P:real^3->real^3->bool) S R u v.
     FINITE {w | Q w} /\ (!w. Q w ==> closed (P w)) /\
     UNIONS {P w | w | Q w} = S /\
     (!w. Q w /\ ~(w = u) /\ ~(w = v) ==> R INTER P w = {})
     ==> ?U. open U /\ R SUBSET U /\ S INTER U SUBSET P u UNION P v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `(:real^3) DIFF UNIONS {(P:real^3->real^3->bool) w | w |
                                     Q w /\ ~(w = u) /\ ~(w = v)}` THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{w:real^3 | Q w}` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN s` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(y:real^3) IN R` THEN SET_TAC[];
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM; IN_UNION] THEN
    MESON_TAC[]]);;

(* N and X are regular closed: MOI_FSP_REG_CLOSED of pc_moi_fnd_split with  *)
(* the same proof, repeated here to keep the load closure of this file and  *)
(* of pc_moi_s33_match small; the proof uses only lemmas of pc_moi_fnd_m3a, *)
(* which is in the closure.                                                 *)

let MOI_S3MS_REG_CLOSED = prove
 (`!c:(real^3->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 3 c
     ==> closure (interior (UNIONS c)) = UNIONS c`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS c:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    ASM_MESON_TAC[MOI_FM3_LF_COMPACT];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[INTERIOR_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(p:real^3) IN complex_boundary c` THENL
   [ALL_TAC;
    MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN
    MATCH_MP_TAC MOI_FM3_NOT_CB_INTERIOR THEN ASM_REWRITE_TAC[]] THEN
  UNDISCH_TAC `(p:real^3) IN complex_boundary c` THEN
  REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r:real^3->bool. r IN c /\ aff_dim r = &3 /\ s SUBSET r` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!k:(real^3->bool)->bool. ~(k = {}) /\ (!r. r IN k ==> P r)
                           ==> ?r. P r`) THEN
    EXISTS_TAC `{r:real^3->bool | r IN c /\ aff_dim r = &3 /\ s SUBSET r}` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_TAC THEN UNDISCH_TAC
     `CARD {r:real^3->bool | r IN c /\ aff_dim r = &3 /\ s SUBSET r} = 1` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (r:real^3->bool) /\ closed r` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_CONVEX; MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `relative_interior (r:real^3->bool) = interior r` ASSUME_TAC THENL
   [MATCH_MP_TAC RELATIVE_INTERIOR_NONEMPTY_INTERIOR THEN
    ASM_SIMP_TAC[GSYM AFF_DIM_NONEMPTY_INTERIOR_EQ; DIMINDEX_3] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN closure (relative_interior r)` MP_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `!s t:real^3->bool. s SUBSET t ==> x IN s ==> x IN t`) THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN MATCH_MP_TAC SUBSET_INTERIOR THEN
  REWRITE_TAC[SUBSET; IN_UNIONS] THEN ASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* M2. SIDES: Bd N and Bd X are unions of finite combinatorial 2-manifolds  *)
(* (the boundary complex of the derived neighbourhood complex, resp. bx),   *)
(* and the interior and the complement of N (resp. X) are the two open      *)
(* sides, both with frontier the surface (N and X are regular closed).      *)
(* ------------------------------------------------------------------------- *)

let MOI_S3MS_SIDES = prove
 (`!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool)
   (x:(real^3->bool)->bool) (bx:(real^3->bool)->bool).
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_pieces l e c x bx
     ==> (?m. FINITE m /\ combinatorial_manifold 2 m /\ UNIONS m = derived_frontier t l) /\
         (?ee. open (interior (derived_nbhd t l)) /\ open ee /\
               DISJOINT (interior (derived_nbhd t l)) ee /\
               interior (derived_nbhd t l) UNION ee = (:real^3) DIFF derived_frontier t l /\
               frontier (interior (derived_nbhd t l)) = derived_frontier t l /\
               frontier ee = derived_frontier t l) /\
         (?m. FINITE m /\ combinatorial_manifold 2 m /\ UNIONS m = frontier (UNIONS x)) /\
         (?ee. open (interior (UNIONS x)) /\ open ee /\
               DISJOINT (interior (UNIONS x)) ee /\
               interior (UNIONS x) UNION ee = (:real^3) DIFF frontier (UNIONS x) /\
               frontier (interior (UNIONS x)) = frontier (UNIONS x) /\
               frontier ee = frontier (UNIONS x))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3MS_HD_FACTS) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
    GRAPH_NBHD_BOUNDARY_EULER) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`] GRAPH_TUBE_FRONTIER_3) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(ASSUME_TAC o CONJUNCT1)] THEN
  UNDISCH_TAC `moi_s33_inv t l h e x` THEN
  REWRITE_TAC[moi_s33_inv; moi_s33_x2] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s33_pieces l e c x bx` THEN
  REWRITE_TAC[moi_s33_pieces] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [EXISTS_TAC `boundary_complex (derived_nbhd_complex t (l:(real^3->bool)->bool))` THEN
    MP_TAC(ISPEC `derived_nbhd_complex t (l:(real^3->bool)->bool)`
      BOUNDARY_COMPLEX_SURFACE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `derived_nbhd_complex t (l:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[boundary_complex] THEN SET_TAC[];
    MATCH_MP_TAC MOI_S3MS_TWO_SIDES THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPEC `derived_nbhd_complex t (l:(real^3->bool)->bool)` MOI_S3MS_REG_CLOSED) THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `bx:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_S3MS_TWO_SIDES THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; MOI_S3MS_COMPLEX_COMPACT; MOI_S3MS_REG_CLOSED]]);;

(* ------------------------------------------------------------------------- *)
(* M3. VDATA: for a vertex v of degree d + 1, an enumeration nb of its      *)
(* neighbours, PL charts G of A_v (GRAPH_TUBE_HOLED_TRACE) and G2 of A'_v   *)
(* (moi_s33_holed) from holed_disk_model d with the model frontier onto the *)
(* rims, resp. the traces, at v; rims and traces are PL circles, pairwise   *)
(* disjoint (rims by TUBE_TRIPLE, traces by the disjoint pseudo-cells).    *)
(* The statement term moi_s3ms_vdata_tm.                                    *)
(* ------------------------------------------------------------------------- *)

let moi_s3ms_vdata_tm =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool)
   (x:(real^3->bool)->bool) (v:real^3).
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_holed l e c x /\
     {v} IN l
     ==> ?d (nb:num->real^3) (G:real^2->real^3) (G':real^3->real^2)
           (G2:real^2->real^3) (G2':real^3->real^2).
           CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s} = d + 1 /\
           (!i. i <= d ==> ~(nb i = v) /\ segment[v,nb i] IN l) /\
           (!i j. i <= d /\ j <= d /\ nb i = nb j ==> i = j) /\
           (!u. ~(u = v) /\ segment[v,u] IN l ==> ?i. i <= d /\ u = nb i) /\
           pl_homeomorphism (holed_disk_model d,
                             derived_dual_cell t l v INTER derived_frontier t l) (G,G') /\
           pl_homeomorphism (holed_disk_model d,c v INTER frontier (UNIONS x)) (G2,G2') /\
           IMAGE G (frontier (holed_disk_model d)) =
           UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l (nb i) INTER
                   derived_frontier t l | i <= d} /\
           IMAGE G2 (frontier (holed_disk_model d)) =
           UNIONS {e(segment[v,nb i]) INTER frontier (UNIONS x) | i <= d} /\
           (!i. i <= d
                ==> pl_sphere 1 (derived_dual_cell t l v INTER derived_dual_cell t l (nb i) INTER
                                 derived_frontier t l) /\
                    pl_sphere 1 (e(segment[v,nb i]) INTER frontier (UNIONS x))) /\
           (!i i'. i <= d /\ i' <= d /\ ~(i = i')
                   ==> DISJOINT (derived_dual_cell t l v INTER derived_dual_cell t l (nb i) INTER
                                 derived_frontier t l)
                                (derived_dual_cell t l v INTER derived_dual_cell t l (nb i') INTER
                                 derived_frontier t l) /\
                       DISJOINT (e(segment[v,nb i]) INTER frontier (UNIONS x))
                                (e(segment[v,nb i']) INTER frontier (UNIONS x)))`;;

let MOI_S3MS_VDATA = prove
 (mk_imp(inst [`:3`,`:N`] MOI_S33_TUBE_TRIPLE, moi_s3ms_vdata_tm),
  DISCH_THEN(LABEL_TAC "triple") THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`; `v:real^3`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3MS_HD_FACTS) THEN
  SUBGOAL_THEN `!s s'. s IN l /\ s' IN l /\ aff_dim s = &1 /\ aff_dim s' = &1 /\ ~(s = s')
                       ==> DISJOINT ((e:(real^3->bool)->real^3->bool) s) (e s')`
  (LABEL_TAC "edis") THENL
   [UNDISCH_TAC `moi_s33_hd t l h e c` THEN REWRITE_TAC[moi_s33_hd] THEN STRIP_TAC THEN
    FIRST_ASSUM ACCEPT_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!u w. ~(u = w) /\ segment[u,w] IN l
                      ==> pl_sphere 1 ((e:(real^3->bool)->real^3->bool)(segment[u,w]) INTER
                                       frontier (UNIONS x))`
  (LABEL_TAC "trc") THENL
   [UNDISCH_TAC `moi_s33_inv t l h e x` THEN
    REWRITE_TAC[moi_s33_inv; moi_s33_traces] THEN STRIP_TAC THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_s33_holed l e c x` THEN REWRITE_TAC[moi_s33_holed] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `G2:real^2->real^3` (X_CHOOSE_THEN `G2':real^3->real^2`
    (X_CHOOSE_THEN `d:num` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `v:real^3`; `d:num`]
    MOI_FTH_NBRS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `nb:num->real^3` (CONJUNCTS_THEN2 (LABEL_TAC "nb1")
    (CONJUNCTS_THEN2 (LABEL_TAC "nb2") (LABEL_TAC "nb3")))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `v:real^3`; `d:num`]
    GRAPH_TUBE_HOLED_TRACE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^2->real^3` (X_CHOOSE_THEN `G':real^3->real^2`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!X:real^3->real^3->bool.
      UNIONS {X u | u | ~(u = v) /\ segment[v,u] IN l} =
      UNIONS {X ((nb:num->real^3) i) | i <= d}`
  (LABEL_TAC "IX") THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_FTH_NBR_UNIONS THEN
    USE_THEN "nb1" (fun th -> REWRITE_TAC[th]) THEN USE_THEN "nb3" ACCEPT_TAC;
    ALL_TAC] THEN
  USE_THEN "IX" (fun th ->
    RULE_ASSUM_TAC(REWRITE_RULE
     [BETA_RULE(ISPEC `\u:real^3. derived_dual_cell t l v INTER derived_dual_cell t l u INTER
                                   derived_frontier t l` th);
      BETA_RULE(ISPEC `\u:real^3. (e:(real^3->bool)->real^3->bool)(segment[v,u]) INTER
                                   frontier (UNIONS x)` th)])) THEN
  REMOVE_THEN "IX" (K ALL_TAC) THEN
  MAP_EVERY EXISTS_TAC [`d:num`; `nb:num->real^3`; `G:real^2->real^3`; `G':real^3->real^2`;
                        `G2:real^2->real^3`; `G2':real^3->real^2`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `i:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(v = (nb:num->real^3) i) /\ segment[v,nb i] IN l` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FTH_CELL_SPHERE THEN
      EXISTS_TAC `derived_dual_cell t l v INTER derived_dual_cell t l ((nb:num->real^3) i)` THEN
      REWRITE_TAC[ARITH_RULE `1 + 1 = 2`] THEN MATCH_MP_TAC MOI_FTA_CELL2 THEN
      ASM_REWRITE_TAC[];
      USE_THEN "trc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`i:num`; `i':num`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(v = (nb:num->real^3) i) /\ segment[v,nb i] IN l /\
                  ~(v = nb i') /\ segment[v,nb i'] IN l /\ ~(nb i = nb i')`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [USE_THEN "triple" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
        `v:real^3`; `(nb:num->real^3) i`; `(nb:num->real^3) i'`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_S3MS_EDGE_ENDS]; SET_TAC[]];
      USE_THEN "edis" (MP_TAC o SPECL [`segment[v:real^3,(nb:num->real^3) i]`;
                                       `segment[v:real^3,(nb:num->real^3) i']`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN MATCH_MP_TAC MOI_S3MS_SEG_NE THEN
        ASM_MESON_TAC[];
        SET_TAC[]]]]);;

(* ------------------------------------------------------------------------- *)
(* M4. PCS: the vertex set is finite, edge ends are vertices, the pieces    *)
(* A_v, A'_v are compact and locally polyhedral, meet in the rim (trace) of *)
(* their edge or not at all, cover Bd N (Bd X), and near the rim (trace) of *)
(* an edge u v the surface lies in the two pieces A_u, A_v (A'_u, A'_v).    *)
(* The statement term moi_s3ms_pcs_tm.                                      *)
(* ------------------------------------------------------------------------- *)

let moi_s3ms_pcs_tm =
 `!(t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
   (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool)
   (x:(real^3->bool)->bool).
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_holed l e c x
     ==> FINITE {v | {v} IN l} /\
         (!u v. ~(u = v) /\ segment[u,v] IN l ==> {u} IN l /\ {v} IN l) /\
         (!v. {v} IN l
              ==> compact (derived_dual_cell t l v INTER derived_frontier t l) /\
                  compact (c v INTER frontier (UNIONS x)) /\
                  locally_polyhedral (derived_dual_cell t l v INTER derived_frontier t l) /\
                  locally_polyhedral (c v INTER frontier (UNIONS x))) /\
         (!u v. {u} IN l /\ {v} IN l /\ ~(u = v)
                ==> (derived_dual_cell t l u INTER derived_frontier t l) INTER
                    (derived_dual_cell t l v INTER derived_frontier t l) =
                    (if segment[u,v] IN l
                     then derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                          derived_frontier t l
                     else {}) /\
                    (c u INTER frontier (UNIONS x)) INTER (c v INTER frontier (UNIONS x)) =
                    (if segment[u,v] IN l then e(segment[u,v]) INTER frontier (UNIONS x)
                     else {})) /\
         UNIONS {derived_dual_cell t l v INTER derived_frontier t l | v | {v} IN l} =
         derived_frontier t l /\
         UNIONS {c v INTER frontier (UNIONS x) | v | {v} IN l} = frontier (UNIONS x) /\
         (!u v. ~(u = v) /\ segment[u,v] IN l
                ==> (?U. open U /\
                         derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                         derived_frontier t l SUBSET U /\
                         derived_frontier t l INTER U SUBSET
                         (derived_dual_cell t l u INTER derived_frontier t l) UNION
                         (derived_dual_cell t l v INTER derived_frontier t l)) /\
                    (?U'. open U' /\
                          e(segment[u,v]) INTER frontier (UNIONS x) SUBSET U' /\
                          frontier (UNIONS x) INTER U' SUBSET
                          (c u INTER frontier (UNIONS x)) UNION
                          (c v INTER frontier (UNIONS x))))`;;

let MOI_S3MS_HD_C = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c
     ==> (!s s'. s IN l /\ s' IN l /\ aff_dim s = &1 /\ aff_dim s' = &1 /\ ~(s = s')
                 ==> DISJOINT (e s) (e s')) /\
         (!v. {v} IN l ==> closed (c v)) /\
         IMAGE h (derived_nbhd t l) = UNIONS {c v | {v} IN l} /\
         (!v w. {v} IN l /\ {w} IN l /\ ~(v = w)
                ==> c v INTER c w = (if segment[v,w] IN l then e(segment[v,w]) else {}))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_hd] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(fun th -> SUBST1_TAC(CONJUNCT1(MP (SPEC `v:real^3` th)
    (ASSUME `{v:real^3} IN l`)))) THEN
  REWRITE_TAC[CLOSED_CLOSURE]);;

let MOI_S3MS_SRC_COMPACT = prove
 (`!(t:(real^3->bool)->bool) l v.
     graph_in_complex t l /\ FINITE l /\ {v} IN l
     ==> compact (derived_dual_cell t l v INTER derived_frontier t l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`] GRAPH_TUBE_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
  MATCH_MP_TAC COMPACT_INTER_CLOSED THEN REWRITE_TAC[FRONTIER_CLOSED] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `v:real^3`]
    MOI_FTA_CELL3) THEN
  ASM_REWRITE_TAC[] THEN MESON_TAC[MOI_S3MS_CELL_COMPACT]);;

let MOI_S3MS_SRC_LPOLY = prove
 (`!(t:(real^3->bool)->bool) l v d.
     graph_in_complex t l /\ {v} IN l /\
     CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s} = d + 1
     ==> locally_polyhedral (derived_dual_cell t l v INTER derived_frontier t l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `v:real^3`; `d:num`]
    GRAPH_TUBE_HOLED_TRACE) THEN
  ASM_REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
  FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL));;

let MOI_S3MS_TGT_PIECE = prove
 (`!(a:real^3->bool) (X:real^3->bool) k (f:real^2->real^3) g.
     closed a /\ compact X /\
     pl_homeomorphism (holed_disk_model k, a INTER frontier X) (f,g)
     ==> compact (a INTER frontier X) /\ locally_polyhedral (a INTER frontier X)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_SIMP_TAC[COMPACT_FRONTIER];
    FIRST_ASSUM(MATCH_ACCEPT_TAC o MATCH_MP PL_MAP_ON_IMP_LOCALLY_POLYHEDRAL)]);;

let MOI_S3MS_SRC_INTER = prove
 (`!(t:(real^3->bool)->bool) l u v.
     graph_in_complex t l /\ {u} IN l /\ {v} IN l /\ ~(u = v)
     ==> (derived_dual_cell t l u INTER derived_frontier t l) INTER
         (derived_dual_cell t l v INTER derived_frontier t l) =
         (if segment[u,v] IN l
          then derived_dual_cell t l u INTER derived_dual_cell t l v INTER
               derived_frontier t l
          else {})`,
  REPEAT STRIP_TAC THEN COND_CASES_TAC THENL
   [SET_TAC[];
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
      MOI_FTA_CELLS_DISJOINT) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]]);;

let MOI_S3MS_TGT_INTER = prove
 (`!(c:real^3->real^3->bool) (e:(real^3->bool)->real^3->bool) b u v l.
     c u INTER c v = (if segment[u,v] IN l then e(segment[u,v]) else {})
     ==> (c u INTER b) INTER (c v INTER b) =
         (if segment[u,v] IN l then e(segment[u,v]) INTER b else {})`,
  REPEAT GEN_TAC THEN COND_CASES_TAC THEN DISCH_TAC THEN ASM SET_TAC[]);;

let MOI_S3MS_SRC_COVER = prove
 (`!(t:(real^3->bool)->bool) l.
     graph_in_complex t l /\ FINITE l
     ==> UNIONS {derived_dual_cell t l v INTER derived_frontier t l | v | {v} IN l} =
         derived_frontier t l`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `derived_frontier t l SUBSET
                UNIONS {derived_dual_cell t l v | v | {v:real^3} IN l}` MP_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
      GRAPH_TUBE_DUAL_CELLS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
      GRAPH_TUBE_FRONTIER_3) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`] DERIVED_NBHD_BASIC) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [graph_in_complex]) THEN
    ASM_SIMP_TAC[];
    SET_TAC[]]);;

let MOI_S3MS_PCS = prove
 (mk_imp(inst [`:3`,`:N`] MOI_S33_TUBE_TRIPLE, moi_s3ms_pcs_tm),
  DISCH_THEN(LABEL_TAC "triple") THEN
  MAP_EVERY X_GEN_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                       `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3MS_HD_FACTS) THEN
  SUBGOAL_THEN `compact (UNIONS (x:(real^3->bool)->bool)) /\
                UNIONS x SUBSET IMAGE (h:real^3->real^3) (derived_nbhd t l)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_inv t l h e x` THEN REWRITE_TAC[moi_s33_inv; moi_s33_x2] THEN
    STRIP_TAC THEN ASM_SIMP_TAC[MOI_S3MS_COMPLEX_COMPACT] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!v. {v} IN l
        ==> ?d. CARD {s | s IN l /\ aff_dim s = &1 /\ v IN s} = d + 1 /\
                ?(f:real^2->real^3) g.
                  pl_homeomorphism (holed_disk_model d,
                                    (c:real^3->real^3->bool) v INTER frontier (UNIONS x))
                                   (f,g)`
  (LABEL_TAC "hol") THENL
   [UNDISCH_TAC `moi_s33_holed l e c x` THEN REWRITE_TAC[moi_s33_holed] THEN MESON_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3MS_HD_C) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "edis") (CONJUNCTS_THEN2 (LABEL_TAC "cclo")
    (CONJUNCTS_THEN2 (LABEL_TAC "ccov") (LABEL_TAC "cint")))) THEN
  SUBGOAL_THEN `UNIONS {(c:real^3->real^3->bool) v INTER frontier (UNIONS x) | v | {v} IN l} =
                frontier (UNIONS x)` (LABEL_TAC "tcov") THENL
   [SUBGOAL_THEN `frontier (UNIONS x) SUBSET UNIONS {(c:real^3->real^3->bool) v | {v} IN l}`
    MP_TAC THENL
     [USE_THEN "ccov" (SUBST1_TAC o SYM) THEN MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `UNIONS (x:(real^3->bool)->bool)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED];
        FIRST_ASSUM ACCEPT_TAC];
      SET_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3MS_FINITE_VERTS THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3MS_EDGE_ENDS THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "hol" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `f:real^2->real^3` (X_CHOOSE_TAC `g:real^3->real^2`)))) THEN
    MP_TAC(ISPECL [`(c:real^3->real^3->bool) v`; `UNIONS (x:(real^3->bool)->bool)`;
                   `d:num`; `f:real^2->real^3`; `g:real^3->real^2`] MOI_S3MS_TGT_PIECE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "cclo" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3MS_SRC_COMPACT THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3MS_SRC_LPOLY THEN EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[]];
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3MS_SRC_INTER THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3MS_TGT_INTER THEN USE_THEN "cint" MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_S3MS_SRC_COVER THEN ASM_REWRITE_TAC[];
    USE_THEN "tcov" ACCEPT_TAC;
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    SUBGOAL_THEN `{u:real^3} IN l /\ {v} IN l` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S3MS_EDGE_ENDS THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [MP_TAC(BETA_RULE(ISPECL
       [`\w:real^3. {w} IN l`;
        `\w:real^3. derived_dual_cell t l w INTER derived_frontier t (l:(real^3->bool)->bool)`;
        `derived_frontier t (l:(real^3->bool)->bool)`;
        `derived_dual_cell t l u INTER derived_dual_cell t l v INTER
         derived_frontier t (l:(real^3->bool)->bool)`;
        `u:real^3`; `v:real^3`] MOI_S3MS_NBHD)) THEN
      ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S3MS_FINITE_VERTS THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MATCH_MP_TAC MOI_S3MS_SRC_COMPACT THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC MOI_S3MS_SRC_COVER THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
        USE_THEN "triple" (MP_TAC o SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
          `u:real^3`; `v:real^3`; `w:real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; SET_TAC[]]];
      MP_TAC(BETA_RULE(ISPECL
       [`\w:real^3. {w} IN l`;
        `\w:real^3. (c:real^3->real^3->bool) w INTER frontier (UNIONS x)`;
        `frontier (UNIONS (x:(real^3->bool)->bool))`;
        `(e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER frontier (UNIONS x)`;
        `u:real^3`; `v:real^3`] MOI_S3MS_NBHD)) THEN
      ANTS_TAC THENL [ALL_TAC; REWRITE_TAC[]] THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_S3MS_FINITE_VERTS THEN ASM_REWRITE_TAC[];
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC CLOSED_INTER THEN
        REWRITE_TAC[FRONTIER_CLOSED] THEN USE_THEN "cclo" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        USE_THEN "tcov" ACCEPT_TAC;
        X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
        SUBGOAL_THEN `~(u:real^3 = w) /\ ~(v = w)` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        SUBGOAL_THEN `(c:real^3->real^3->bool) u INTER c v = e(segment[u,v])` ASSUME_TAC THENL
         [USE_THEN "cint" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
          ALL_TAC] THEN
        SUBGOAL_THEN `DISJOINT ((e:(real^3->bool)->real^3->bool)(segment[u,v]))
                               ((c:real^3->real^3->bool) u INTER c w)` ASSUME_TAC THENL
         [USE_THEN "cint" (MP_TAC o SPECL [`u:real^3`; `w:real^3`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
          COND_CASES_TAC THEN REWRITE_TAC[DISJOINT_EMPTY] THEN
          USE_THEN "edis" MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
          MATCH_MP_TAC MOI_S3MS_SEG_NE THEN ASM_MESON_TAC[];
          ALL_TAC] THEN
        UNDISCH_TAC `DISJOINT ((e:(real^3->bool)->real^3->bool)(segment[u,v]))
                              ((c:real^3->real^3->bool) u INTER c w)` THEN
        UNDISCH_TAC `(c:real^3->real^3->bool) u INTER c v = e(segment[u,v])` THEN
        SET_TAC[]]]]);;

