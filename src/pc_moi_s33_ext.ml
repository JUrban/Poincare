needs "src/pc_moi_s33_stmt.ml";;
needs "src/pc_moi_fnd_tubea.ml";;
needs "src/pc_moi_cone.ml";;
needs "src/pc_moi_s26_sep.ml";;
needs "src/pc_moi_sch3_push.ml";;
needs "src/pc_moi_fnd_m3a.ml";;
needs "src/pc_moi_cells.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* pc_moi_s33_ext: Moise 33.1, proof of Theorem 1 continued (p.238).  Main  *)
(* theorem S33_EXT : |- MOI_S33_EXT.  The extension of the boundary         *)
(* match g over the dual cells: PL disks F_e replacing the traces near the  *)
(* centres (32.4, DISK_RECOG), cone extensions over the splitting disks, PL *)
(* Schoenflies balls B_v bounded by the image spheres, and the topology     *)
(* showing that the B_v meet only along the F_e, cover int X and lie in the *)
(* pieces c v up to small balls at the centres.                             *)
(* ========================================================================= *)

(* 26.6, from pc_moi_s26_cross, pc_moi_s26_local and pc_moi_s26_sep (as     *)
(* MOI_CST_266 of pc_moi_core_status).                                      *)

let MOI_S3XT_266 = prove
 (`MOISE_266_STATEMENT`,
  ACCEPT_TAC(MP SEP_266 (CONJ EVEN_CROSSING (CONJ LOCAL_TRI LOCAL_EDGE))));;

(* ========================================================================= *)
(* Part 1: basic facts.  FINITE_RADIUS: a radius good for each of            *)
(* finitely many points (for a property inherited by smaller radii) is good *)
(* for all of them.  EDGE_VERTICES: the ends of an edge of l are vertices of *)
(* l.  HD_EDGE: the pseudo-cell of an edge lies in the pieces of its ends,   *)
(* contains its centre (a point of K'), is compact, and misses the other     *)
(* pieces.                                                                    *)
(* ========================================================================= *)

let MOI_S3XT_FINITE_RADIUS = prove
 (`!(s:A->bool) (P:A->real->bool).
     FINITE s /\ (!x r r'. P x r /\ &0 < r' /\ r' <= r ==> P x r') /\
     (!x. x IN s ==> ?r. &0 < r /\ P x r)
     ==> ?r. &0 < r /\ !x. x IN s ==> P x r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_CASES_TAC `s:A->bool = {}` THENL
   [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[NOT_IN_EMPTY; REAL_LT_01]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE BINDER_CONV [RIGHT_IMP_EXISTS_THM]) THEN
  REWRITE_TAC[SKOLEM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:A->real` (LABEL_TAC "r")) THEN
  EXISTS_TAC `inf (IMAGE (r:A->real) s)` THEN
  SUBGOAL_THEN `FINITE (IMAGE (r:A->real) s) /\ ~(IMAGE (r:A->real) s = {})`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[FINITE_IMAGE; IMAGE_EQ_EMPTY]; ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_INF_FINITE; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `x:A` THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `(r:A->real) x` THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    ASM_SIMP_TAC[REAL_LT_INF_FINITE; FORALL_IN_IMAGE] THEN ASM_MESON_TAC[];
    ASM_MESON_TAC[INF_FINITE; FUN_IN_IMAGE]]);;

let MOI_S3XT_EDGE_VERTICES = prove
 (`!(t:(real^3->bool)->bool) l u v.
     graph_in_complex t l /\ ~(u = v) /\ segment[u,v] IN l
     ==> {u} IN l /\ {v} IN l /\ aff_dim(segment[u,v]) = &1`,
  REPEAT GEN_TAC THEN REWRITE_TAC[graph_in_complex; simplicial_subcomplex] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `segment[u:real^3,v]` THEN
  ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

let MOI_S3XT_HD_EDGE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c u v.
     moi_s33_hd t l h e c /\ compact (IMAGE h (derived_nbhd t l)) /\
     ~(u = v) /\ segment[u,v] IN l
     ==> {u} IN l /\ {v} IN l /\ aff_dim(segment[u,v]) = &1 /\
         e(segment[u,v]) SUBSET c u /\ e(segment[u,v]) SUBSET c v /\
         c u INTER c v = e(segment[u,v]) /\
         compact (e(segment[u,v])) /\
         h(midpoint(u,v)) IN e(segment[u,v]) /\
         h(midpoint(u,v)) IN IMAGE h (UNIONS l) /\
         (!w. {w} IN l /\ ~(w = u) /\ ~(w = v) ==> c w INTER e(segment[u,v]) = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_hd] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pc")
     (CONJUNCTS_THEN2 (LABEL_TAC "dj") (CONJUNCTS_THEN2 (K ALL_TAC)
       (CONJUNCTS_THEN2 (LABEL_TAC "cover") (LABEL_TAC "cc"))))))
   STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `graph_in_complex (t:(real^3->bool)->bool) l` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s33_tube]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3XT_EDGE_VERTICES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(c:real^3->real^3->bool) u INTER c v = e(segment[u,v])` ASSUME_TAC THENL
   [USE_THEN "cc" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  USE_THEN "pc" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pseudo_cell] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:real^3->real^3->bool) u SUBSET IMAGE (h:real^3->real^3) (derived_nbhd t l)`
  ASSUME_TAC THENL
   [USE_THEN "cover" SUBST1_TAC THEN REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    EXISTS_TAC `(c:real^3->real^3->bool) u` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `u:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(c:real^3->real^3->bool) u INTER c v = e(segment[u,v])` THEN SET_TAC[];
    UNDISCH_TAC `(c:real^3->real^3->bool) u INTER c v = e(segment[u,v])` THEN SET_TAC[];
    REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN
      EXISTS_TAC `IMAGE (h:real^3->real^3) (derived_nbhd t l)` THEN CONJ_TAC THENL
       [MATCH_MP_TAC COMPACT_IMP_BOUNDED THEN FIRST_ASSUM ACCEPT_TAC;
        MAP_EVERY UNDISCH_TAC
         [`(c:real^3->real^3->bool) u INTER c v = e(segment[u,v])`;
          `(c:real^3->real^3->bool) u SUBSET IMAGE (h:real^3->real^3) (derived_nbhd t l)`] THEN
        SET_TAC[]];
      UNDISCH_TAC `closure((e:(real^3->bool)->real^3->bool)(segment[u,v]) DIFF
                           moi_s33_rim t l h u v) = e(segment[u,v])` THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      REWRITE_TAC[CLOSED_CLOSURE]];
    UNDISCH_TAC `(h:real^3->real^3)(midpoint(u,v)) IN
                 (e:(real^3->bool)->real^3->bool)(segment[u,v]) DIFF moi_s33_rim t l h u v` THEN
    SET_TAC[];
    MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `segment[u:real^3,v]` THEN ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
    X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    USE_THEN "cc" (MP_TAC o SPECL [`w:real^3`; `u:real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    COND_CASES_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `DISJOINT (e(segment[w:real^3,u]):real^3->bool) (e(segment[u,v]))`
      MP_TAC THENL
       [USE_THEN "dj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT; SEGMENT_EQ] THEN
        REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`(c:real^3->real^3->bool) w INTER c u = e(segment[w,u])`;
          `(c:real^3->real^3->bool) u INTER c v = e(segment[u,v])`] THEN
        SET_TAC[]];
      DISCH_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`(c:real^3->real^3->bool) w INTER c u = {}`;
        `(c:real^3->real^3->bool) u INTER c v = e(segment[u,v])`] THEN
      SET_TAC[]]]);;

let MOI_S3XT_FINITE_RADIUS2 = prove
 (`!(s:A#B->bool) (P:A->B->real->bool).
     FINITE s /\ (!x y r r'. P x y r /\ &0 < r' /\ r' <= r ==> P x y r') /\
     (!x y. (x,y) IN s ==> ?r. &0 < r /\ P x y r)
     ==> ?r. &0 < r /\ !x y. (x,y) IN s ==> P x y r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:A#B->bool`; `\(z:A#B) (r:real). (P:A->B->real->bool) (FST z) (SND z) r`]
    MOI_S3XT_FINITE_RADIUS) THEN
  REWRITE_TAC[FORALL_PAIR_THM; FST; SND] THEN ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; REWRITE_TAC[]]);;

(* Pieces are closed; pseudo-cells of distinct edges are disjoint. *)

let MOI_S3XT_HD_MISC = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c
     ==> (!w. {w} IN l ==> closed((c:real^3->real^3->bool) w)) /\
         (!u v u' v'. ~(u = v) /\ segment[u,v] IN l /\ ~(u' = v') /\ segment[u',v'] IN l /\
                      ~(segment[u',v'] = segment[u,v])
                      ==> DISJOINT (e(segment[u,v]):real^3->bool) (e(segment[u',v'])))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `graph_in_complex (t:(real^3->bool)->bool) l` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_s33_hd; moi_s33_tube]; ALL_TAC] THEN
  UNDISCH_TAC `moi_s33_hd (t:(real^3->bool)->bool) l h e c` THEN REWRITE_TAC[moi_s33_hd] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
    (CONJUNCTS_THEN2 (LABEL_TAC "dj") (CONJUNCTS_THEN2 (LABEL_TAC "cv") (K ALL_TAC))))) THEN
  CONJ_TAC THENL
   [X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "cv" (MP_TAC o SPEC `w:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN REWRITE_TAC[CLOSED_CLOSURE];
    REPEAT STRIP_TAC THEN USE_THEN "dj" MATCH_MP_TAC THEN
    ASM_MESON_TAC[MOI_S3XT_EDGE_VERTICES]]);;

(* The radius rho of the construction: the 2 rho balls at the centres lie in *)
(* int X, miss the other pseudo-cells and the pieces not at the edge, and   *)
(* the centres are 3 rho apart; 2 rho < d.                                   *)

let MOI_S3XT_RADIUS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (X:real^3->bool) d.
     moi_s33_hd t l h e c /\ compact (IMAGE h (derived_nbhd t l)) /\ FINITE l /\
     IMAGE h (UNIONS l) SUBSET interior X /\ &0 < d
     ==> ?rho. &0 < rho /\ &2 * rho < d /\
           !u v. ~(u = v) /\ segment[u,v] IN l
                 ==> ball(h(midpoint(u,v)),&2 * rho) SUBSET interior X /\
                     (!u' v'. ~(u' = v') /\ segment[u',v'] IN l /\
                              ~(segment[u',v'] = segment[u,v])
                              ==> ball(h(midpoint(u,v)),&2 * rho) INTER
                                  e(segment[u',v']) = {} /\
                                  &3 * rho <= dist(h(midpoint(u,v)),h(midpoint(u',v')))) /\
                     (!w. {w} IN l /\ ~(w = u) /\ ~(w = v)
                          ==> ball(h(midpoint(u,v)),&2 * rho) INTER c w = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {x:real^3 | {x} IN l}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `S2 = {(u,v) | ~(u = v) /\ segment[u:real^3,v] IN l}` THEN
  SUBGOAL_THEN `FINITE (S2:real^3#real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(u:real^3,v:real^3) | u IN {x | {x} IN l} /\ v IN {x | {x} IN l}}` THEN
    ASM_SIMP_TAC[FINITE_PRODUCT] THEN
    EXPAND_TAC "S2" THEN REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; IN_ELIM_PAIR_THM] THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `u:real^3`; `v:real^3`] MOI_S3XT_HD_EDGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL
   [`S2:real^3#real^3->bool`;
    `\(u:real^3) (v:real^3) (r:real).
       ball((h:real^3->real^3)(midpoint(u,v)),r) SUBSET interior X /\
       (!u' v'. ~(u' = v') /\ segment[u',v'] IN l /\ ~(segment[u',v'] = segment[u,v])
                ==> ball(h(midpoint(u,v)),r) INTER
                    (e:(real^3->bool)->real^3->bool)(segment[u',v']) = {} /\
                    r <= dist(h(midpoint(u,v)),h(midpoint(u',v')))) /\
       (!w. {w} IN l /\ ~(w = u) /\ ~(w = v)
            ==> ball(h(midpoint(u,v)),r) INTER (c:real^3->real^3->bool) w = {})`]
    MOI_S3XT_FINITE_RADIUS2) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`; `r:real`; `r':real`] THEN
      DISCH_THEN(CONJUNCTS_THEN2
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pe") (LABEL_TAC "pw")))
        STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `ball((h:real^3->real^3)(midpoint(u,v)),r') SUBSET ball(h(midpoint(u,v)),r)`
      ASSUME_TAC THENL [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[];
        MAP_EVERY X_GEN_TAC [`u':real^3`; `v':real^3`] THEN DISCH_TAC THEN
        USE_THEN "pe" (MP_TAC o SPECL [`u':real^3`; `v':real^3`]) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN CONJ_TAC THENL
         [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        USE_THEN "pw" (MP_TAC o SPEC `w:real^3`) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]]];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN EXPAND_TAC "S2" THEN
    REWRITE_TAC[IN_ELIM_PAIR_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `u:real^3`; `v:real^3`] MOI_S3XT_HD_EDGE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
      MOI_S3XT_HD_MISC) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "cl") (LABEL_TAC "dis")) THEN
    ABBREV_TAC `p = (h:real^3->real^3)(midpoint(u,v))` THEN
    SUBGOAL_THEN `(p:real^3) IN interior X` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior X`;
                             `(p:real^3) IN IMAGE (h:real^3->real^3) (UNIONS l)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `interior X:real^3->bool` OPEN_CONTAINS_BALL) THEN
    REWRITE_TAC[OPEN_INTERIOR] THEN DISCH_THEN(MP_TAC o SPEC `p:real^3`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL
     [`S2:real^3#real^3->bool`;
      `\(u':real^3) (v':real^3) (r:real).
         ~(segment[u',v'] = segment[u:real^3,v])
         ==> ball(p:real^3,r) INTER (e:(real^3->bool)->real^3->bool)(segment[u',v']) = {} /\
             r <= dist(p,(h:real^3->real^3)(midpoint(u',v')))`]
      MOI_S3XT_FINITE_RADIUS2) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`; `r:real`; `r':real`] THEN
        STRIP_TAC THEN DISCH_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
        STRIP_TAC THEN CONJ_TAC THENL
         [SUBGOAL_THEN `ball(p:real^3,r') SUBSET ball(p,r)` MP_TAC THENL
           [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; ASM SET_TAC[]];
          ASM_REAL_ARITH_TAC];
        MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN EXPAND_TAC "S2" THEN
        REWRITE_TAC[IN_ELIM_PAIR_THM] THEN STRIP_TAC THEN
        ASM_CASES_TAC `segment[a:real^3,b] = segment[u,v]` THENL
         [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01]; ALL_TAC] THEN
        MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                       `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                       `a:real^3`; `b:real^3`] MOI_S3XT_HD_EDGE) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
        MP_TAC(ISPECL [`(e:(real^3->bool)->real^3->bool)(segment[a,b])`; `p:real^3`]
          SEPARATE_POINT_CLOSED) THEN
        ANTS_TAC THENL
         [ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
          USE_THEN "dis" (MP_TAC o SPECL [`u:real^3`; `v:real^3`; `a:real^3`; `b:real^3`]) THEN
          ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
          UNDISCH_TAC `(p:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[u,v])` THEN
          SET_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `r2:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [REWRITE_TAC[EXTENSION; IN_INTER; IN_BALL; NOT_IN_EMPTY] THEN
          X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
          FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
          ASM_REAL_ARITH_TAC;
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r2"))) THEN
    MP_TAC(ISPECL
     [`{x:real^3 | {x} IN l}`;
      `\(w:real^3) (r:real).
         ~(w = u) /\ ~(w = v) ==> ball(p:real^3,r) INTER (c:real^3->real^3->bool) w = {}`]
      MOI_S3XT_FINITE_RADIUS) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`w:real^3`; `r:real`; `r':real`] THEN
        STRIP_TAC THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `ball(p:real^3,r') SUBSET ball(p,r)` MP_TAC THENL
         [MATCH_MP_TAC SUBSET_BALL THEN ASM_REWRITE_TAC[]; SET_TAC[]];
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        ASM_CASES_TAC `w:real^3 = u \/ w = v` THENL
         [EXISTS_TAC `&1` THEN ASM_REWRITE_TAC[REAL_LT_01] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
        MP_TAC(ISPECL [`(c:real^3->real^3->bool) w`; `p:real^3`] SEPARATE_POINT_CLOSED) THEN
        ANTS_TAC THENL
         [CONJ_TAC THENL [USE_THEN "cl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          SUBGOAL_THEN `~(w:real^3 = u) /\ ~(w = v)` STRIP_ASSUME_TAC THENL
           [ASM_MESON_TAC[]; ALL_TAC] THEN
          SUBGOAL_THEN `(c:real^3->real^3->bool) w INTER (e:(real^3->bool)->real^3->bool)(segment[u,v]) = {}` MP_TAC THENL
           [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
          UNDISCH_TAC `(p:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[u,v])` THEN
          SET_TAC[];
          ALL_TAC] THEN
        DISCH_THEN(X_CHOOSE_THEN `r3:real` STRIP_ASSUME_TAC) THEN
        EXISTS_TAC `r3:real` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        REWRITE_TAC[EXTENSION; IN_INTER; IN_BALL; NOT_IN_EMPTY] THEN
        X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r3:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r3"))) THEN
    EXISTS_TAC `min r1 (min r2 r3)` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `ball(p:real^3,min r1 (min r2 r3)) SUBSET ball(p,r1) /\
                  ball(p:real^3,min r1 (min r2 r3)) SUBSET ball(p,r2) /\
                  ball(p:real^3,min r1 (min r2 r3)) SUBSET ball(p,r3)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN STRIP_TAC THEN
      USE_THEN "r2" (MP_TAC o SPECL [`a:real^3`; `b:real^3`]) THEN
      ANTS_TAC THENL [EXPAND_TAC "S2" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN ASM_REWRITE_TAC[];
                      ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
      X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      USE_THEN "r3" (MP_TAC o SPEC `w:real^3`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r0:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "r0"))) THEN
  EXISTS_TAC `min (r0 / &3) (d / &3)` THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  USE_THEN "r0" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN
  ANTS_TAC THENL [EXPAND_TAC "S2" THEN REWRITE_TAC[IN_ELIM_PAIR_THM] THEN ASM_REWRITE_TAC[];
                  ALL_TAC] THEN
  SUBGOAL_THEN
   `ball((h:real^3->real^3)(midpoint(u,v)),&2 * min (r0 / &3) (d / &3)) SUBSET
    ball(h(midpoint(u,v)),r0)`
  ASSUME_TAC THENL [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pe") (LABEL_TAC "pw"))) THEN
  REPEAT CONJ_TAC THENL
   [ASM SET_TAC[];
    MAP_EVERY X_GEN_TAC [`u':real^3`; `v':real^3`] THEN DISCH_TAC THEN
    USE_THEN "pe" (MP_TAC o SPECL [`u':real^3`; `v':real^3`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ASM_REAL_ARITH_TAC];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
    USE_THEN "pw" (MP_TAC o SPEC `w:real^3`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ASM SET_TAC[]]]);;

(* ========================================================================= *)
(* Part 2: topological disks.  CIRCLE_EXT: a homeomorphism of the unit      *)
(* circle extends to one of the unit disk (JORDAN_SCHOENFLIES).  HOMEO_RI:  *)
(* homeomorphisms between sets of equal affine dimension preserve relative  *)
(* interiors.  CELL2_DISK: a PL 2-cell is a topological disk with the same  *)
(* boundary.  DISK_SWAP: two disks with a common boundary are homeomorphic  *)
(* by a map fixing the boundary.  DISK_REPLACE: replacing a subdisk (inside *)
(* a disk, off its boundary) by another disk with the same boundary that    *)
(* meets the big disk only there gives a disk with the old boundary.        *)
(* ========================================================================= *)

let MOI_S3XT_CIRCLE_EXT = prove
 (`!(w:real^2->real^2) w'.
     homeomorphism (sphere(vec 0,&1),sphere(vec 0,&1)) (w,w')
     ==> ?r r'. homeomorphism (cball(vec 0,&1),cball(vec 0,&1)) (r,r') /\
                (!x. x IN sphere(vec 0,&1) ==> r x = w x)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`circlepath(vec 0:real^2,&1)`; `circlepath(vec 0:real^2,&1)`;
                 `w:real^2->real^2`; `w':real^2->real^2`] JORDAN_SCHOENFLIES) THEN
  ASM_SIMP_TAC[SIMPLE_PATH_CIRCLEPATH; PATH_IMAGE_CIRCLEPATH; REAL_POS; REAL_OF_NUM_EQ;
               ARITH_EQ; INSIDE_SPHERE] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^2->real^2` (X_CHOOSE_THEN `k':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`k:real^2->real^2`; `k':real^2->real^2`] THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
  MAP_EVERY EXISTS_TAC [`(:real^2)`; `(:real^2)`] THEN ASM_REWRITE_TAC[SUBSET_UNIV] THEN
  SUBGOAL_THEN `cball(vec 0:real^2,&1) = ball(vec 0,&1) UNION sphere(vec 0,&1)`
  SUBST1_TAC THENL
   [MP_TAC(ISPECL [`vec 0:real^2`; `&1`] CBALL_DIFF_BALL) THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `&1`] BALL_SUBSET_CBALL) THEN SET_TAC[];
    ASM_REWRITE_TAC[IMAGE_UNION]]);;

let MOI_S3XT_HOMEO_RI = prove
 (`!(f:real^M->real^N) g s t.
     homeomorphism (s,t) (f,g) /\ aff_dim s = aff_dim t
     ==> IMAGE f (relative_interior s) = relative_interior t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`f:real^M->real^N`; `s:real^M->bool`; `t:real^N->bool`]
      CONTINUOUS_IMAGE_SUBSET_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; INT_LE_REFL] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    MP_TAC(ISPECL [`g:real^N->real^M`; `t:real^N->bool`; `s:real^M->bool`]
      CONTINUOUS_IMAGE_SUBSET_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[SUBSET_REFL; INT_LE_REFL] THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[]]);;

let MOI_S3XT_CELL2_DISK = prove
 (`!(a:real^N->bool) j. pl_cell_with_boundary 2 a j ==> disk_with_boundary a j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `f':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ compact k /\ aff_dim k = &2` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`cball(vec 0:real^2,&1)`; `k:real^N->bool`]
    HOMEOMORPHIC_CONVEX_COMPACT_SETS) THEN
  ASM_REWRITE_TAC[CONVEX_CBALL; COMPACT_CBALL; AFF_DIM_CBALL; REAL_LT_01; DIMINDEX_2] THEN
  REWRITE_TAC[homeomorphic] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^2->real^N` (X_CHOOSE_THEN `p':real^N->real^2`
    ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`p:real^2->real^N`; `p':real^N->real^2`; `cball(vec 0:real^2,&1)`;
                 `k:real^N->bool`] MOI_S3XT_HOMEO_RI) THEN
  ASM_REWRITE_TAC[AFF_DIM_CBALL; REAL_LT_01; DIMINDEX_2; RELATIVE_INTERIOR_CBALL;
                  REAL_OF_NUM_EQ; ARITH_EQ] THEN
  DISCH_TAC THEN REWRITE_TAC[disk_with_boundary] THEN
  MAP_EVERY EXISTS_TAC [`(f:real^N->real^N) o (p:real^2->real^N)`;
                        `(p':real^N->real^2) o (f':real^N->real^N)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[IMAGE_o] THEN AP_TERM_TAC THEN
  REWRITE_TAC[relative_frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
  UNDISCH_TAC `homeomorphism (cball(vec 0:real^2,&1),(k:real^N->bool))
                             (p:real^2->real^N,p')` THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] CBALL_DIFF_BALL) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] BALL_SUBSET_CBALL) THEN
  UNDISCH_TAC `IMAGE (p:real^2->real^N) (ball(vec 0,&1)) = relative_interior k` THEN
  ASM SET_TAC[]);;

let MOI_S3XT_DISK_SWAP = prove
 (`!(d:real^N->bool) a j.
     disk_with_boundary d j /\ disk_with_boundary a j
     ==> ?q q'. homeomorphism (d,a) (q,q') /\ (!x. x IN j ==> q x = x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[disk_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `f':real^N->real^2`
      (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))))
    (X_CHOOSE_THEN `g:real^2->real^N` (X_CHOOSE_THEN `g':real^N->real^2`
      (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM))))) THEN
  SUBGOAL_THEN `(j:real^N->bool) SUBSET d /\ j SUBSET a` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`homeomorphism (cball(vec 0:real^2,&1),(d:real^N->bool)) (f:real^2->real^N,f')`;
      `homeomorphism (cball(vec 0:real^2,&1),(a:real^N->bool)) (g:real^2->real^N,g')`] THEN
    REWRITE_TAC[homeomorphism] THEN REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_SUBSET_CBALL) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homeomorphism (sphere(vec 0:real^2,&1),sphere(vec 0,&1))
                  ((g':real^N->real^2) o (f:real^2->real^N),
                   (f':real^N->real^2) o (g:real^2->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `j:real^N->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`cball(vec 0:real^2,&1)`; `d:real^N->bool`] THEN
      ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`cball(vec 0:real^2,&1)`; `a:real^N->bool`] THEN
      ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL]];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_S3XT_CIRCLE_EXT) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^2->real^2` (X_CHOOSE_THEN `r':real^2->real^2`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`(g:real^2->real^N) o (r:real^2->real^2) o (f':real^N->real^2)`;
                        `((f:real^2->real^N) o (r':real^2->real^2)) o (g':real^N->real^2)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
  MAP_EVERY UNDISCH_TAC
   [`homeomorphism (cball(vec 0:real^2,&1),(d:real^N->bool)) (f:real^2->real^N,f')`;
    `homeomorphism (cball(vec 0:real^2,&1),(a:real^N->bool)) (g:real^2->real^N,g')`] THEN
  REWRITE_TAC[homeomorphism] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(f':real^N->real^2) x IN sphere(vec 0,&1)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_SUBSET_CBALL) THEN
    MAP_EVERY UNDISCH_TAC
     [`IMAGE (f:real^2->real^N) (sphere(vec 0,&1)) = j`;
      `!x. x IN cball(vec 0:real^2,&1) ==> (f':real^N->real^2)(f x) = x`;
      `(x:real^N) IN j`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^2->real^2)((f':real^N->real^2) x) =
                ((g':real^N->real^2) o (f:real^2->real^N)) (f' x)` SUBST1_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^2->real^N)(f' x) = x /\ (g:real^2->real^N)(g' x) = x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
    MAP_EVERY UNDISCH_TAC [`(j:real^N->bool) SUBSET d`; `(j:real^N->bool) SUBSET a`;
                           `(x:real^N) IN j`] THEN
    SET_TAC[];
    ASM_REWRITE_TAC[o_THM]]);;

let MOI_S3XT_DISK_FACTS = prove
 (`!(d:real^N->bool) j. disk_with_boundary d j ==> j SUBSET d /\ compact d /\ compact j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[disk_with_boundary; homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (IMAGE (f:real^2->real^N) (cball(vec 0,&1))) /\
                compact (IMAGE (f:real^2->real^N) (sphere(vec 0,&1)))`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN
    REWRITE_TAC[COMPACT_CBALL; COMPACT_SPHERE] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
    ASM_REWRITE_TAC[SPHERE_SUBSET_CBALL];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_SUBSET_CBALL) THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^N) (cball(vec 0,&1)) = d` THEN SET_TAC[]);;

let MOI_S3XT_DISK_REPLACE = prove
 (`!(dk:real^N->bool) t dd jj a.
     disk_with_boundary dk t /\ disk_with_boundary dd jj /\ disk_with_boundary a jj /\
     dd SUBSET dk /\ dd INTER t = {} /\ a INTER dk = jj
     ==> disk_with_boundary ((dk DIFF (dd DIFF jj)) UNION a) t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`dd:real^N->bool`; `a:real^N->bool`; `jj:real^N->bool`]
    MOI_S3XT_DISK_SWAP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->real^N` (X_CHOOSE_THEN `q':real^N->real^N`
    (CONJUNCTS_THEN2 MP_TAC (LABEL_TAC "qj")))) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(jj:real^N->bool) SUBSET dd /\ compact (dd:real^N->bool) /\
                compact (a:real^N->bool) /\ compact (dk:real^N->bool) /\
                (t:real^N->bool) SUBSET dk`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3XT_DISK_FACTS]; ALL_TAC] THEN
  UNDISCH_TAC `disk_with_boundary (dk:real^N->bool) t` THEN
  UNDISCH_TAC `disk_with_boundary (dd:real^N->bool) jj` THEN
  REWRITE_TAC[disk_with_boundary] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^2->real^N` (X_CHOOSE_THEN `s':real^N->real^2`
    (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism])
                     (ASSUME_TAC o SYM)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `f':real^N->real^2`
    (CONJUNCTS_THEN2
      (fun th -> ASSUME_TAC th THEN STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism] th))
      (ASSUME_TAC o SYM)))) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_SUBSET_CBALL) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] BALL_SUBSET_CBALL) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] CBALL_DIFF_BALL) THEN
  REPEAT DISCH_TAC THEN
  (* the interior of dd is the image of an open subset u of the parameter disk *)
  ABBREV_TAC `u = IMAGE ((f':real^N->real^2) o (s:real^2->real^N)) (ball(vec 0,&1))` THEN
  SUBGOAL_THEN `IMAGE (s:real^2->real^N) (ball(vec 0,&1)) = dd DIFF jj` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE (s:real^2->real^N) (cball(vec 0,&1)) = dd`;
      `IMAGE (s:real^2->real^N) (sphere(vec 0,&1)) = jj`;
      `!x. x IN cball(vec 0:real^2,&1) ==> (s':real^N->real^2)(s x) = x`;
      `cball(vec 0:real^2,&1) DIFF ball(vec 0,&1) = sphere(vec 0,&1)`;
      `ball(vec 0:real^2,&1) SUBSET cball(vec 0,&1)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (u:real^2->bool) /\ u SUBSET cball(vec 0,&1) /\
                IMAGE (f:real^2->real^N) u = dd DIFF jj`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "u" THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
         [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
          ASM_REWRITE_TAC[];
          MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `dk:real^N->bool` THEN
          ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
        REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
        STRIP_TAC THEN
        SUBGOAL_THEN `(s:real^2->real^N) x = s y` MP_TAC THENL
         [SUBGOAL_THEN `(s:real^2->real^N) x IN dk /\ s y IN dk` STRIP_ASSUME_TAC THENL
           [ASM SET_TAC[]; ASM_MESON_TAC[]];
          ASM_MESON_TAC[SUBSET]]];
      REWRITE_TAC[IMAGE_o] THEN ASM SET_TAC[];
      REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`!y. y IN dk ==> (f:real^2->real^N)((f':real^N->real^2) y) = y`;
        `(dd:real^N->bool) SUBSET dk`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `G = (dk:real^N->bool) DIFF (dd DIFF jj)` THEN
  SUBGOAL_THEN `compact (G:real^N->bool) /\ G INTER dd = jj /\ dk = dd UNION G /\
                t SUBSET G DIFF dd`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `G = IMAGE (f:real^2->real^N) (cball(vec 0,&1) DIFF u)` SUBST1_TAC THENL
       [EXPAND_TAC "G" THEN
        MAP_EVERY UNDISCH_TAC
         [`IMAGE (f:real^2->real^N) (cball(vec 0,&1)) = dk`;
          `IMAGE (f:real^2->real^N) u = dd DIFF jj`;
          `!x. x IN cball(vec 0:real^2,&1) ==> (f':real^N->real^2)(f x) = x`;
          `(u:real^2->bool) SUBSET cball(vec 0,&1)`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED] THEN CONJ_TAC THENL
         [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
          REWRITE_TAC[BOUNDED_CBALL] THEN SET_TAC[];
          MATCH_MP_TAC CLOSED_DIFF THEN ASM_REWRITE_TAC[CLOSED_CBALL]]];
      EXPAND_TAC "G" THEN UNDISCH_TAC `(jj:real^N->bool) SUBSET dd` THEN
      UNDISCH_TAC `(dd:real^N->bool) SUBSET dk` THEN SET_TAC[];
      EXPAND_TAC "G" THEN UNDISCH_TAC `(dd:real^N->bool) SUBSET dk` THEN SET_TAC[];
      EXPAND_TAC "G" THEN
      MAP_EVERY UNDISCH_TAC [`(t:real^N->bool) SUBSET dk`; `dd INTER (t:real^N->bool) = {}`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  (* the map that replaces dd by a *)
  ABBREV_TAC `th = \x:real^N. if x IN dd then (q:real^N->real^N) x else x` THEN
  SUBGOAL_THEN `(!x. x IN dd ==> (th:real^N->real^N) x = q x) /\
                (!x. ~(x IN dd) ==> (th:real^N->real^N) x = x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "th" THEN SIMP_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?th'. homeomorphism (dk,G UNION a) (th:real^N->real^N,th')`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPACT THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ONCE_ASM_REWRITE_TAC[] THEN EXPAND_TAC "th" THEN
      MATCH_MP_TAC CONTINUOUS_ON_CASES THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; CONTINUOUS_ON_ID] THEN
      X_GEN_TAC `x:real^N` THEN STRIP_TAC THENL
       [USE_THEN "qj" MATCH_MP_TAC THEN ASM SET_TAC[]; ASM SET_TAC[]];
      MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
        ASM_CASES_TAC `(x:real^N) IN dd` THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[];
        REWRITE_TAC[SUBSET; IN_UNION; IN_IMAGE] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THENL
         [ASM_CASES_TAC `(y:real^N) IN dd` THENL
           [EXISTS_TAC `y:real^N` THEN
            SUBGOAL_THEN `(y:real^N) IN jj` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
            ASM_SIMP_TAC[] THEN CONJ_TAC THENL
             [CONV_TAC SYM_CONV THEN USE_THEN "qj" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
              ASM SET_TAC[]];
            EXISTS_TAC `y:real^N` THEN ASM_SIMP_TAC[] THEN ASM SET_TAC[]];
          EXISTS_TAC `(q':real^N->real^N) y` THEN
          SUBGOAL_THEN `(q':real^N->real^N) y IN dd` ASSUME_TAC THENL
           [ASM SET_TAC[]; ALL_TAC] THEN
          ASM_SIMP_TAC[] THEN ASM SET_TAC[]]];
      MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC MP_TAC)) THEN
      ASM_CASES_TAC `(x:real^N) IN dd` THEN ASM_CASES_TAC `(y:real^N) IN dd` THEN
      ASM_SIMP_TAC[] THENL
       [ASM_MESON_TAC[];
        DISCH_TAC THEN SUBGOAL_THEN `(y:real^N) IN a` ASSUME_TAC THENL
         [UNDISCH_TAC `(q:real^N->real^N) x = y` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
          ASM SET_TAC[];
          ASM SET_TAC[]];
        DISCH_TAC THEN SUBGOAL_THEN `(x:real^N) IN a` ASSUME_TAC THENL
         [UNDISCH_TAC `x = (q:real^N->real^N) y` THEN DISCH_THEN SUBST1_TAC THEN
          ASM SET_TAC[];
          ASM SET_TAC[]]]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`(th:real^N->real^N) o (f:real^2->real^N)`;
                        `(f':real^N->real^2) o (th':real^N->real^N)`] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `dk:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE
   `!f:A->A s. (!x. x IN s ==> f x = x) ==> s = IMAGE f s`) THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN
  ASM SET_TAC[]);;

(* ========================================================================= *)
(* Part 3: polyhedrality of the replaced disks.  CX_RI_POINT and             *)
(* CX_RI_SUB: points of a simplicial complex lie in relative interiors of   *)
(* its simplices, and a simplex whose relative interior meets another lies  *)
(* in it.  SIDE_POLY: removing from a polyhedron s a relatively clopen part *)
(* of s minus a subpolyhedron q leaves a polyhedron.  LP_INTER_POLYTOPE,    *)
(* CELL2_POLY, OPEN_IN_SUBDISK (invariance of domain in a pseudo-cell).     *)
(* FPOLY: ((E INTER X) DIFF (dd DIFF jj)) UNION a is a polyhedron.          *)
(* ========================================================================= *)

let MOI_S3XT_CX_RI_POINT = prove
 (`!(t:(real^N->bool)->bool) z.
     simplicial_complex t /\ z IN UNIONS t ==> ?k. k IN t /\ z IN relative_interior k`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex; IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `z:real^N`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]; ASM_MESON_TAC[]]);;

let MOI_S3XT_CX_RI_SUB = prove
 (`!(t:(real^N->bool)->bool) k s.
     simplicial_complex t /\ k IN t /\ s IN t /\ ~(relative_interior k INTER s = {})
     ==> k SUBSET s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(k:real^N->bool) INTER s face_of k` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(k:real^N->bool) INTER s = k` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(k:real^N->bool) INTER s`; `k:real^N->bool`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[]);;

let MOI_S3XT_SIDE_POLY = prove
 (`!(s:real^N->bool) q w.
     pl_polyhedron s /\ pl_polyhedron q /\ q SUBSET s /\ w SUBSET s DIFF q /\
     open_in (subtopology euclidean s) w /\
     open_in (subtopology euclidean s) ((s DIFF q) DIFF w)
     ==> pl_polyhedron (s DIFF w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_polyhedron (s:real^N->bool)` THEN
  UNDISCH_TAC `pl_polyhedron (q:real^N->bool)` THEN REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `cq:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  DISCH_THEN(X_CHOOSE_THEN `cs:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))) THEN
  MP_TAC(ISPEC `cs UNION cq:(real^N->bool)->bool` POLYTOPES_SIMPLICIAL_REFINEMENT) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[FINITE_UNION; IN_UNION] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `UNIONS t = (s:real^N->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[UNIONS_UNION] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^N. z IN q ==> ?k. k IN t /\ k SUBSET q /\ z IN k` ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?k:real^N->bool. k IN cq /\ z IN k` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `cs UNION cq:(real^N->bool)->bool`))
        (concl th))) THEN
    ASM_REWRITE_TAC[IN_UNION] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?j:real^N->bool. j IN f /\ z IN j` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `j:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  EXISTS_TAC `{k:real^N->bool | k IN t /\ DISJOINT k w}` THEN
  ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM] THEN CONJ_TAC THENL
   [X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; IN_DIFF] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [UNDISCH_TAC `UNIONS t = (s:real^N->bool)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `k:real^N->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `DISJOINT (k:real^N->bool) w` THEN UNDISCH_TAC `(x:real^N) IN k` THEN
      SET_TAC[]]] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `z:real^N`] MOI_S3XT_CX_RI_POINT) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    UNDISCH_TAC `UNIONS t = (s:real^N->bool)` THEN UNDISCH_TAC `(z:real^N) IN s` THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `k:real^N->bool` THEN
  SUBGOAL_THEN `(z:real^N) IN k /\ k SUBSET s` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `UNIONS t = (s:real^N->bool)` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `relative_interior (k:real^N->bool) INTER q = {}` THENL
   [ALL_TAC;
    FIRST_X_ASSUM(X_CHOOSE_THEN `y:real^N` MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term (fun t -> t = `q:real^N->bool`)) (concl th) &&
      can (find_term (fun t -> t = `t:(real^N->bool)->bool`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `k:real^N->bool`; `j:real^N->bool`]
      MOI_S3XT_CX_RI_SUB) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM SET_TAC[]] THEN
  (* the relative interior of k misses q, so lies on one side of the clopen split *)
  SUBGOAL_THEN `connected (relative_interior (k:real^N->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC CONVEX_CONNECTED THEN MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  UNDISCH_TAC `open_in (subtopology euclidean s) (w:real^N->bool)` THEN
  UNDISCH_TAC `open_in (subtopology euclidean s) ((s DIFF q) DIFF w:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `relative_interior (k:real^N->bool) INTER u = {}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN DISCH_TAC THEN
    SUBGOAL_THEN `relative_interior (k:real^N->bool) SUBSET u UNION v /\
                  u INTER v INTER relative_interior k = {} /\
                  ~(v INTER relative_interior k = {})` STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`relative_interior (k:real^N->bool) SUBSET k`;
          `relative_interior (k:real^N->bool) INTER q = {}`; `(k:real^N->bool) SUBSET s`;
          `(w:real^N->bool) = s INTER u`; `((s DIFF q) DIFF w:real^N->bool) = s INTER v`] THEN
        SET_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`relative_interior (k:real^N->bool) SUBSET k`; `(k:real^N->bool) SUBSET s`;
          `(w:real^N->bool) = s INTER u`; `((s DIFF q) DIFF w:real^N->bool) = s INTER v`] THEN
        SET_TAC[];
        MAP_EVERY UNDISCH_TAC
         [`(z:real^N) IN relative_interior k`; `~((z:real^N) IN w)`;
          `relative_interior (k:real^N->bool) INTER q = {}`; `(z:real^N) IN s`;
          `((s DIFF q) DIFF w:real^N->bool) = s INTER v`] THEN
        SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `connected (relative_interior (k:real^N->bool))` THEN
    REWRITE_TAC[CONNECTED_OPEN_IN; NOT_EXISTS_THM] THEN
    DISCH_THEN(MP_TAC o SPECL [`relative_interior (k:real^N->bool) INTER u`;
                               `relative_interior (k:real^N->bool) INTER v`]) THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    MATCH_MP_TAC(TAUT `a /\ b /\ c /\ d /\ f ==> ~(a /\ b /\ c /\ d /\ ~e /\ f) ==> e`) THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `u:real^N->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `v:real^N->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `relative_interior (k:real^N->bool) SUBSET u UNION v` THEN SET_TAC[];
      UNDISCH_TAC `u INTER v INTER relative_interior (k:real^N->bool) = {}` THEN SET_TAC[];
      UNDISCH_TAC `~(v INTER relative_interior (k:real^N->bool) = {})` THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN closure(relative_interior k)` MP_TAC THENL
   [SUBGOAL_THEN `closure(relative_interior k) = (k:real^N->bool)` (fun th -> ASM_REWRITE_TAC[th]) THEN
    SUBGOAL_THEN `convex (k:real^N->bool) /\ compact k` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT]; ALL_TAC] THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  SUBGOAL_THEN `(y:real^N) IN u` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `open (u:real^N->bool)` THEN REWRITE_TAC[open_def] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN u` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[DIST_SYM]; ASM SET_TAC[]]);;

let MOI_S3XT_LP_INTER_POLYTOPE = prove
 (`!(s:real^N->bool) k.
     locally_polyhedral s /\ polytope k ==> locally_polyhedral (s INTER k)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[locally_polyhedral] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "lp") ASSUME_TAC) THEN
  X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
  REMOVE_THEN "lp" (MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool`
    (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`IMAGE (\p:real^N->bool. p INTER k) c`; `u:real^N->bool`] THEN
  ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_IMAGE] THEN ASM SET_TAC[];
    X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC POLYTOPE_INTER THEN ASM_SIMP_TAC[]; ASM SET_TAC[]]]);;

let MOI_S3XT_CELL2_POLY = prove
 (`!(a:real^N->bool) j.
     pl_cell_with_boundary 2 a j ==> pl_polyhedron a /\ pl_polyhedron j`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `polytope (k:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]; ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE (f:real^N->real^N) k = a` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN
    ASM_SIMP_TAC[MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER] THEN
    MATCH_MP_TAC PL_MAP_ON_SUBSET THEN EXISTS_TAC `k:real^N->bool` THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER] THEN
    MATCH_MP_TAC RELATIVE_FRONTIER_SUBSET THEN
    ASM_SIMP_TAC[POLYTOPE_IMP_COMPACT; COMPACT_IMP_CLOSED]]);;

let MOI_S3XT_OPEN_IN_SUBDISK = prove
 (`!(e:real^N->bool) j dd jj.
     (e DIFF j) homeomorphic ball(vec 0:real^2,&1) /\ closed j /\
     disk_with_boundary dd jj /\ dd SUBSET e DIFF j
     ==> open_in (subtopology euclidean e) (dd DIFF jj)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[homeomorphic; disk_with_boundary] THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `p:real^N->real^2` (X_CHOOSE_THEN `p':real^2->real^N` ASSUME_TAC))
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^2->real^N` (X_CHOOSE_THEN `s':real^N->real^2`
        (CONJUNCTS_THEN2 (STRIP_ASSUME_TAC o REWRITE_RULE[homeomorphism]) (ASSUME_TAC o SYM))))
      ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] SPHERE_SUBSET_CBALL) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] BALL_SUBSET_CBALL) THEN
  MP_TAC(ISPECL [`vec 0:real^2`; `&1`] CBALL_DIFF_BALL) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `IMAGE (s:real^2->real^N) (ball(vec 0,&1)) = dd DIFF jj` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`IMAGE (s:real^2->real^N) (cball(vec 0,&1)) = dd`;
      `IMAGE (s:real^2->real^N) (sphere(vec 0,&1)) = jj`;
      `!x. x IN cball(vec 0:real^2,&1) ==> (s':real^N->real^2)(s x) = x`;
      `cball(vec 0:real^2,&1) DIFF ball(vec 0,&1) = sphere(vec 0,&1)`;
      `ball(vec 0:real^2,&1) SUBSET cball(vec 0,&1)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `homeomorphism ((e:real^N->bool) DIFF j,ball(vec 0:real^2,&1))
                             (p:real^N->real^2,p')` THEN
  DISCH_THEN(fun th -> ASSUME_TAC th THEN
    STRIP_ASSUME_TAC(REWRITE_RULE[homeomorphism] th)) THEN
  SUBGOAL_THEN `open (IMAGE ((p:real^N->real^2) o (s:real^2->real^N)) (ball(vec 0,&1)))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC INVARIANCE_OF_DOMAIN THEN REWRITE_TAC[OPEN_BALL] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `cball(vec 0:real^2,&1)` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `(e:real^N->bool) DIFF j` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      REWRITE_TAC[o_THM] THEN MAP_EVERY X_GEN_TAC [`x:real^2`; `y:real^2`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN `(s:real^2->real^N) x = s y` MP_TAC THENL
       [SUBGOAL_THEN `(s:real^2->real^N) x IN e DIFF j /\ s y IN e DIFF j`
        STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
        ASM_MESON_TAC[SUBSET]]];
    ALL_TAC] THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `(e:real^N->bool) DIFF j` THEN CONJ_TAC THENL
   [SUBGOAL_THEN `dd DIFF jj = IMAGE (p':real^2->real^N)
                                (IMAGE ((p:real^N->real^2) o (s:real^2->real^N))
                                       (ball(vec 0,&1)))`
    SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`!x. x IN (e:real^N->bool) DIFF j ==> (p':real^2->real^N)(p x) = x`;
        `(dd:real^N->bool) SUBSET e DIFF j`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`p:real^N->real^2`; `ball(vec 0:real^2,&1)`] THEN
    ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    EXISTS_TAC `IMAGE ((p:real^N->real^2) o (s:real^2->real^N)) (ball(vec 0,&1))` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (p:real^N->real^2) (e DIFF j) = ball(vec 0,&1)` THEN
    UNDISCH_TAC `(dd:real^N->bool) SUBSET e DIFF j` THEN SET_TAC[];
    SUBGOAL_THEN `(e:real^N->bool) DIFF j = e DIFF (e INTER j)` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_SIMP_TAC[CLOSED_IN_CLOSED_INTER; OPEN_IN_SUBTOPOLOGY_REFL; TOPSPACE_EUCLIDEAN;
                 SUBSET_UNIV]]);;

let MOI_S3XT_FPOLY = prove
 (`!(e:real^3->bool) j p (x:real^3->bool) dd jj a.
     pseudo_cell e j p /\ pl_polyhedron x /\ DISJOINT j x /\
     disk_with_boundary dd jj /\ pl_cell_with_boundary 2 a jj /\
     dd SUBSET e /\ dd SUBSET x /\ p IN dd DIFF jj
     ==> pl_polyhedron (((e INTER x) DIFF (dd DIFF jj)) UNION a)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pseudo_cell] THEN STRIP_TAC THEN
  SUBGOAL_THEN `closed (j:real^3->bool) /\ closed (e:real^3->bool) /\ compact (x:real^3->bool) /\
                compact (dd:real^3->bool) /\ jj SUBSET dd /\
                pl_polyhedron (a:real^3->bool) /\ pl_polyhedron (jj:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MP_TAC(ISPECL [`j:real^3->bool`; `sphere(vec 0:real^2,&1)`] HOMEOMORPHIC_COMPACTNESS) THEN
      ASM_REWRITE_TAC[COMPACT_SPHERE];
      UNDISCH_TAC `closure((e:real^3->bool) DIFF j) = e` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[CLOSED_CLOSURE];
      ASM_SIMP_TAC[PL_POLYHEDRON_IMP_COMPACT];
      ASM_MESON_TAC[MOI_S3XT_DISK_FACTS];
      ASM_MESON_TAC[MOI_S3XT_DISK_FACTS];
      ASM_MESON_TAC[MOI_S3XT_CELL2_POLY];
      ASM_MESON_TAC[MOI_S3XT_CELL2_POLY]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (dd:real^3->bool) j` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`DISJOINT (j:real^3->bool) x`; `(dd:real^3->bool) SUBSET x`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`e:real^3->bool`; `j:real^3->bool`; `dd:real^3->bool`; `jj:real^3->bool`]
    MOI_S3XT_OPEN_IN_SUBDISK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`DISJOINT (dd:real^3->bool) j`; `(dd:real^3->bool) SUBSET e`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `U:real^3->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `G = ((e:real^3->bool) INTER x) DIFF (dd DIFF jj)` THEN
  MATCH_MP_TAC PL_POLYHEDRON_UNION THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_PTR_COMPACT_LOCALLY_POLYHEDRAL THEN CONJ_TAC THENL
   [SUBGOAL_THEN `G = ((e:real^3->bool) INTER x) INTER ((:real^3) DIFF U)` SUBST1_TAC THENL
     [EXPAND_TAC "G" THEN UNDISCH_TAC `(dd:real^3->bool) DIFF jj = e INTER U` THEN SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC COMPACT_INTER_CLOSED THEN
    ASM_SIMP_TAC[GSYM OPEN_CLOSED; CLOSED_INTER_COMPACT];
    ALL_TAC] THEN
  REWRITE_TAC[locally_polyhedral] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((y:real^3) IN j) /\ ~(y = p)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(y:real^3) IN G`; `DISJOINT (j:real^3->bool) x`;
                           `(p:real^3) IN dd DIFF jj`] THEN
    EXPAND_TAC "G" THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `(:real^3) DIFF (p INSERT j)` OPEN_CONTAINS_INTERVAL) THEN
  REWRITE_TAC[GSYM closed] THEN ASM_SIMP_TAC[CLOSED_INSERT] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DIFF; IN_UNIV; IN_INSERT]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a0:real^3` (X_CHOOSE_THEN `b0:real^3` STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `s0 = ((e:real^3->bool) INTER interval[a0,b0]) INTER x` THEN
  SUBGOAL_THEN `pl_polyhedron (s0:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "s0" THEN MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_PTR_COMPACT_LOCALLY_POLYHEDRAL THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_INTER_COMPACT THEN ASM_REWRITE_TAC[COMPACT_INTERVAL];
      ALL_TAC] THEN
    SUBGOAL_THEN `(e:real^3->bool) INTER interval[a0,b0] =
                  ((e DIFF j) DELETE p) INTER interval[a0,b0]` SUBST1_TAC THENL
     [UNDISCH_TAC `interval[a0:real^3,b0] SUBSET (:real^3) DIFF (p INSERT j)` THEN SET_TAC[];
      MATCH_MP_TAC MOI_S3XT_LP_INTER_POLYTOPE THEN ASM_REWRITE_TAC[POLYTOPE_INTERVAL]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s0:real^3->bool`; `(jj:real^3->bool) INTER interval[a0,b0] INTER x`;
                 `((dd:real^3->bool) DIFF jj) INTER interval[a0,b0] INTER x`]
    MOI_S3XT_SIDE_POLY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC PL_POLYHEDRON_INTER THEN
      ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON; POLYTOPE_INTERVAL];
      EXPAND_TAC "s0" THEN
      MAP_EVERY UNDISCH_TAC [`(jj:real^3->bool) SUBSET dd`; `(dd:real^3->bool) SUBSET e`] THEN
      SET_TAC[];
      EXPAND_TAC "s0" THEN
      MAP_EVERY UNDISCH_TAC [`(dd:real^3->bool) DIFF jj = e INTER U`;
                             `(dd:real^3->bool) SUBSET e`] THEN SET_TAC[];
      REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `U:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "s0" THEN
      UNDISCH_TAC `(dd:real^3->bool) DIFF jj = e INTER U` THEN SET_TAC[];
      REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `(:real^3) DIFF dd` THEN
      ASM_SIMP_TAC[GSYM closed; COMPACT_IMP_CLOSED] THEN
      EXPAND_TAC "s0" THEN
      MAP_EVERY UNDISCH_TAC [`(dd:real^3->bool) DIFF jj = e INTER U`;
                             `(jj:real^3->bool) SUBSET dd`; `(dd:real^3->bool) SUBSET e`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s0 DIFF ((dd DIFF jj) INTER interval[a0,b0] INTER x) =
                (G:real^3->bool) INTER interval[a0,b0]` SUBST1_TAC THENL
   [MAP_EVERY EXPAND_TAC ["s0"; "G"] THEN SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[pl_polyhedron] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`cc:(real^3->bool)->bool`; `interval(a0:real^3,b0)`] THEN
  ASM_REWRITE_TAC[OPEN_INTERVAL] THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`a0:real^3`; `b0:real^3`] INTERVAL_OPEN_SUBSET_CLOSED) THEN
    UNDISCH_TAC `(G:real^3->bool) INTER interval[a0,b0] = UNIONS cc` THEN SET_TAC[];
    X_GEN_TAC `k:real^3->bool` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    UNDISCH_TAC `(G:real^3->bool) INTER interval[a0,b0] = UNIONS cc` THEN
    UNDISCH_TAC `(k:real^3->bool) IN cc` THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Part 4: the PL disks F_e.  FDISK: for a pseudo-cell E                    *)
(* whose trace on the polyhedron X is a disk bounded by the polygon         *)
(* E INTER frontier X, and a ball of radius rho at the centre inside int X,  *)
(* 32.4 gives a PL disk F with the same boundary, inside X, meeting         *)
(* frontier X only in the trace, agreeing with E INTER X off the ball.       *)
(* ========================================================================= *)

let MOI_S3XT_FDISK = prove
 (`!(e:real^3->bool) j p (x:real^3->bool) rho.
     MOISE_324_STATEMENT /\
     (!d jd:real^3->bool. pl_polyhedron d /\ disk_with_boundary d jd /\ pl_sphere 1 jd
                          ==> pl_cell_with_boundary 2 d jd) /\
     pseudo_cell e j p /\ &0 < rho /\ ball(p,rho) SUBSET interior x /\ pl_polyhedron x /\
     DISJOINT j x /\
     pl_sphere 1 (e INTER frontier x) /\ disk_with_boundary (e INTER x) (e INTER frontier x)
     ==> ?f. pl_cell_with_boundary 2 f (e INTER frontier x) /\ f SUBSET x /\
             f INTER frontier x = e INTER frontier x /\
             f SUBSET e UNION ball(p,rho) /\ (e INTER x) DIFF ball(p,rho) SUBSET f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `MOISE_324_STATEMENT` THEN REWRITE_TAC[MOISE_324_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPECL [`e:real^3->bool`; `j:real^3->bool`; `p:real^3`; `rho:real`]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^3->bool` (X_CHOOSE_THEN `jj:real^3->bool`
    (X_CHOOSE_THEN `dd:real^3->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `interior x SUBSET (x:real^3->bool) /\ frontier x SUBSET x /\
                DISJOINT (interior x) (frontier (x:real^3->bool))`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_SUBSET] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED; PL_POLYHEDRON_IMP_COMPACT];
      REWRITE_TAC[frontier] THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(dd:real^3->bool) SUBSET interior x /\ (a:real^3->bool) SUBSET interior x`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `ball(p:real^3,rho)` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(jj:real^3->bool) SUBSET dd` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_S3XT_DISK_FACTS]; ALL_TAC] THEN
  EXISTS_TAC `(((e:real^3->bool) INTER x) DIFF (dd DIFF jj)) UNION a` THEN
  REPEAT CONJ_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3XT_FPOLY THEN
      MAP_EVERY EXISTS_TAC [`j:real^3->bool`; `p:real^3`] THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]];
      MATCH_MP_TAC MOI_S3XT_DISK_REPLACE THEN
      ASM_SIMP_TAC[MOI_S3XT_CELL2_DISK] THEN REPEAT CONJ_TAC THENL
       [ASM SET_TAC[]; ASM SET_TAC[]; ASM SET_TAC[]]];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

(* ========================================================================= *)
(* Part 5: local topology of PL 2-spheres.  SPHERE_FACTS: the Jordan-       *)
(* Brouwer facts and (with PL Schoenflies) the ball s UNION inside s.        *)
(* SPHERE_TRIANG: a PL 2-sphere is triangulated by a combinatorial          *)
(* 2-manifold of dimension at most 2 (boundary complex of a triangulated     *)
(* ball).  LOCAL_SIDES: off the vertices, a small ball minus such a surface  *)
(* has two nonempty connected open local sides (LOCAL_TRI, LOCAL_EDGE).      *)
(* TWO_SIDES: where two PL spheres with disjoint insides coincide locally,   *)
(* one local side lies inside each, so a small ball lies in their balls.    *)
(* ========================================================================= *)

let MOI_S3XT_SPHERE_FACTS = prove
 (`!s:real^3->bool.
     pl_sphere 2 s
     ==> compact s /\ ~(inside s = {}) /\ open(inside s) /\ connected(inside s) /\
         open(outside s) /\ connected(outside s) /\ ~bounded(outside s) /\
         inside s INTER outside s = {} /\ inside s UNION outside s = (:real^3) DIFF s /\
         frontier(inside s) = s /\ frontier(outside s) = s /\
         compact (s UNION inside s) /\ interior (s UNION inside s) = inside s /\
         frontier (s UNION inside s) = s`,
  GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` JORDAN_INSIDE_OUTSIDE_GEN) THEN
  ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC; DIMINDEX_3; ARITH] THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (s:real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`s:real^3->bool`; `sphere(vec 0:real^3,&1)`] HOMEOMORPHIC_COMPACTNESS) THEN
    ASM_SIMP_TAC[MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC; COMPACT_SPHERE];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact ((s:real^3->bool) UNION inside s)` ASSUME_TAC THENL
   [REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; BOUNDED_UNION] THEN
    ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
    SUBGOAL_THEN `(s:real^3->bool) UNION inside s = (:real^3) DIFF outside s` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`inside s INTER outside s:real^3->bool = {}`;
        `inside s UNION outside s:real^3->bool = (:real^3) DIFF s`] THEN
      SET_TAC[];
      ASM_REWRITE_TAC[GSYM OPEN_CLOSED]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_SCD_FILLED_FRONTIER) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[]);;

let MOI_S3XT_SPHERE_TRIANG = prove
 (`!s:real^3->bool.
     PL_SCHOENFLIES_3_STATEMENT /\ pl_sphere 2 s
     ==> ?c. simplicial_complex c /\ (!k. k IN c ==> aff_dim k <= &2) /\
             combinatorial_manifold 2 c /\ UNIONS c = s`,
  REWRITE_TAC[PL_SCHOENFLIES_3_STATEMENT] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `s:real^3->bool`) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S3XT_SPHERE_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `b = (s:real^3->bool) UNION inside s` THEN
  SUBGOAL_THEN `pl_cell_with_boundary 3 (b:real^3->bool) s /\ pl_polyhedron b`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_ball 3 (b:real^3->bool)` THEN REWRITE_TAC[pl_ball] THEN
    DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `f:real^3->real^3`
      (X_CHOOSE_THEN `g:real^3->real^3` STRIP_ASSUME_TAC))) THEN
    CONJ_TAC THENL
     [REWRITE_TAC[pl_cell_with_boundary] THEN
      MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `f:real^3->real^3`; `g:real^3->real^3`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
      UNDISCH_TAC `frontier (b:real^3->bool) = s` THEN
      DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) THEN
      MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN EXISTS_TAC `g:real^3->real^3` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `pl_homeomorphism ((k:real^3->bool),(b:real^3->bool)) (f,g)` THEN
      REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
      UNDISCH_TAC `IMAGE (f:real^3->real^3) k = b` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_polyhedron (b:real^3->bool)` THEN
  REWRITE_TAC[PL_POLYHEDRON_EQ_SIMPLICIAL_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`d:(real^3->bool)->bool`; `s:real^3->bool`]
    PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  STRIP_TAC THEN
  MP_TAC(MATCH_MP BOUNDARY_COMPLEX_SURFACE
    (ASSUME `combinatorial_manifold_with_boundary 3 (d:(real^3->bool)->bool)`)) THEN
  STRIP_TAC THEN
  EXISTS_TAC `boundary_complex (d:(real^3->bool)->bool)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `simplicial_complex (d:(real^3->bool)->bool)` THEN
    UNDISCH_TAC `simplicial_subcomplex (boundary_complex d) (d:(real^3->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex; simplicial_subcomplex] THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[FINITE_SUBSET; SUBSET];
    ALL_TAC] THEN
  X_GEN_TAC `k:real^3->bool` THEN REWRITE_TAC[boundary_complex; IN_ELIM_THM] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `k:real^3->bool` AFF_DIM_LE_UNIV) THEN REWRITE_TAC[DIMINDEX_3] THEN
  MATCH_MP_TAC(INT_ARITH `~(x:int = &3) ==> x <= &3 ==> x <= &2`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?n. n simplex (k:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `n:int = &3` SUBST_ALL_TAC THENL
   [ASM_MESON_TAC[AFF_DIM_SIMPLEX]; ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `z:real^3` o MATCH_MP MOI_FN1_SIMPLEX_3_INTERIOR) THEN
  SUBGOAL_THEN `interior(frontier(inside(s:real^3->bool))) = {}` MP_TAC THENL
   [MATCH_MP_TAC INTERIOR_FRONTIER_EMPTY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `interior (k:real^3->bool) SUBSET interior s` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_INTERIOR THEN UNDISCH_TAC `(k:real^3->bool) SUBSET complex_boundary d` THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let MOI_S3XT_LOCAL_SIDES = prove
 (`!(c:(real^3->bool)->bool) y.
     simplicial_complex c /\ (!k. k IN c ==> aff_dim k <= &2) /\
     combinatorial_manifold 2 c /\ y IN UNIONS c /\ ~({y} IN c)
     ==> ?r0. &0 < r0 /\
              !r. &0 < r /\ r <= r0
                  ==> ?u v. open u /\ open v /\ connected u /\ connected v /\
                            DISJOINT u v /\ u UNION v = ball(y,r) DIFF UNIONS c /\
                            ~(u = {}) /\ ~(v = {})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (c:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `y:real^3`] MOI_S3XT_CX_RI_POINT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?n. n simplex (k:real^3->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (k:real^3->bool) = &1 \/ aff_dim k = &2` MP_TAC THENL
   [SUBGOAL_THEN `aff_dim (k:real^3->bool) <= &2` MP_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim (k:real^3->bool) = -- &1) /\ ~(aff_dim k = &0)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_MINUS1; AFF_DIM_EQ_0] THEN CONJ_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `(y:real^3) IN relative_interior k` THEN
        ASM_REWRITE_TAC[RELATIVE_INTERIOR_EMPTY; NOT_IN_EMPTY];
        DISCH_THEN(X_CHOOSE_THEN `a:real^3` SUBST_ALL_TAC) THEN
        UNDISCH_TAC `(y:real^3) IN relative_interior {a}` THEN
        REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING] THEN DISCH_THEN SUBST_ALL_TAC THEN
        ASM_MESON_TAC[]];
      MP_TAC(ISPEC `k:real^3->bool` AFF_DIM_GE) THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `k:real^3->bool`] MOI_FSA_CM_EDGE2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
    SUBGOAL_THEN `{t:real^3->bool | t IN c /\ aff_dim t = &2 /\ k SUBSET t} HAS_SIZE 2`
    MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE] THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `c:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` (X_CHOOSE_THEN `q':real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `k:real^3->bool`; `q:real^3->bool`;
                   `q':real^3->bool`; `y:real^3`] LOCAL_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r0:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) IN ball(y,r) INTER (q UNION q')` ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^3) IN ball(y,r)` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[CENTRE_IN_BALL]; ALL_TAC] THEN
      MAP_EVERY UNDISCH_TAC
       [`ball(y:real^3,r) INTER UNIONS c = ball(y,r) INTER (q UNION q')`;
        `(y:real^3) IN UNIONS c`; `(y:real^3) IN ball(y,r)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ball(y:real^3,r) INTER UNIONS c = ball(y,r) INTER (q UNION q')` THEN
      UNDISCH_TAC `u UNION v = ball(y:real^3,r) DIFF (q UNION q')` THEN SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `ball(y:real^3,r) INTER (q UNION q') SUBSET closure u INTER closure v` THEN
      ASM_REWRITE_TAC[CLOSURE_EMPTY] THEN ASM SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `ball(y:real^3,r) INTER (q UNION q') SUBSET closure u INTER closure v` THEN
      ASM_REWRITE_TAC[CLOSURE_EMPTY] THEN ASM SET_TAC[]];
    MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `k:real^3->bool`; `y:real^3`] LOCAL_TRI) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r0:real` THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool` STRIP_ASSUME_TAC))) THEN
    MAP_EVERY EXISTS_TAC [`u:real^3->bool`; `v:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(y:real^3) IN ball(y,r) INTER affine hull k` ASSUME_TAC THENL
     [REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN
      MP_TAC(ISPEC `k:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `ball(y:real^3,r) INTER UNIONS c = ball(y,r) INTER affine hull k` THEN
      UNDISCH_TAC `u UNION v = ball(y:real^3,r) DIFF affine hull k` THEN SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `ball(y:real^3,r) INTER affine hull k SUBSET closure u INTER closure v` THEN
      ASM_REWRITE_TAC[CLOSURE_EMPTY] THEN ASM SET_TAC[];
      DISCH_TAC THEN
      UNDISCH_TAC `ball(y:real^3,r) INTER affine hull k SUBSET closure u INTER closure v` THEN
      ASM_REWRITE_TAC[CLOSURE_EMPTY] THEN ASM SET_TAC[]]]);;

let MOI_S3XT_CONN_SPLIT = prove
 (`!c u v:real^N->bool.
     connected c /\ open u /\ open v /\ DISJOINT u v /\ c SUBSET u UNION v
     ==> c SUBSET u \/ c SUBSET v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONNECTED; NOT_EXISTS_THM] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^N->bool`; `v:real^N->bool`]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DISJOINT]) THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

(* A connected set missing a PL 2-sphere lies inside or outside it; a small *)
(* ball at a point of the sphere meets both sides.                          *)

let MOI_S3XT_SPHERE_SIDE = prove
 (`!(s:real^3->bool) w.
     pl_sphere 2 s /\ connected w /\ DISJOINT w s
     ==> w SUBSET inside s \/ w SUBSET outside s`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3XT_CONN_SPLIT THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S3XT_SPHERE_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[DISJOINT] THEN ASM SET_TAC[]);;

let MOI_S3XT_SPHERE_BALL_MEETS = prove
 (`!(s:real^3->bool) y r.
     pl_sphere 2 s /\ y IN s /\ &0 < r
     ==> ~(ball(y,r) INTER inside s = {}) /\ ~(ball(y,r) INTER outside s = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S3XT_SPHERE_FACTS) THEN ASM_REWRITE_TAC[] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(y:real^3) IN closure(inside s)` MP_TAC THENL
     [UNDISCH_TAC `frontier(inside s) = (s:real^3->bool)` THEN REWRITE_TAC[frontier] THEN
      UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[];
      ALL_TAC];
    SUBGOAL_THEN `(y:real^3) IN closure(outside s)` MP_TAC THENL
     [UNDISCH_TAC `frontier(outside s) = (s:real^3->bool)` THEN REWRITE_TAC[frontier] THEN
      UNDISCH_TAC `(y:real^3) IN s` THEN SET_TAC[];
      ALL_TAC]] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `r:real`) THEN
  ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN MESON_TAC[DIST_SYM]);;

let MOI_S3XT_SPLIT_TWO = prove
 (`!(s:real^3->bool) y r u v.
     pl_sphere 2 s /\ y IN s /\ &0 < r /\ connected u /\ connected v /\
     u UNION v = ball(y,r) DIFF s
     ==> (u SUBSET inside s /\ v SUBSET outside s) \/
         (v SUBSET inside s /\ u SUBSET outside s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `y:real^3`; `r:real`] MOI_S3XT_SPHERE_BALL_MEETS) THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S3XT_SPHERE_FACTS) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `u:real^3->bool`] MOI_S3XT_SPHERE_SIDE) THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `v:real^3->bool`] MOI_S3XT_SPHERE_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `DISJOINT (u:real^3->bool) s /\ DISJOINT (v:real^3->bool) s`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `u UNION v = ball(y:real^3,r) DIFF s` THEN SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `u UNION v = ball(y:real^3,r) DIFF s` THEN
  SET_TAC[]);;

let MOI_S3XT_TWO_SIDES = prove
 (`!(s1:real^3->bool) s2 c y r0.
     pl_sphere 2 s1 /\ pl_sphere 2 s2 /\ DISJOINT (inside s1) (inside s2) /\
     simplicial_complex c /\ (!k. k IN c ==> aff_dim k <= &2) /\
     combinatorial_manifold 2 c /\ UNIONS c = s1 /\ y IN s1 /\ ~({y} IN c) /\
     &0 < r0 /\ ball(y,r0) INTER s1 = ball(y,r0) INTER s2
     ==> ?r u v. &0 < r /\ r <= r0 /\ open u /\ open v /\ connected u /\ connected v /\
                 ~(u = {}) /\ ~(v = {}) /\ u UNION v = ball(y,r) DIFF s1 /\
                 u SUBSET inside s1 /\ v SUBSET inside s2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^3->bool)->bool`; `y:real^3`] MOI_S3XT_LOCAL_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `min r0 r1`))) THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3->bool` (X_CHOOSE_THEN `v:real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  ABBREV_TAC `r = min r0 r1` THEN
  SUBGOAL_THEN `&0 < r /\ r <= r0` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `u UNION v = ball(y:real^3,r) DIFF s1 /\ u UNION v = ball(y:real^3,r) DIFF s2 /\
                ball(y:real^3,r) DIFF s1 = ball(y,r) DIFF s2 /\ (y:real^3) IN s2`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `ball(y:real^3,r) SUBSET ball(y,r0) /\ (y:real^3) IN ball(y,r0)` MP_TAC THENL
     [ASM_SIMP_TAC[SUBSET_BALL; CENTRE_IN_BALL]; ALL_TAC] THEN
    MAP_EVERY UNDISCH_TAC [`ball(y:real^3,r0) INTER s1 = ball(y,r0) INTER s2`;
                           `(y:real^3) IN s1`; `u UNION v = ball(y:real^3,r) DIFF s1`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s1:real^3->bool`; `y:real^3`; `r:real`; `u:real^3->bool`; `v:real^3->bool`]
    MOI_S3XT_SPLIT_TWO) THEN
  MP_TAC(ISPECL [`s2:real^3->bool`; `y:real^3`; `r:real`; `u:real^3->bool`; `v:real^3->bool`]
    MOI_S3XT_SPLIT_TWO) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!w:real^3->bool. ~(w = {}) /\ w SUBSET inside s1 ==> ~(w SUBSET inside s2)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (inside s1) (inside (s2:real^3->bool))` THEN SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN STRIP_TAC THENL
   [ASM_MESON_TAC[];
    MAP_EVERY EXISTS_TAC [`r:real`; `v:real^3->bool`; `u:real^3->bool`] THEN
    ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[UNION_COMM] THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`r:real`; `u:real^3->bool`; `v:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Part 6: the abstract ball configuration.  moi_s3xt_cfg V adj A FF X:      *)
(* finitely many vertices V with a symmetric adjacency, disks FF u v = FF v u *)
(* in X meeting frontier X, pairwise disjoint for distinct edges, pieces     *)
(* A v of frontier X (meeting only along the disks of adjacent vertices),    *)
(* free points, and the PL spheres moi_s3xt_sph A FF adj v = A v UNION the  *)
(* disks at v.  With connected complement of X: the balls lie in X (BALL_IN),*)
(* their interiors miss every disk (INT_MISS), are pairwise disjoint        *)
(* (INT_DISJ), and two balls meet only in the disk of their edge (MEET).     *)
(* With PL Schoenflies the balls cover the interior of X (COVER).           *)
(* ========================================================================= *)

let moi_s3xt_sph = new_definition
 `moi_s3xt_sph (A:real^3->real^3->bool) (FF:real^3->real^3->real^3->bool)
               (adj:real^3->real^3->bool) (v:real^3) =
    A v UNION UNIONS {FF v w | w | adj v w}`;;

let moi_s3xt_cfg = new_definition
 `moi_s3xt_cfg (V:real^3->bool) (adj:real^3->real^3->bool) (A:real^3->real^3->bool)
               (FF:real^3->real^3->real^3->bool) (X:real^3->bool) <=>
    FINITE V /\ ~(V = {}) /\ compact X /\ connected (interior X) /\
    connected ((:real^3) DIFF X) /\
    (!u v. adj u v ==> adj v u /\ ~(u = v) /\ u IN V /\ v IN V /\ FF u v = FF v u) /\
    (!u v. adj u v ==> FF u v SUBSET X /\ connected (FF u v) /\ closed (FF u v) /\
                       ~(FF u v INTER frontier X = {})) /\
    (!u v u' v'. adj u v /\ adj u' v' /\ ~({u,v} = {u',v'})
                 ==> DISJOINT (FF u v) (FF u' v')) /\
    (!v. v IN V ==> A v SUBSET frontier X /\ closed (A v) /\
                    pl_sphere 2 (moi_s3xt_sph A FF adj v)) /\
    (!u v w. adj u v /\ w IN V /\ ~(w = u) /\ ~(w = v) ==> DISJOINT (A w) (FF u v)) /\
    (!u v. u IN V /\ v IN V /\ ~(u = v)
           ==> A u INTER A v SUBSET (if adj u v then FF u v else {})) /\
    (!v. v IN V ==> ?y. y IN A v /\ (!w. w IN V /\ ~(w = v) ==> ~(y IN A w)) /\
                        (!a b. adj a b ==> ~(y IN FF a b)))`;;

let MOI_S3XT_SPH_FF = prove
 (`!(A:real^3->real^3->bool) FF adj v w.
     adj v w ==> FF v w SUBSET moi_s3xt_sph A FF adj v`,
  REWRITE_TAC[moi_s3xt_sph] THEN SET_TAC[]);;

(* A PL 2-sphere inside X bounds a ball inside X when the complement of X  *)
(* is connected; its inside is then in the interior of X.                   *)

let MOI_S3XT_BALL_IN = prove
 (`!(s:real^3->bool) X.
     pl_sphere 2 s /\ s SUBSET X /\ compact X /\ connected ((:real^3) DIFF X)
     ==> s UNION inside s SUBSET X /\ inside s SUBSET interior X`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `s:real^3->bool` MOI_S3XT_SPHERE_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:real^3->bool`; `(:real^3) DIFF X`] MOI_S3XT_SPHERE_SIDE) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [UNDISCH_TAC `(s:real^3->bool) SUBSET X` THEN SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `bounded ((:real^3) DIFF X)` MP_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `inside s:real^3->bool` THEN
      ASM_SIMP_TAC[BOUNDED_INSIDE; COMPACT_IMP_BOUNDED];
      DISCH_THEN(MP_TAC o MATCH_MP COBOUNDED_IMP_UNBOUNDED) THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `s UNION inside s SUBSET (X:real^3->bool)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(:real^3) DIFF X SUBSET outside s`; `inside s INTER outside s:real^3->bool = {}`;
      `(s:real^3->bool) SUBSET X`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let MOI_S3XT_CFG_V = prove
 (`!(V:real^3->bool) adj A FF X v.
     moi_s3xt_cfg V adj A FF X /\ v IN V
     ==> A v SUBSET frontier X /\ closed (A v) /\
         pl_sphere 2 (moi_s3xt_sph A FF adj v) /\
         (?y. y IN A v /\ (!w. w IN V /\ ~(w = v) ==> ~(y IN A w)) /\
              (!a b. adj a b ==> ~(y IN FF a b)))`,
  REWRITE_TAC[moi_s3xt_cfg] THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[]);;

let MOI_S3XT_CFG_E = prove
 (`!(V:real^3->bool) adj A FF X u v.
     moi_s3xt_cfg V adj A FF X /\ adj u v
     ==> adj v u /\ ~(u = v) /\ u IN V /\ v IN V /\ FF u v = FF v u /\
         FF u v SUBSET X /\ connected (FF u v) /\ closed (FF u v) /\
         ~(FF u v INTER frontier X = {})`,
  REWRITE_TAC[moi_s3xt_cfg] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[]);;

let MOI_S3XT_CFG_SPHERE = prove
 (`!(V:real^3->bool) adj A FF X v.
     moi_s3xt_cfg V adj A FF X /\ v IN V
     ==> pl_sphere 2 (moi_s3xt_sph A FF adj v) /\
         moi_s3xt_sph A FF adj v SUBSET X /\
         moi_s3xt_sph A FF adj v UNION inside(moi_s3xt_sph A FF adj v) SUBSET X /\
         inside(moi_s3xt_sph A FF adj v) SUBSET interior X /\
         DISJOINT (inside(moi_s3xt_sph A FF adj v)) (frontier X) /\
         DISJOINT (inside(moi_s3xt_sph A FF adj v)) (moi_s3xt_sph A FF adj v)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3xt_cfg] THEN STRIP_TAC THEN
  SUBGOAL_THEN `frontier X SUBSET (X:real^3->bool)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[FRONTIER_SUBSET_CLOSED; COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (moi_s3xt_sph A FF adj (v:real^3)) /\
                moi_s3xt_sph A FF adj v SUBSET (X:real^3->bool)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_s3xt_sph; UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    ASM_MESON_TAC[SUBSET_TRANS];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s3xt_sph A FF adj (v:real^3)`; `X:real^3->bool`] MOI_S3XT_BALL_IN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `moi_s3xt_sph A FF adj (v:real^3)` MOI_S3XT_SPHERE_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [UNDISCH_TAC `inside(moi_s3xt_sph A FF adj (v:real^3)) SUBSET interior X` THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    UNDISCH_TAC `inside (moi_s3xt_sph A FF adj (v:real^3)) UNION
                 outside (moi_s3xt_sph A FF adj v) =
                 (:real^3) DIFF moi_s3xt_sph A FF adj v` THEN
    SET_TAC[]]);;

let MOI_S3XT_INT_MISS = prove
 (`!(V:real^3->bool) adj A FF X v a b.
     moi_s3xt_cfg V adj A FF X /\ v IN V /\ adj a b
     ==> DISJOINT (inside(moi_s3xt_sph A FF adj v)) (FF a b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                 `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`]
    MOI_S3XT_CFG_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s3xt_cfg V adj A (FF:real^3->real^3->real^3->bool) X` THEN
  REWRITE_TAC[moi_s3xt_cfg] THEN STRIP_TAC THEN
  ASM_CASES_TAC `v:real^3 = a \/ v = b` THENL
   [SUBGOAL_THEN `(FF:real^3->real^3->real^3->bool) a b SUBSET moi_s3xt_sph A FF adj v`
    MP_TAC THENL
     [FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
       [MATCH_MP_TAC MOI_S3XT_SPH_FF THEN ASM_REWRITE_TAC[];
        SUBGOAL_THEN `(FF:real^3->real^3->real^3->bool) a b = FF b a` SUBST1_TAC THENL
         [ASM_MESON_TAC[]; ALL_TAC] THEN
        MATCH_MP_TAC MOI_S3XT_SPH_FF THEN ASM_MESON_TAC[]];
      UNDISCH_TAC `DISJOINT (inside(moi_s3xt_sph A FF adj (v:real^3)))
                            (moi_s3xt_sph A FF adj v)` THEN SET_TAC[]];
    ALL_TAC] THEN
  RULE_ASSUM_TAC(REWRITE_RULE[DE_MORGAN_THM]) THEN
  MP_TAC(ISPECL [`moi_s3xt_sph A FF adj (v:real^3)`;
                 `(FF:real^3->real^3->real^3->bool) a b`] MOI_S3XT_SPHERE_SIDE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[] THEN REWRITE_TAC[moi_s3xt_sph] THEN
    SUBGOAL_THEN `DISJOINT ((FF:real^3->real^3->real^3->bool) a b) (A (v:real^3)) /\
                  (!w. adj v w ==> DISJOINT ((FF:real^3->real^3->real^3->bool) a b) (FF v w))`
    MP_TAC THENL
     [CONJ_TAC THENL
       [ONCE_REWRITE_TAC[DISJOINT_SYM] THEN ASM_MESON_TAC[];
        X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN
        UNDISCH_TAC `!u v u' v'. adj u v /\ adj u' v' /\ ~({u, v} = {u', v'})
                      ==> DISJOINT ((FF:real^3->real^3->real^3->bool) u v) (FF u' v')` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[]];
      SET_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `~((FF:real^3->real^3->real^3->bool) a b INTER frontier X = {})` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (inside(moi_s3xt_sph A FF adj (v:real^3))) (frontier X)` THEN
    UNDISCH_TAC `(FF:real^3->real^3->real^3->bool) a b SUBSET inside(moi_s3xt_sph A FF adj v)` THEN
    SET_TAC[];
    MP_TAC(ISPEC `moi_s3xt_sph A FF adj (v:real^3)` MOI_S3XT_SPHERE_FACTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[]]);;

let MOI_S3XT_INT_SPH = prove
 (`!(V:real^3->bool) adj A FF X a b.
     moi_s3xt_cfg V adj A FF X /\ a IN V /\ b IN V
     ==> DISJOINT (inside(moi_s3xt_sph A FF adj a)) (moi_s3xt_sph A FF adj b)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                 `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `a:real^3`]
    MOI_S3XT_CFG_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(A:real^3->real^3->bool) b SUBSET frontier X` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                   `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `b:real^3`]
      MOI_S3XT_CFG_V) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!w. adj b w ==> DISJOINT (inside(moi_s3xt_sph A FF adj (a:real^3)))
                                         ((FF:real^3->real^3->real^3->bool) b w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3XT_INT_MISS THEN
    MAP_EVERY EXISTS_TAC [`V:real^3->bool`; `X:real^3->bool`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC RAND_CONV [moi_s3xt_sph] THEN
  UNDISCH_TAC `DISJOINT (inside(moi_s3xt_sph A FF adj (a:real^3))) (frontier X)` THEN
  UNDISCH_TAC `(A:real^3->real^3->bool) b SUBSET frontier X` THEN
  UNDISCH_TAC `!w. adj b w ==> DISJOINT (inside(moi_s3xt_sph A FF adj (a:real^3)))
                                        ((FF:real^3->real^3->real^3->bool) b w)` THEN
  SET_TAC[]);;

let MOI_S3XT_INT_DISJ = prove
 (`!(V:real^3->bool) adj A FF X u v.
     moi_s3xt_cfg V adj A FF X /\ u IN V /\ v IN V /\ ~(u = v)
     ==> DISJOINT (inside(moi_s3xt_sph A FF adj u)) (inside(moi_s3xt_sph A FF adj v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a:real^3. a IN V ==> pl_sphere 2 (moi_s3xt_sph A FF adj a)` ASSUME_TAC THENL
   [X_GEN_TAC `a:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                   `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `a:real^3`]
      MOI_S3XT_CFG_V) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!a b:real^3. a IN V /\ b IN V /\
                  (z:real^3) IN inside(moi_s3xt_sph A FF adj a) /\
                  z IN inside(moi_s3xt_sph A FF adj b)
                  ==> inside(moi_s3xt_sph A FF adj a) SUBSET
                      inside(moi_s3xt_sph A FF adj b)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`moi_s3xt_sph A FF adj (b:real^3)`;
                   `inside(moi_s3xt_sph A FF adj (a:real^3))`] MOI_S3XT_SPHERE_SIDE) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [ASM_SIMP_TAC[];
        MP_TAC(ISPEC `moi_s3xt_sph A FF adj (a:real^3)` MOI_S3XT_SPHERE_FACTS) THEN
        ASM_SIMP_TAC[];
        MATCH_MP_TAC MOI_S3XT_INT_SPH THEN
        MAP_EVERY EXISTS_TAC [`V:real^3->bool`; `X:real^3->bool`] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPEC `moi_s3xt_sph A FF adj (b:real^3)` MOI_S3XT_SPHERE_FACTS) THEN
    ASM_SIMP_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s3xt_sph A FF adj (u:real^3) = moi_s3xt_sph A FF adj v` ASSUME_TAC THENL
   [SUBGOAL_THEN `inside(moi_s3xt_sph A FF adj (u:real^3)) =
                  inside(moi_s3xt_sph A FF adj v)` MP_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `moi_s3xt_sph A FF adj (u:real^3)` MOI_S3XT_SPHERE_FACTS) THEN
    MP_TAC(ISPEC `moi_s3xt_sph A FF adj (v:real^3)` MOI_S3XT_SPHERE_FACTS) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                 `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `u:real^3`]
    MOI_S3XT_CFG_V) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s3xt_sph A FF adj v` MP_TAC THENL
   [UNDISCH_TAC `moi_s3xt_sph A FF adj (u:real^3) = moi_s3xt_sph A FF adj v` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[moi_s3xt_sph] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3xt_sph; IN_UNION; IN_UNIONS; IN_ELIM_THM] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[]; ASM_MESON_TAC[]]);;

let MOI_S3XT_MEET = prove
 (`!(V:real^3->bool) adj A FF X u v.
     moi_s3xt_cfg V adj A FF X /\ u IN V /\ v IN V /\ ~(u = v)
     ==> (moi_s3xt_sph A FF adj u UNION inside(moi_s3xt_sph A FF adj u)) INTER
         (moi_s3xt_sph A FF adj v UNION inside(moi_s3xt_sph A FF adj v)) SUBSET
         (if adj u v then FF u v else {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                 `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `u:real^3`; `v:real^3`]
    MOI_S3XT_INT_DISJ) THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                 `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `u:real^3`; `v:real^3`]
    MOI_S3XT_INT_SPH) THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                 `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`; `u:real^3`]
    MOI_S3XT_INT_SPH) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `moi_s3xt_sph A FF adj (u:real^3) INTER moi_s3xt_sph A FF adj v SUBSET
                (if adj u v then FF u v else {})` MP_TAC THENL
   [ALL_TAC;
    MAP_EVERY UNDISCH_TAC
     [`DISJOINT (inside(moi_s3xt_sph A FF adj (u:real^3)))
                (inside(moi_s3xt_sph A FF adj v))`;
      `DISJOINT (inside(moi_s3xt_sph A FF adj (u:real^3))) (moi_s3xt_sph A FF adj v)`;
      `DISJOINT (inside(moi_s3xt_sph A FF adj (v:real^3))) (moi_s3xt_sph A FF adj u)`] THEN
    SET_TAC[]] THEN
  UNDISCH_TAC `moi_s3xt_cfg V adj A (FF:real^3->real^3->real^3->bool) X` THEN
  REWRITE_TAC[moi_s3xt_cfg] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_s3xt_sph] THEN
  MATCH_MP_TAC(SET_RULE
   `!a b (U1:(real^3->bool)->bool) U2 r.
      a INTER b SUBSET r /\ (!t. t IN U2 ==> a INTER t SUBSET r) /\
      (!t. t IN U1 ==> t INTER b SUBSET r) /\
      (!t. t IN U1 ==> !t'. t' IN U2 ==> t INTER t' SUBSET r)
      ==> (a UNION UNIONS U1) INTER (b UNION UNIONS U2) SUBSET r`) THEN
  REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT CONJ_TAC THENL
   [ASM_SIMP_TAC[];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `w:real^3 = u` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      SUBGOAL_THEN `adj (u:real^3) v /\ (FF:real^3->real^3->real^3->bool) v u = FF u v`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `DISJOINT ((A:real^3->real^3->bool) u) ((FF:real^3->real^3->real^3->bool) v w)` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!u v w. adj u v /\ w IN V /\ ~(w = u) /\ ~(w = v)
                                ==> DISJOINT ((A:real^3->real^3->bool) w) (FF u v)`)
            (concl th))) THEN
        ASM_REWRITE_TAC[];
        SET_TAC[]]];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN ASM_CASES_TAC `w:real^3 = v` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `DISJOINT ((A:real^3->real^3->bool) v) ((FF:real^3->real^3->real^3->bool) u w)` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!u v w. adj u v /\ w IN V /\ ~(w = u) /\ ~(w = v)
                                ==> DISJOINT ((A:real^3->real^3->bool) w) (FF u v)`)
            (concl th))) THEN
        ASM_REWRITE_TAC[];
        SET_TAC[]]];
    X_GEN_TAC `w:real^3` THEN DISCH_TAC THEN X_GEN_TAC `w':real^3` THEN DISCH_TAC THEN
    ASM_CASES_TAC `{u:real^3,w} = {v,w'}` THENL
     [SUBGOAL_THEN `w:real^3 = v /\ w' = (u:real^3)` (CONJUNCTS_THEN SUBST_ALL_TAC) THENL
       [UNDISCH_TAC `{u:real^3,w} = {v,w'}` THEN
        REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      SUBGOAL_THEN `DISJOINT ((FF:real^3->real^3->real^3->bool) u w) (FF v w')` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
          can (term_match [] `!u v u' v'. adj u v /\ adj u' v' /\ ~({u,v} = {u',v'})
                                ==> DISJOINT ((FF:real^3->real^3->real^3->bool) u v) (FF u' v')`)
            (concl th))) THEN
        ASM_REWRITE_TAC[];
        SET_TAC[]]]]);;

(* The cover: the balls fill the interior of X.  Off the finitely many      *)
(* vertices of triangulations of the spheres, a point of the interior of X  *)
(* on a sphere lies on exactly one disk FF v w, the spheres of v and w agree *)
(* near it, and the two local sides lie in the two balls (TWO_SIDES); so    *)
(* the union of the balls is open there, and connectedness finishes.        *)

let MOI_S3XT_CFG_G = prove
 (`!(V:real^3->bool) adj A FF X.
     moi_s3xt_cfg V adj A FF X
     ==> FINITE V /\ ~(V = {}) /\ compact X /\ connected (interior X) /\
         connected ((:real^3) DIFF X)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3xt_cfg] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_S3XT_BALL_SUB = prove
 (`!(A:real^3->real^3->bool) FF adj V v.
     v IN V
     ==> moi_s3xt_sph A FF adj v UNION inside(moi_s3xt_sph A FF adj v) SUBSET
         UNIONS {moi_s3xt_sph A FF adj u UNION inside(moi_s3xt_sph A FF adj u) | u IN V}`,
  REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_S3XT_SPH_INT = prove
 (`!(V:real^3->bool) adj A FF X v z.
     moi_s3xt_cfg V adj A FF X /\ v IN V /\ z IN moi_s3xt_sph A FF adj v /\
     z IN interior X
     ==> ?w. adj v w /\ z IN FF v w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                 `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`]
    MOI_S3XT_CFG_V) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(z:real^3) IN moi_s3xt_sph A FF adj v` THEN
  REWRITE_TAC[moi_s3xt_sph; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w0:real^3` STRIP_ASSUME_TAC)) THENL
   [MAP_EVERY UNDISCH_TAC
     [`(A:real^3->real^3->bool) v SUBSET frontier X`;
      `(z:real^3) IN (A:real^3->real^3->bool) v`;
      `(z:real^3) IN interior X`] THEN
    REWRITE_TAC[frontier] THEN SET_TAC[];
    EXISTS_TAC `w0:real^3` THEN ASM_REWRITE_TAC[]]);;

let MOI_S3XT_LOCAL_EQ = prove
 (`!(V:real^3->bool) adj A FF X v w z.
     moi_s3xt_cfg V adj A FF X /\ adj v w /\ z IN FF v w /\ z IN interior X
     ==> ?r0. &0 < r0 /\
              ball(z,r0) INTER moi_s3xt_sph A FF adj v = ball(z,r0) INTER FF v w /\
              ball(z,r0) INTER moi_s3xt_sph A FF adj w = ball(z,r0) INTER FF v w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                 `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`] MOI_S3XT_CFG_G) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `adj (w:real^3) v /\ ~(v = w) /\ v IN V /\ w IN V /\
                (FF:real^3->real^3->real^3->bool) w v = FF v w`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                   `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`; `w:real^3`]
      MOI_S3XT_CFG_E) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^3->real^3->bool) v SUBSET frontier X /\ A w SUBSET frontier X`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                     `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`]
        MOI_S3XT_CFG_V);
      MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                     `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `w:real^3`]
        MOI_S3XT_CFG_V)] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a b. adj a b /\ ~({a,b} = {v:real^3,w})
          ==> DISJOINT ((FF:real^3->real^3->real^3->bool) a b) (FF v w)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    UNDISCH_TAC `moi_s3xt_cfg V adj A (FF:real^3->real^3->real^3->bool) X` THEN
    REWRITE_TAC[moi_s3xt_cfg] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!u v u' v'. adj u v /\ adj u' v' /\ ~({u,v} = {u',v'})
                            ==> DISJOINT ((FF:real^3->real^3->real^3->bool) u v) (FF u' v')`)
        (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `C = frontier X UNION
                  UNIONS {(FF:real^3->real^3->real^3->bool) a b | a,b |
                          adj a b /\ ~({a,b} = {v:real^3,w})}` THEN
  SUBGOAL_THEN `closed (C:real^3->bool) /\ ~((z:real^3) IN C)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNION THEN REWRITE_TAC[FRONTIER_CLOSED] THEN
      MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{(FF:real^3->real^3->real^3->bool) a b | a IN V /\ b IN V}` THEN
        CONJ_TAC THENL
         [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:real^3->bool` THEN
          DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
          MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`] THEN ASM_REWRITE_TAC[] THEN
          MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`;
                         `A:real^3->real^3->bool`; `FF:real^3->real^3->real^3->bool`;
                         `X:real^3->bool`; `a:real^3`; `b:real^3`] MOI_S3XT_CFG_E) THEN
          ASM_SIMP_TAC[]];
        REWRITE_TAC[FORALL_IN_GSPEC] THEN REPEAT STRIP_TAC THEN
        MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`;
                       `A:real^3->real^3->bool`; `FF:real^3->real^3->real^3->bool`;
                       `X:real^3->bool`; `a:real^3`; `b:real^3`] MOI_S3XT_CFG_E) THEN
        ASM_SIMP_TAC[]];
      REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
      MATCH_MP_TAC(TAUT `~p /\ ~q ==> ~(p \/ q)`) THEN CONJ_TAC THENL
       [UNDISCH_TAC `(z:real^3) IN interior X` THEN REWRITE_TAC[frontier] THEN SET_TAC[];
        REWRITE_TAC[NOT_EXISTS_THM] THEN
        MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN STRIP_TAC THEN
        SUBGOAL_THEN `DISJOINT ((FF:real^3->real^3->real^3->bool) a b) (FF v w)` MP_TAC THENL
         [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
        MAP_EVERY UNDISCH_TAC
         [`(z:real^3) IN (FF:real^3->real^3->real^3->bool) v w`;
          `(z:real^3) IN (FF:real^3->real^3->real^3->bool) a b`] THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r0. &0 < r0 /\ ball(z:real^3,r0) INTER C = {}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `closed (C:real^3->bool)` THEN REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `r0:real` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!x:real^3. x IN ball(z,r0)
               ==> ~(x IN frontier X) /\
                   (!a b. adj a b /\ ~({a,b} = {v,w})
                          ==> ~(x IN (FF:real^3->real^3->real^3->bool) a b))`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((x:real^3) IN C)` MP_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`ball(z:real^3,r0) INTER C = {}`; `(x:real^3) IN ball(z,r0)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    EXPAND_TAC "C" THEN REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. adj v y /\ ~(y = w) ==> ~({v,y} = {v,w})` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                   `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`; `y:real^3`]
      MOI_S3XT_CFG_E) THEN
    ASM_SIMP_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. adj w y /\ ~(y = v) ==> ~({w,y} = {v,w})` ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `!b s t:real^3->bool. (!x. x IN b ==> (x IN s <=> x IN t)) ==> b INTER s = b INTER t`) THEN
  X_GEN_TAC `x:real^3` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME `(x:real^3) IN ball(z,r0)`) o check (fun th ->
    is_forall(concl th) && can (term_match [] `!x:real^3. x IN ball(z,r0) ==> P x`) (concl th))) THEN
  REWRITE_TAC[moi_s3xt_sph; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN STRIP_TAC THEN
  EQ_TAC THENL
   [DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THENL
     [MAP_EVERY UNDISCH_TAC
       [`(A:real^3->real^3->bool) v SUBSET frontier X`; `(x:real^3) IN (A:real^3->real^3->bool) v`;
        `~((x:real^3) IN frontier X)`] THEN
      SET_TAC[];
      ASM_CASES_TAC `y:real^3 = w` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_REWRITE_TAC[]; ASM_MESON_TAC[]]];
    DISCH_TAC THEN DISJ2_TAC THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC)) THENL
     [MAP_EVERY UNDISCH_TAC
       [`(A:real^3->real^3->bool) w SUBSET frontier X`; `(x:real^3) IN (A:real^3->real^3->bool) w`;
        `~((x:real^3) IN frontier X)`] THEN
      SET_TAC[];
      ASM_CASES_TAC `y:real^3 = v` THENL
       [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ASM_MESON_TAC[]]];
    DISCH_TAC THEN DISJ2_TAC THEN EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[]]);;

let MOI_S3XT_LOCAL_BALL = prove
 (`!(V:real^3->bool) adj A FF X c v z.
     moi_s3xt_cfg V adj A FF X /\ v IN V /\
     simplicial_complex c /\ (!k. k IN c ==> aff_dim k <= &2) /\
     combinatorial_manifold 2 c /\ UNIONS c = moi_s3xt_sph A FF adj v /\
     z IN moi_s3xt_sph A FF adj v /\ ~({z} IN c) /\ z IN interior X
     ==> ?r. &0 < r /\
             ball(z,r) SUBSET
             UNIONS {moi_s3xt_sph A FF adj u UNION inside(moi_s3xt_sph A FF adj u) | u IN V}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                 `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`; `z:real^3`]
    MOI_S3XT_SPH_INT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                 `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`; `w:real^3`;
                 `z:real^3`] MOI_S3XT_LOCAL_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r0:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^3) IN V /\ ~(v = w)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                   `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`; `w:real^3`]
      MOI_S3XT_CFG_E) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s3xt_sph A FF adj (v:real^3)`; `moi_s3xt_sph A FF adj (w:real^3)`;
                 `c:(real^3->bool)->bool`; `z:real^3`; `r0:real`] MOI_S3XT_TWO_SIDES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                     `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`]
        MOI_S3XT_CFG_V) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                     `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `w:real^3`]
        MOI_S3XT_CFG_V) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC MOI_S3XT_INT_DISJ THEN
      MAP_EVERY EXISTS_TAC [`V:real^3->bool`; `X:real^3->bool`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `p:real^3->bool`
    (X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC))) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`A:real^3->real^3->bool`; `FF:real^3->real^3->real^3->bool`;
                 `adj:real^3->real^3->bool`; `V:real^3->bool`; `v:real^3`] MOI_S3XT_BALL_SUB) THEN
  MP_TAC(ISPECL [`A:real^3->real^3->bool`; `FF:real^3->real^3->real^3->bool`;
                 `adj:real^3->real^3->bool`; `V:real^3->bool`; `w:real^3`] MOI_S3XT_BALL_SUB) THEN
  ASM_REWRITE_TAC[] THEN
  SPEC_TAC(`UNIONS {moi_s3xt_sph A FF adj u UNION inside(moi_s3xt_sph A FF adj u) |
                    u:real^3 IN V}`, `U:real^3->bool`) THEN
  MAP_EVERY UNDISCH_TAC
   [`p UNION q = ball(z:real^3,r) DIFF moi_s3xt_sph A FF adj v`;
    `(p:real^3->bool) SUBSET inside(moi_s3xt_sph A FF adj v)`;
    `(q:real^3->bool) SUBSET inside(moi_s3xt_sph A FF adj w)`] THEN
  SET_TAC[]);;

let MOI_S3XT_COVER = prove
 (`!(V:real^3->bool) adj A FF X.
     PL_SCHOENFLIES_3_STATEMENT /\ moi_s3xt_cfg V adj A FF X
     ==> interior X SUBSET
         UNIONS {moi_s3xt_sph A FF adj v UNION inside(moi_s3xt_sph A FF adj v) | v IN V}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                 `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`] MOI_S3XT_CFG_G) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v:real^3. v IN V
               ==> ?c. simplicial_complex c /\ (!k. k IN c ==> aff_dim k <= &2) /\
                       combinatorial_manifold 2 c /\ UNIONS c = moi_s3xt_sph A FF adj v`
  MP_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3XT_SPHERE_TRIANG THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                   `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`]
      MOI_S3XT_CFG_V) THEN
    ASM_SIMP_TAC[];
    REWRITE_TAC[RIGHT_IMP_EXISTS_THM; SKOLEM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `cc:real^3->(real^3->bool)->bool` (LABEL_TAC "cc"))] THEN
  ABBREV_TAC `V0 = {y:real^3 | ?v. v IN V /\
                                    {y} IN (cc:real^3->(real^3->bool)->bool) v}` THEN
  SUBGOAL_THEN `FINITE (V0:real^3->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `V0 = UNIONS (IMAGE (\v. {y:real^3 | {y} IN
                                (cc:real^3->(real^3->bool)->bool) v}) (V:real^3->bool))`
    SUBST1_TAC THENL
     [EXPAND_TAC "V0" THEN REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; EXTENSION] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`\y:real^3. {y}`; `(cc:real^3->(real^3->bool)->bool) v`]
      FINITE_IMAGE_INJ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
     [SET_TAC[];
      USE_THEN "cc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(v:real^3) IN V`))) THEN
      REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `BB = UNIONS {moi_s3xt_sph A FF adj v UNION inside(moi_s3xt_sph A FF adj v) |
                           v:real^3 IN V}` THEN
  SUBGOAL_THEN `closed (BB:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "BB" THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC COMPACT_UNIONS THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SIMPLE_IMAGE] THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      SUBGOAL_THEN `pl_sphere 2 (moi_s3xt_sph A FF adj (v:real^3))` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                       `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`]
          MOI_S3XT_CFG_V) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPEC `moi_s3xt_sph A FF adj (v:real^3)` MOI_S3XT_SPHERE_FACTS) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!z:real^3. z IN interior X DIFF V0 /\ z IN BB ==> z IN interior BB`
  (LABEL_TAC "key") THENL
   [X_GEN_TAC `z:real^3` THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?v. v IN V /\ ((z:real^3) IN moi_s3xt_sph A FF adj v \/
                                 z IN inside(moi_s3xt_sph A FF adj v))`
    (X_CHOOSE_THEN `v:real^3` (CONJUNCTS_THEN2 ASSUME_TAC DISJ_CASES_TAC)) THENL
     [UNDISCH_TAC `(z:real^3) IN BB` THEN EXPAND_TAC "BB" THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; IN_UNION] THEN MESON_TAC[];
      MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                     `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`;
                     `(cc:real^3->(real^3->bool)->bool) v`; `v:real^3`; `z:real^3`]
        MOI_S3XT_LOCAL_BALL) THEN
      ANTS_TAC THENL
       [USE_THEN "cc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(v:real^3) IN V`))) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~((z:real^3) IN V0)` THEN EXPAND_TAC "V0" THEN
        REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_INTERIOR] THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[];
      SUBGOAL_THEN `pl_sphere 2 (moi_s3xt_sph A FF adj (v:real^3))` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                       `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`]
          MOI_S3XT_CFG_V) THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `open(inside(moi_s3xt_sph A FF adj (v:real^3))) /\
                    inside(moi_s3xt_sph A FF adj v) SUBSET BB`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [MP_TAC(ISPEC `moi_s3xt_sph A FF adj (v:real^3)` MOI_S3XT_SPHERE_FACTS) THEN
          ASM_SIMP_TAC[];
          MP_TAC(ISPECL [`A:real^3->real^3->bool`; `FF:real^3->real^3->real^3->bool`;
                         `adj:real^3->real^3->bool`; `V:real^3->bool`; `v:real^3`]
            MOI_S3XT_BALL_SUB) THEN
          ASM_REWRITE_TAC[] THEN SET_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`BB:real^3->bool`; `inside(moi_s3xt_sph A FF adj (v:real^3))`]
        INTERIOR_MAXIMAL) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN inside(moi_s3xt_sph A FF adj v)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior X DIFF V0 SUBSET (BB:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`interior X DIFF V0:real^3->bool`; `BB:real^3->bool`]
      CONNECTED_INTER_FRONTIER) THEN
    ANTS_TAC THENL
     [REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC CONNECTED_OPEN_DIFF_COUNTABLE THEN
        ASM_SIMP_TAC[OPEN_INTERIOR; FINITE_IMP_COUNTABLE; DIMINDEX_3; ARITH];
        UNDISCH_TAC `~(V:real^3->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
        DISCH_THEN(X_CHOOSE_TAC `v:real^3`) THEN
        MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                       `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`]
          MOI_S3XT_CFG_SPHERE) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MP_TAC(ISPEC `moi_s3xt_sph A FF adj (v:real^3)` MOI_S3XT_SPHERE_FACTS) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MP_TAC(ISPEC `inside(moi_s3xt_sph A FF adj (v:real^3))` OPEN_IMP_INFINITE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`inside(moi_s3xt_sph A FF adj (v:real^3))`; `V0:real^3->bool`]
          INFINITE_DIFF_FINITE) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN
        DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
        MP_TAC(ISPECL [`A:real^3->real^3->bool`; `FF:real^3->real^3->real^3->bool`;
                       `adj:real^3->real^3->bool`; `V:real^3->bool`; `v:real^3`]
          MOI_S3XT_BALL_SUB) THEN
        ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^3` THEN
        MAP_EVERY UNDISCH_TAC
         [`(y:real^3) IN inside(moi_s3xt_sph A FF adj v)`; `~((y:real^3) IN V0)`;
          `inside(moi_s3xt_sph A FF adj (v:real^3)) SUBSET interior X`;
          `moi_s3xt_sph A FF adj (v:real^3) UNION inside(moi_s3xt_sph A FF adj v)
           SUBSET BB`] THEN
        SET_TAC[];
        UNDISCH_TAC `~(interior X DIFF V0 SUBSET (BB:real^3->bool))` THEN SET_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC o
               REWRITE_RULE[GSYM MEMBER_NOT_EMPTY; IN_INTER]) THEN
    SUBGOAL_THEN `(z:real^3) IN BB` ASSUME_TAC THENL
     [MP_TAC(ISPEC `BB:real^3->bool` FRONTIER_SUBSET_CLOSED) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(z:real^3) IN frontier BB` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^3) IN interior BB` MP_TAC THENL
     [USE_THEN "key" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `(z:real^3) IN frontier BB` THEN REWRITE_TAC[frontier] THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(z:real^3,r) INTER BB = {}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `closed (BB:real^3->bool)` THEN REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (ball(z:real^3,r) INTER interior X) /\
                ~(ball(z:real^3,r) INTER interior X = {})`
  STRIP_ASSUME_TAC THENL
   [SIMP_TAC[OPEN_INTER; OPEN_BALL; OPEN_INTERIOR] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `z:real^3` THEN ASM_REWRITE_TAC[IN_INTER; CENTRE_IN_BALL];
    ALL_TAC] THEN
  MP_TAC(ISPEC `ball(z:real^3,r) INTER interior X` OPEN_IMP_INFINITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ball(z:real^3,r) INTER interior X`; `V0:real^3->bool`]
    INFINITE_DIFF_FINITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
  MAP_EVERY UNDISCH_TAC
   [`interior X DIFF V0 SUBSET (BB:real^3->bool)`; `ball(z:real^3,r) INTER BB = {}`] THEN
  SET_TAC[]);;

(* ========================================================================= *)
(* Part 7: facts of the source tube.  moi_s3xt_sig t l v is the             *)
(* boundary sphere of the dual cell C_v: its part on Bd N and the splitting *)
(* disks at v (GRAPH_TUBE_DUAL_CELLS).  Every vertex has two neighbours,    *)
(* and C_v INTER Bd N has a point outside every other dual cell.            *)
(* ========================================================================= *)

let moi_s3xt_sig = new_definition
 `moi_s3xt_sig (t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (v:real^3) =
    (derived_dual_cell t l v INTER derived_frontier t l) UNION
    UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w | w |
            ~(w = v) /\ segment[v,w] IN l}`;;

let MOI_S3XT_TUBE_GRAPH = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3).
     moi_s33_tube t l h
     ==> graph_in_complex t l /\ simplicial_complex l /\ FINITE l /\
         (!s. s IN l ==> aff_dim s <= &1) /\ l SUBSET t /\
         connected (UNIONS l) /\ (?a. a IN l /\ aff_dim a = &1) /\
         FINITE {v:real^3 | {v} IN l}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_tube] THEN STRIP_TAC THEN
  SUBGOAL_THEN `l SUBSET (t:(real^3->bool)->bool) /\ lf_simplicial_complex t /\
                simplicial_subcomplex l t /\ (!s. s IN l ==> aff_dim s <= &1)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `graph_in_complex t (l:(real^3->bool)->bool)` THEN
    REWRITE_TAC[graph_in_complex; simplicial_subcomplex] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `t:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {v:real^3 | {v} IN l}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\v:real^3. {v}`; `l:(real^3->bool)->bool`] FINITE_IMAGE_INJ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_S3XT_SRC_CELL = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) v.
     moi_s33_tube t l h /\ {v} IN l
     ==> pl_cell_with_boundary 3 (derived_dual_cell t l v) (moi_s3xt_sig t l v) /\
         pl_ball 3 (derived_dual_cell t l v) /\
         frontier (derived_dual_cell t l v) = moi_s3xt_sig t l v /\
         pl_sphere 2 (moi_s3xt_sig t l v) /\
         pl_polyhedron (derived_dual_cell t l v) /\
         pl_polyhedron (derived_dual_cell t l v INTER derived_frontier t l) /\
         compact (derived_dual_cell t l v) /\
         v IN derived_dual_cell t l v /\
         (!w. {w} IN l /\ w IN derived_dual_cell t l v ==> w = v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
    GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `v:real^3` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[GSYM moi_s3xt_sig] THEN STRIP_TAC THEN
  SUBGOAL_THEN `v IN derived_dual_cell t l (v:real^3) /\
                (!w. {w} IN l /\ w IN derived_dual_cell t l v ==> w = v)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{w:real^3 | {w} IN t /\ w IN derived_dual_cell t l v} = {v}` THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING] THEN DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ASM_MESON_TAC[SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (derived_dual_cell t l (v:real^3) INTER derived_frontier t l)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `v:real^3`]
      MOI_FTA_SETUP) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `v:real^3`]
      MOI_FTA_CELL_FRONTIER_CHAINS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_FTA_CHAIN_UNIONS_POLY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [pl_cell_with_boundary] o check (fun th ->
    can (term_match [] `pl_cell_with_boundary 3 c (moi_s3xt_sig t l v)`) (concl th))) THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^3`
    (X_CHOOSE_THEN `q:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `frontier (derived_dual_cell t l (v:real^3)) = moi_s3xt_sig t l v`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCD_BALL_FRONTIER THEN
    EXISTS_TAC `q:real^3->real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_polyhedron (derived_dual_cell t l (v:real^3))` ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (k:real^3->bool,derived_dual_cell t l (v:real^3))
                                  (p:real^3->real^3,q)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (p:real^3->real^3) k = derived_dual_cell t l v` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC PL_POLYHEDRON_PL_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC POLYTOPE_IMP_PL_POLYHEDRON THEN ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_homeomorphism (relative_frontier k,
                                  frontier (derived_dual_cell t l (v:real^3)))
                                 (p:real^3->real^3,q)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCD_BALL_BOUNDARY_PLH THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `pl_ball 3 (derived_dual_cell t l (v:real^3)) /\
                pl_sphere 2 (moi_s3xt_sig t l v)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[pl_ball] THEN
      MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `p:real^3->real^3`; `q:real^3->real^3`] THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[pl_sphere; ARITH_RULE `2 + 1 = 3`] THEN
      MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `p:real^3->real^3`; `q:real^3->real^3`] THEN
      UNDISCH_TAC `frontier (derived_dual_cell t l (v:real^3)) = moi_s3xt_sig t l v` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (derived_dual_cell t l (v:real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3XT_SRC_DISK = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) u v.
     moi_s33_tube t l h /\ ~(u = v) /\ segment[u,v] IN l
     ==> {u} IN l /\ {v} IN l /\
         pl_cell_with_boundary 2
           (derived_dual_cell t l u INTER derived_dual_cell t l v)
           (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
            derived_frontier t l) /\
         midpoint(u,v) IN derived_dual_cell t l u INTER derived_dual_cell t l v /\
         compact (derived_dual_cell t l u INTER derived_dual_cell t l v) /\
         pl_polyhedron (derived_dual_cell t l u INTER derived_dual_cell t l v) /\
         pl_polyhedron (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                        derived_frontier t l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3XT_EDGE_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `u:real^3`] MOI_S3XT_SRC_CELL) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `v:real^3`] MOI_S3XT_SRC_CELL) THEN
  ASM_REWRITE_TAC[] THEN REPEAT(DISCH_THEN STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
    GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_polyhedron (derived_dual_cell t l u INTER derived_dual_cell t l (v:real^3))`
  ASSUME_TAC THENL [MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `midpoint(u,v) IN derived_dual_cell t l u INTER
                               derived_dual_cell t l (v:real^3)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `derived_dual_cell t l u INTER derived_dual_cell t l v INTER UNIONS l =
                 {midpoint(u:real^3,v)}` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_polyhedron (derived_dual_cell t l (u:real^3) INTER derived_dual_cell t l v INTER
                   derived_frontier t l)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `derived_dual_cell t l u INTER derived_dual_cell t l v INTER derived_frontier t l =
      (derived_dual_cell t l u INTER derived_frontier t l) INTER
      (derived_dual_cell t l (v:real^3) INTER derived_frontier t l)`
    SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC PL_POLYHEDRON_INTER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (derived_dual_cell t l u INTER derived_dual_cell t l (v:real^3))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S3XT_SRC_APART = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) u v.
     moi_s33_tube t l h /\ {u} IN l /\ {v} IN l /\ ~(u = v) /\ ~(segment[u,v] IN l)
     ==> derived_dual_cell t l u INTER derived_dual_cell t l v = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
    GRAPH_TUBE_DUAL_CELLS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

(* Every vertex lies on an edge (the graph is connected and has an edge),  *)
(* so (no vertex of degree one) every vertex has two neighbours.           *)

let MOI_S3XT_VERTEX_EDGE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) v.
     moi_s33_tube t l h /\ {v} IN l
     ==> ?s. s IN l /\ aff_dim s = &1 /\ v IN s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `!r:real^3->bool. r IN l /\ v IN r ==> r = {v}` ASSUME_TAC THENL
   [X_GEN_TAC `r:real^3->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `aff_dim (r:real^3->bool) = &0` MP_TAC THENL
     [MP_TAC(ISPEC `r:real^3->bool` AFF_DIM_GE) THEN
      SUBGOAL_THEN `aff_dim (r:real^3->bool) <= &1 /\ ~(aff_dim r = &1) /\
                    ~(aff_dim r = -- &1)` MP_TAC THENL
       [REPEAT CONJ_TAC THENL
         [ASM_MESON_TAC[];
          ASM_MESON_TAC[];
          REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN ASM SET_TAC[]];
        INT_ARITH_TAC];
      REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_THEN `a:real^3` SUBST_ALL_TAC) THEN
      UNDISCH_TAC `(v:real^3) IN {a}` THEN REWRITE_TAC[IN_SING] THEN
      DISCH_THEN SUBST1_TAC THEN REFL_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v:real^3) IN a) /\ ~(a:real^3->bool = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[];
      REWRITE_TAC[GSYM AFF_DIM_EQ_MINUS1] THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  UNDISCH_TAC `connected (UNIONS l:real^3->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC [`{v:real^3}`; `UNIONS {r:real^3->bool | r IN l /\ ~(v IN r)}`] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[CLOSED_SING];
    MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `r:real^3->bool` THEN STRIP_TAC THEN
      UNDISCH_TAC `simplicial_complex (l:(real^3->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPEC `r:real^3->bool` o CONJUNCT1 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[SIMPLEX_IMP_CLOSED]];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_SING; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(v:real^3) IN r` THENL
     [DISJ1_TAC THEN
      SUBGOAL_THEN `r = {v:real^3}` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `(y:real^3) IN {v}` THEN REWRITE_TAC[IN_SING];
      DISJ2_TAC THEN EXISTS_TAC `r:real^3->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_SING; IN_UNIONS] THEN
    EXISTS_TAC `v:real^3` THEN REWRITE_TAC[] THEN EXISTS_TAC `{v:real^3}` THEN
    ASM_REWRITE_TAC[IN_SING];
    UNDISCH_TAC `~(a:real^3->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^3`) THEN EXISTS_TAC `y:real^3` THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    CONJ_TAC THEN EXISTS_TAC `a:real^3->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_S3XT_TWO_NBRS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) v.
     moi_s33_tube t l h /\ {v} IN l
     ==> ?w1 w2. ~(w1 = w2) /\ ~(w1 = v) /\ ~(w2 = v) /\
                 segment[v,w1] IN l /\ segment[v,w2] IN l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  SUBGOAL_THEN `~(CARD {s | s IN l /\ aff_dim s = &1 /\ (v:real^3) IN s} = 1)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_tube t l (h:real^3->real^3)` THEN REWRITE_TAC[moi_s33_tube] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {s | s IN l /\ aff_dim s = &1 /\ (v:real^3) IN s} /\
                ~({s | s IN l /\ aff_dim s = &1 /\ (v:real^3) IN s} = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^3->bool)->bool` THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      MATCH_MP_TAC MOI_S3XT_VERTEX_EDGE THEN
      MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `h:real^3->real^3`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `E = {s:real^3->bool | s IN l /\ aff_dim s = &1 /\ v IN s}` THEN
  SUBGOAL_THEN `?s1 s2:real^3->bool. s1 IN E /\ s2 IN E /\ ~(s1 = s2)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~(CARD (E:(real^3->bool)->bool) <= 1)` MP_TAC THENL
     [MP_TAC(ISPEC `E:(real^3->bool)->bool` CARD_EQ_0) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(CARD (E:(real^3->bool)->bool) = 1)` THEN ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPEC `E:(real^3->bool)->bool` CARD_LE_1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NOT_EXISTS_THM] THEN DISCH_TAC THEN
    UNDISCH_TAC `~(E:(real^3->bool)->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `s1:real^3->bool`) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `s1:real^3->bool`) THEN
    REWRITE_TAC[SUBSET; IN_SING; NOT_FORALL_THM; NOT_IMP] THEN
    DISCH_THEN(X_CHOOSE_THEN `s2:real^3->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`s1:real^3->bool`; `s2:real^3->bool`] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN E ==> ?w. ~(w = v) /\ s = segment[v,w] /\ {w} IN l`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^3->bool` THEN EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    STRIP_TAC THEN MATCH_MP_TAC MOI_FSA_EDGE_SEG THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(MATCH_MP th (ASSUME `(s1:real^3->bool) IN E`)) THEN
    MP_TAC(MATCH_MP th (ASSUME `(s2:real^3->bool) IN E`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `w2:real^3` STRIP_ASSUME_TAC) THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`w1:real^3`; `w2:real^3`] THEN
  SUBGOAL_THEN `segment[v:real^3,w1] IN l /\ segment[v,w2] IN l` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`(s1:real^3->bool) IN E`; `(s2:real^3->bool) IN E`] THEN
    EXPAND_TAC "E" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]);;

let MOI_S3XT_NBR_FINITE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) v.
     moi_s33_tube t l h
     ==> FINITE {w:real^3 | ~(w = v) /\ segment[v,w] IN l}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{w:real^3 | {w} IN l}` THEN
  ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `v:real^3`; `w:real^3`]
    MOI_S3XT_EDGE_VERTICES) THEN
  ASM_MESON_TAC[]);;

let MOI_S3XT_SPHERE2_CONNECTED = prove
 (`!s:real^3->bool. pl_sphere 2 s ==> connected s`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_SCD_PL_SPHERE_2_HOMEOMORPHIC) THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_CONNECTEDNESS) THEN
  SIMP_TAC[CONNECTED_SPHERE; DIMINDEX_3; ARITH]);;

let MOI_S3XT_SRC_FREE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) v.
     moi_s33_tube t l h /\
     (!u v w. {u} IN l /\ {v} IN l /\ {w} IN l /\ ~(u = v) /\ ~(u = w) /\ ~(v = w)
              ==> derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                  derived_dual_cell t l w = {}) /\
     {v} IN l
     ==> ?z. z IN derived_dual_cell t l v INTER derived_frontier t l /\
             !w. {w} IN l /\ ~(w = v) ==> ~(z IN derived_dual_cell t l w)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `v:real^3`] MOI_S3XT_SRC_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `v:real^3`] MOI_S3XT_TWO_NBRS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w1:real^3` (X_CHOOSE_THEN `w2:real^3` STRIP_ASSUME_TAC)) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(LABEL_TAC "neg" o REWRITE_RULE[NOT_FORALL_THM; NOT_IMP; IMP_CONJ] o
             REWRITE_RULE[NOT_EXISTS_THM; IN_INTER; TAUT `~(p /\ q) <=> p ==> ~q`]) THEN
  ABBREV_TAC `e1 = derived_dual_cell t l v INTER derived_dual_cell t l (w1:real^3)` THEN
  ABBREV_TAC `e2 = UNIONS {derived_dual_cell t l v INTER derived_dual_cell t l w | w |
                           ~(w = v) /\ segment[v,w] IN l /\ ~(w = w1:real^3)}` THEN
  SUBGOAL_THEN `closed (e1:real^3->bool) /\ closed (e2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [EXPAND_TAC "e1" THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `v:real^3`; `w1:real^3`] MOI_S3XT_SRC_DISK) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      EXPAND_TAC "e2" THEN MATCH_MP_TAC CLOSED_UNIONS THEN
      REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_SUBSET THEN
        EXISTS_TAC `{w:real^3 | ~(w = v) /\ segment[v,w] IN l}` THEN CONJ_TAC THENL
         [MATCH_MP_TAC MOI_S3XT_NBR_FINITE THEN
          MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `h:real^3->real^3`] THEN
          ASM_REWRITE_TAC[];
          SET_TAC[]];
        X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `v:real^3`; `w:real^3`] MOI_S3XT_SRC_DISK) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_s3xt_sig t l v SUBSET (e1:real^3->bool) UNION e2` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN
    REWRITE_TAC[moi_s3xt_sig; SUBSET; IN_UNION; IN_INTER; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN
    SUBGOAL_THEN `!w. ~(w = v) /\ segment[v,w] IN l /\ z IN derived_dual_cell t l w
                      ==> z IN derived_dual_cell t l (w1:real^3) \/
                          (?w'. (~(w' = v) /\ segment[v,w'] IN l /\ ~(w' = w1)) /\
                                z IN derived_dual_cell t l w')`
    ASSUME_TAC THENL
     [X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN ASM_CASES_TAC `w:real^3 = w1` THENL
       [DISJ1_TAC THEN UNDISCH_TAC `(z:real^3) IN derived_dual_cell t l w` THEN
        ASM_REWRITE_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 STRIP_ASSUME_TAC (X_CHOOSE_THEN `w:real^3`
      STRIP_ASSUME_TAC)) THENL
     [USE_THEN "neg" (fun th -> MP_TAC(MATCH_MP (MATCH_MP (SPEC `z:real^3` th)
        (ASSUME `(z:real^3) IN derived_dual_cell t l v`))
        (ASSUME `(z:real^3) IN derived_frontier t l`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `segment[v:real^3,w] IN l` ASSUME_TAC THENL
       [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                       `h:real^3->real^3`; `v:real^3`; `w:real^3`] MOI_S3XT_SRC_APART) THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC [`(z:real^3) IN derived_dual_cell t l v`;
                               `(z:real^3) IN derived_dual_cell t l w`] THEN
        SET_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `w:real^3` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `w:real^3` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(e1:real^3->bool) INTER e2 = {}` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; UNIONS_GSPEC; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC (X_CHOOSE_THEN `w:real^3`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `{w1:real^3} IN l /\ {w:real^3} IN l` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `v:real^3`; `w1:real^3`] MOI_S3XT_SRC_DISK); MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `v:real^3`; `w:real^3`] MOI_S3XT_SRC_DISK)] THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `!u v w. {u} IN l /\ {v} IN l /\ {w} IN l /\ ~(u = v) /\ ~(u = w) /\
                         ~(v = w)
                         ==> derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                             derived_dual_cell (t:(real^3->bool)->bool) l (w:real^3) =
                             {}` THEN
    DISCH_THEN(MP_TAC o SPECL [`v:real^3`; `w1:real^3`; `w:real^3`]) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC [`(z:real^3) IN derived_dual_cell t l v`;
                           `(z:real^3) IN derived_dual_cell t l w1`;
                           `(z:real^3) IN derived_dual_cell t l w`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `midpoint(v,w1) IN (e1:real^3->bool) /\ midpoint(v,w2) IN (e2:real^3->bool) /\
                e1 SUBSET moi_s3xt_sig t l v /\ e2 SUBSET moi_s3xt_sig t l v`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["e1"; "e2"] THEN REPEAT CONJ_TAC THENL
     [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `v:real^3`; `w1:real^3`] MOI_S3XT_SRC_DISK) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `w2:real^3` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `v:real^3`; `w2:real^3`] MOI_S3XT_SRC_DISK) THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      REWRITE_TAC[moi_s3xt_sig; SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN DISJ2_TAC THEN EXISTS_TAC `w1:real^3` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[moi_s3xt_sig; SUBSET; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
      X_GEN_TAC `z:real^3` THEN
      DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN DISJ2_TAC THEN
      EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (moi_s3xt_sig t l (v:real^3))` MP_TAC THENL
   [MATCH_MP_TAC MOI_S3XT_SPHERE2_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[CONNECTED_CLOSED; NOT_EXISTS_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`e1:real^3->bool`; `e2:real^3->bool`]) THEN
  ASM_REWRITE_TAC[] THEN
  MAP_EVERY UNDISCH_TAC
   [`(e1:real^3->bool) INTER e2 = {}`; `midpoint(v:real^3,w1) IN e1`;
    `midpoint(v:real^3,w2) IN e2`; `(e1:real^3->bool) SUBSET moi_s3xt_sig t l v`;
    `(e2:real^3->bool) SUBSET moi_s3xt_sig t l v`] THEN
  SET_TAC[]);;

(* ========================================================================= *)
(* Part 8: the target X = UNIONS x.  With 26.6 on its boundary              *)
(* surface, the interior of X is the bounded complementary component and    *)
(* the complement of X is the outside, both connected (XFACTS).  SYM_SKOLEM *)
(* chooses one object per edge, symmetric in the ends; FF are the PL disks  *)
(* of FDISK at radius rho / 2.                                               *)
(* ========================================================================= *)

let MOI_S3XT_XFACTS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (x:(real^3->bool)->bool).
     moi_s33_inv t l h e x /\ ~(IMAGE h (UNIONS l) = {})
     ==> FINITE x /\ pl_polyhedron (UNIONS x) /\ compact (UNIONS x) /\
         frontier (UNIONS x) SUBSET UNIONS x /\
         connected (interior (UNIONS x)) /\ connected ((:real^3) DIFF UNIONS x) /\
         IMAGE h (UNIONS l) SUBSET interior (UNIONS x) /\
         UNIONS x SUBSET interior (IMAGE h (derived_nbhd t l)) /\
         connected (frontier (UNIONS x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_inv; moi_s33_x2] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` BOUNDARY_COMPLEX_SURFACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `x:(real^3->bool)->bool` COMPLEX_BOUNDARY_FRONTIER_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
  SUBGOAL_THEN `FINITE (boundary_complex (x:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `x:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `simplicial_subcomplex (boundary_complex x) (x:(real^3->bool)->bool)` THEN
    SIMP_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  ABBREV_TAC `X = UNIONS (x:(real^3->bool)->bool)` THEN
  SUBGOAL_THEN `pl_polyhedron (X:real^3->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[pl_polyhedron] THEN
    EXISTS_TAC `x:(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
    MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (X:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `frontier X SUBSET (X:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FRONTIER_SUBSET_CLOSED THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED]; ALL_TAC] THEN
  SUBGOAL_THEN `~(interior X:real^3->bool = {})` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`~(IMAGE (h:real^3->real^3) (UNIONS l) = {})`;
      `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior X`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(frontier X:real^3->bool = {})` ASSUME_TAC THENL
   [REWRITE_TAC[FRONTIER_EQ_EMPTY; DE_MORGAN_THM] THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `~(interior X:real^3->bool = {})` THEN SET_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `compact (X:real^3->bool)` THEN
      ASM_REWRITE_TAC[COMPACT_EQ_BOUNDED_CLOSED; NOT_BOUNDED_UNIV]];
    ALL_TAC] THEN
  MP_TAC MOI_S3XT_266 THEN REWRITE_TAC[MOISE_266_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `boundary_complex (x:(real^3->bool)->bool)`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `O = outside (frontier X:real^3->bool)` THEN
  SUBGOAL_THEN `b IN components ((:real^3) DIFF frontier X) /\
                O IN components ((:real^3) DIFF frontier X)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `open (b:real^3->bool) /\ connected b /\ open (O:real^3->bool) /\ connected O /\
                b UNION O = (:real^3) DIFF frontier X`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open ((:real^3) DIFF frontier X)` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM closed; FRONTIER_CLOSED]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[OPEN_COMPONENTS];
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      ASM_MESON_TAC[OPEN_COMPONENTS];
      ASM_MESON_TAC[IN_COMPONENTS_CONNECTED];
      MP_TAC(ISPEC `(:real^3) DIFF frontier X` UNIONS_COMPONENTS) THEN
      ASM_REWRITE_TAC[UNIONS_2] THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(:real^3) DIFF frontier X = interior X UNION ((:real^3) DIFF X) /\
                DISJOINT (interior X) ((:real^3) DIFF X) /\
                open (interior X) /\ open ((:real^3) DIFF X)`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[OPEN_INTERIOR; GSYM closed] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
    MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `frontier X SUBSET (X:real^3->bool)` THEN
    REWRITE_TAC[frontier] THEN ASM_SIMP_TAC[CLOSURE_CLOSED; COMPACT_IMP_CLOSED] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(O:real^3->bool) SUBSET (:real^3) DIFF X` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`O:real^3->bool`; `interior X:real^3->bool`; `(:real^3) DIFF X`]
      MOI_S3XT_CONN_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `bounded (O:real^3->bool)` MP_TAC THENL
     [MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `X:real^3->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED] THEN
      MP_TAC(ISPEC `X:real^3->bool` INTERIOR_SUBSET) THEN ASM SET_TAC[];
      EXPAND_TAC "O" THEN REWRITE_TAC[] THEN MATCH_MP_TAC UNBOUNDED_OUTSIDE THEN
      MATCH_MP_TAC BOUNDED_SUBSET THEN EXISTS_TAC `X:real^3->bool` THEN
      ASM_SIMP_TAC[COMPACT_IMP_BOUNDED]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(b:real^3->bool) SUBSET interior X` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`b:real^3->bool`; `interior X:real^3->bool`; `(:real^3) DIFF X`]
      MOI_S3XT_CONN_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN DISCH_TAC THEN
    UNDISCH_TAC `~(interior X:real^3->bool = {})` THEN
    MAP_EVERY UNDISCH_TAC
     [`(b:real^3->bool) SUBSET (:real^3) DIFF X`;
      `(O:real^3->bool) SUBSET (:real^3) DIFF X`;
      `b UNION O = (:real^3) DIFF frontier X`;
      `(:real^3) DIFF frontier X = interior X UNION ((:real^3) DIFF X)`;
      `DISJOINT (interior X) ((:real^3) DIFF X)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `interior X = (b:real^3->bool) /\ (:real^3) DIFF X = O` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(b:real^3->bool) SUBSET interior X`;
      `(O:real^3->bool) SUBSET (:real^3) DIFF X`;
      `b UNION O = (:real^3) DIFF frontier X`;
      `(:real^3) DIFF frontier X = interior X UNION ((:real^3) DIFF X)`;
      `DISJOINT (interior X) ((:real^3) DIFF X)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* One choice per edge of l, the same for both orders of the ends.          *)

let MOI_S3XT_SYM_SKOLEM = prove
 (`!(l:(real^3->bool)->bool) (P:real^3->real^3->A->bool).
     (!u v. ~(u = v) /\ segment[u,v] IN l ==> ?x. P u v x) /\
     (!u v x. P u v x ==> P v u x)
     ==> ?f. (!u v. f u v = f v u) /\
             (!u v. ~(u = v) /\ segment[u,v] IN l ==> P u v (f u v))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "ex") (LABEL_TAC "sym")) THEN
  EXISTS_TAC `\u v:real^3. @x:A. !u' v'. ~(u' = v') /\ segment[u',v'] = segment[u,v]
                                         ==> P u' v' x` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REWRITE_TAC[CONJUNCT1 SEGMENT_SYM]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?x:A. !u' v'. ~(u' = v') /\ segment[u',v'] = segment[u:real^3,v]
                              ==> P u' v' x`
  MP_TAC THENL
   [USE_THEN "ex" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `~(u:real^3 = v)`) (ASSUME `segment[u:real^3,v] IN l`))) THEN
    DISCH_THEN(X_CHOOSE_TAC `x:A`) THEN EXISTS_TAC `x:A` THEN
    MAP_EVERY X_GEN_TAC [`u':real^3`; `v':real^3`] THEN
    REWRITE_TAC[SEGMENT_EQ] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(u':real^3 = u /\ v' = v) \/ (u' = v /\ v' = u)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{u':real^3,v'} = {u,v}` THEN
      REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    DISCH_THEN(MP_TAC o SELECT_RULE) THEN
    DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN ASM_REWRITE_TAC[]]);;

let MOI_S3XT_HD_RIM = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c u v.
     moi_s33_hd t l h e c /\ ~(u = v) /\ segment[u,v] IN l
     ==> pseudo_cell (e(segment[u,v])) (moi_s33_rim t l h u v) (h(midpoint(u,v))) /\
         e(segment[u,v]) INTER frontier (IMAGE h (derived_nbhd t l)) =
         moi_s33_rim t l h u v`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_hd] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let MOI_S3XT_FF = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool) rho.
     MOISE_324_STATEMENT /\
     (!d jd:real^3->bool. pl_polyhedron d /\ disk_with_boundary d jd /\ pl_sphere 1 jd
                          ==> pl_cell_with_boundary 2 d jd) /\
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ &0 < rho /\
     (!u v. ~(u = v) /\ segment[u,v] IN l
            ==> ball(h(midpoint(u,v)),&2 * rho) SUBSET interior (UNIONS x))
     ==> ?FF. (!u v. FF u v = FF v u) /\
              !u v. ~(u = v) /\ segment[u,v] IN l
                    ==> pl_cell_with_boundary 2 (FF u v)
                          (e(segment[u,v]) INTER frontier (UNIONS x)) /\
                        FF u v SUBSET UNIONS x /\
                        FF u v INTER frontier (UNIONS x) =
                        e(segment[u,v]) INTER frontier (UNIONS x) /\
                        FF u v SUBSET e(segment[u,v]) UNION ball(h(midpoint(u,v)),rho / &2) /\
                        (e(segment[u,v]) INTER UNIONS x) DIFF ball(h(midpoint(u,v)),rho / &2)
                        SUBSET FF u v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`l:(real^3->bool)->bool`;
    `\u v (fd:real^3->bool).
       pl_cell_with_boundary 2 fd (e(segment[u,v]) INTER frontier (UNIONS x)) /\
       fd SUBSET UNIONS x /\
       fd INTER frontier (UNIONS x) = e(segment[u,v]) INTER frontier (UNIONS x) /\
       fd SUBSET e(segment[u,v]) UNION ball((h:real^3->real^3)(midpoint(u,v)),rho / &2) /\
       (e(segment[u,v]) INTER UNIONS x) DIFF ball(h(midpoint(u,v)),rho / &2) SUBSET fd`]
    MOI_S3XT_SYM_SKOLEM) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`; `fd:real^3->bool`] THEN
    REWRITE_TAC[ISPECL [`v:real^3`; `u:real^3`] (CONJUNCT1 SEGMENT_SYM);
                ISPECL [`v:real^3`; `u:real^3`] MIDPOINT_SYM]] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_s33_inv t l h e (x:(real^3->bool)->bool)` THEN
  REWRITE_TAC[moi_s33_inv; moi_s33_x2; moi_s33_traces] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `u:real^3`; `v:real^3`] MOI_S3XT_HD_RIM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_S3XT_FDISK THEN
  EXISTS_TAC `moi_s33_rim t l h u v` THEN ASM_SIMP_TAC[REAL_HALF] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball((h:real^3->real^3)(midpoint(u,v)),&2 * rho)` THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[pl_polyhedron] THEN EXISTS_TAC `x:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (x:(real^3->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary; lf_simplicial_complex] THEN
    MESON_TAC[SIMPLEX_IMP_POLYTOPE];
    SUBGOAL_THEN `moi_s33_rim t l h u v SUBSET
                  frontier (IMAGE (h:real^3->real^3) (derived_nbhd t l))`
    MP_TAC THENL
     [UNDISCH_TAC `e(segment[u:real^3,v]) INTER
                   frontier (IMAGE (h:real^3->real^3) (derived_nbhd t l)) =
                   moi_s33_rim t l h u v` THEN SET_TAC[];
      UNDISCH_TAC `UNIONS x SUBSET interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
      REWRITE_TAC[frontier] THEN SET_TAC[]]]);;

(* ========================================================================= *)
(* Part 9: the context of the construction and the sphere maps.             *)
(* moi_s3xt_ctx collects the data: the handle decomposition, X, the match   *)
(* g with its inverse g', the triple condition, the radius and the disks FF.*)
(* PHI: PL homeomorphisms of the splitting disks onto the FF extending g    *)
(* (2D cone extension); PSI: one map on Bd N and all splitting disks, a PL  *)
(* homeomorphism of each sphere moi_s3xt_sig v onto moi_s3xt_sph v.         *)
(* ========================================================================= *)

let moi_s3xt_ctx = new_definition
 `moi_s3xt_ctx (t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (h:real^3->real^3)
               (e:(real^3->bool)->real^3->bool) (c:real^3->real^3->bool)
               (x:(real^3->bool)->bool) (g:real^3->real^3) (g':real^3->real^3)
               (FF:real^3->real^3->real^3->bool) (rho:real) <=>
    moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\
    pl_homeomorphism (derived_frontier t l,frontier (UNIONS x)) (g,g') /\
    (!v. {v} IN l
         ==> IMAGE g (derived_dual_cell t l v INTER derived_frontier t l) =
             c v INTER frontier (UNIONS x)) /\
    (!u v. ~(u = v) /\ segment[u,v] IN l
           ==> IMAGE g (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                        derived_frontier t l) =
               e(segment[u,v]) INTER frontier (UNIONS x)) /\
    (!u v w. {u} IN l /\ {v} IN l /\ {w} IN l /\ ~(u = v) /\ ~(u = w) /\ ~(v = w)
             ==> derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                 derived_dual_cell t l w = {}) /\
    compact (IMAGE h (derived_nbhd t l)) /\ derived_nbhd t l SUBSET UNIONS t /\
    &0 < rho /\
    (!u v. ~(u = v) /\ segment[u,v] IN l
           ==> ball(h(midpoint(u,v)),&2 * rho) SUBSET interior (UNIONS x) /\
               (!u' v'. ~(u' = v') /\ segment[u',v'] IN l /\
                        ~(segment[u',v'] = segment[u,v])
                        ==> ball(h(midpoint(u,v)),&2 * rho) INTER e(segment[u',v']) = {} /\
                            &3 * rho <= dist(h(midpoint(u,v)),h(midpoint(u',v')))) /\
               (!w. {w} IN l /\ ~(w = u) /\ ~(w = v)
                    ==> ball(h(midpoint(u,v)),&2 * rho) INTER c w = {})) /\
    (!u v. FF u v = FF v u) /\
    (!u v. ~(u = v) /\ segment[u,v] IN l
           ==> pl_cell_with_boundary 2 (FF u v) (e(segment[u,v]) INTER frontier (UNIONS x)) /\
               FF u v SUBSET UNIONS x /\
               FF u v INTER frontier (UNIONS x) = e(segment[u,v]) INTER frontier (UNIONS x) /\
               FF u v SUBSET e(segment[u,v]) UNION ball(h(midpoint(u,v)),rho / &2) /\
               (e(segment[u,v]) INTER UNIONS x) DIFF ball(h(midpoint(u,v)),rho / &2)
               SUBSET FF u v)`;;

let MOI_S3XT_CTX_BASE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho.
     moi_s3xt_ctx t l h e c x g g' FF rho
     ==> moi_s33_hd t l h e c /\ moi_s33_tube t l h /\ moi_s33_inv t l h e x /\
         pl_homeomorphism (derived_frontier t l,frontier (UNIONS x)) (g,g') /\
         (!u v w. {u} IN l /\ {v} IN l /\ {w} IN l /\ ~(u = v) /\ ~(u = w) /\ ~(v = w)
                  ==> derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                      derived_dual_cell t l w = {}) /\
         compact (IMAGE h (derived_nbhd t l)) /\ &0 < rho /\
         (!u v. FF u v = FF v u)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3xt_ctx] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[moi_s33_hd]);;

let MOI_S3XT_CTX_EDGE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho u v.
     moi_s3xt_ctx t l h e c x g g' FF rho /\ ~(u = v) /\ segment[u,v] IN l
     ==> pl_cell_with_boundary 2 (FF u v) (e(segment[u,v]) INTER frontier (UNIONS x)) /\
         FF u v SUBSET UNIONS x /\
         FF u v INTER frontier (UNIONS x) = e(segment[u,v]) INTER frontier (UNIONS x) /\
         FF u v SUBSET e(segment[u,v]) UNION ball(h(midpoint(u,v)),rho / &2) /\
         (e(segment[u,v]) INTER UNIONS x) DIFF ball(h(midpoint(u,v)),rho / &2)
         SUBSET FF u v /\
         IMAGE g (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                  derived_frontier t l) =
         e(segment[u,v]) INTER frontier (UNIONS x) /\
         ball(h(midpoint(u,v)),&2 * rho) SUBSET interior (UNIONS x) /\
         (!u' v'. ~(u' = v') /\ segment[u',v'] IN l /\ ~(segment[u',v'] = segment[u,v])
                  ==> ball(h(midpoint(u,v)),&2 * rho) INTER e(segment[u',v']) = {} /\
                      &3 * rho <= dist(h(midpoint(u,v)),h(midpoint(u',v')))) /\
         (!w. {w} IN l /\ ~(w = u) /\ ~(w = v)
              ==> ball(h(midpoint(u,v)),&2 * rho) INTER c w = {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3xt_ctx] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let MOI_S3XT_CTX_VERTEX = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho v.
     moi_s3xt_ctx t l h e c x g g' FF rho /\ {v} IN l
     ==> IMAGE g (derived_dual_cell t l v INTER derived_frontier t l) =
         c v INTER frontier (UNIONS x)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3xt_ctx] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let MOI_S3XT_FF_DISJ = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho u v u' v'.
     moi_s3xt_ctx t l h e c x g g' FF rho /\
     ~(u = v) /\ segment[u,v] IN l /\ ~(u' = v') /\ segment[u',v'] IN l /\
     ~(segment[u',v'] = segment[u,v])
     ==> DISJOINT (FF u v) (FF u' v')`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`; `u:real^3`; `v:real^3`]
    MOI_S3XT_CTX_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`; `u':real^3`; `v':real^3`]
    MOI_S3XT_CTX_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `ball((h:real^3->real^3)(midpoint(u,v)),&2 * rho) INTER e(segment[u',v']) = {} /\
    &3 * rho <= dist(h(midpoint(u,v)),h(midpoint(u',v'))) /\
    ball(h(midpoint(u',v')),&2 * rho) INTER e(segment[u,v]) = {}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM(fun th ->
      MP_TAC(SPECL [`u':real^3`; `v':real^3`] th) THEN
      MP_TAC(SPECL [`u:real^3`; `v:real^3`] th)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (e(segment[u:real^3,v]):real^3->bool) (e(segment[u',v']))`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
      MOI_S3XT_HD_MISC) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `ball((h:real^3->real^3)(midpoint(u,v)),rho / &2) SUBSET ball(h(midpoint(u,v)),&2 * rho) /\
    ball(h(midpoint(u',v')),rho / &2) SUBSET ball(h(midpoint(u',v')),&2 * rho) /\
    ball(h(midpoint(u,v)),rho / &2) INTER ball(h(midpoint(u',v')),rho / &2) = {}`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC;
      REWRITE_TAC[EXTENSION; IN_INTER; IN_BALL; NOT_IN_EMPTY] THEN
      X_GEN_TAC `z:real^3` THEN
      UNDISCH_TAC `&3 * rho <= dist((h:real^3->real^3)(midpoint(u,v)),h(midpoint(u',v')))` THEN
      UNDISCH_TAC `&0 < rho` THEN CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`(FF:real^3->real^3->real^3->bool) u v SUBSET
     e(segment[u,v]) UNION ball((h:real^3->real^3)(midpoint(u,v)),rho / &2)`;
    `(FF:real^3->real^3->real^3->bool) u' v' SUBSET
     e(segment[u',v']) UNION ball((h:real^3->real^3)(midpoint(u',v')),rho / &2)`;
    `ball((h:real^3->real^3)(midpoint(u,v)),&2 * rho) INTER
     (e:(real^3->bool)->real^3->bool)(segment[u',v']) = {}`;
    `ball((h:real^3->real^3)(midpoint(u',v')),&2 * rho) INTER
     (e:(real^3->bool)->real^3->bool)(segment[u,v]) = {}`;
    `DISJOINT (e(segment[u:real^3,v]):real^3->bool) (e(segment[u',v']))`;
    `ball((h:real^3->real^3)(midpoint(u,v)),rho / &2) SUBSET ball(h(midpoint(u,v)),&2 * rho)`;
    `ball((h:real^3->real^3)(midpoint(u',v')),rho / &2) SUBSET
     ball(h(midpoint(u',v')),&2 * rho)`;
    `ball((h:real^3->real^3)(midpoint(u,v)),rho / &2) INTER
     ball(h(midpoint(u',v')),rho / &2) = {}`] THEN
  SET_TAC[]);;

let MOI_S3XT_PHI = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho.
     moi_s3xt_ctx t l h e c x g g' FF rho
     ==> ?phi. (!u v. phi u v = phi v u) /\
               !u v. ~(u = v) /\ segment[u,v] IN l
                     ==> (?phi'. pl_homeomorphism
                                   (derived_dual_cell t l u INTER derived_dual_cell t l v,
                                    FF u v) (phi u v,phi')) /\
                         (!y. y IN derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                                   derived_frontier t l
                              ==> phi u v y = g y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`l:(real^3->bool)->bool`;
    `\u v (p:real^3->real^3).
       (?p'. pl_homeomorphism
               (derived_dual_cell t l u INTER derived_dual_cell t l v,
                (FF:real^3->real^3->real^3->bool) u v) (p,p')) /\
       (!y. y IN derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                 derived_frontier t l
            ==> p y = (g:real^3->real^3) y)`]
    MOI_S3XT_SYM_SKOLEM) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [ALL_TAC;
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`; `p:real^3->real^3`] THEN
    SUBGOAL_THEN
     `derived_dual_cell t l v INTER derived_dual_cell t l u =
      derived_dual_cell t l u INTER derived_dual_cell t l (v:real^3) /\
      derived_dual_cell t l v INTER derived_dual_cell t l u INTER derived_frontier t l =
      derived_dual_cell t l u INTER derived_dual_cell t l (v:real^3) INTER
      derived_frontier t l /\
      (FF:real^3->real^3->real^3->bool) v u = FF u v`
    (fun th -> REWRITE_TAC[th]) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[]] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `u:real^3`; `v:real^3`] MOI_S3XT_SRC_DISK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`; `u:real^3`; `v:real^3`]
    MOI_S3XT_CTX_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`derived_dual_cell t l u INTER derived_dual_cell t l (v:real^3)`;
    `derived_dual_cell t l u INTER derived_dual_cell t l (v:real^3) INTER
     derived_frontier t l`;
    `(FF:real^3->real^3->real^3->bool) u v`;
    `(e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER frontier (UNIONS x)`;
    `g:real^3->real^3`; `g':real^3->real^3`] MOI_SPU_CELL_EXTEND) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(fun th ->
      if concl th = `IMAGE (g:real^3->real^3)
                      (derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                       derived_frontier t l) =
                     (e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER
                     frontier (UNIONS x)`
      then SUBST1_TAC(SYM th) else failwith "") THEN
    MATCH_MP_TAC MOI_CEL_PLH_RESTRICT THEN
    MAP_EVERY EXISTS_TAC [`derived_frontier (t:(real^3->bool)->bool) l`;
                          `frontier (UNIONS x:real^3->bool)`] THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON] THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^3->real^3` (X_CHOOSE_THEN `p':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `p:real^3->real^3` THEN ASM_SIMP_TAC[] THEN
  EXISTS_TAC `p':real^3->real^3` THEN ASM_REWRITE_TAC[]);;

(* The splitting disks of distinct edges are disjoint (triple condition),  *)
(* so g and the phi paste to one map Psi.                                   *)

let MOI_S3XT_DISK_EDGE_UNIQUE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) u v u' v' y.
     moi_s33_tube t l h /\
     (!u v w. {u} IN l /\ {v} IN l /\ {w} IN l /\ ~(u = v) /\ ~(u = w) /\ ~(v = w)
              ==> derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                  derived_dual_cell t l w = {}) /\
     ~(u = v) /\ segment[u,v] IN l /\ ~(u' = v') /\ segment[u',v'] IN l /\
     y IN derived_dual_cell t l u INTER derived_dual_cell t l v /\
     y IN derived_dual_cell t l u' INTER derived_dual_cell t l v'
     ==> (u' = u /\ v' = v) \/ (u' = v /\ v' = u)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
    MOI_S3XT_EDGE_VERTICES) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `u':real^3`; `v':real^3`]
    MOI_S3XT_EDGE_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(u':real^3 = u \/ u' = v) /\ (v' = u \/ v' = v)` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`; `u':real^3`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 3));
      FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`; `v':real^3`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 3))] THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(y:real^3) IN derived_dual_cell t l u INTER derived_dual_cell t l v`;
      `(y:real^3) IN derived_dual_cell t l u' INTER derived_dual_cell t l v'`] THEN
    SET_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S3XT_PSI = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) (g:real^3->real^3)
    (phi:real^3->real^3->real^3->real^3).
     moi_s33_tube t l h /\
     (!u v w. {u} IN l /\ {v} IN l /\ {w} IN l /\ ~(u = v) /\ ~(u = w) /\ ~(v = w)
              ==> derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                  derived_dual_cell t l w = {}) /\
     (!u v. phi u v = phi v u) /\
     (!u v y. ~(u = v) /\ segment[u,v] IN l /\
              y IN derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                   derived_frontier t l
              ==> phi u v y = g y)
     ==> ?Psi. (!y. y IN derived_frontier t l ==> Psi y = g y) /\
               (!u v y. ~(u = v) /\ segment[u,v] IN l /\
                        y IN derived_dual_cell t l u INTER derived_dual_cell t l v
                        ==> Psi y = phi u v y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  EXISTS_TAC `\y:real^3. if y IN derived_frontier t l then g y
                         else @z:real^3. ?u v. ~(u = v) /\ segment[u,v] IN l /\
                                               y IN derived_dual_cell t l u INTER
                                                    derived_dual_cell t l v /\
                                               z = phi u v y` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`; `y:real^3`] THEN STRIP_TAC THEN
  COND_CASES_TAC THENL
   [CONV_TAC SYM_CONV THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 3)) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN
    UNDISCH_TAC `(y:real^3) IN derived_dual_cell t l u INTER derived_dual_cell t l v` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `z:real^3` THEN REWRITE_TAC[] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `v':real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `u:real^3`; `v:real^3`; `u':real^3`; `v':real^3`; `y:real^3`]
      MOI_S3XT_DISK_EDGE_UNIQUE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[];
    DISCH_TAC THEN MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[]]);;

let MOI_S3XT_NE_SYM = prove
 (`!(f:real^3->real^3->bool) (P:real^3->bool) (v:real^3).
     {f w | w | ~(w = v) /\ P w} = {f w | w | ~(v = w) /\ P w}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;

let moi_s3xt_maps = new_definition
 `moi_s3xt_maps (t:(real^3->bool)->bool) (l:(real^3->bool)->bool) (g:real^3->real^3)
                (FF:real^3->real^3->real^3->bool) (phi:real^3->real^3->real^3->real^3)
                (Psi:real^3->real^3) <=>
    (!u v. ~(u = v) /\ segment[u,v] IN l
           ==> ?phi'. pl_homeomorphism
                        (derived_dual_cell t l u INTER derived_dual_cell t l v,FF u v)
                        (phi u v,phi')) /\
    (!y. y IN derived_frontier t l ==> Psi y = g y) /\
    (!u v y. ~(u = v) /\ segment[u,v] IN l /\
             y IN derived_dual_cell t l u INTER derived_dual_cell t l v
             ==> Psi y = phi u v y)`;;

let MOI_S3XT_MAPS_DISK = prove
 (`!(t:(real^3->bool)->bool) l (g:real^3->real^3) FF phi Psi u v.
     moi_s3xt_maps t l g FF phi Psi /\ ~(u = v) /\ segment[u,v] IN l
     ==> IMAGE Psi (derived_dual_cell t l u INTER derived_dual_cell t l v) = FF u v /\
         (!y z. y IN derived_dual_cell t l u INTER derived_dual_cell t l v /\
                z IN derived_dual_cell t l u INTER derived_dual_cell t l v /\
                Psi y = Psi z ==> y = z) /\
         pl_map_on (derived_dual_cell t l u INTER derived_dual_cell t l v) Psi`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s3xt_maps] THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`u:real^3`; `v:real^3`] o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
  ASM_REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `p':real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!y. y IN derived_dual_cell t l u INTER derived_dual_cell t l v
                    ==> (Psi:real^3->real^3) y = phi u v y`
  ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `IMAGE ((phi:real^3->real^3->real^3->real^3) u v)
                  (derived_dual_cell t l u INTER derived_dual_cell t l v) =
                (FF:real^3->real^3->real^3->bool) u v` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE
     `!f g s. (!x. x IN s ==> f x = g x) ==> IMAGE (f:real^3->real^3) s = IMAGE g s`) THEN
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    MATCH_MP_TAC PL_MAP_ON_EQ THEN
    EXISTS_TAC `(phi:real^3->real^3->real^3->real^3) u v` THEN ASM_SIMP_TAC[]]);;

let MOI_S3XT_PSI_IMAGE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi v.
     moi_s3xt_ctx t l h e c x g g' FF rho /\ moi_s3xt_maps t l g FF phi Psi /\ {v} IN l
     ==> IMAGE Psi (moi_s3xt_sig t l v) =
         (c v INTER frontier (UNIONS x)) UNION
         UNIONS {FF v w | w | ~(v = w) /\ segment[v,w] IN l}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!w. ~(w = v) /\ segment[v,w] IN l
                    ==> IMAGE (Psi:real^3->real^3)
                          (derived_dual_cell t l v INTER derived_dual_cell t l w) = FF v w`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `g:real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `phi:real^3->real^3->real^3->real^3`;
                   `Psi:real^3->real^3`; `v:real^3`; `w:real^3`] MOI_S3XT_MAPS_DISK) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (Psi:real^3->real^3)
                  (derived_dual_cell t l v INTER derived_frontier t l) =
                c v INTER frontier (UNIONS x)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `v:real^3`]
      MOI_S3XT_CTX_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE
     `!f g s. (!x. x IN s ==> f x = g x) ==> IMAGE (f:real^3->real^3) s = IMAGE g s`) THEN
    UNDISCH_TAC `moi_s3xt_maps t l g FF phi (Psi:real^3->real^3)` THEN
    REWRITE_TAC[moi_s3xt_maps; IN_INTER] THEN SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3xt_sig; IMAGE_UNION; IMAGE_UNIONS; GSYM MOI_S3XT_NE_SYM] THEN
  ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^3->bool` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `d:real^3->bool` (CONJUNCTS_THEN2 SUBST1_TAC
      (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `w:real^3` THEN ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `derived_dual_cell t l v INTER derived_dual_cell t l (w:real^3)` THEN
    ASM_SIMP_TAC[] THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[]]);;

let MOI_S3XT_BD_TO_DISK = prove
 (`!(g:real^3->real^3) g' (Psi:real^3->real^3) B d fd r Y y z.
     (!y. y IN B ==> g'(g y) = y) /\ (!y. y IN B ==> Psi y = g y) /\
     IMAGE g B = Y /\ IMAGE Psi d = fd /\ fd INTER Y = IMAGE g r /\ r SUBSET B /\
     y IN B /\ z IN d /\ Psi y = Psi z
     ==> y IN r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^3->real^3) y IN IMAGE g r` MP_TAC THENL
   [ASM SET_TAC[]; REWRITE_TAC[IN_IMAGE] THEN ASM_MESON_TAC[SUBSET]]);;

let MOI_S3XT_PSI_INJ = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi v.
     moi_s3xt_ctx t l h e c x g g' FF rho /\ moi_s3xt_maps t l g FF phi Psi /\ {v} IN l
     ==> !y z. y IN moi_s3xt_sig t l v /\ z IN moi_s3xt_sig t l v /\ Psi y = Psi z
               ==> y = z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(!y. y IN derived_frontier t l ==> (g':real^3->real^3) (g y) = y) /\
                IMAGE (g:real^3->real^3) (derived_frontier t l) = frontier (UNIONS x)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (derived_frontier t l,frontier (UNIONS x))
                                  (g:real^3->real^3,g')` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y. y IN derived_frontier t l ==> (Psi:real^3->real^3) y = g y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s3xt_maps t l g FF phi (Psi:real^3->real^3)` THEN
    SIMP_TAC[moi_s3xt_maps];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!w. ~(w = v) /\ segment[v,w] IN l
        ==> IMAGE (Psi:real^3->real^3)
              (derived_dual_cell t l v INTER derived_dual_cell t l w) = FF v w /\
            (!y z. y IN derived_dual_cell t l v INTER derived_dual_cell t l w /\
                   z IN derived_dual_cell t l v INTER derived_dual_cell t l w /\
                   Psi y = Psi z ==> y = z) /\
            (FF:real^3->real^3->real^3->bool) v w INTER frontier (UNIONS x) =
            IMAGE g (derived_dual_cell t l v INTER derived_dual_cell t l w INTER
                     derived_frontier t l) /\
            (!y. y IN derived_dual_cell t l v INTER derived_frontier t l /\
                 (?z. z IN derived_dual_cell t l v INTER derived_dual_cell t l w /\
                      Psi y = Psi z)
                 ==> y IN derived_dual_cell t l v INTER derived_dual_cell t l w)`
  (LABEL_TAC "w") THENL
   [X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `g:real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `phi:real^3->real^3->real^3->real^3`;
                   `Psi:real^3->real^3`; `v:real^3`; `w:real^3`] MOI_S3XT_MAPS_DISK) THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `v:real^3`; `w:real^3`]
      MOI_S3XT_CTX_EDGE) THEN
    SUBGOAL_THEN `~(v:real^3 = w)` ASSUME_TAC THENL
     [UNDISCH_TAC `~(w:real^3 = v)` THEN MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^3) IN derived_dual_cell t l v INTER derived_dual_cell t l w INTER
                                derived_frontier t l` MP_TAC THENL
     [MATCH_MP_TAC MOI_S3XT_BD_TO_DISK THEN
      MAP_EVERY EXISTS_TAC
       [`g:real^3->real^3`; `g':real^3->real^3`; `Psi:real^3->real^3`;
        `derived_frontier (t:(real^3->bool)->bool) l`;
        `derived_dual_cell t l v INTER derived_dual_cell t l (w:real^3)`;
        `(FF:real^3->real^3->real^3->bool) v w`; `frontier (UNIONS x:real^3->bool)`;
        `z:real^3`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^3) IN derived_dual_cell t l v INTER derived_frontier t l` THEN
      SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN
  REWRITE_TAC[moi_s3xt_sig; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
  DISCH_THEN(fun th ->
    let yth,rest = CONJ_PAIR th in
    let zth,eqth = CONJ_PAIR rest in
    ASSUME_TAC eqth THEN MP_TAC zth THEN MP_TAC yth) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THEN
  DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC (X_CHOOSE_THEN `w':real^3` STRIP_ASSUME_TAC)) THENL
   [SUBGOAL_THEN `(g':real^3->real^3) (g y) = y /\ g' (g z) = z /\
                  (g:real^3->real^3) y = g z`
    MP_TAC THENL
     [REPEAT CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(y:real^3) IN derived_dual_cell t l v INTER derived_frontier t l` THEN
        SET_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN
        UNDISCH_TAC `(z:real^3) IN derived_dual_cell t l v INTER derived_frontier t l` THEN
        SET_TAC[];
        SUBGOAL_THEN `(Psi:real^3->real^3) y = g y /\ Psi z = g z` MP_TAC THENL
         [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
           [UNDISCH_TAC `(y:real^3) IN derived_dual_cell t l v INTER derived_frontier t l`;
            UNDISCH_TAC `(z:real^3) IN derived_dual_cell t l v INTER derived_frontier t l`] THEN
          SET_TAC[];
          UNDISCH_TAC `(Psi:real^3->real^3) y = Psi z` THEN MESON_TAC[]]];
      MESON_TAC[]];
    USE_THEN "w" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `~(w':real^3 = v)`) (ASSUME `segment[v:real^3,w'] IN l`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN derived_dual_cell t l v INTER derived_dual_cell t l w'`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `z:real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[];
    USE_THEN "w" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `~(w:real^3 = v)`) (ASSUME `segment[v:real^3,w] IN l`))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN derived_dual_cell t l v INTER derived_dual_cell t l w`
    ASSUME_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN EXISTS_TAC `y:real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
    ASM_REWRITE_TAC[];
    ASM_CASES_TAC `w':real^3 = w` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "w" (MP_TAC o C MATCH_MP
        (CONJ (ASSUME `~(w:real^3 = v)`) (ASSUME `segment[v:real^3,w] IN l`))) THEN
      STRIP_TAC THEN
      FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(v:real^3 = w) /\ ~(v = w') /\ ~(segment[v,w'] = segment[v:real^3,w])`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THENL
       [UNDISCH_TAC `~(w:real^3 = v)` THEN MESON_TAC[];
        UNDISCH_TAC `~(w':real^3 = v)` THEN MESON_TAC[];
        REWRITE_TAC[SEGMENT_EQ; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `w':real^3`) THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `v:real^3`; `w:real^3`;
                   `v:real^3`; `w':real^3`] MOI_S3XT_FF_DISJ) THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "w" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `~(w:real^3 = v)`) (ASSUME `segment[v:real^3,w] IN l`))) THEN
    USE_THEN "w" (MP_TAC o C MATCH_MP
      (CONJ (ASSUME `~(w':real^3 = v)`) (ASSUME `segment[v:real^3,w'] IN l`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
    SUBGOAL_THEN `(Psi:real^3->real^3) y IN (FF:real^3->real^3->real^3->bool) v w /\
                  Psi z IN FF v w'` MP_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `IMAGE (Psi:real^3->real^3)
                       (derived_dual_cell t l v INTER derived_dual_cell t l w) =
                     (FF:real^3->real^3->real^3->bool) v w`;
        UNDISCH_TAC `IMAGE (Psi:real^3->real^3)
                       (derived_dual_cell t l v INTER derived_dual_cell t l w') =
                     (FF:real^3->real^3->real^3->bool) v w'`] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(Psi:real^3->real^3) y = Psi z` THEN
    DISCH_THEN SUBST1_TAC THEN SET_TAC[]]);;

let MOI_S3XT_PSI_PLMAP = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi v.
     moi_s3xt_ctx t l h e c x g g' FF rho /\ moi_s3xt_maps t l g FF phi Psi /\ {v} IN l
     ==> pl_map_on (moi_s3xt_sig t l v) Psi`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `v:real^3`] MOI_S3XT_SRC_CELL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_s3xt_sig t l v =
    UNIONS ((derived_dual_cell t l v INTER derived_frontier t l) INSERT
            {derived_dual_cell t l v INTER derived_dual_cell t l w | w |
             ~(w = v) /\ segment[v:real^3,w] IN l})`
  SUBST1_TAC THENL [REWRITE_TAC[moi_s3xt_sig; UNIONS_INSERT]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_CEL_PL_MAP_ON_UNIONS_FINITE THEN CONJ_TAC THENL
   [REWRITE_TAC[FINITE_INSERT] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC MOI_S3XT_NBR_FINITE THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `h:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_INSERT; FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN MATCH_MP_TAC PL_POLYHEDRON_IMP_COMPACT THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `g:real^3->real^3` THEN CONJ_TAC THENL
       [UNDISCH_TAC `moi_s3xt_maps t l g FF phi (Psi:real^3->real^3)` THEN
        REWRITE_TAC[moi_s3xt_maps; IN_INTER] THEN MESON_TAC[];
        MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
        EXISTS_TAC `derived_frontier (t:(real^3->bool)->bool) l` THEN
        ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_PL_POLYHEDRON; INTER_SUBSET] THEN
        UNDISCH_TAC `pl_homeomorphism (derived_frontier t l,frontier (UNIONS x))
                                      (g:real^3->real^3,g')` THEN
        SIMP_TAC[pl_homeomorphism]]];
    X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `v:real^3`; `w:real^3`] MOI_S3XT_SRC_DISK) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; SIMP_TAC[]];
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `g:real^3->real^3`;
                     `FF:real^3->real^3->real^3->bool`; `phi:real^3->real^3->real^3->real^3`;
                     `Psi:real^3->real^3`; `v:real^3`; `w:real^3`] MOI_S3XT_MAPS_DISK) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; SIMP_TAC[]]]]);;

let MOI_S3XT_PSI_SIG = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi v.
     moi_s3xt_ctx t l h e c x g g' FF rho /\ moi_s3xt_maps t l g FF phi Psi /\ {v} IN l
     ==> (?psi'. pl_homeomorphism
                   (moi_s3xt_sig t l v,
                    (c v INTER frontier (UNIONS x)) UNION
                    UNIONS {FF v w | w | ~(v = w) /\ segment[v,w] IN l})
                   (Psi,psi')) /\
         pl_sphere 2 ((c v INTER frontier (UNIONS x)) UNION
                      UNIONS {FF v w | w | ~(v = w) /\ segment[v,w] IN l})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 2 (moi_s3xt_sig t l (v:real^3))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `v:real^3`] MOI_S3XT_SRC_CELL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`; `v:real^3`]
    MOI_S3XT_PSI_PLMAP) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`; `v:real^3`]
    MOI_S3XT_PSI_IMAGE) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`; `v:real^3`]
    MOI_S3XT_PSI_INJ) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `?psi'. pl_homeomorphism
             (moi_s3xt_sig t l v,
              (c v INTER frontier (UNIONS x)) UNION
              UNIONS {(FF:real^3->real^3->real^3->bool) v w | w | ~(v = w) /\ segment[v,w] IN l})
             (Psi:real^3->real^3,psi')`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_s3xt_sig t l (v:real^3)`; `Psi:real^3->real^3`;
                   `(c v INTER frontier (UNIONS x)) UNION
                    UNIONS {(FF:real^3->real^3->real^3->bool) v w | w |
                            ~(v = w) /\ segment[v,w] IN l}`]
      HOMEOMORPHISM_COMPACT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPEC `moi_s3xt_sig t l (v:real^3)` MOI_S3XT_SPHERE_FACTS) THEN
        ASM_REWRITE_TAC[] THEN SIMP_TAC[];
        MATCH_MP_TAC PL_MAP_ON_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `psi':real^3->real^3`) THEN
    EXISTS_TAC `psi':real^3->real^3` THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [EXISTS_TAC `psi':real^3->real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `pl_sphere 2 (moi_s3xt_sig t l (v:real^3))` THEN
  REWRITE_TAC[pl_sphere] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^3->bool` (X_CHOOSE_THEN `p:real^3->real^3`
    (X_CHOOSE_THEN `q:real^3->real^3` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^3->bool`; `(Psi:real^3->real^3) o (p:real^3->real^3)`;
                        `(q:real^3->real^3) o (psi':real^3->real^3)`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
  EXISTS_TAC `moi_s3xt_sig t l (v:real^3)` THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Part 10: the configuration of the target.  TGT_FREE: free points         *)
(* g z of the pieces A_v from the source free points.  CFG_INST: the        *)
(* abstract configuration of Part 6 holds for the vertices of l, the pieces *)
(* A_v = c v INTER Bd X and the disks FF, so INT_DISJ, MEET and COVER apply. *)
(* ========================================================================= *)

let MOI_S3XT_CELL_CONNECTED = prove
 (`!n (s:real^N->bool) b. pl_cell_with_boundary n s b ==> connected s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[pl_cell_with_boundary; pl_homeomorphism; homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `f':real^N->real^N` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `IMAGE (f:real^N->real^N) k = s` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC CONVEX_CONNECTED THEN ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]);;

let MOI_S3XT_TGT_FREE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho v.
     moi_s3xt_ctx t l h e c x g g' FF rho /\ {v} IN l
     ==> ?y. y IN c v INTER frontier (UNIONS x) /\
             (!w. {w} IN l /\ ~(w = v) ==> ~(y IN c w INTER frontier (UNIONS x))) /\
             (!a b. ~(a = b) /\ segment[a,b] IN l ==> ~(y IN FF a b))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `v:real^3`] MOI_S3XT_SRC_FREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(!y. y IN derived_frontier t l ==> (g':real^3->real^3) (g y) = y) /\
                IMAGE (g:real^3->real^3) (derived_frontier t l) = frontier (UNIONS x)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (derived_frontier t l,frontier (UNIONS x))
                                  (g:real^3->real^3,g')` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r. r SUBSET derived_frontier t l /\ (g:real^3->real^3) z IN IMAGE g r
                    ==> z IN r`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^3->bool` THEN REWRITE_TAC[IN_IMAGE] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `z':real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `z':real^3 = z` (fun th -> ASM_MESON_TAC[th]) THEN
    SUBGOAL_THEN `(g':real^3->real^3) (g z') = z' /\ g' (g z) = z` MP_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
       [ASM_MESON_TAC[SUBSET]; ASM SET_TAC[]];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `(g:real^3->real^3) z` THEN REPEAT CONJ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `v:real^3`]
      MOI_S3XT_CTX_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
    X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `w:real^3`]
      MOI_S3XT_CTX_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN derived_dual_cell t l w INTER derived_frontier t l`
    MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
        can (find_term (fun t -> t = `IMAGE (g:real^3->real^3)`)) (concl th))) THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      ASM SET_TAC[]];
    MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN STRIP_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `a:real^3`; `b:real^3`]
      MOI_S3XT_CTX_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `a:real^3`; `b:real^3`]
      MOI_S3XT_EDGE_VERTICES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(z:real^3) IN derived_dual_cell t l a INTER derived_dual_cell t l b INTER
                                derived_frontier t l` MP_TAC THENL
     [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
        is_forall(concl th) && is_imp(snd(dest_forall(concl th))) &&
        can (find_term (fun t -> t = `IMAGE (g:real^3->real^3)`)) (concl th))) THEN
      CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3)
                     (derived_dual_cell t l a INTER derived_dual_cell t l b INTER
                      derived_frontier t l) =
                   (e:(real^3->bool)->real^3->bool)(segment[a,b]) INTER
                   frontier (UNIONS x)` THEN
      DISCH_THEN SUBST1_TAC THEN
      UNDISCH_TAC `(FF:real^3->real^3->real^3->bool) a b INTER frontier (UNIONS x) =
                   (e:(real^3->bool)->real^3->bool)(segment[a,b]) INTER
                   frontier (UNIONS x)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `IMAGE (g:real^3->real^3) (derived_frontier t l) = frontier (UNIONS x)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC FUN_IN_IMAGE THEN ASM SET_TAC[];
      REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
      ASM_CASES_TAC `a:real^3 = v` THENL
       [UNDISCH_TAC `!w. {w} IN l /\ ~(w = v) ==> ~((z:real^3) IN derived_dual_cell t l w)` THEN
        DISCH_THEN(MP_TAC o SPEC `b:real^3`) THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
        UNDISCH_TAC `!w. {w} IN l /\ ~(w = v) ==> ~((z:real^3) IN derived_dual_cell t l w)` THEN
        DISCH_THEN(MP_TAC o SPEC `a:real^3`) THEN ASM_REWRITE_TAC[]]]]);;

let MOI_S3XT_HD_MEET = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c u v.
     moi_s33_hd t l h e c /\ {u} IN l /\ {v} IN l /\ ~(u = v)
     ==> c u INTER c v = (if segment[u,v] IN l then e(segment[u,v]) else {})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_hd] THEN STRIP_TAC THEN ASM_SIMP_TAC[]);;

let MOI_S3XT_INV_TRACE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e (x:(real^3->bool)->bool) u v.
     moi_s33_inv t l h e x /\ ~(u = v) /\ segment[u,v] IN l
     ==> pl_sphere 1 (e(segment[u,v]) INTER frontier (UNIONS x)) /\
         disk_with_boundary (e(segment[u,v]) INTER UNIONS x)
                            (e(segment[u,v]) INTER frontier (UNIONS x))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_inv; moi_s33_traces] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[]);;

let MOI_S3XT_CFG_INST = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi.
     moi_s3xt_ctx t l h e c x g g' FF rho /\ moi_s3xt_maps t l g FF phi Psi
     ==> moi_s3xt_cfg {v | {v} IN l} (\u v. ~(u = v) /\ segment[u,v] IN l)
                      (\v. c v INTER frontier (UNIONS x)) FF (UNIONS x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  SUBGOAL_THEN `?p:real^3. {p} IN l /\ p IN UNIONS l` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `a:real^3->bool`] MOI_FSA_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EXISTS_TAC `p:real^3` THEN
    ASM_REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{p:real^3}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `x:(real^3->bool)->bool`] MOI_S3XT_XFACTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_IMAGE] THEN ASM_MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `!w. {w} IN l ==> closed((c:real^3->real^3->bool) w)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
      MOI_S3XT_HD_MISC) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3xt_cfg; moi_s3xt_sph; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN ASM_MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `u:real^3`; `v:real^3`]
      MOI_S3XT_EDGE_VERTICES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(u:real^3 = v)` THEN MESON_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `u:real^3`; `v:real^3`]
      MOI_S3XT_CTX_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3XT_CELL_CONNECTED THEN
      MAP_EVERY EXISTS_TAC [`2`; `(e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER
                                  frontier (UNIONS x)`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MP_TAC(ISPECL [`2`; `(FF:real^3->real^3->real^3->bool) u v`;
                     `(e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER
                      frontier (UNIONS x)`] MOI_CEL_CELL_COMPACT) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `e:(real^3->bool)->real^3->bool`; `x:(real^3->bool)->bool`;
                     `u:real^3`; `v:real^3`] MOI_S3XT_INV_TRACE) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[MOI_SCD_PL_SPHERE_NONEMPTY]];
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`; `u':real^3`; `v':real^3`] THEN
    STRIP_TAC THEN
    MATCH_MP_TAC MOI_S3XT_FF_DISJ THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                          `h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                          `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
                          `g:real^3->real^3`; `g':real^3->real^3`; `rho:real`] THEN
    ASM_REWRITE_TAC[SEGMENT_EQ] THEN
    UNDISCH_TAC `~({u:real^3,v} = {u',v'})` THEN MESON_TAC[];
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      MATCH_MP_TAC CLOSED_INTER THEN ASM_SIMP_TAC[FRONTIER_CLOSED];
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                     `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                     `FF:real^3->real^3->real^3->bool`; `rho:real`;
                     `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`; `v:real^3`]
        MOI_S3XT_PSI_SIG) THEN
      ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`; `w:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `u:real^3`; `v:real^3`]
      MOI_S3XT_CTX_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `u:real^3`; `v:real^3`] MOI_S3XT_HD_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^3` o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(FF:real^3->real^3->real^3->bool) u v INTER frontier (UNIONS x) =
       (e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER frontier (UNIONS x)`] THEN
    SET_TAC[];
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `u:real^3`; `v:real^3`] MOI_S3XT_HD_MEET) THEN
    ASM_REWRITE_TAC[] THEN COND_CASES_TAC THEN ASM_REWRITE_TAC[] THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                     `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                     `FF:real^3->real^3->real^3->bool`; `rho:real`; `u:real^3`; `v:real^3`]
        MOI_S3XT_CTX_EDGE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`(FF:real^3->real^3->real^3->bool) u v INTER frontier (UNIONS x) =
         (e:(real^3->bool)->real^3->bool)(segment[u,v]) INTER frontier (UNIONS x)`;
        `(c:real^3->real^3->bool) u INTER c v = e(segment[u,v])`] THEN
      SET_TAC[];
      SET_TAC[]];
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3XT_TGT_FREE THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `h:real^3->real^3`;
                          `e:(real^3->bool)->real^3->bool`; `g:real^3->real^3`;
                          `g':real^3->real^3`; `rho:real`] THEN
    ASM_REWRITE_TAC[]]);;

(* The balls B_v bounded by the image spheres, and PL homeomorphisms of the *)
(* dual cells onto them extending Psi (PL Schoenflies, MOI_SCD_COR_EXTEND).  *)

let MOI_S3XT_SPH_EQ = prove
 (`!(c:real^3->real^3->bool) (x:(real^3->bool)->bool) FF (l:(real^3->bool)->bool) v.
     moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                  (\u v. ~(u = v) /\ segment[u,v] IN l) v =
     (c v INTER frontier (UNIONS x)) UNION
     UNIONS {FF v w | w | ~(v = w) /\ segment[v,w] IN l}`,
  REWRITE_TAC[moi_s3xt_sph]);;

let MOI_S3XT_BALLS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi.
     PL_SCHOENFLIES_3_STATEMENT /\
     moi_s3xt_ctx t l h e c x g g' FF rho /\ moi_s3xt_maps t l g FF phi Psi
     ==> ?fv. !v. {v} IN l
                  ==> (?fv'. pl_homeomorphism
                               (derived_dual_cell t l v,
                                moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                                  (\u v. ~(u = v) /\ segment[u,v] IN l) v UNION
                                inside(moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                                  (\u v. ~(u = v) /\ segment[u,v] IN l) v))
                               (fv v,fv')) /\
                      (!y. y IN moi_s3xt_sig t l v ==> fv v y = Psi y)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[GSYM SKOLEM_THM; RIGHT_EXISTS_IMP_THM] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  REWRITE_TAC[MOI_S3XT_SPH_EQ] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`; `v:real^3`]
    MOI_S3XT_PSI_SIG) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `S = (c v INTER frontier (UNIONS x)) UNION
                  UNIONS {(FF:real^3->real^3->real^3->bool) v w | w |
                          ~(v = w) /\ segment[v:real^3,w] IN l}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `psi':real^3->real^3`) ASSUME_TAC) THEN
  SUBGOAL_THEN `pl_ball 3 (derived_dual_cell t l (v:real^3)) /\
                frontier (derived_dual_cell t l v) = moi_s3xt_sig t l v`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `v:real^3`] MOI_S3XT_SRC_CELL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_ball 3 ((S:real^3->bool) UNION inside S) /\
                frontier (S UNION inside S) = S`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `PL_SCHOENFLIES_3_STATEMENT` THEN REWRITE_TAC[PL_SCHOENFLIES_3_STATEMENT] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPEC `S:real^3->bool` MOI_S3XT_SPHERE_FACTS) THEN ASM_REWRITE_TAC[] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`derived_dual_cell t l (v:real^3)`; `(S:real^3->bool) UNION inside S`;
                 `Psi:real^3->real^3`; `psi':real^3->real^3`] MOI_SCD_COR_EXTEND_BALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` (X_CHOOSE_THEN `f':real^3->real^3`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `f:real^3->real^3` THEN ASM_SIMP_TAC[] THEN
  EXISTS_TAC `f':real^3->real^3` THEN ASM_REWRITE_TAC[]);;

let MOI_S3XT_SIG_FF = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi u v y.
     moi_s3xt_ctx t l h e c x g g' FF rho /\ moi_s3xt_maps t l g FF phi Psi /\
     {u} IN l /\ ~(u = v) /\ segment[u,v] IN l /\
     y IN moi_s3xt_sig t l u /\ Psi y IN FF u v
     ==> y IN derived_dual_cell t l u INTER derived_dual_cell t l v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `g:real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `phi:real^3->real^3->real^3->real^3`;
                 `Psi:real^3->real^3`; `u:real^3`; `v:real^3`] MOI_S3XT_MAPS_DISK) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?z. z IN derived_dual_cell t l u INTER derived_dual_cell t l v /\
                    (Psi:real^3->real^3) z = Psi y`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(Psi:real^3->real^3) y IN (FF:real^3->real^3->real^3->bool) u v` THEN
    UNDISCH_TAC `IMAGE (Psi:real^3->real^3)
                   (derived_dual_cell t l u INTER derived_dual_cell t l v) = FF u v` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_IMAGE] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `y:real^3 = z` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`; `u:real^3`]
    MOI_S3XT_PSI_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_s3xt_sig; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN DISJ2_TAC THEN
  EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(u:real^3 = v)` THEN MESON_TAC[]);;

let MOI_S3XT_FRONT_PRE = prove
 (`!(f:real^3->real^3) f' (Psi:real^3->real^3) C B sg S y.
     homeomorphism (C,B) (f,f') /\ sg SUBSET C /\ IMAGE Psi sg = S /\
     (!y. y IN sg ==> f y = Psi y) /\ y IN C /\ f y IN S
     ==> y IN sg`,
  REWRITE_TAC[homeomorphism] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?y'. y' IN sg /\ (Psi:real^3->real^3) y' = (f:real^3->real^3) y`
  STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `y':real^3 = y` (fun th -> ASM_MESON_TAC[th]) THEN
  ASM_MESON_TAC[SUBSET]);;

let MOI_S3XT_SIG_SUBSET = prove
 (`!(t:(real^3->bool)->bool) l v.
     moi_s3xt_sig t l v SUBSET derived_dual_cell t l v`,
  REWRITE_TAC[moi_s3xt_sig; UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN SET_TAC[]);;

let MOI_S3XT_GLUE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi fv.
     moi_s3xt_ctx t l h e c x g g' FF rho /\ moi_s3xt_maps t l g FF phi Psi /\
     (!v. {v} IN l
          ==> (?fv'. pl_homeomorphism
                       (derived_dual_cell t l v,
                        moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                          (\u v. ~(u = v) /\ segment[u,v] IN l) v UNION
                        inside(moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                          (\u v. ~(u = v) /\ segment[u,v] IN l) v))
                       (fv v,fv')) /\
              (!y. y IN moi_s3xt_sig t l v ==> fv v y = Psi y))
     ==> ?f. pl_map_on (derived_nbhd t l) f /\
             (!y z. y IN derived_nbhd t l /\ z IN derived_nbhd t l /\ f y = f z ==> y = z) /\
             (!v. {v} IN l
                  ==> IMAGE f (derived_dual_cell t l v) =
                      moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                        (\u v. ~(u = v) /\ segment[u,v] IN l) v UNION
                      inside(moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                        (\u v. ~(u = v) /\ segment[u,v] IN l) v))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fv"))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  ABBREV_TAC `B = \v:real^3. moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                    (\u v. ~(u = v) /\ segment[u,v] IN l) v UNION
                  inside(moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                    (\u v. ~(u = v) /\ segment[u,v] IN l) v)` THEN
  SUBGOAL_THEN
   `!v. {v} IN l
        ==> (?fv'. homeomorphism (derived_dual_cell t l v,(B:real^3->real^3->bool) v)
                                 ((fv:real^3->real^3->real^3) v,fv')) /\
            pl_map_on (derived_dual_cell t l v) (fv v) /\
            (!y. y IN moi_s3xt_sig t l v ==> fv v y = (Psi:real^3->real^3) y) /\
            compact (derived_dual_cell t l v)`
  (LABEL_TAC "fvh") THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "fv" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[pl_homeomorphism] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `fv':real^3->real^3` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `v:real^3`] MOI_S3XT_SRC_CELL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v y. {u} IN l /\ {v} IN l /\ y IN derived_dual_cell t l u /\
            y IN derived_dual_cell t l v
            ==> (fv:real^3->real^3->real^3) u y = fv v y`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`; `y:real^3`] THEN STRIP_TAC THEN
    ASM_CASES_TAC `u:real^3 = v` THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `segment[u:real^3,v] IN l` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                     `h:real^3->real^3`; `u:real^3`; `v:real^3`] MOI_S3XT_SRC_APART) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3) IN moi_s3xt_sig t l u /\ y IN moi_s3xt_sig t l v`
    STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[moi_s3xt_sig; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
      CONJ_TAC THEN DISJ2_TAC THENL
       [EXISTS_TAC `v:real^3`; EXISTS_TAC `u:real^3`] THEN
      ASM_REWRITE_TAC[IN_INTER] THEN
      ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(u:real^3 = v)` THEN MESON_TAC[];
      ALL_TAC] THEN
    USE_THEN "fvh" (fun th ->
      MP_TAC(MATCH_MP th (ASSUME `{u:real^3} IN l`)) THEN
      MP_TAC(MATCH_MP th (ASSUME `{v:real^3} IN l`))) THEN
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `\y:real^3. (fv:real^3->real^3->real^3)
                           (@v. {v} IN l /\ y IN derived_dual_cell t l v) y` THEN
  SUBGOAL_THEN
   `!v y. {v} IN l /\ y IN derived_dual_cell t l v
          ==> (\y:real^3. (fv:real^3->real^3->real^3)
                           (@v. {v} IN l /\ y IN derived_dual_cell t l v) y) y = fv v y`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 3 &&
      can (find_term (fun t -> t = `fv:real^3->real^3->real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    CONV_TAC(ONCE_DEPTH_CONV SELECT_CONV) THEN
    EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `f = \y:real^3. (fv:real^3->real^3->real^3)
                               (@v. {v} IN l /\ y IN derived_dual_cell t l v) y` THEN
  SUBGOAL_THEN `derived_nbhd t l = UNIONS {derived_dual_cell t l v | v | {v:real^3} IN l}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
      GRAPH_TUBE_DUAL_CELLS) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v. {v} IN l ==> IMAGE (f:real^3->real^3) (derived_dual_cell t l v) = B v`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    USE_THEN "fvh" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN
    REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_eq(concl th) && rand(concl th) = `(B:real^3->real^3->bool) v`
                            then SUBST1_TAC(SYM th) else failwith "") THEN
    MATCH_MP_TAC(SET_RULE
     `!f g s. (!x. x IN s ==> f x = g x) ==> IMAGE (f:real^3->real^3) s = IMAGE g s`) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_CEL_PL_MAP_ON_UNIONS_FINITE THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
      USE_THEN "fvh" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN STRIP_TAC THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `(fv:real^3->real^3->real^3) v` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC;
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
                               can (find_term (fun t -> t = `IMAGE (f:real^3->real^3)`))
                                   (concl th)
                            then REWRITE_TAC[MATCH_MP th (ASSUME `{v:real^3} IN l`)]
                            else failwith "") THEN
    EXPAND_TAC "B" THEN REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN
  MAP_EVERY X_GEN_TAC [`y:real^3`; `z:real^3`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `u:real^3` STRIP_ASSUME_TAC)
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `(f:real^3->real^3) y = (fv:real^3->real^3->real^3) u y /\
                f z = fv v z` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `fv:real^3->real^3->real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "fvh" (MP_TAC o C MATCH_MP (ASSUME `{u:real^3} IN l`)) THEN
  REWRITE_TAC[homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `fu':real^3->real^3` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `u:real^3 = v` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  USE_THEN "fvh" (MP_TAC o C MATCH_MP (ASSUME `{v:real^3} IN l`)) THEN
  REWRITE_TAC[homeomorphism] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `fw':real^3->real^3` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_CFG_INST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{v:real^3 | {v} IN l}`; `\u v:real^3. ~(u = v) /\ segment[u,v] IN l`;
                 `\v:real^3. (c:real^3->real^3->bool) v INTER frontier (UNIONS x)`;
                 `FF:real^3->real^3->real^3->bool`; `UNIONS x:real^3->bool`;
                 `u:real^3`; `v:real^3`] MOI_S3XT_MEET) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  SUBGOAL_THEN `(f:real^3->real^3) y IN (B:real^3->real^3->bool) u /\ f y IN B v` MP_TAC THENL
   [CONJ_TAC THENL
     [FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
                                 can (find_term (fun t -> t = `IMAGE (f:real^3->real^3)`))
                                     (concl th)
                              then SUBST1_TAC(SYM(MATCH_MP th (ASSUME `{u:real^3} IN l`)))
                              else failwith "") THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[];
      FIRST_X_ASSUM(fun th -> if is_forall(concl th) &&
                                 can (find_term (fun t -> t = `IMAGE (f:real^3->real^3)`))
                                     (concl th)
                              then SUBST1_TAC(SYM(MATCH_MP th (ASSUME `{v:real^3} IN l`)))
                              else failwith "") THEN
      UNDISCH_TAC `(f:real^3->real^3) y = f (z:real^3)` THEN DISCH_THEN SUBST1_TAC THEN
      MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM IN_INTER] THEN
  DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o C MATCH_MP th o REWRITE_RULE[SUBSET])) THEN
  COND_CASES_TAC THEN REWRITE_TAC[NOT_IN_EMPTY] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `IMAGE (Psi:real^3->real^3) (moi_s3xt_sig t l u) =
    moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                 (\u v. ~(u = v) /\ segment[u,v] IN l) u /\
    IMAGE (Psi:real^3->real^3) (moi_s3xt_sig t l v) =
    moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                 (\u v. ~(u = v) /\ segment[u,v] IN l) v`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S3XT_SPH_EQ] THEN CONJ_TAC THEN MATCH_MP_TAC MOI_S3XT_PSI_IMAGE THEN
    MAP_EVERY EXISTS_TAC [`h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                          `g:real^3->real^3`; `g':real^3->real^3`; `rho:real`;
                          `phi:real^3->real^3->real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(FF:real^3->real^3->real^3->bool) u v SUBSET
                moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                             (\u v. ~(u = v) /\ segment[u,v] IN l) u /\
                FF u v SUBSET
                moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                             (\u v. ~(u = v) /\ segment[u,v] IN l) v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3XT_SPH_FF THEN ASM_REWRITE_TAC[];
      ONCE_ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S3XT_SPH_FF THEN
      REWRITE_TAC[] THEN ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~(u:real^3 = v)` THEN MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s3xt_sig t l u /\ (z:real^3) IN moi_s3xt_sig t l v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S3XT_FRONT_PRE THENL
     [MAP_EVERY EXISTS_TAC
       [`(fv:real^3->real^3->real^3) u`; `fu':real^3->real^3`; `Psi:real^3->real^3`;
        `derived_dual_cell t l (u:real^3)`; `(B:real^3->real^3->bool) u`;
        `moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                      (\u v. ~(u = v) /\ segment[u,v] IN l) (u:real^3)`];
      MAP_EVERY EXISTS_TAC
       [`(fv:real^3->real^3->real^3) v`; `fw':real^3->real^3`; `Psi:real^3->real^3`;
        `derived_dual_cell t l (v:real^3)`; `(B:real^3->real^3->bool) v`;
        `moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                      (\u v. ~(u = v) /\ segment[u,v] IN l) (v:real^3)`]] THEN
    ASM_REWRITE_TAC[MOI_S3XT_SIG_SUBSET; homeomorphism] THENL
     [UNDISCH_TAC `(f:real^3->real^3) y = (fv:real^3->real^3->real^3) u y` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MAP_EVERY UNDISCH_TAC
       [`(FF:real^3->real^3->real^3->bool) u v SUBSET
         moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                      (\u v. ~(u = v) /\ segment[u,v] IN l) u`;
        `(f:real^3->real^3) y IN (FF:real^3->real^3->real^3->bool) u v`] THEN
      SET_TAC[];
      UNDISCH_TAC `(f:real^3->real^3) z = (fv:real^3->real^3->real^3) v z` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(f:real^3->real^3) y = f (z:real^3)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MAP_EVERY UNDISCH_TAC
       [`(FF:real^3->real^3->real^3->bool) u v SUBSET
         moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                      (\u v. ~(u = v) /\ segment[u,v] IN l) v`;
        `(f:real^3->real^3) y IN (FF:real^3->real^3->real^3->bool) u v`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(Psi:real^3->real^3) y = (f:real^3->real^3) y /\ Psi z = f (z:real^3)` STRIP_ASSUME_TAC THENL
   [USE_THEN "fvh" (fun th ->
      MP_TAC(MATCH_MP th (ASSUME `{u:real^3} IN l`)) THEN
      MP_TAC(MATCH_MP th (ASSUME `{v:real^3} IN l`))) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN derived_dual_cell t l u INTER derived_dual_cell t l v /\
                (z:real^3) IN derived_dual_cell t l v INTER derived_dual_cell t l u`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S3XT_SIG_FF THEN
    MAP_EVERY EXISTS_TAC [`h:real^3->real^3`; `e:(real^3->bool)->real^3->bool`;
                          `c:real^3->real^3->bool`; `x:(real^3->bool)->bool`;
                          `g:real^3->real^3`; `g':real^3->real^3`;
                          `FF:real^3->real^3->real^3->bool`; `rho:real`;
                          `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`] THEN
    ASM_REWRITE_TAC[] THENL
     [ASM_MESON_TAC[];
      ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`; `u:real^3`]
    MOI_S3XT_PSI_INJ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_s3xt_sig; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN DISJ2_TAC THEN
  EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(z:real^3) IN derived_dual_cell t l v INTER derived_dual_cell t l u` THEN
  SET_TAC[]);;

(* ========================================================================= *)
(* Part 11: labels.  LABEL_ABS: a predicate on a connected open set O       *)
(* that is locally constant off a wall W, has the local dichotomy at wall    *)
(* points (where O minus W is dense), and holds at one point, holds on all  *)
(* of O minus W.  CONN_DIFF_CBALLS: removing finitely many disjoint closed  *)
(* balls keeps an open set of real^3 connected.                              *)
(* ========================================================================= *)

let MOI_S3XT_OPEN_LOCAL = prove
 (`!(O:real^3->bool) (P:real^3->bool).
     open {z | ?r. &0 < r /\ ball(z,r) SUBSET O /\ !y. y IN ball(z,r) ==> P y}`,
  REPEAT GEN_TAC THEN REWRITE_TAC[OPEN_CONTAINS_BALL; IN_ELIM_THM] THEN
  X_GEN_TAC `z:real^3` THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
  X_GEN_TAC `z':real^3` THEN DISCH_TAC THEN EXISTS_TAC `r - dist(z:real^3,z')` THEN
  SUBGOAL_THEN `ball(z':real^3,r - dist(z,z')) SUBSET ball(z,r)` ASSUME_TAC THENL
   [UNDISCH_TAC `(z':real^3) IN ball(z,r)` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [UNDISCH_TAC `(z':real^3) IN ball(z,r)` THEN REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC;
    ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_S3XT_LABEL_ABS = prove
 (`!(O:real^3->bool) W (ag:real^3->bool).
     open O /\ connected O /\
     (!z. z IN O /\ ~(z IN W)
          ==> ?r. &0 < r /\ ball(z,r) SUBSET O /\
                  ((!y. y IN ball(z,r) /\ ~(y IN W) ==> ag y) \/
                   (!y. y IN ball(z,r) /\ ~(y IN W) ==> ~ag y))) /\
     (!z r0. z IN O /\ z IN W /\ &0 < r0
             ==> ?r. &0 < r /\ r <= r0 /\ ball(z,r) SUBSET O /\
                     (?y. y IN ball(z,r) /\ ~(y IN W)) /\
                     ((!y. y IN ball(z,r) /\ ~(y IN W) ==> ag y) \/
                      (!y. y IN ball(z,r) /\ ~(y IN W) ==> ~ag y))) /\
     (?z. z IN O /\ ~(z IN W) /\ ag z)
     ==> !z. z IN O /\ ~(z IN W) ==> ag z`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "nw") (CONJUNCTS_THEN2 (LABEL_TAC "w")
      (X_CHOOSE_THEN `z0:real^3` STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC `G1 = {z:real^3 | ?r. &0 < r /\ ball(z,r) SUBSET O /\
                                   !y. y IN ball(z,r) ==> (~(y IN W) ==> ag y)}` THEN
  ABBREV_TAC `G2 = {z:real^3 | ?r. &0 < r /\ ball(z,r) SUBSET O /\
                                   !y. y IN ball(z,r) ==> (~(y IN W) ==> ~ag y)}` THEN
  SUBGOAL_THEN `open (G1:real^3->bool) /\ open (G2:real^3->bool)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["G1"; "G2"] THEN REWRITE_TAC[MOI_S3XT_OPEN_LOCAL]; ALL_TAC] THEN
  SUBGOAL_THEN `(O:real^3->bool) SUBSET G1 UNION G2` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
    MAP_EVERY EXPAND_TAC ["G1"; "G2"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_CASES_TAC `(z:real^3) IN W` THENL
     [USE_THEN "w" (MP_TAC o C MATCH_MP
        (CONJ (ASSUME `(z:real^3) IN O`) (CONJ (ASSUME `(z:real^3) IN W`) REAL_LT_01)) o
        SPECL [`z:real^3`; `&1`]) THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THENL
       [DISJ1_TAC; DISJ2_TAC] THEN EXISTS_TAC `r:real` THEN ASM_MESON_TAC[];
      USE_THEN "nw" (MP_TAC o C MATCH_MP
        (CONJ (ASSUME `(z:real^3) IN O`) (ASSUME `~((z:real^3) IN W)`)) o SPEC `z:real^3`) THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THENL
       [DISJ1_TAC; DISJ2_TAC] THEN EXISTS_TAC `r:real` THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (G1:real^3->bool) G2` ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN X_GEN_TAC `z:real^3` THEN
    MAP_EVERY EXPAND_TAC ["G1"; "G2"] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC)
                               (X_CHOOSE_THEN `r2:real` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(z:real^3) IN O` ASSUME_TAC THENL
     [MAP_EVERY UNDISCH_TAC [`ball(z:real^3,r1) SUBSET O`; `&0 < r1`] THEN
      REWRITE_TAC[SUBSET] THEN MESON_TAC[CENTRE_IN_BALL];
      ALL_TAC] THEN
    ASM_CASES_TAC `(z:real^3) IN W` THENL
     [SUBGOAL_THEN `&0 < min r1 r2` ASSUME_TAC THENL
       [ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
      USE_THEN "w" (MP_TAC o C MATCH_MP
        (CONJ (ASSUME `(z:real^3) IN O`) (CONJ (ASSUME `(z:real^3) IN W`)
           (ASSUME `&0 < min r1 r2`))) o SPECL [`z:real^3`; `min r1 r2`]) THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
          (CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) (K ALL_TAC)))))) THEN
      SUBGOAL_THEN `(y:real^3) IN ball(z,r1) /\ y IN ball(z,r2)` STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `(y:real^3) IN ball(z,r)` THEN REWRITE_TAC[IN_BALL] THEN
        UNDISCH_TAC `r <= min r1 r2` THEN REAL_ARITH_TAC;
        ASM_MESON_TAC[]];
      ASM_MESON_TAC[CENTRE_IN_BALL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z0:real^3) IN G1` ASSUME_TAC THENL
   [SUBGOAL_THEN `(z0:real^3) IN G1 UNION G2` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNION] THEN MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
    EXPAND_TAC "G2" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[CENTRE_IN_BALL];
    ALL_TAC] THEN
  SUBGOAL_THEN `(O:real^3->bool) SUBSET G1` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`O:real^3->bool`; `G1:real^3->bool`; `G2:real^3->bool`]
      MOI_S3XT_CONN_SPLIT) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~q ==> p \/ q ==> p`) THEN
    DISCH_TAC THEN
    MAP_EVERY UNDISCH_TAC [`DISJOINT (G1:real^3->bool) G2`; `(z0:real^3) IN G1`;
                           `(z0:real^3) IN O`; `(O:real^3->bool) SUBSET G2`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN G1` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  EXPAND_TAC "G1" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[CENTRE_IN_BALL]);;

let MOI_S3XT_CONN_DIFF_CBALLS = prove
 (`!(P:real^3->bool) r s.
     FINITE P /\ open s /\ connected s /\
     (!p. p IN P ==> cball(p,r) SUBSET s) /\
     (!p q. p IN P /\ q IN P /\ ~(p = q) ==> DISJOINT (cball(p,r)) (cball(q,r)))
     ==> open (s DIFF UNIONS {cball(p,r) | p IN P}) /\
         connected (s DIFF UNIONS {cball(p,r) | p IN P})`,
  REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM] THEN
  MATCH_MP_TAC FINITE_INDUCT_STRONG THEN CONJ_TAC THENL
   [REPEAT GEN_TAC THEN REPEAT DISCH_TAC THEN
    REWRITE_TAC[SET_RULE `{(f:real^3->real^3->bool) p | p IN {}} = {}`; UNIONS_0; DIFF_EMPTY] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`q:real^3`; `P:real^3->bool`] THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`r:real`; `s:real^3->bool`] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `{cball(p:real^3,r) | p IN q INSERT P} =
                cball(q,r) INSERT {cball(p,r) | p IN P}`
  SUBST1_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[UNIONS_INSERT; SET_RULE `(s:real^3->bool) DIFF (a UNION b) = (s DIFF b) DIFF a`] THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`r:real`; `s:real^3->bool`] o check (fun th ->
    is_forall(concl th) && length(fst(strip_forall(concl th))) = 2)) THEN
  REWRITE_TAC[IMP_IMP] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[IN_INSERT]; ASM_MESON_TAC[IN_INSERT]];
    ALL_TAC] THEN
  STRIP_TAC THEN CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[CLOSED_CBALL];
    MATCH_MP_TAC CONNECTED_OPEN_DIFF_CBALL THEN
    ASM_REWRITE_TAC[DIMINDEX_3; ARITH] THEN
    SUBGOAL_THEN `cball(q:real^3,r) SUBSET s /\
                  !p. p IN P ==> DISJOINT (cball(q,r)) (cball(p:real^3,r))`
    MP_TAC THENL
     [CONJ_TAC THENL
       [ASM_MESON_TAC[IN_INSERT];
        X_GEN_TAC `p:real^3` THEN DISCH_TAC THEN
        SUBGOAL_THEN `~(q:real^3 = p)` ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
        ASM_MESON_TAC[IN_INSERT]];
      REWRITE_TAC[SUBSET; IN_DIFF; UNIONS_GSPEC; IN_ELIM_THM; DISJOINT; EXTENSION;
                  IN_INTER; NOT_IN_EMPTY] THEN
      MESON_TAC[]]]);;

(* The finitely many vertices of triangulations of the spheres.            *)

let MOI_S3XT_VTX = prove
 (`!(V:real^3->bool) adj A FF X.
     PL_SCHOENFLIES_3_STATEMENT /\ moi_s3xt_cfg V adj A FF X
     ==> ?cc:real^3->(real^3->bool)->bool.
           FINITE {y:real^3 | ?v. v IN V /\ {y} IN cc v} /\
           !v. v IN V
               ==> simplicial_complex (cc v) /\ (!k. k IN cc v ==> aff_dim k <= &2) /\
                   combinatorial_manifold 2 (cc v) /\
                   UNIONS (cc v) = moi_s3xt_sph A FF adj v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                 `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`] MOI_S3XT_CFG_G) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!v:real^3. v IN V
               ==> ?c. simplicial_complex c /\ (!k. k IN c ==> aff_dim k <= &2) /\
                       combinatorial_manifold 2 c /\ UNIONS c = moi_s3xt_sph A FF adj v`
  MP_TAC THENL
   [X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_S3XT_SPHERE_TRIANG THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`V:real^3->bool`; `adj:real^3->real^3->bool`; `A:real^3->real^3->bool`;
                   `FF:real^3->real^3->real^3->bool`; `X:real^3->bool`; `v:real^3`]
      MOI_S3XT_CFG_V) THEN
    ASM_SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `cc:real^3->(real^3->bool)->bool` (LABEL_TAC "cc") o
               REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM])] THEN
  EXISTS_TAC `cc:real^3->(real^3->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{y:real^3 | ?v. v IN V /\ {y} IN cc v} =
                UNIONS (IMAGE (\v. {y:real^3 | {y} IN
                                (cc:real^3->(real^3->bool)->bool) v}) (V:real^3->bool))`
  SUBST1_TAC THENL
   [REWRITE_TAC[UNIONS_IMAGE; IN_ELIM_THM; EXTENSION] THEN MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[FINITE_UNIONS] THEN ASM_SIMP_TAC[FINITE_IMAGE; FORALL_IN_IMAGE] THEN
  X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\y:real^3. {y}`; `(cc:real^3->(real^3->bool)->bool) v`]
    FINITE_IMAGE_INJ) THEN
  REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN CONJ_TAC THENL
   [SET_TAC[];
    USE_THEN "cc" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(v:real^3) IN V`))) THEN
    REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]]);;

(* The closed balls of radius rho / 2 at the centres.                       *)

let MOI_S3XT_RBALLS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho.
     moi_s3xt_ctx t l h e c x g g' FF rho
     ==> FINITE {h(midpoint(u,v)) | u,v | ~(u = v) /\ segment[u,v] IN l} /\
         (!p. p IN {h(midpoint(u,v)) | u,v | ~(u = v) /\ segment[u,v] IN l}
              ==> cball(p,rho / &2) SUBSET interior (UNIONS x)) /\
         (!p q. p IN {h(midpoint(u,v)) | u,v | ~(u = v) /\ segment[u,v] IN l} /\
                q IN {h(midpoint(u,v)) | u,v | ~(u = v) /\ segment[u,v] IN l} /\
                ~(p = q)
                ==> DISJOINT (cball(p,rho / &2)) (cball(q,rho / &2)))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{(h:real^3->real^3)(midpoint(u,v)) | u IN {w:real^3 | {w} IN l} /\
                                                     v IN {w:real^3 | {w} IN l}}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_PRODUCT_DEPENDENT THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `p:real^3` THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`u:real^3`; `v:real^3`] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                     `u:real^3`; `v:real^3`] MOI_S3XT_EDGE_VERTICES) THEN
      ASM_SIMP_TAC[]];
    REWRITE_TAC[FORALL_IN_GSPEC] THEN MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `u:real^3`; `v:real^3`]
      MOI_S3XT_CTX_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball((h:real^3->real^3)(midpoint(u,v)),&2 * rho)` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
    UNDISCH_TAC `&0 < rho` THEN REAL_ARITH_TAC;
    REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
    MAP_EVERY X_GEN_TAC [`u:real^3`; `v:real^3`] THEN REPEAT DISCH_TAC THEN
    MAP_EVERY X_GEN_TAC [`u':real^3`; `v':real^3`] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `~(segment[u':real^3,v'] = segment[u,v])` ASSUME_TAC THENL
     [REWRITE_TAC[SEGMENT_EQ] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((h:real^3->real^3)(midpoint(u,v)) = h(midpoint(u',v')))` THEN
      REWRITE_TAC[] THEN AP_TERM_TAC THEN
      SUBGOAL_THEN `(u':real^3 = u /\ v' = v) \/ (u' = v /\ v' = u)` MP_TAC THENL
       [UNDISCH_TAC `{u':real^3,v'} = {u,v}` THEN
        REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
        STRIP_TAC THEN ASM_REWRITE_TAC[MIDPOINT_SYM]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `u:real^3`; `v:real^3`]
      MOI_S3XT_CTX_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`u':real^3`; `v':real^3`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `dist:real^3#real^3->real`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_CBALL; NOT_IN_EMPTY] THEN
    X_GEN_TAC `z:real^3` THEN
    UNDISCH_TAC `&3 * rho <= dist((h:real^3->real^3)(midpoint(u,v)),h(midpoint(u',v')))` THEN
    UNDISCH_TAC `&0 < rho` THEN CONV_TAC NORM_ARITH]);;

(* ========================================================================= *)
(* Part 12: the labels on the tube.  moi_s3xt_S: the image spheres;         *)
(* moi_s3xt_R: the closed rho / 2 balls at the centres; moi_s3xt_E: the     *)
(* pseudo-cells; moi_s3xt_ag: the piece label and the ball label agree.      *)
(* LAB_BASE collects the facts used below.                                   *)
(* ========================================================================= *)

let moi_s3xt_S = new_definition
 `moi_s3xt_S (c:real^3->real^3->bool) (x:(real^3->bool)->bool)
             (FF:real^3->real^3->real^3->bool) (l:(real^3->bool)->bool) (v:real^3) =
    moi_s3xt_sph (\v. c v INTER frontier (UNIONS x)) FF
                 (\u v. ~(u = v) /\ segment[u,v] IN l) v`;;

let moi_s3xt_R = new_definition
 `moi_s3xt_R (h:real^3->real^3) (l:(real^3->bool)->bool) rho =
    UNIONS {cball(p,rho / &2) | p IN {h(midpoint(u,v)) | u,v | ~(u = v) /\ segment[u,v] IN l}}`;;

let moi_s3xt_E = new_definition
 `moi_s3xt_E (l:(real^3->bool)->bool) (e:(real^3->bool)->real^3->bool) =
    UNIONS {e s | s IN l /\ aff_dim s = &1}`;;

let moi_s3xt_ag = new_definition
 `moi_s3xt_ag (l:(real^3->bool)->bool) (c:real^3->real^3->bool) (x:(real^3->bool)->bool)
              (FF:real^3->real^3->real^3->bool) (z:real^3) <=>
    ?a. {a} IN l /\ z IN c a /\ z IN inside(moi_s3xt_S c x FF l a)`;;

let MOI_S3XT_HD_COVER = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c.
     moi_s33_hd t l h e c
     ==> IMAGE h (derived_nbhd t l) = UNIONS {c v | {v} IN l}`,
  REWRITE_TAC[moi_s33_hd] THEN MESON_TAC[]);;

let MOI_S3XT_LAB_BASE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi.
     PL_SCHOENFLIES_3_STATEMENT /\
     moi_s3xt_ctx t l h e c x g g' FF rho /\ moi_s3xt_maps t l g FF phi Psi
     ==> closed (moi_s3xt_R h l rho) /\ moi_s3xt_R h l rho SUBSET interior (UNIONS x) /\
         closed (moi_s3xt_E l e) /\
         (!a b. {a} IN l /\ {b} IN l /\ ~(a = b) ==> c a INTER c b SUBSET moi_s3xt_E l e) /\
         UNIONS x SUBSET UNIONS {c a | a | {a} IN l} /\
         (!a. {a} IN l ==> closed (c a)) /\
         (!a b. {a} IN l /\ {b} IN l /\ ~(a = b)
                ==> DISJOINT (inside(moi_s3xt_S c x FF l a)) (inside(moi_s3xt_S c x FF l b))) /\
         interior (UNIONS x) SUBSET
         UNIONS {moi_s3xt_S c x FF l a UNION inside(moi_s3xt_S c x FF l a) | a | {a} IN l} /\
         (!a. {a} IN l ==> open (inside(moi_s3xt_S c x FF l a)) /\
                           pl_sphere 2 (moi_s3xt_S c x FF l a) /\
                           inside(moi_s3xt_S c x FF l a) SUBSET interior (UNIONS x)) /\
         (!a z. {a} IN l /\ z IN interior (UNIONS x) /\ ~(z IN moi_s3xt_R h l rho) /\
                ~(z IN moi_s3xt_E l e)
                ==> ~(z IN moi_s3xt_S c x FF l a))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S3XT_TUBE_GRAPH) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_CFG_INST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_RBALLS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^3->bool. s IN l /\ aff_dim s = &1
                  ==> ?u v. ~(u = v) /\ s = segment[u,v] /\ {u} IN l /\ {v} IN l`
  (LABEL_TAC "edge") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s3xt_S] THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[moi_s3xt_R] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE; CLOSED_CBALL] THEN
    MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s3xt_R; UNIONS_SUBSET] THEN
    REWRITE_TAC[SIMPLE_IMAGE; FORALL_IN_IMAGE] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[moi_s3xt_E] THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `s:real^3->bool` THEN STRIP_TAC THEN
      USE_THEN "edge" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(s:real^3->bool) IN l`)
                                             (ASSUME `aff_dim(s:real^3->bool) = &1`))) THEN
      DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `v:real^3` STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                     `u:real^3`; `v:real^3`] MOI_S3XT_HD_EDGE) THEN
      ASM_SIMP_TAC[]];
    MAP_EVERY X_GEN_TAC [`a:real^3`; `b:real^3`] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `a:real^3`; `b:real^3`] MOI_S3XT_HD_MEET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN COND_CASES_TAC THEN
    REWRITE_TAC[EMPTY_SUBSET; moi_s3xt_E] THEN
    MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN s ==> a SUBSET UNIONS s`) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `segment[a:real^3,b]` THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `x:(real^3->bool)->bool`]
      MOI_S3XT_XFACTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `a:real^3->bool`] MOI_FSA_EDGE_VERTS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_IMAGE; IN_UNIONS] THEN
      MAP_EVERY EXISTS_TAC [`(h:real^3->real^3) p`; `p:real^3`] THEN REWRITE_TAC[] THEN
      EXISTS_TAC `{p:real^3}` THEN ASM_REWRITE_TAC[IN_SING];
      STRIP_TAC] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
      MOI_S3XT_HD_COVER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `interior (IMAGE (h:real^3->real^3) (derived_nbhd t l))` THEN
    ASM_REWRITE_TAC[INTERIOR_SUBSET];
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
      MOI_S3XT_HD_MISC) THEN
    ASM_SIMP_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3XT_INT_DISJ THEN
    MAP_EVERY EXISTS_TAC [`{v:real^3 | {v} IN l}`; `UNIONS x:real^3->bool`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    MP_TAC(ISPECL [`{v:real^3 | {v} IN l}`; `\u v:real^3. ~(u = v) /\ segment[u,v] IN l`;
                   `\v:real^3. (c:real^3->real^3->bool) v INTER frontier (UNIONS x)`;
                   `FF:real^3->real^3->real^3->bool`; `UNIONS x:real^3->bool`]
      MOI_S3XT_COVER) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    X_GEN_TAC `a:real^3` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`{v:real^3 | {v} IN l}`; `\u v:real^3. ~(u = v) /\ segment[u,v] IN l`;
                   `\v:real^3. (c:real^3->real^3->bool) v INTER frontier (UNIONS x)`;
                   `FF:real^3->real^3->real^3->bool`; `UNIONS x:real^3->bool`; `a:real^3`]
      MOI_S3XT_CFG_SPHERE) THEN
    ASM_REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `moi_s3xt_sph (\v. (c:real^3->real^3->bool) v INTER frontier (UNIONS x)) FF
                    (\u v. ~(u = v) /\ segment[u,v] IN l) a` MOI_S3XT_SPHERE_FACTS) THEN
    ASM_SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`a:real^3`; `z:real^3`] THEN STRIP_TAC THEN
    REWRITE_TAC[MOI_S3XT_SPH_EQ; IN_UNION; UNIONS_GSPEC; IN_ELIM_THM; IN_INTER] THEN
    MATCH_MP_TAC(TAUT `~p /\ ~q ==> ~(p \/ q)`) THEN CONJ_TAC THENL
     [UNDISCH_TAC `(z:real^3) IN interior (UNIONS x)` THEN
      REWRITE_TAC[frontier] THEN SET_TAC[];
      REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                     `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                     `FF:real^3->real^3->real^3->bool`; `rho:real`; `a:real^3`; `w:real^3`]
        MOI_S3XT_CTX_EDGE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN `~((z:real^3) IN e(segment[a,w])) /\
                    ~(z IN ball((h:real^3->real^3)(midpoint(a,w)),rho / &2))`
      MP_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `~((z:real^3) IN moi_s3xt_E l e)` THEN
          REWRITE_TAC[moi_s3xt_E; IN_UNIONS; IN_ELIM_THM] THEN
          REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
          EXISTS_TAC `(e:(real^3->bool)->real^3->bool)(segment[a,w])` THEN
          ASM_REWRITE_TAC[] THEN EXISTS_TAC `segment[a:real^3,w]` THEN
          ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
          UNDISCH_TAC `~((z:real^3) IN moi_s3xt_R h l rho)` THEN
          REWRITE_TAC[moi_s3xt_R; IN_UNIONS; IN_ELIM_THM] THEN
          REWRITE_TAC[CONTRAPOS_THM] THEN DISCH_TAC THEN
          EXISTS_TAC `cball((h:real^3->real^3)(midpoint(a,w)),rho / &2)` THEN
          CONJ_TAC THENL
           [EXISTS_TAC `(h:real^3->real^3)(midpoint(a,w))` THEN REWRITE_TAC[] THEN
            MAP_EVERY EXISTS_TAC [`a:real^3`; `w:real^3`] THEN ASM_REWRITE_TAC[];
            MP_TAC(ISPECL [`(h:real^3->real^3)(midpoint(a,w))`; `rho / &2`]
              BALL_SUBSET_CBALL) THEN ASM SET_TAC[]]];
        MAP_EVERY UNDISCH_TAC
         [`(FF:real^3->real^3->real^3->bool) a w SUBSET
           e(segment[a,w]) UNION ball((h:real^3->real^3)(midpoint(a,w)),rho / &2)`;
          `(z:real^3) IN (FF:real^3->real^3->real^3->bool) a w`] THEN
        SET_TAC[]]]]);;

(* Off the walls the two labels are locally constant.                       *)

let MOI_S3XT_LAB_NW = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi (V0:real^3->bool) z.
     PL_SCHOENFLIES_3_STATEMENT /\ moi_s3xt_ctx t l h e c x g g' FF rho /\
     moi_s3xt_maps t l g FF phi Psi /\ FINITE V0 /\
     z IN interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0 /\ ~(z IN moi_s3xt_E l e)
     ==> ?r. &0 < r /\
             ball(z,r) SUBSET interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0 /\
             ((!y. y IN ball(z,r) /\ ~(y IN moi_s3xt_E l e) ==> moi_s3xt_ag l c x FF y) \/
              (!y. y IN ball(z,r) /\ ~(y IN moi_s3xt_E l e) ==> ~moi_s3xt_ag l c x FF y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_LAB_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {v:real^3 | {v} IN l}` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S3XT_TUBE_GRAPH (ASSUME `moi_s33_tube t l (h:real^3->real^3)`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?a:real^3. {a} IN l /\ z IN (c:real^3->real^3->bool) a` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `UNIONS x:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `UNIONS x SUBSET UNIONS {(c:real^3->real^3->bool) a | a | {a} IN l}` THEN
    UNDISCH_TAC `(z:real^3) IN interior (UNIONS x)` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?b:real^3. {b} IN l /\ z IN inside(moi_s3xt_S c x FF l b)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?b:real^3. {b} IN l /\
                  (z IN moi_s3xt_S c x FF l b \/ z IN inside(moi_s3xt_S c x FF l b))`
    MP_TAC THENL
     [UNDISCH_TAC `interior (UNIONS x) SUBSET
                   UNIONS {moi_s3xt_S c x FF l a UNION inside(moi_s3xt_S c x FF l a) | a |
                           {a:real^3} IN l}` THEN
      UNDISCH_TAC `(z:real^3) IN interior (UNIONS x)` THEN
      REWRITE_TAC[SUBSET; UNIONS_GSPEC; IN_ELIM_THM; IN_UNION] THEN MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ABBREV_TAC `C' = UNIONS {(c:real^3->real^3->bool) a' | a' | {a'} IN l /\ ~(a' = a)}` THEN
  SUBGOAL_THEN `closed (C':real^3->bool) /\ ~((z:real^3) IN C')` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "C'" THEN CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{v:real^3 | {v} IN l}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
      X_GEN_TAC `a':real^3` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3`; `a':real^3`] o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
        (let b = snd(strip_forall(concl th)) in
         is_imp b && (try fst(dest_const(fst(strip_comb(rand b)))) = "SUBSET"
                      with Failure _ -> false)))) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((z:real^3) IN moi_s3xt_E l e)` THEN
      UNDISCH_TAC `(z:real^3) IN c(a:real^3)` THEN
      UNDISCH_TAC `(z:real^3) IN (c:real^3->real^3->bool) a'` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?r. &0 < r /\
        ball(z:real^3,r) SUBSET
        ((interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0) INTER
         inside(moi_s3xt_S c x FF l b)) DIFF C'`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN
     `open (((interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0) INTER
             inside(moi_s3xt_S c x FF l (b:real^3))) DIFF C')`
    MP_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC OPEN_INTER THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[FINITE_IMP_CLOSED] THEN
      MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
      REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
      ASM_REWRITE_TAC[IN_DIFF; IN_INTER]];
    ALL_TAC] THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `ball(z:real^3,r) SUBSET
                 ((interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0) INTER
                  inside(moi_s3xt_S c x FF l b)) DIFF C'` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN ball(z,r) /\ ~(y IN moi_s3xt_E l e)
        ==> y IN (c:real^3->real^3->bool) a /\ y IN inside(moi_s3xt_S c x FF l b) /\
            (!a'. {a'} IN l /\ y IN c a' ==> a' = a)`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN interior (UNIONS x) /\ y IN inside(moi_s3xt_S c x FF l b) /\
                  ~(y IN C')` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `ball(z:real^3,r) SUBSET
                   ((interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0) INTER
                    inside(moi_s3xt_S c x FF l b)) DIFF C'` THEN
      UNDISCH_TAC `(y:real^3) IN ball(z,r)` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `!a'. {a'} IN l /\ (y:real^3) IN (c:real^3->real^3->bool) a' ==> a' = a`
    ASSUME_TAC THENL
     [X_GEN_TAC `a':real^3` THEN STRIP_TAC THEN
      MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      UNDISCH_TAC `~((y:real^3) IN C')` THEN EXPAND_TAC "C'" THEN
      REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `a':real^3` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `?a'. {a'} IN l /\ (y:real^3) IN (c:real^3->real^3->bool) a'`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `UNIONS x:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `UNIONS x SUBSET UNIONS {(c:real^3->real^3->bool) a | a | {a} IN l}` THEN
      UNDISCH_TAC `(y:real^3) IN interior (UNIONS x)` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real^3 = b` THENL
   [DISJ1_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[moi_s3xt_ag] THEN EXISTS_TAC `a:real^3` THEN ASM_MESON_TAC[];
    DISJ2_TAC THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    REWRITE_TAC[moi_s3xt_ag; NOT_EXISTS_THM] THEN X_GEN_TAC `a':real^3` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o C MATCH_MP (ASSUME
      `(y:real^3) IN ball(z,r) /\ ~(y IN moi_s3xt_E l e)`) o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> t = `ball:real^3#real->real^3->bool`)) (concl th))) THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `a':real^3 = a` SUBST_ALL_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3`; `b:real^3`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `DISJOINT:(real^3->bool)->(real^3->bool)->bool`))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

(* The two local sides of a wall lie in the two pieces of its ends.          *)

let MOI_S3XT_SIDE_PIECE = prove
 (`!(U:real^3->bool) P1 P2 W.
     connected U /\ closed P1 /\ closed P2 /\ U SUBSET P1 UNION P2 /\
     P1 INTER P2 SUBSET W /\ U INTER W = {}
     ==> U SUBSET P1 \/ U SUBSET P2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
  UNDISCH_TAC `connected (U:real^3->bool)` THEN REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC [`P1:real^3->bool`; `P2:real^3->bool`] THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S3XT_TWO_PIECES = prove
 (`!(B:real^3->bool) U1 U2 P1 P2 K1 K2 W z.
     B DIFF W = U1 UNION U2 /\ open B /\ z IN B /\
     P1 = closure K1 /\ P2 = closure K2 /\ K1 INTER W = {} /\ K2 INTER W = {} /\
     z IN P1 /\ z IN P2 /\ P1 INTER P2 SUBSET W /\
     (U1 SUBSET P1 \/ U1 SUBSET P2) /\ (U2 SUBSET P1 \/ U2 SUBSET P2)
     ==> (U1 SUBSET P1 /\ U2 SUBSET P2) \/ (U1 SUBSET P2 /\ U2 SUBSET P1)`,
  REPEAT GEN_TAC THEN DISCH_THEN(fun th -> MAP_EVERY ASSUME_TAC (CONJUNCTS th)) THEN
  SUBGOAL_THEN `~(B INTER (K1:real^3->bool) = {}) /\ ~(B INTER (K2:real^3->bool) = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    W(fun (asl,w) -> MP_TAC(ISPECL [`B:real^3->bool`; rand(lhand(rand w))]
                              OPEN_INTER_CLOSURE_EQ_EMPTY)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(K1:real^3->bool) SUBSET P1 /\ (K2:real^3->bool) SUBSET P2`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[CLOSURE_SUBSET]; ALL_TAC] THEN
  ASM SET_TAC[]);;

let MOI_S3XT_HD_PIECE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c v.
     moi_s33_hd t l h e c /\ {v} IN l
     ==> c v = closure (connected_component
                 (IMAGE h (derived_nbhd t l) DIFF moi_s3xt_E l e) (h v))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s33_hd; moi_s3xt_E] THEN MESON_TAC[]);;

(* Near a wall point z of O: the wall is the pseudo-cell of one edge u w,    *)
(* which there is the disk FF u w and the common part of the spheres of u   *)
(* and w, and the pieces of u and w cover a ball at z.                       *)

let MOI_S3XT_LAB_WALL_EDGE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi (V0:real^3->bool) z.
     PL_SCHOENFLIES_3_STATEMENT /\ moi_s3xt_ctx t l h e c x g g' FF rho /\
     moi_s3xt_maps t l g FF phi Psi /\ FINITE V0 /\
     z IN interior (UNIONS x) /\ ~(z IN moi_s3xt_R h l rho) /\ ~(z IN V0) /\
     z IN moi_s3xt_E l e
     ==> ?u w rs. ~(u = w) /\ segment[u,w] IN l /\ {u} IN l /\ {w} IN l /\
                  z IN e(segment[u,w]) /\ z IN FF u w /\ &0 < rs /\
                  ball(z,rs) SUBSET interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0 /\
                  ball(z,rs) INTER moi_s3xt_E l e =
                  ball(z,rs) INTER moi_s3xt_S c x FF l u /\
                  ball(z,rs) INTER moi_s3xt_S c x FF l u =
                  ball(z,rs) INTER moi_s3xt_S c x FF l w /\
                  ball(z,rs) SUBSET c u UNION c w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_LAB_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {v:real^3 | {v} IN l} /\ FINITE (l:(real^3->bool)->bool) /\
                simplicial_complex l`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S3XT_TUBE_GRAPH (ASSUME `moi_s33_tube t l (h:real^3->real^3)`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?u w. ~(u = w) /\ segment[u,w] IN l /\ {u} IN l /\ {w} IN l /\
                      (z:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[u,w])`
  (X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `w:real^3` STRIP_ASSUME_TAC)) THENL
   [UNDISCH_TAC `(z:real^3) IN moi_s3xt_E l e` THEN
    REWRITE_TAC[moi_s3xt_E; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`p:real^3`; `q:real^3`] THEN
    UNDISCH_TAC `(z:real^3) IN t0` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(s:real^3->bool) IN l` THEN ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`u:real^3`; `w:real^3`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`; `u:real^3`; `w:real^3`]
    MOI_S3XT_CTX_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `u:real^3`; `w:real^3`] MOI_S3XT_HD_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `p = (h:real^3->real^3)(midpoint(u,w))` THEN
  SUBGOAL_THEN `~((z:real^3) IN cball(p,rho / &2))` ASSUME_TAC THENL
   [UNDISCH_TAC `~((z:real^3) IN moi_s3xt_R h l rho)` THEN
    REWRITE_TAC[moi_s3xt_R; IN_UNIONS; IN_ELIM_THM; CONTRAPOS_THM] THEN DISCH_TAC THEN
    EXISTS_TAC `cball(p:real^3,rho / &2)` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `p:real^3` THEN REWRITE_TAC[] THEN
    MAP_EVERY EXISTS_TAC [`u:real^3`; `w:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(z:real^3) IN FF (u:real^3) (w:real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `(e(segment[u:real^3,w]) INTER UNIONS x) DIFF ball(p,rho / &2)
                 SUBSET (FF:real^3->real^3->real^3->bool) u w` THEN
    MP_TAC(ISPEC `UNIONS x:real^3->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPECL [`p:real^3`; `rho / &2`] BALL_SUBSET_CBALL) THEN
    MAP_EVERY UNDISCH_TAC
     [`(z:real^3) IN interior (UNIONS x)`; `(z:real^3) IN e(segment[u:real^3,w])`;
      `~((z:real^3) IN cball(p,rho / &2))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_CFG_INST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{v:real^3 | {v} IN l}`; `\u v:real^3. ~(u = v) /\ segment[u,v] IN l`;
                 `\v:real^3. (c:real^3->real^3->bool) v INTER frontier (UNIONS x)`;
                 `FF:real^3->real^3->real^3->bool`; `UNIONS x:real^3->bool`;
                 `u:real^3`; `w:real^3`; `z:real^3`] MOI_S3XT_LOCAL_EQ) THEN
  ASM_REWRITE_TAC[GSYM moi_s3xt_S] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?r2. &0 < r2 /\
                     ball(z:real^3,r2) SUBSET
                     interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open (interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF (V0:real^3->bool))`
    MP_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[FINITE_IMP_CLOSED] THEN
      MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
      REWRITE_TAC[OPEN_CONTAINS_BALL] THEN DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN
      ASM_REWRITE_TAC[IN_DIFF]];
    ALL_TAC] THEN
  ABBREV_TAC `Q = cball(p:real^3,rho / &2) UNION
                  UNIONS {(e:(real^3->bool)->real^3->bool) s' | s' |
                          s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,w])} UNION
                  UNIONS {(c:real^3->real^3->bool) a | a |
                          {a} IN l /\ ~(a = u) /\ ~(a = w)}` THEN
  SUBGOAL_THEN
   `!s':real^3->bool. s' IN l /\ aff_dim s' = &1
        ==> ?u' w'. ~(u' = w') /\ s' = segment[u',w'] /\ {u'} IN l /\ {w'} IN l`
  (LABEL_TAC "edge") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `s':real^3->bool`] MOI_FSA_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (Q:real^3->bool) /\ ~((z:real^3) IN Q)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN REWRITE_TAC[CLOSED_CBALL] THEN
      MATCH_MP_TAC CLOSED_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
       [ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `l:(real^3->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        X_GEN_TAC `s':real^3->bool` THEN STRIP_TAC THEN
        USE_THEN "edge" (MP_TAC o C MATCH_MP
          (CONJ (ASSUME `(s':real^3->bool) IN l`) (ASSUME `aff_dim(s':real^3->bool) = &1`))) THEN
        DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `w':real^3`
          STRIP_ASSUME_TAC)) THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN MATCH_MP_TAC COMPACT_IMP_CLOSED THEN
        MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                       `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                       `u':real^3`; `w':real^3`] MOI_S3XT_HD_EDGE) THEN
        ASM_SIMP_TAC[];
        ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN MATCH_MP_TAC FINITE_IMAGE THEN
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{v:real^3 | {v} IN l}` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        ASM_SIMP_TAC[]];
      REWRITE_TAC[IN_UNION; UNIONS_GSPEC; IN_ELIM_THM] THEN
      MATCH_MP_TAC(TAUT `~p /\ ~q /\ ~r ==> ~(p \/ q \/ r)`) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `s':real^3->bool` THEN STRIP_TAC THEN
        USE_THEN "edge" (MP_TAC o C MATCH_MP
          (CONJ (ASSUME `(s':real^3->bool) IN l`) (ASSUME `aff_dim(s':real^3->bool) = &1`))) THEN
        DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `w':real^3`
          STRIP_ASSUME_TAC)) THEN
        FIRST_X_ASSUM SUBST_ALL_TAC THEN
        MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                       `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`]
          MOI_S3XT_HD_MISC) THEN
        ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPECL [`u:real^3`; `w:real^3`; `u':real^3`; `w':real^3`] o
                   last o CONJUNCTS) THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`(z:real^3) IN e(segment[u:real^3,w])`;
          `(z:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[u',w'])`] THEN
        SET_TAC[];
        REWRITE_TAC[NOT_EXISTS_THM] THEN X_GEN_TAC `a:real^3` THEN STRIP_TAC THEN
        FIRST_X_ASSUM(MP_TAC o SPEC `a:real^3` o check (fun th ->
          is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
          can (find_term (fun t -> t = `(e:(real^3->bool)->real^3->bool)(segment[u,w])`))
              (concl th) &&
          can (find_term (fun t -> t = `(c:real^3->real^3->bool)`)) (concl th))) THEN
        ASM_REWRITE_TAC[] THEN
        MAP_EVERY UNDISCH_TAC
         [`(z:real^3) IN e(segment[u:real^3,w])`;
          `(z:real^3) IN (c:real^3->real^3->bool) a`] THEN
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r3. &0 < r3 /\ ball(z:real^3,r3) INTER Q = {}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `closed (Q:real^3->bool)` THEN REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `min r1 (min r2 r3)` THEN
  SUBGOAL_THEN `&0 < min r1 (min r2 r3) /\
                ball(z:real^3,min r1 (min r2 r3)) SUBSET ball(z,r1) /\
                ball(z:real^3,min r1 (min r2 r3)) SUBSET ball(z,r2) /\
                ball(z:real^3,min r1 (min r2 r3)) SUBSET ball(z,r3)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC SUBSET_BALL THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `B = ball(z:real^3,min r1 (min r2 r3))` THEN
  SUBGOAL_THEN `!y:real^3. y IN B ==> ~(y IN Q)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`B SUBSET ball(z:real^3,r3)`; `ball(z:real^3,r3) INTER Q = {}`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^3. y IN B ==> y IN interior (UNIONS x)` ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`B SUBSET ball(z:real^3,r2)`;
      `ball(z:real^3,r2) SUBSET interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `B INTER moi_s3xt_S c x FF l u = B INTER (FF:real^3->real^3->real^3->bool) u w /\
                B INTER moi_s3xt_S c x FF l w = B INTER FF u w`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`B SUBSET ball(z:real^3,r1)`;
      `ball(z:real^3,r1) INTER moi_s3xt_S c x FF l u = ball(z,r1) INTER FF u w`;
      `ball(z:real^3,r1) INTER moi_s3xt_S c x FF l w = ball(z,r1) INTER FF u w`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    MAP_EVERY UNDISCH_TAC
     [`B SUBSET ball(z:real^3,r2)`;
      `ball(z:real^3,r2) SUBSET interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0`] THEN
    SET_TAC[];
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[EXTENSION; IN_INTER] THEN
    X_GEN_TAC `y:real^3` THEN ASM_CASES_TAC `(y:real^3) IN B` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((y:real^3) IN Q) /\ y IN interior (UNIONS x)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "Q" THEN REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
    EQ_TAC THENL
     [REWRITE_TAC[moi_s3xt_E; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `t0:real^3->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `s'':real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      SUBGOAL_THEN `s'':real^3->bool = segment[u,w]` SUBST_ALL_TAC THENL
       [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
        UNDISCH_TAC `~((y:real^3) IN
                       UNIONS {(e:(real^3->bool)->real^3->bool) s' | s' |
                               s' IN l /\ aff_dim s' = &1 /\ ~(s' = segment[u,w])})` THEN
        REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `t0:real^3->bool` THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `s'':real^3->bool` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `(e(segment[u:real^3,w]) INTER UNIONS x) DIFF ball(p,rho / &2)
                   SUBSET (FF:real^3->real^3->real^3->bool) u w` THEN
      MP_TAC(ISPEC `UNIONS x:real^3->bool` INTERIOR_SUBSET) THEN
      MP_TAC(ISPECL [`p:real^3`; `rho / &2`] BALL_SUBSET_CBALL) THEN
      MAP_EVERY UNDISCH_TAC
       [`(y:real^3) IN t0`; `t0 = (e:(real^3->bool)->real^3->bool)(segment[u,w])`;
        `(y:real^3) IN interior (UNIONS x)`; `~((y:real^3) IN cball(p,rho / &2))`] THEN
      SET_TAC[];
      DISCH_TAC THEN REWRITE_TAC[moi_s3xt_E; IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `(e:(real^3->bool)->real^3->bool)(segment[u,w])` THEN CONJ_TAC THENL
       [EXISTS_TAC `segment[u:real^3,w]` THEN ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
        MP_TAC(ISPECL [`p:real^3`; `rho / &2`] BALL_SUBSET_CBALL) THEN
        UNDISCH_TAC `(FF:real^3->real^3->real^3->bool) u w SUBSET
                     e(segment[u,w]) UNION ball(p,rho / &2)` THEN
        MAP_EVERY UNDISCH_TAC
         [`(y:real^3) IN (FF:real^3->real^3->real^3->bool) u w`;
          `~((y:real^3) IN cball(p,rho / &2))`] THEN
        SET_TAC[]]];
    ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `y:real^3` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~((y:real^3) IN Q) /\ y IN interior (UNIONS x)` MP_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "Q" THEN REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?a:real^3. {a} IN l /\ y IN (c:real^3->real^3->bool) a`
    STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPEC `UNIONS x:real^3->bool` INTERIOR_SUBSET) THEN
      UNDISCH_TAC `UNIONS x SUBSET UNIONS {(c:real^3->real^3->bool) a | a | {a} IN l}` THEN
      UNDISCH_TAC `(y:real^3) IN interior (UNIONS x)` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p /\ ~q ==> F) ==> p \/ q`) THEN STRIP_TAC THEN
    UNDISCH_TAC `~((y:real^3) IN
                   UNIONS {(c:real^3->real^3->bool) a | a | {a} IN l /\ ~(a = u) /\
                                                          ~(a = w)})` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `(c:real^3->real^3->bool) a` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `a:real^3` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]]);;

(* The local dichotomy at wall points: the two local sides of the wall lie  *)
(* in the two balls (TWO_SIDES) and in the two pieces (TWO_PIECES), either  *)
(* matching or crossed.                                                      *)

let MOI_S3XT_LAB_WALL = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi (cc:real^3->(real^3->bool)->bool)
    (V0:real^3->bool) z r0.
     PL_SCHOENFLIES_3_STATEMENT /\ moi_s3xt_ctx t l h e c x g g' FF rho /\
     moi_s3xt_maps t l g FF phi Psi /\ FINITE V0 /\
     (!v. {v} IN l
          ==> simplicial_complex (cc v) /\ (!k. k IN cc v ==> aff_dim k <= &2) /\
              combinatorial_manifold 2 (cc v) /\ UNIONS (cc v) = moi_s3xt_S c x FF l v /\
              (!y. {y} IN cc v ==> y IN V0)) /\
     z IN interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0 /\ z IN moi_s3xt_E l e /\
     &0 < r0
     ==> ?r. &0 < r /\ r <= r0 /\
             ball(z,r) SUBSET interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0 /\
             (?y. y IN ball(z,r) /\ ~(y IN moi_s3xt_E l e)) /\
             ((!y. y IN ball(z,r) /\ ~(y IN moi_s3xt_E l e) ==> moi_s3xt_ag l c x FF y) \/
              (!y. y IN ball(z,r) /\ ~(y IN moi_s3xt_E l e) ==> ~moi_s3xt_ag l c x FF y))`,
  REPEAT GEN_TAC THEN REWRITE_TAC[IN_DIFF] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "cc") STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_LAB_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`;
                 `V0:real^3->bool`; `z:real^3`] MOI_S3XT_LAB_WALL_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^3` (X_CHOOSE_THEN `w:real^3`
    (X_CHOOSE_THEN `rs:real` STRIP_ASSUME_TAC))) THEN
  USE_THEN "cc" (MP_TAC o C MATCH_MP (ASSUME `{u:real^3} IN l`)) THEN STRIP_TAC THEN
  SUBGOAL_THEN `(z:real^3) IN moi_s3xt_S c x FF l u` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`\v:real^3. (c:real^3->real^3->bool) v INTER frontier (UNIONS x)`;
                   `FF:real^3->real^3->real^3->bool`;
                   `\u v:real^3. ~(u = v) /\ segment[u,v] IN l`; `u:real^3`; `w:real^3`]
      MOI_S3XT_SPH_FF) THEN
    ASM_REWRITE_TAC[GSYM moi_s3xt_S] THEN
    UNDISCH_TAC `(z:real^3) IN (FF:real^3->real^3->real^3->bool) u w` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`moi_s3xt_S c x FF l (u:real^3)`; `moi_s3xt_S c x FF l (w:real^3)`;
                 `(cc:real^3->(real^3->bool)->bool) u`; `z:real^3`; `min r0 rs`]
    MOI_S3XT_TWO_SIDES) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[REAL_LT_MIN] THEN REPEAT CONJ_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `!y:real^3. {y} IN (cc:real^3->(real^3->bool)->bool) u ==> y IN V0` THEN
      DISCH_THEN(MP_TAC o SPEC `z:real^3`) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`z:real^3`; `min r0 rs`; `rs:real`] SUBSET_BALL) THEN
      ANTS_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
      UNDISCH_TAC `ball(z:real^3,rs) INTER moi_s3xt_S c x FF l u =
                   ball(z,rs) INTER moi_s3xt_S c x FF l w` THEN
      SET_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (X_CHOOSE_THEN `U1:real^3->bool`
    (X_CHOOSE_THEN `U2:real^3->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `ball(z:real^3,r) SUBSET ball(z,rs) /\ r <= r0` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [MATCH_MP_TAC SUBSET_BALL; ALL_TAC] THEN
    UNDISCH_TAC `r <= min r0 rs` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(z:real^3,r) DIFF moi_s3xt_E l e = U1 UNION U2` ASSUME_TAC THENL
   [UNDISCH_TAC `U1 UNION U2 = ball(z:real^3,r) DIFF moi_s3xt_S c x FF l u` THEN
    UNDISCH_TAC `ball(z:real^3,rs) INTER moi_s3xt_E l e =
                 ball(z,rs) INTER moi_s3xt_S c x FF l u` THEN
    UNDISCH_TAC `ball(z:real^3,r) SUBSET ball(z,rs)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U1:real^3->bool) SUBSET (c:real^3->real^3->bool) u \/ U1 SUBSET c w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3XT_SIDE_PIECE THEN
    EXISTS_TAC `moi_s3xt_E l (e:(real^3->bool)->real^3->bool)` THEN
    ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`ball(z:real^3,r) DIFF moi_s3xt_E l e = U1 UNION U2`;
        `ball(z:real^3,r) SUBSET ball(z,rs)`;
        `ball(z:real^3,rs) SUBSET (c:real^3->real^3->bool) u UNION c w`] THEN
      SET_TAC[];
      UNDISCH_TAC `ball(z:real^3,r) DIFF moi_s3xt_E l e = U1 UNION U2` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(U2:real^3->bool) SUBSET (c:real^3->real^3->bool) u \/ U2 SUBSET c w`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S3XT_SIDE_PIECE THEN
    EXISTS_TAC `moi_s3xt_E l (e:(real^3->bool)->real^3->bool)` THEN
    ASM_SIMP_TAC[] THEN REPEAT CONJ_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`ball(z:real^3,r) DIFF moi_s3xt_E l e = U1 UNION U2`;
        `ball(z:real^3,r) SUBSET ball(z,rs)`;
        `ball(z:real^3,rs) SUBSET (c:real^3->real^3->bool) u UNION c w`] THEN
      SET_TAC[];
      UNDISCH_TAC `ball(z:real^3,r) DIFF moi_s3xt_E l e = U1 UNION U2` THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `u:real^3`; `w:real^3`] MOI_S3XT_HD_EDGE) THEN
  ANTS_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
    ASM_SIMP_TAC[];
    STRIP_TAC] THEN
  SUBGOAL_THEN `moi_s33_hd t l h e (c:real^3->real^3->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`ball(z:real^3,r)`; `U1:real^3->bool`; `U2:real^3->bool`;
                 `(c:real^3->real^3->bool) u`; `(c:real^3->real^3->bool) w`;
                 `connected_component
                    (IMAGE (h:real^3->real^3) (derived_nbhd t l) DIFF moi_s3xt_E l e) (h u)`;
                 `connected_component
                    (IMAGE (h:real^3->real^3) (derived_nbhd t l) DIFF moi_s3xt_E l e) (h w)`;
                 `moi_s3xt_E l (e:(real^3->bool)->real^3->bool)`; `z:real^3`]
    MOI_S3XT_TWO_PIECES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[OPEN_BALL; CENTRE_IN_BALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S3XT_HD_PIECE THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S3XT_HD_PIECE THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`IMAGE (h:real^3->real^3) (derived_nbhd t l) DIFF moi_s3xt_E l e`;
                     `(h:real^3->real^3) u`] CONNECTED_COMPONENT_SUBSET) THEN
      SET_TAC[];
      MP_TAC(ISPECL [`IMAGE (h:real^3->real^3) (derived_nbhd t l) DIFF moi_s3xt_E l e`;
                     `(h:real^3->real^3) w`] CONNECTED_COMPONENT_SUBSET) THEN
      SET_TAC[];
      UNDISCH_TAC `(z:real^3) IN e(segment[u:real^3,w])` THEN
      UNDISCH_TAC `e(segment[u:real^3,w]) SUBSET (c:real^3->real^3->bool) u` THEN SET_TAC[];
      UNDISCH_TAC `(z:real^3) IN e(segment[u:real^3,w])` THEN
      UNDISCH_TAC `e(segment[u:real^3,w]) SUBSET (c:real^3->real^3->bool) w` THEN SET_TAC[];
      REWRITE_TAC[moi_s3xt_E] THEN
      MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN s ==> a SUBSET UNIONS s`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `segment[u:real^3,w]` THEN
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT]];
    ALL_TAC] THEN
  DISCH_TAC THEN EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`ball(z:real^3,r) SUBSET ball(z,rs)`;
      `ball(z:real^3,rs) SUBSET interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0`] THEN
    SET_TAC[];
    UNDISCH_TAC `~(U1:real^3->bool = {})` THEN
    UNDISCH_TAC `ball(z:real^3,r) DIFF moi_s3xt_E l e = U1 UNION U2` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(c:real^3->real^3->bool) u INTER c w SUBSET moi_s3xt_E l e /\
                DISJOINT (inside(moi_s3xt_S c x FF l u)) (inside(moi_s3xt_S c x FF l w))`
  STRIP_ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th ->
    is_disj(concl th) &&
    can (find_term (fun t -> t = `U2:real^3->bool`)) (concl th) &&
    can (find_term (fun t -> t = `U1:real^3->bool`)) (concl th))) THENL
   [DISJ1_TAC THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN U1 \/ y IN U2` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC; ALL_TAC] THEN
    REWRITE_TAC[moi_s3xt_ag] THENL
     [EXISTS_TAC `u:real^3`; EXISTS_TAC `w:real^3`] THEN ASM SET_TAC[];
    DISJ2_TAC THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    REWRITE_TAC[moi_s3xt_ag; NOT_EXISTS_THM] THEN X_GEN_TAC `a:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN U1 \/ y IN U2` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC; ALL_TAC] THENL
     [ASM_CASES_TAC `a:real^3 = u` THENL
       [UNDISCH_TAC `(y:real^3) IN (c:real^3->real^3->bool) a` THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN
        MAP_EVERY UNDISCH_TAC
         [`(c:real^3->real^3->bool) u INTER c w SUBSET moi_s3xt_E l e`;
          `(U1:real^3->bool) SUBSET (c:real^3->real^3->bool) w`;
          `(y:real^3) IN U1`; `~((y:real^3) IN moi_s3xt_E l e)`;
          `(y:real^3) IN (c:real^3->real^3->bool) u`] THEN
        SET_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3`; `u:real^3`] o check (fun th ->
          is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
          can (find_term (fun t -> t = `DISJOINT:(real^3->bool)->(real^3->bool)->bool`))
              (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
      ASM_CASES_TAC `a:real^3 = w` THENL
       [UNDISCH_TAC `(y:real^3) IN (c:real^3->real^3->bool) a` THEN ASM_REWRITE_TAC[] THEN
        DISCH_TAC THEN
        MAP_EVERY UNDISCH_TAC
         [`(c:real^3->real^3->bool) u INTER c w SUBSET moi_s3xt_E l e`;
          `(U2:real^3->bool) SUBSET (c:real^3->real^3->bool) u`;
          `(y:real^3) IN U2`; `~((y:real^3) IN moi_s3xt_E l e)`;
          `(y:real^3) IN (c:real^3->real^3->bool) w`] THEN
        SET_TAC[];
        FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3`; `w:real^3`] o check (fun th ->
          is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
          can (find_term (fun t -> t = `DISJOINT:(real^3->bool)->(real^3->bool)->bool`))
              (concl th))) THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]]]);;

(* A point of agreement near the free point of a piece.                     *)

let MOI_S3XT_LAB_SEED = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi (V0:real^3->bool) v.
     PL_SCHOENFLIES_3_STATEMENT /\ moi_s3xt_ctx t l h e c x g g' FF rho /\
     moi_s3xt_maps t l g FF phi Psi /\ FINITE V0 /\ {v} IN l
     ==> ?z. z IN interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0 /\
             ~(z IN moi_s3xt_E l e) /\ moi_s3xt_ag l c x FF z /\
             z IN inside(moi_s3xt_S c x FF l v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_LAB_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {w:real^3 | {w} IN l}` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(MATCH_MP MOI_S3XT_TUBE_GRAPH (ASSUME `moi_s33_tube t l (h:real^3->real^3)`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`; `v:real^3`]
    MOI_S3XT_TGT_FREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN frontier (UNIONS x) /\ y IN (c:real^3->real^3->bool) v`
  STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((y:real^3) IN moi_s3xt_E l e)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3xt_E; IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `t0:real^3->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC)
                               ASSUME_TAC) THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_EDGE_VERTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                     `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                     `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                     `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(MATCH_MP MOI_S3XT_TUBE_GRAPH (ASSUME `moi_s33_tube t l (h:real^3->real^3)`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `a:real^3`; `b:real^3`]
      MOI_S3XT_CTX_EDGE) THEN
    SUBGOAL_THEN `segment[a:real^3,b] IN l` ASSUME_TAC THENL
     [UNDISCH_TAC `(s:real^3->bool) IN l` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `(y:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[a,b])`
    ASSUME_TAC THENL
     [UNDISCH_TAC `(y:real^3) IN t0` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `!a b. ~(a = b) /\ segment[a,b] IN l
                       ==> ~((y:real^3) IN (FF:real^3->real^3->real^3->bool) a b)` THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^3`; `b:real^3`]) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(FF:real^3->real^3->real^3->bool) a b INTER frontier (UNIONS x) =
       e(segment[a,b]) INTER frontier (UNIONS x)`;
      `(y:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[a,b])`;
      `(y:real^3) IN frontier (UNIONS x)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Q = moi_s3xt_R h l rho UNION moi_s3xt_E l e UNION
                  UNIONS {(c:real^3->real^3->bool) w | w | {w} IN l /\ ~(w = v)}` THEN
  SUBGOAL_THEN `closed (Q:real^3->bool) /\ ~((y:real^3) IN Q)` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Q" THEN CONJ_TAC THENL
     [REPEAT(MATCH_MP_TAC CLOSED_UNION THEN CONJ_TAC) THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CLOSED_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN
      ASM_SIMP_TAC[] THEN ONCE_REWRITE_TAC[SIMPLE_IMAGE_GEN] THEN
      MATCH_MP_TAC FINITE_IMAGE THEN MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `{w:real^3 | {w} IN l}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MAP_EVERY UNDISCH_TAC
         [`moi_s3xt_R h l rho SUBSET interior (UNIONS x)`;
          `(y:real^3) IN frontier (UNIONS x)`] THEN
        REWRITE_TAC[frontier] THEN SET_TAC[];
        REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM; NOT_EXISTS_THM] THEN
        X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
        UNDISCH_TAC `!w. {w} IN l /\ ~(w = v)
                         ==> ~((y:real^3) IN (c:real^3->real^3->bool) w INTER
                                            frontier (UNIONS x))` THEN
        DISCH_THEN(MP_TAC o SPEC `w:real^3`) THEN ASM_REWRITE_TAC[IN_INTER]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r. &0 < r /\ ball(y:real^3,r) INTER Q = {}` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `closed (Q:real^3->bool)` THEN REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[IN_DIFF; IN_UNIV] THEN
    MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN moi_s3xt_S c x FF l v` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3xt_S; MOI_S3XT_SPH_EQ] THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `open (ball(y:real^3,r) INTER inside(moi_s3xt_S c x FF l v)) /\
                ~(ball(y:real^3,r) INTER inside(moi_s3xt_S c x FF l v) = {})`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN ASM_SIMP_TAC[OPEN_BALL];
      MP_TAC(ISPECL [`moi_s3xt_S c x FF l (v:real^3)`; `y:real^3`; `r:real`]
        MOI_S3XT_SPHERE_BALL_MEETS) THEN
      ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `ball(y:real^3,r) INTER inside(moi_s3xt_S c x FF l v)` OPEN_IMP_INFINITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`ball(y:real^3,r) INTER inside(moi_s3xt_S c x FF l v)`; `V0:real^3->bool`]
    INFINITE_DIFF_FINITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `z:real^3` THEN
  SUBGOAL_THEN `~((z:real^3) IN Q) /\ z IN interior (UNIONS x)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ASM SET_TAC[]]; ALL_TAC] THEN
  UNDISCH_TAC `~((z:real^3) IN Q)` THEN EXPAND_TAC "Q" THEN
  REWRITE_TAC[IN_UNION; DE_MORGAN_THM] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[IN_DIFF] THEN REWRITE_TAC[moi_s3xt_ag] THEN
  EXISTS_TAC `v:real^3` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `?a:real^3. {a} IN l /\ z IN (c:real^3->real^3->bool) a`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `UNIONS x:real^3->bool` INTERIOR_SUBSET) THEN
    UNDISCH_TAC `UNIONS x SUBSET UNIONS {(c:real^3->real^3->bool) a | a | {a} IN l}` THEN
    UNDISCH_TAC `(z:real^3) IN interior (UNIONS x)` THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `a:real^3 = v` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~((z:real^3) IN
                 UNIONS {(c:real^3->real^3->bool) w | w | {w} IN l /\ ~(w = v)})` THEN
  MATCH_MP_TAC(TAUT `q ==> ~q ==> p`) THEN
  REWRITE_TAC[UNIONS_GSPEC; IN_ELIM_THM] THEN EXISTS_TAC `a:real^3` THEN
  ASM_REWRITE_TAC[]);;

(* The labels agree everywhere off the walls (LABEL_ABS).                    *)

let MOI_S3XT_LAB_AGREE = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi (cc:real^3->(real^3->bool)->bool)
    (V0:real^3->bool).
     PL_SCHOENFLIES_3_STATEMENT /\ moi_s3xt_ctx t l h e c x g g' FF rho /\
     moi_s3xt_maps t l g FF phi Psi /\ FINITE V0 /\
     (!v. {v} IN l
          ==> simplicial_complex (cc v) /\ (!k. k IN cc v ==> aff_dim k <= &2) /\
              combinatorial_manifold 2 (cc v) /\ UNIONS (cc v) = moi_s3xt_S c x FF l v /\
              (!y. {y} IN cc v ==> y IN V0))
     ==> !z. z IN interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0 /\
             ~(z IN moi_s3xt_E l e)
             ==> moi_s3xt_ag l c x FF z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_LAB_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_RBALLS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `connected (interior (UNIONS x:real^3->bool))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`;
                   `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
      MOI_S3XT_CFG_INST) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP MOI_S3XT_CFG_G) THEN SIMP_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3XT_LABEL_ABS THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[FINITE_IMP_CLOSED] THEN
    MATCH_MP_TAC OPEN_DIFF THEN ASM_REWRITE_TAC[OPEN_INTERIOR];
    MATCH_MP_TAC CONNECTED_OPEN_DIFF_COUNTABLE THEN
    ASM_SIMP_TAC[FINITE_IMP_COUNTABLE; DIMINDEX_3; ARITH] THEN
    MP_TAC(ISPECL [`{(h:real^3->real^3)(midpoint(u,v)) | u,v | ~(u = v) /\ segment[u,v] IN l}`;
                   `rho / &2`; `interior (UNIONS x:real^3->bool)`]
      MOI_S3XT_CONN_DIFF_CBALLS) THEN
    ASM_REWRITE_TAC[OPEN_INTERIOR; moi_s3xt_R];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3XT_LAB_NW THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `g:real^3->real^3`;
                          `g':real^3->real^3`; `phi:real^3->real^3->real^3->real^3`;
                          `Psi:real^3->real^3`] THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3XT_LAB_WALL THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `g:real^3->real^3`;
                          `g':real^3->real^3`; `phi:real^3->real^3->real^3->real^3`;
                          `Psi:real^3->real^3`; `cc:real^3->(real^3->bool)->bool`] THEN
    ASM_REWRITE_TAC[];
    MP_TAC(MATCH_MP MOI_S3XT_TUBE_GRAPH (ASSUME `moi_s33_tube t l (h:real^3->real^3)`)) THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 (K ALL_TAC)
        (CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) (K ALL_TAC)))))))) THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^3` (X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`;
                   `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`;
                   `V0:real^3->bool`; `p:real^3`] MOI_S3XT_LAB_SEED) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

let MOI_S3XT_LAB_SETUP = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi.
     PL_SCHOENFLIES_3_STATEMENT /\ moi_s3xt_ctx t l h e c x g g' FF rho /\
     moi_s3xt_maps t l g FF phi Psi
     ==> ?V0:real^3->bool.
           FINITE V0 /\
           !z. z IN interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0 /\
               ~(z IN moi_s3xt_E l e)
               ==> moi_s3xt_ag l c x FF z`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_CFG_INST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{v:real^3 | {v} IN l}`; `\u v:real^3. ~(u = v) /\ segment[u,v] IN l`;
                 `\v:real^3. (c:real^3->real^3->bool) v INTER frontier (UNIONS x)`;
                 `FF:real^3->real^3->real^3->bool`; `UNIONS x:real^3->bool`]
    MOI_S3XT_VTX) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM; GSYM moi_s3xt_S] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:real^3->(real^3->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `{y:real^3 | ?v. {v} IN l /\
                             {y} IN (cc:real^3->(real^3->bool)->bool) v}` THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_S3XT_LAB_AGREE THEN
  MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                        `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`;
                        `cc:real^3->(real^3->bool)->bool`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]);;

(* The ball of v misses the rho / 2 balls of the edges not at v: otherwise  *)
(* the connected inside of S_v would cross the annulus around the centre,   *)
(* where the labels say it lies in a piece of an end of that edge.           *)

let MOI_S3XT_ANNULUS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi (V0:real^3->bool) v a b.
     PL_SCHOENFLIES_3_STATEMENT /\ moi_s3xt_ctx t l h e c x g g' FF rho /\
     moi_s3xt_maps t l g FF phi Psi /\ FINITE V0 /\
     (!z. z IN interior (UNIONS x) DIFF moi_s3xt_R h l rho DIFF V0 /\
          ~(z IN moi_s3xt_E l e)
          ==> moi_s3xt_ag l c x FF z) /\
     {v} IN l /\ ~(a = b) /\ segment[a,b] IN l /\ ~(v = a) /\ ~(v = b)
     ==> DISJOINT (inside(moi_s3xt_S c x FF l v)) (cball(h(midpoint(a,b)),rho / &2))`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "ag") STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_LAB_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`; `a:real^3`; `b:real^3`]
    MOI_S3XT_CTX_EDGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_CFG_INST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `DISJOINT (inside(moi_s3xt_S c x FF l v))
                         ((FF:real^3->real^3->real^3->bool) a b)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3xt_S] THEN MATCH_MP_TAC MOI_S3XT_INT_MISS THEN
    MAP_EVERY EXISTS_TAC [`{v:real^3 | {v} IN l}`; `UNIONS x:real^3->bool`] THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (inside(moi_s3xt_S c x FF l v))` ASSUME_TAC THENL
   [MP_TAC(ISPEC `moi_s3xt_S c x FF l v` MOI_S3XT_SPHERE_FACTS) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`; `v:real^3`]
    MOI_S3XT_TGT_FREE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `p = (h:real^3->real^3)(midpoint(a,b))` THEN
  ABBREV_TAC `Iv = inside(moi_s3xt_S c x FF l v)` THEN
  SUBGOAL_THEN `open (Iv:real^3->bool) /\ Iv SUBSET interior (UNIONS x) /\
                pl_sphere 2 (moi_s3xt_S c x FF l v)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "Iv" THEN ASM_SIMP_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
  X_GEN_TAC `z:real^3` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?q:real^3. q IN Iv /\ ~(q IN ball(p,rho))` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(y:real^3) IN moi_s3xt_S c x FF l v` ASSUME_TAC THENL
     [REWRITE_TAC[moi_s3xt_S; MOI_S3XT_SPH_EQ] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`moi_s3xt_S c x FF l (v:real^3)`; `y:real^3`; `rho:real`]
      MOI_S3XT_SPHERE_BALL_MEETS) THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_BALL] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3` STRIP_ASSUME_TAC o CONJUNCT1) THEN
    EXISTS_TAC `q:real^3` THEN ASM_REWRITE_TAC[IN_BALL] THEN
    SUBGOAL_THEN `~(dist(p:real^3,y) < &2 * rho)` MP_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^3) IN interior (UNIONS x)` MP_TAC THENL
       [UNDISCH_TAC `ball(p:real^3,&2 * rho) SUBSET interior (UNIONS x)` THEN
        REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(y:real^3) IN (c:real^3->real^3->bool) v INTER frontier (UNIONS x)` THEN
        REWRITE_TAC[frontier] THEN SET_TAC[]];
      UNDISCH_TAC `dist(y:real^3,q) < rho` THEN CONV_TAC NORM_ARITH];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((Iv:real^3->bool) INTER (ball(p,rho) DIFF cball(p,rho / &2)) = {})`
  ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `connected (Iv:real^3->bool)` THEN
    REWRITE_TAC[CONNECTED_CLOSED] THEN
    MAP_EVERY EXISTS_TAC [`cball(p:real^3,rho / &2)`; `(:real^3) DIFF ball(p,rho)`] THEN
    REWRITE_TAC[CLOSED_CBALL] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_DIFF THEN REWRITE_TAC[CLOSED_UNIV; OPEN_BALL];
      UNDISCH_TAC `(Iv:real^3->bool) INTER (ball(p,rho) DIFF cball(p,rho / &2)) = {}` THEN
      SET_TAC[];
      REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_UNIV; IN_CBALL; IN_BALL; NOT_IN_EMPTY] THEN
      X_GEN_TAC `q':real^3` THEN MATCH_MP_TAC(TAUT `~(p /\ q) ==> ~(p /\ q /\ r)`) THEN
      UNDISCH_TAC `&0 < rho` THEN REAL_ARITH_TAC;
      ASM SET_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z1:real^3. z1 IN Iv /\ z1 IN ball(p,rho) /\ ~(z1 IN cball(p,rho / &2)) /\
                            ~(z1 IN V0)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `open ((Iv:real^3->bool) INTER (ball(p,rho) DIFF cball(p,rho / &2)))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC OPEN_DIFF THEN REWRITE_TAC[OPEN_BALL; CLOSED_CBALL];
      ALL_TAC] THEN
    MP_TAC(ISPEC `(Iv:real^3->bool) INTER (ball(p,rho) DIFF cball(p,rho / &2))`
      OPEN_IMP_INFINITE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`(Iv:real^3->bool) INTER (ball(p,rho) DIFF cball(p,rho / &2))`;
                   `V0:real^3->bool`] INFINITE_DIFF_FINITE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF; IN_INTER] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `ball(p:real^3,rho) SUBSET ball(p,&2 * rho)` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_BALL THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `~((z1:real^3) IN moi_s3xt_R h l rho)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3xt_R; IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `cb:real^3->bool` THEN
    REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    DISCH_THEN(X_CHOOSE_THEN `p':real^3` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `w':real^3` STRIP_ASSUME_TAC))
      SUBST1_TAC)) THEN
    ASM_CASES_TAC `segment[u':real^3,w'] = segment[a,b]` THENL
     [SUBGOAL_THEN `p':real^3 = p` SUBST1_TAC THENL
       [UNDISCH_TAC `p' = (h:real^3->real^3)(midpoint(u',w'))` THEN
        DISCH_THEN SUBST1_TAC THEN EXPAND_TAC "p" THEN AP_TERM_TAC THEN
        UNDISCH_TAC `segment[u':real^3,w'] = segment[a,b]` THEN
        REWRITE_TAC[SEGMENT_EQ; EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
        DISCH_THEN(fun th -> MP_TAC(SPEC `u':real^3` th) THEN MP_TAC(SPEC `w':real^3` th) THEN
                             MP_TAC(SPEC `a:real^3` th)) THEN
        UNDISCH_TAC `~(u':real^3 = w')` THEN UNDISCH_TAC `~(a:real^3 = b)` THEN
        REWRITE_TAC[] THEN
        MESON_TAC[MIDPOINT_SYM];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `!u' v'. ~(u' = v') /\ segment[u',v'] IN l /\
                         ~(segment[u',v'] = segment[a,b])
                         ==> ball(p:real^3,&2 * rho) INTER
                             (e:(real^3->bool)->real^3->bool)(segment[u',v']) = {} /\
                             &3 * rho <= dist(p,(h:real^3->real^3)(midpoint(u',v')))` THEN
    DISCH_THEN(MP_TAC o SPECL [`u':real^3`; `w':real^3`]) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN REWRITE_TAC[IN_CBALL] THEN
    UNDISCH_TAC `(z1:real^3) IN ball(p,rho)` THEN REWRITE_TAC[IN_BALL] THEN
    UNDISCH_TAC `&3 * rho <= dist(p:real^3,(h:real^3->real^3)(midpoint(u',w')))` THEN
    UNDISCH_TAC `&0 < rho` THEN UNDISCH_TAC `p' = (h:real^3->real^3)(midpoint(u',w'))` THEN
    DISCH_THEN SUBST1_TAC THEN CONV_TAC NORM_ARITH;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((z1:real^3) IN moi_s3xt_E l e)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3xt_E; IN_UNIONS; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `t0:real^3->bool` THEN
    REWRITE_TAC[TAUT `~(p /\ q) <=> p ==> ~q`] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_EDGE_VERTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(MATCH_MP MOI_S3XT_TUBE_GRAPH (ASSUME `moi_s33_tube t l (h:real^3->real^3)`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u':real^3` (X_CHOOSE_THEN `w':real^3` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `s = segment[u':real^3,w']` THEN DISCH_THEN SUBST_ALL_TAC THEN
    ASM_CASES_TAC `segment[u':real^3,w'] = segment[a,b]` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z1:real^3) IN (FF:real^3->real^3->real^3->bool) a b` MP_TAC THENL
       [UNDISCH_TAC `(e(segment[a:real^3,b]) INTER UNIONS x) DIFF ball(p,rho / &2)
                     SUBSET (FF:real^3->real^3->real^3->bool) a b` THEN
        MP_TAC(ISPEC `UNIONS x:real^3->bool` INTERIOR_SUBSET) THEN
        MP_TAC(ISPECL [`p:real^3`; `rho / &2`] BALL_SUBSET_CBALL) THEN
        MAP_EVERY UNDISCH_TAC
         [`(z1:real^3) IN (e:(real^3->bool)->real^3->bool)(segment[a,b])`;
          `~((z1:real^3) IN cball(p,rho / &2))`; `(z1:real^3) IN Iv`;
          `(Iv:real^3->bool) SUBSET interior (UNIONS x)`] THEN
        SET_TAC[];
        UNDISCH_TAC `DISJOINT (Iv:real^3->bool) ((FF:real^3->real^3->real^3->bool) a b)` THEN
        UNDISCH_TAC `(z1:real^3) IN Iv` THEN SET_TAC[]];
      UNDISCH_TAC `!u' v'. ~(u' = v') /\ segment[u',v'] IN l /\
                           ~(segment[u',v'] = segment[a,b])
                           ==> ball(p:real^3,&2 * rho) INTER
                               (e:(real^3->bool)->real^3->bool)(segment[u',v']) = {} /\
                               &3 * rho <= dist(p,(h:real^3->real^3)(midpoint(u',v')))` THEN
      DISCH_THEN(MP_TAC o SPECL [`u':real^3`; `w':real^3`]) THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY UNDISCH_TAC
       [`(z1:real^3) IN ball(p,rho)`; `ball(p:real^3,rho) SUBSET ball(p,&2 * rho)`] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "ag" (MP_TAC o SPEC `z1:real^3`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_DIFF] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_s3xt_ag] THEN
  DISCH_THEN(X_CHOOSE_THEN `a':real^3` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `a':real^3 = v` THENL
   [UNDISCH_TAC `(z1:real^3) IN (c:real^3->real^3->bool) a'` THEN ASM_REWRITE_TAC[] THEN
    DISCH_TAC THEN
    UNDISCH_TAC `!w. {w} IN l /\ ~(w = a) /\ ~(w = b)
                     ==> ball(p:real^3,&2 * rho) INTER (c:real^3->real^3->bool) w = {}` THEN
    DISCH_THEN(MP_TAC o SPEC `v:real^3`) THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(z1:real^3) IN ball(p,rho)`; `ball(p:real^3,rho) SUBSET ball(p,&2 * rho)`;
      `(z1:real^3) IN (c:real^3->real^3->bool) v`] THEN
    SET_TAC[];
    FIRST_X_ASSUM(MP_TAC o SPECL [`a':real^3`; `v:real^3`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `DISJOINT:(real^3->bool)->(real^3->bool)->bool`))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN
    MAP_EVERY UNDISCH_TAC
     [`(z1:real^3) IN Iv`; `(z1:real^3) IN inside(moi_s3xt_S c x FF l a')`] THEN
    SET_TAC[]]);;

(* The labels: the ball B_v lies in the piece c v up to the d-balls at the  *)
(* centres of the edges at v.                                                 *)

let MOI_S3XT_LABELS = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) g' FF rho phi Psi d v.
     PL_SCHOENFLIES_3_STATEMENT /\ moi_s3xt_ctx t l h e c x g g' FF rho /\
     moi_s3xt_maps t l g FF phi Psi /\ &2 * rho < d /\ {v} IN l
     ==> moi_s3xt_S c x FF l v UNION inside(moi_s3xt_S c x FF l v) SUBSET
         c v UNION UNIONS {ball(h(midpoint(v,w)),d) | w | ~(w = v) /\ segment[v,w] IN l}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_LAB_SETUP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `V0:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ag"))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_LAB_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_CTX_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_CFG_INST) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `Bs = UNIONS {ball((h:real^3->real^3)(midpoint(v,w)),d) | w |
                           ~(w = v) /\ segment[v,w] IN l}` THEN
  SUBGOAL_THEN
   `!w. ~(w = v) /\ segment[v,w] IN l
        ==> cball((h:real^3->real^3)(midpoint(v,w)),rho / &2) SUBSET Bs`
  ASSUME_TAC THENL
   [X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN EXPAND_TAC "Bs" THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `ball((h:real^3->real^3)(midpoint(v,w)),d)` THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_CBALL; IN_BALL] THEN
      UNDISCH_TAC `&2 * rho < d` THEN UNDISCH_TAC `&0 < rho` THEN REAL_ARITH_TAC;
      MATCH_MP_TAC(SET_RULE `(a:real^3->bool) IN s ==> a SUBSET UNIONS s`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `w:real^3` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y. y IN inside(moi_s3xt_S c x FF l v) /\ ~(y IN moi_s3xt_R h l rho) /\
        ~(y IN moi_s3xt_E l e) /\ ~(y IN V0)
        ==> y IN (c:real^3->real^3->bool) v`
  (LABEL_TAC "inc") THENL
   [X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
    USE_THEN "ag" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[IN_DIFF] THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[moi_s3xt_ag] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `a:real^3 = v` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^3`; `v:real^3`] o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 2 &&
      can (find_term (fun t -> t = `DISJOINT:(real^3->bool)->(real^3->bool)->bool`))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_s3xt_S; MOI_S3XT_SPH_EQ; UNION_SUBSET; UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    X_GEN_TAC `w:real^3` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `v:real^3`; `w:real^3`]
      MOI_S3XT_CTX_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `v:real^3`; `w:real^3`] MOI_S3XT_HD_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^3` o check (fun th ->
      is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
      can (find_term (fun t -> t = `Bs:real^3->bool`)) (concl th))) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`(h:real^3->real^3)(midpoint(v,w))`; `rho / &2`] BALL_SUBSET_CBALL) THEN
    MAP_EVERY UNDISCH_TAC
     [`(FF:real^3->real^3->real^3->bool) v w SUBSET
       e(segment[v,w]) UNION ball((h:real^3->real^3)(midpoint(v,w)),rho / &2)`;
      `e(segment[v:real^3,w]) SUBSET (c:real^3->real^3->bool) v`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNION] THEN X_GEN_TAC `z:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(z:real^3) IN moi_s3xt_R h l rho` THENL
   [SUBGOAL_THEN `?a b. ~(a = b) /\ segment[a,b] IN l /\
                        (z:real^3) IN cball((h:real^3->real^3)(midpoint(a,b)),rho / &2)`
    (X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THENL
     [UNDISCH_TAC `(z:real^3) IN moi_s3xt_R h l rho` THEN
      REWRITE_TAC[moi_s3xt_R; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISJ2_TAC THEN
    ASM_CASES_TAC `v:real^3 = a` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `b:real^3` o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> t = `Bs:real^3->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `v:real^3 = b` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `a:real^3` o check (fun th ->
        is_forall(concl th) && length(fst(strip_forall(concl th))) = 1 &&
        can (find_term (fun t -> t = `Bs:real^3->bool`)) (concl th))) THEN
      ONCE_REWRITE_TAC[CONJUNCT1 SEGMENT_SYM; MIDPOINT_SYM] THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`;
                   `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`;
                   `V0:real^3->bool`; `v:real^3`; `a:real^3`; `b:real^3`] MOI_S3XT_ANNULUS) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(z:real^3) IN inside(moi_s3xt_S c x FF l v)` THEN
    UNDISCH_TAC `(z:real^3) IN cball((h:real^3->real^3)(midpoint(a,b)),rho / &2)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(z:real^3) IN moi_s3xt_E l e` THENL
   [UNDISCH_TAC `(z:real^3) IN moi_s3xt_E l e` THEN
    REWRITE_TAC[moi_s3xt_E; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t0:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^3->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`l:(real^3->bool)->bool`; `s:real^3->bool`] MOI_FSA_EDGE_VERTS) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(MATCH_MP MOI_S3XT_TUBE_GRAPH (ASSUME `moi_s33_tube t l (h:real^3->real^3)`)) THEN
      SIMP_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^3` (X_CHOOSE_THEN `b:real^3` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `s = segment[a:real^3,b]` THEN DISCH_THEN SUBST_ALL_TAC THEN
    MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                   `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                   `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                   `FF:real^3->real^3->real^3->bool`; `rho:real`; `a:real^3`; `b:real^3`]
      MOI_S3XT_CTX_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `DISJOINT (inside(moi_s3xt_S c x FF l v))
                           ((FF:real^3->real^3->real^3->bool) a b)` MP_TAC THENL
     [REWRITE_TAC[moi_s3xt_S] THEN MATCH_MP_TAC MOI_S3XT_INT_MISS THEN
      MAP_EVERY EXISTS_TAC [`{v:real^3 | {v} IN l}`; `UNIONS x:real^3->bool`] THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((z:real^3) IN cball((h:real^3->real^3)(midpoint(a,b)),rho / &2))`
    ASSUME_TAC THENL
     [UNDISCH_TAC `~((z:real^3) IN moi_s3xt_R h l rho)` THEN
      REWRITE_TAC[moi_s3xt_R; IN_UNIONS; IN_ELIM_THM; CONTRAPOS_THM] THEN DISCH_TAC THEN
      EXISTS_TAC `cball((h:real^3->real^3)(midpoint(a,b)),rho / &2)` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `(h:real^3->real^3)(midpoint(a,b))` THEN
      REWRITE_TAC[] THEN MAP_EVERY EXISTS_TAC [`a:real^3`; `b:real^3`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `inside(moi_s3xt_S c x FF l v) SUBSET interior (UNIONS x)` ASSUME_TAC THENL
     [ASM_SIMP_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `UNIONS x:real^3->bool` INTERIOR_SUBSET) THEN
    MP_TAC(ISPECL [`(h:real^3->real^3)(midpoint(a,b))`; `rho / &2`] BALL_SUBSET_CBALL) THEN
    MAP_EVERY UNDISCH_TAC
     [`(e(segment[a:real^3,b]) INTER UNIONS x) DIFF
       ball((h:real^3->real^3)(midpoint(a,b)),rho / &2) SUBSET
       (FF:real^3->real^3->real^3->bool) a b`;
      `(z:real^3) IN t0`; `t0 = (e:(real^3->bool)->real^3->bool)(segment[a,b])`;
      `(z:real^3) IN inside(moi_s3xt_S c x FF l v)`;
      `inside(moi_s3xt_S c x FF l v) SUBSET interior (UNIONS x)`;
      `~((z:real^3) IN cball((h:real^3->real^3)(midpoint(a,b)),rho / &2))`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  DISJ1_TAC THEN
  ASM_CASES_TAC `(z:real^3) IN V0` THENL
   [ALL_TAC; USE_THEN "inc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]] THEN
  MP_TAC(ISPECL [`z:real^3`; `(c:real^3->real^3->bool) v`] CLOSED_APPROACHABLE) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  X_GEN_TAC `r:real` THEN DISCH_TAC THEN
  ABBREV_TAC `U = (inside(moi_s3xt_S c x FF l v) INTER ball(z:real^3,r)) DIFF
                  (moi_s3xt_R h l rho UNION moi_s3xt_E l e)` THEN
  SUBGOAL_THEN `open (U:real^3->bool) /\ (z:real^3) IN U` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U" THEN CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_DIFF THEN ASM_SIMP_TAC[CLOSED_UNION] THEN
      MATCH_MP_TAC OPEN_INTER THEN ASM_SIMP_TAC[OPEN_BALL];
      ASM_REWRITE_TAC[IN_DIFF; IN_INTER; IN_UNION; CENTRE_IN_BALL]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `U:real^3->bool` OPEN_IMP_INFINITE) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(U:real^3->bool = {})` (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `(z:real^3) IN U` THEN SET_TAC[]; DISCH_TAC] THEN
  MP_TAC(ISPECL [`U:real^3->bool`; `V0:real^3->bool`] INFINITE_DIFF_FINITE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o MATCH_MP INFINITE_NONEMPTY) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `y:real^3` THEN
  UNDISCH_TAC `(y:real^3) IN U` THEN EXPAND_TAC "U" THEN
  REWRITE_TAC[IN_DIFF; IN_INTER; IN_UNION; DE_MORGAN_THM; IN_BALL] THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [USE_THEN "inc" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Part 13: assembly.  MAIN: the extension f for the data of 33.1           *)
(* (radius, disks FF, sphere maps, balls, gluing, cover, labels); then the  *)
(* headline S33_EXT : |- MOI_S33_EXT from the five antecedents.             *)
(* ========================================================================= *)

let MOI_S3XT_MAIN = prove
 (`!(t:(real^3->bool)->bool) l (h:real^3->real^3) e c (x:(real^3->bool)->bool)
    (g:real^3->real^3) d.
     MOISE_324_STATEMENT /\ PL_SCHOENFLIES_3_STATEMENT /\
     (!d j:real^3->bool. pl_polyhedron d /\ disk_with_boundary d j /\ pl_sphere 1 j
                         ==> pl_cell_with_boundary 2 d j) /\
     (!u v w. {u} IN l /\ {v} IN l /\ {w} IN l /\ ~(u = v) /\ ~(u = w) /\ ~(v = w)
              ==> derived_dual_cell t l u INTER derived_dual_cell t l v INTER
                  derived_dual_cell t l w = {}) /\
     compact (derived_nbhd t l) /\ derived_nbhd t l SUBSET UNIONS t /\
     moi_s33_hd t l h e c /\ moi_s33_inv t l h e x /\ moi_s33_match t l e c x g /\
     &0 < d
     ==> ?f:real^3->real^3.
           pl_map_on (derived_nbhd t l) f /\
           (!y z. y IN derived_nbhd t l /\ z IN derived_nbhd t l /\ f y = f z ==> y = z) /\
           IMAGE h (UNIONS l) SUBSET interior (IMAGE f (derived_nbhd t l)) /\
           (!v. {v} IN l
                ==> IMAGE f (derived_dual_cell t l v) SUBSET
                    c v UNION UNIONS {ball(h(midpoint(v,w)),d) | w |
                                      ~(w = v) /\ segment[v,w] IN l})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s33_tube t l (h:real^3->real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_hd t l h e (c:real^3->real^3->bool)` THEN SIMP_TAC[moi_s33_hd];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S3XT_TUBE_GRAPH (ASSUME `moi_s33_tube t l (h:real^3->real^3)`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (IMAGE (h:real^3->real^3) (derived_nbhd t l))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN EXISTS_TAC `UNIONS t:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_s33_tube t l (h:real^3->real^3)` THEN SIMP_TAC[moi_s33_tube];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (h:real^3->real^3) (UNIONS l) SUBSET interior (UNIONS x)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_inv t l h e (x:(real^3->bool)->bool)` THEN
    SIMP_TAC[moi_s33_inv; moi_s33_x2];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `UNIONS x:real^3->bool`; `d:real`] MOI_S3XT_RADIUS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `rho:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rad")))) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `rho:real`] MOI_S3XT_FF) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    USE_THEN "rad" (MP_TAC o SPECL [`u:real^3`; `v:real^3`]) THEN ASM_SIMP_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `FF:real^3->real^3->real^3->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `moi_s33_match t l e c x (g:real^3->real^3)` THEN
  REWRITE_TAC[moi_s33_match] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `g':real^3->real^3`) STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s3xt_ctx t l h e c x g g' FF rho` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3xt_ctx] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "rad" ACCEPT_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`] MOI_S3XT_PHI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `phi:real^3->real^3->real^3->real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `g:real^3->real^3`; `phi:real^3->real^3->real^3->real^3`] MOI_S3XT_PSI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `Psi:real^3->real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_s3xt_maps t l g FF phi (Psi:real^3->real^3)` ASSUME_TAC THENL
   [REWRITE_TAC[moi_s3xt_maps] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_BALLS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `fv:real^3->real^3->real^3`) THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`;
                 `fv:real^3->real^3->real^3`] MOI_S3XT_GLUE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->real^3` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `f:real^3->real^3` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`; `h:real^3->real^3`;
                 `e:(real^3->bool)->real^3->bool`; `c:real^3->real^3->bool`;
                 `x:(real^3->bool)->bool`; `g:real^3->real^3`; `g':real^3->real^3`;
                 `FF:real^3->real^3->real^3->bool`; `rho:real`;
                 `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`]
    MOI_S3XT_LAB_BASE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v. {v} IN l
                    ==> IMAGE (f:real^3->real^3) (derived_dual_cell t l v) =
                        moi_s3xt_S c x FF l v UNION inside(moi_s3xt_S c x FF l v)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[moi_s3xt_S]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `interior (UNIONS x:real^3->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC INTERIOR_MAXIMAL THEN REWRITE_TAC[OPEN_INTERIOR] THEN
    SUBGOAL_THEN `derived_nbhd t l =
                  UNIONS {derived_dual_cell t l v | v | {v:real^3} IN l}`
    SUBST1_TAC THENL
     [MP_TAC(ISPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`]
        GRAPH_TUBE_DUAL_CELLS) THEN
      ANTS_TAC THENL
       [UNDISCH_TAC `moi_s33_tube t l (h:real^3->real^3)` THEN SIMP_TAC[moi_s33_tube];
        SIMP_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[IMAGE_UNIONS] THEN
    UNDISCH_TAC `interior (UNIONS x) SUBSET
                 UNIONS {moi_s3xt_S c x FF l a UNION inside(moi_s3xt_S c x FF l a) | a |
                         {a:real^3} IN l}` THEN
    MATCH_MP_TAC(SET_RULE
     `(!y. y IN U1 ==> y IN U2) ==> i SUBSET U1 ==> (i:real^3->bool) SUBSET U2`) THEN
    REWRITE_TAC[IN_UNIONS; IN_IMAGE; IN_ELIM_THM] THEN X_GEN_TAC `y:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^3->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `a:real^3` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `s:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `derived_dual_cell t l (a:real^3)` THEN CONJ_TAC THENL
     [ASM_SIMP_TAC[moi_s3xt_S]; EXISTS_TAC `a:real^3` THEN ASM_REWRITE_TAC[]];
    X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    REWRITE_TAC[GSYM moi_s3xt_S] THEN MATCH_MP_TAC MOI_S3XT_LABELS THEN
    MAP_EVERY EXISTS_TAC [`t:(real^3->bool)->bool`; `e:(real^3->bool)->real^3->bool`;
                          `g:real^3->real^3`; `g':real^3->real^3`; `rho:real`;
                          `phi:real^3->real^3->real^3->real^3`; `Psi:real^3->real^3`] THEN
    ASM_REWRITE_TAC[]]);;

let S33_EXT = prove
 (MOI_S33_EXT,
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "triple") (LABEL_TAC "tf"))))) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s33_tube t l (h:real^3->real^3)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_hd t l h e (c:real^3->real^3->bool)` THEN SIMP_TAC[moi_s33_hd];
    ALL_TAC] THEN
  SUBGOAL_THEN `graph_in_complex t (l:(real^3->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_s33_tube t l (h:real^3->real^3)` THEN SIMP_TAC[moi_s33_tube];
    ALL_TAC] THEN
  USE_THEN "tf" (MP_TAC o C MATCH_MP (ASSUME `moi_s33_tube t l (h:real^3->real^3)`) o
                 SPECL [`t:(real^3->bool)->bool`; `l:(real^3->bool)->bool`;
                        `h:real^3->real^3`]) THEN
  STRIP_TAC THEN
  MATCH_MP_TAC MOI_S3XT_MAIN THEN
  MAP_EVERY EXISTS_TAC [`e:(real^3->bool)->real^3->bool`; `x:(real^3->bool)->bool`;
                        `g:real^3->real^3`] THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT STRIP_TAC THEN USE_THEN "triple" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;

