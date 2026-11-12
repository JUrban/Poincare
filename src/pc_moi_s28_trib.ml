(* ========================================================================= *)
(* pc_moi_s28_trib: triangulated surfaces (Moise GTM 47, pp.37-38 and p.191) *)
(* -- SURF_LOCAL: a finite simplicial complex whose polyhedron has a plane   *)
(* or half-plane chart at every point is a combinatorial 2-manifold with     *)
(* boundary, its boundary is the set of points without plane chart, and it   *)
(* is a combinatorial 2-manifold if the boundary is empty; SURF_INVARIANT:   *)
(* hence a triangulation of a combinatorial surface is combinatorial, with   *)
(* the same boundary (by transport of charts).  Loads pc_moi_s28_tria        *)
(* (SURF_CHARTS and the local analysis at edges).                            *)
(* ========================================================================= *)

needs "src/pc_moi_s28_tria.ml";;
needs "src/pc_moi_smo_cf.ml";;
needs "src/pc_moi_pl1m.ml";;
needs "src/pc_moi_pl2.ml";;
needs "src/pc_moi_sch3_free.ml";;
needs "src/pc_moi_sch3_lev.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Local consequences of charts on a simplicial complex d (every point       *)
(* of the polyhedron has a plane or a half-plane chart): every simplex has  *)
(* dimension at most 2, d is pure (every nonempty simplex lies in a         *)
(* triangle), and every edge lies in one or two triangles.  (Chart versions *)
(* of MOI_SCF_SURF_DIM_LE, _MAXIMAL, _PURE and _EDGE of pc_moi_smo_cf,       *)
(* which assume a 2-sphere.)                                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S8TB_DIM = prove
 (`!d:(real^N->bool)->bool.
     simplicial_complex d /\
     (!y. y IN UNIONS d
          ==> moi_s28_locally_r2 (UNIONS d) y \/ moi_s28_locally_half (UNIONS d) y)
     ==> !s. s IN d ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
  MATCH_MP_TAC MOI_S8TA_EMB2_DIM THEN
  MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `y:real^N`] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]);;

(* No chart at a point with a neighbourhood inside a set of dimension 1.    *)

let MOI_S8TB_LOW_NO = prove
 (`!(x:real^N->bool) y v s.
     (moi_s28_locally_r2 x y \/ moi_s28_locally_half x y) /\
     open_in (subtopology euclidean x) v /\ y IN v /\ v SUBSET s /\
     aff_dim s <= &1
     ==> F`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`x:real^N->bool`; `y:real^N`; `v:real^N->bool`]
    MOI_S8TA_DISK_IN_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `psi:real^2->real^N` (X_CHOOSE_THEN `z:real^2`
    (X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`psi:real^2->real^N`; `ball(z:real^2,r)`; `s:real^N->bool`]
    INVARIANCE_OF_DIMENSION_CONVEX_DOMAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[CONVEX_BALL] THEN
    MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `s:real^N->bool`] HULL_SUBSET) THEN
    ASM SET_TAC[];
    ASM_REWRITE_TAC[AFF_DIM_BALL; DIMINDEX_2] THEN ASM_INT_ARITH_TAC]);;

(* A nonempty maximal simplex has dimension at least 2.                     *)

let MOI_S8TB_MAXIMAL = prove
 (`!d:(real^N->bool)->bool t.
     simplicial_complex d /\
     (!y. y IN UNIONS d
          ==> moi_s28_locally_r2 (UNIONS d) y \/ moi_s28_locally_half (UNIONS d) y) /\
     t IN d /\ ~(t = {}) /\ (!u. u IN d /\ t SUBSET u ==> u = t)
     ==> &2 <= aff_dim t`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(relative_interior t:real^N->bool = {})` MP_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MOI_CON_SC_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  SUBGOAL_THEN `(y:real^N) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  MATCH_MP_TAC(ISPECL
   [`UNIONS d:real^N->bool`; `y:real^N`;
    `{x:real^N | x IN UNIONS d /\ !u. u IN d /\ x IN u ==> t SUBSET u}`;
    `t:real^N->bool`] MOI_S8TB_LOW_NO) THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[];
    ASM_SIMP_TAC[MOI_SCF_SC_OPEN_STAR];
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[]; ASM_MESON_TAC[MOI_SCF_RELINT_SUBSET]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_UNIONS] THEN ASM_MESON_TAC[SUBSET];
    ASM_INT_ARITH_TAC]);;

(* Purity: every nonempty simplex lies in a triangle.                       *)

let MOI_S8TB_PURE = prove
 (`!d:(real^N->bool)->bool s.
     simplicial_complex d /\
     (!y. y IN UNIONS d
          ==> moi_s28_locally_r2 (UNIONS d) y \/ moi_s28_locally_half (UNIONS d) y) /\
     s IN d /\ ~(s = {})
     ==> ?t. t IN d /\ aff_dim t = &2 /\ s SUBSET t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!u:real^N->bool. u IN d ==> aff_dim u <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TB_DIM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN
   `!u:real^N->bool. u IN d /\ s SUBSET u
                     ==> aff_dim u <= &1 /\ &0 <= aff_dim u`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(u:real^N->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(u:real^N->bool) <= &2` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim(u:real^N->bool) = &2)` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `u:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
    MP_TAC(ISPEC `u:real^N->bool` AFF_DIM_GE) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ASM_CASES_TAC `?t:real^N->bool. t IN d /\ aff_dim t = &1 /\ s SUBSET t` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `t:real^N->bool`] MOI_S8TB_MAXIMAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `d:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t:real^N->bool`; `u:real^N->bool`] AFF_DIM_SUBSET) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `s:real^N->bool`] MOI_S8TB_MAXIMAL) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `d:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`s:real^N->bool`; `u:real^N->bool`] AFF_DIM_SUBSET) THEN
      FIRST_ASSUM(MP_TAC o SPEC `u:real^N->bool`) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
      UNDISCH_TAC `~(?t:real^N->bool. t IN d /\ aff_dim t = &1 /\ s SUBSET t)` THEN
      REWRITE_TAC[NOT_EXISTS_THM] THEN
      DISCH_THEN(MP_TAC o SPEC `u:real^N->bool`) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN INT_ARITH_TAC;
      FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool`) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN INT_ARITH_TAC]]);;

(* Every edge lies in one or two triangles.                                  *)

let MOI_S8TB_EDGE_CARD = prove
 (`!d:(real^N->bool)->bool e.
     simplicial_complex d /\
     (!y. y IN UNIONS d
          ==> moi_s28_locally_r2 (UNIONS d) y \/ moi_s28_locally_half (UNIONS d) y) /\
     e IN d /\ aff_dim e = &1
     ==> CARD {t | t IN d /\ aff_dim t = &2 /\ e SUBSET t} = 1 \/
         CARD {t | t IN d /\ aff_dim t = &2 /\ e SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `ts = {t | t IN d /\ aff_dim t = &2 /\ (e:real^N->bool) SUBSET t}` THEN
  SUBGOAL_THEN `FINITE (ts:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_SIMP_TAC[MOI_SCF_SC_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(ts:(real^N->bool)->bool) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN EXPAND_TAC "ts" THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MATCH_MP_TAC MOI_S8TB_PURE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(ts:(real^N->bool)->bool) <= 2` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`3`; `ts:(real^N->bool)->bool`] CHOOSE_SUBSET_STRONG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_SCF_HAS_SIZE_3]) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
      (X_CHOOSE_THEN `t3:real^N->bool` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(t1:real^N->bool) IN ts /\ t2 IN ts /\ t3 IN ts` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "ts" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    SUBGOAL_THEN `~(relative_interior e:real^N->bool = {})` MP_TAC THENL
     [ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; MOI_CON_SC_CONVEX]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `e:real^N->bool`; `t1:real^N->bool`;
                   `t2:real^N->bool`; `t3:real^N->bool`; `y:real^N`]
      MOI_S8TA_EDGE3_NO) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN FIRST_ASSUM MATCH_MP_TAC THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Punctured chart neighbourhoods are connected: a point with a plane or     *)
(* half-plane chart has arbitrarily small open neighbourhoods V with V minus *)
(* the point connected (the image of a punctured disc or of a punctured half *)
(* disc).  It plays the role of MOI_SCF_PUNCTURED_NBHD (2-sphere).           *)
(* ------------------------------------------------------------------------- *)

let MOI_S8TB_HALF_BALL = prove
 (`!r. &0 < r
       ==> convex ({z:real^2 | &0 <= z$2} INTER ball(vec 0,r)) /\
           ~(aff_dim ({z:real^2 | &0 <= z$2} INTER ball(vec 0,r)) = &1)`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC CONVEX_INTER THEN
    REWRITE_TAC[CONVEX_BALL; GSYM real_ge; CONVEX_HALFSPACE_COMPONENT_GE];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{z:real^2 | &0 < z$2} INTER ball(vec 0,r)` AFF_DIM_OPEN) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_INTER THEN
      REWRITE_TAC[OPEN_BALL; GSYM real_gt; OPEN_HALFSPACE_COMPONENT_GT];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `(r / &2) % basis 2:real^2` THEN
      REWRITE_TAC[IN_INTER; IN_ELIM_THM; IN_BALL_0; NORM_MUL;
                  VECTOR_MUL_COMPONENT] THEN
      SIMP_TAC[BASIS_COMPONENT; NORM_BASIS; DIMINDEX_2; ARITH] THEN
      ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  REWRITE_TAC[DIMINDEX_2] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`{z:real^2 | &0 < z$2} INTER ball(vec 0,r)`;
                 `{z:real^2 | &0 <= z$2} INTER ball(vec 0,r)`] AFF_DIM_SUBSET) THEN
  ANTS_TAC THENL
   [SIMP_TAC[SUBSET; IN_INTER; IN_ELIM_THM; REAL_LT_IMP_LE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

(* Open subsets of a chart domain, as open subsets of the polyhedron.       *)

let MOI_S8TB_OPEN_IN_CHART = prove
 (`!(x:real^N->bool) u u0.
     open_in (subtopology euclidean x) u /\ open_in (subtopology euclidean x) u0
     ==> open_in (subtopology euclidean u) (u0 INTER u)`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN
  EXISTS_TAC `x:real^N->bool` THEN ASM_SIMP_TAC[OPEN_IN_INTER; INTER_SUBSET] THEN
  ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]);;

let MOI_S8TB_PUNCT = prove
 (`!(x:real^N->bool) w u0.
     (moi_s28_locally_r2 x w \/ moi_s28_locally_half x w) /\
     open_in (subtopology euclidean x) u0 /\ w IN u0
     ==> ?v. open_in (subtopology euclidean x) v /\ w IN v /\ v SUBSET u0 /\
             connected (v DELETE w)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[moi_s28_locally_r2; moi_s28_locally_half] THEN STRIP_TAC THENL
   [(* a plane chart *)
    UNDISCH_TAC `(u:real^N->bool) homeomorphic (:real^2)` THEN
    REWRITE_TAC[homeomorphic] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^2` (X_CHOOSE_TAC `k:real^2->real^N`)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    SUBGOAL_THEN `open_in (subtopology euclidean u) (u0 INTER u:real^N->bool)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S8TB_OPEN_IN_CHART THEN EXISTS_TAC `x:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `open (IMAGE (h:real^N->real^2) (u0 INTER u))` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`h:real^N->real^2`; `k:real^2->real^N`; `u:real^N->bool`;
                     `(:real^2)`; `u0 INTER u:real^N->bool`]
        HOMEOMORPHISM_IMP_OPEN_MAP) THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN];
      ALL_TAC] THEN
    UNDISCH_TAC `open (IMAGE (h:real^N->real^2) (u0 INTER u))` THEN
    REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `(h:real^N->real^2) w`) THEN
    ANTS_TAC THENL
     [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `IMAGE (k:real^2->real^N) (ball(h(w:real^N),r))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`h:real^N->real^2`; `(:real^2)`] THEN
      ASM_REWRITE_TAC[SUBTOPOLOGY_UNIV; GSYM OPEN_IN; OPEN_BALL] THEN
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `(h:real^N->real^2) w` THEN
      ASM_SIMP_TAC[CENTRE_IN_BALL];
      ASM SET_TAC[];
      SUBGOAL_THEN `IMAGE (k:real^2->real^N) (ball(h(w:real^N),r)) DELETE w =
                    IMAGE k (ball(h w,r) DELETE h w)` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [ASM_MESON_TAC[CONTINUOUS_ON_SUBSET; SUBSET_UNIV];
        SIMP_TAC[CONNECTED_PUNCTURED_BALL; DIMINDEX_2; LE_REFL]]];
    (* a half-plane chart *)
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    SUBGOAL_THEN `open_in (subtopology euclidean u) (u0 INTER u:real^N->bool)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S8TB_OPEN_IN_CHART THEN EXISTS_TAC `x:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:real^N->real^2`; `k:real^2->real^N`; `u:real^N->bool`;
                   `{z:real^2 | &0 <= z$2}`; `u0 INTER u:real^N->bool`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o SPEC `vec 0:real^2` o CONJUNCT2 o
      GEN_REWRITE_RULE I [OPEN_IN_CONTAINS_BALL]) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `w:real^N` THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(k:real^2->real^N) (vec 0) = w` ASSUME_TAC THENL
     [UNDISCH_TAC `(h:real^N->real^2) w = vec 0` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `IMAGE (k:real^2->real^N)
                  ({z:real^2 | &0 <= z$2} INTER ball(vec 0,r))` THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `u:real^N->bool` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`h:real^N->real^2`; `{z:real^2 | &0 <= z$2}`] THEN
      SIMP_TAC[OPEN_IN_OPEN_INTER; OPEN_BALL] THEN
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `vec 0:real^2` THEN
      ASM_SIMP_TAC[CENTRE_IN_BALL; IN_INTER; IN_ELIM_THM; VEC_COMPONENT;
                   REAL_LE_REFL];
      UNDISCH_TAC `ball(vec 0,r) INTER {z:real^2 | &0 <= z$2} SUBSET
                   IMAGE (h:real^N->real^2) (u0 INTER u)` THEN
      ASM SET_TAC[];
      SUBGOAL_THEN
       `IMAGE (k:real^2->real^N) ({z:real^2 | &0 <= z$2} INTER ball(vec 0,r))
          DELETE w =
        IMAGE k (({z:real^2 | &0 <= z$2} INTER ball(vec 0,r)) DELETE vec 0)`
      SUBST1_TAC THENL
       [SUBGOAL_THEN `(vec 0:real^2) IN {z:real^2 | &0 <= z$2}` MP_TAC THENL
         [REWRITE_TAC[IN_ELIM_THM; VEC_COMPONENT; REAL_LE_REFL]; ALL_TAC] THEN
        UNDISCH_TAC `(k:real^2->real^N) (vec 0) = w` THEN
        UNDISCH_TAC `!y:real^2. y IN {z:real^2 | &0 <= z$2} ==> h((k:real^2->real^N) y) = y` THEN
        SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `{z:real^2 | &0 <= z$2}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
        MP_TAC(SPEC `r:real` MOI_S8TB_HALF_BALL) THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[CONNECTED_PUNCTURED_CONVEX]]]]);;

(* ------------------------------------------------------------------------- *)
(* The triangles at a vertex w are connected under adjacency (sharing       *)
(* an edge at w).  Adapted from MOI_SCF_SURF_VERTEX_CONNECTED of             *)
(* pc_moi_smo_cf: the 2-sphere hypothesis is replaced by purity and by       *)
(* connected punctured neighbourhoods at w (MOI_S8TB_PUNCT); the proof is    *)
(* the same (the open star minus w would split into two disjoint open        *)
(* sets).                                                                    *)
(* ------------------------------------------------------------------------- *)

let MOI_S8TB_VERTEX_CONNECTED = prove
 (`!L:(real^N->bool)->bool w U.
        simplicial_complex L /\
        (!s. s IN L /\ ~(s = {}) ==> ?t. t IN L /\ aff_dim t = &2 /\ s SUBSET t) /\
        (!u0. open_in (subtopology euclidean (UNIONS L)) u0 /\ w IN u0
              ==> ?v. open_in (subtopology euclidean (UNIONS L)) v /\ w IN v /\
                      v SUBSET u0 /\ connected (v DELETE w)) /\
        {w} IN L /\
        U SUBSET {t | t IN L /\ aff_dim t = &2 /\ w IN t} /\ ~(U = {}) /\
        (!t t'. t IN U /\ t' IN L /\ aff_dim t' = &2 /\ w IN t' /\
                aff_dim(t INTER t') = &1 ==> t' IN U)
        ==> U = {t | t IN L /\ aff_dim t = &2 /\ w IN t}`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pure")
    (CONJUNCTS_THEN2 (LABEL_TAC "punct") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "clos"))))))) THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  ABBREV_TAC `U2 = {t | t IN L /\ aff_dim t = &2 /\ w IN t} DIFF
                   (U:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN L /\ aff_dim t = &2 /\ w IN t
                                 ==> t IN U \/ t IN U2`
  (LABEL_TAC "split") THENL
   [EXPAND_TAC "U2" THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN U2 ==> ~(t IN U)` (LABEL_TAC "U2U") THENL
   [EXPAND_TAC "U2" THEN REWRITE_TAC[IN_DIFF] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?t2:real^N->bool. t2 IN U2` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U2" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `?t1:real^N->bool. t1 IN U` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `t1 IN L /\ aff_dim t1 = &2 /\ (w:real^N) IN t1 /\
    t2 IN L /\ aff_dim t2 = &2 /\ w IN t2 /\ ~(t2 IN U)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "U2" THEN ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (U:(real^N->bool)->bool) /\
                FINITE (U2:(real^N->bool)->bool) /\
                U SUBSET L /\ U2 SUBSET L`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(U:(real^N->bool)->bool) SUBSET L /\ U2 SUBSET L`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "U2" THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[FINITE_SUBSET; MOI_SCF_SC_FINITE];
    ALL_TAC] THEN
  ABBREV_TAC
   `st = {x:real^N | x IN UNIONS L /\ !t. t IN L /\ x IN t ==> w IN t}` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS L)) (st:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN ASM_SIMP_TAC[MOI_SCF_SC_OPEN_STAR]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN st` ASSUME_TAC THENL
   [EXPAND_TAC "st" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN st /\ ~(x = w)
               ==> ?t. t IN L /\ aff_dim t = &2 /\ w IN t /\ x IN t`
  (LABEL_TAC "cover") THENL
   [X_GEN_TAC `x:real^N` THEN EXPAND_TAC "st" THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)
      ASSUME_TAC) THEN
    USE_THEN "pure" (MP_TAC o SPEC `u:real^N->bool`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC; ALL_TAC] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N t t'. ~(x = w) /\ t IN U /\ t' IN U2 /\ x IN t /\ x IN t'
                    ==> F`
  (LABEL_TAC "disj") THENL
   [MAP_EVERY X_GEN_TAC [`x:real^N`; `t:real^N->bool`; `t':real^N->bool`] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `(t:real^N->bool) IN L /\ aff_dim t = &2 /\ w IN t /\
                  t' IN L /\ aff_dim t' = &2 /\ w IN t' /\ ~(t' IN U)`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `(t':real^N->bool) IN U2` THEN EXPAND_TAC "U2" THEN
      UNDISCH_TAC `(t:real^N->bool) IN U` THEN
      UNDISCH_TAC `(U:(real^N->bool)->bool) SUBSET
                   {t | t IN L /\ aff_dim t = &2 /\ w IN t}` THEN
      REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(t:real^N->bool = t')` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `~((t':real^N->bool) IN U)` THEN REWRITE_TAC[] THEN
    USE_THEN "clos" MATCH_MP_TAC THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SCF_INTER_DIM1 THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `w:real^N`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `A1 = (st DELETE (w:real^N)) INTER UNIONS U` THEN
  ABBREV_TAC `A2 = (st DELETE (w:real^N)) INTER UNIONS U2` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS L)) (A1:real^N->bool) /\
                open_in (subtopology euclidean (UNIONS L)) (A2:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `A1 = (st DELETE (w:real^N)) DIFF UNIONS U2 /\
                  A2 = (st DELETE (w:real^N)) DIFF UNIONS U`
    (CONJUNCTS_THEN SUBST1_TAC) THENL
     [MAP_EVERY EXPAND_TAC ["A1"; "A2"] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_DIFF; IN_DELETE; IN_UNIONS] THEN
      CONJ_TAC THEN X_GEN_TAC `x:real^N` THEN
      ASM_CASES_TAC `(x:real^N) IN st /\ ~(x = w)` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN
      USE_THEN "cover" (MP_TAC o SPEC `x:real^N`) THEN
      (ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC]) THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "split" (MP_TAC o SPEC `t:real^N->bool`) THEN
      USE_THEN "disj" (MP_TAC o SPEC `x:real^N`) THEN
      UNDISCH_TAC `(x:real^N) IN t` THEN
      UNDISCH_TAC `~(x:real^N = w)` THEN
      UNDISCH_TAC `(t:real^N->bool) IN L` THEN
      UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
      UNDISCH_TAC `(w:real^N) IN t` THEN
      MESON_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC OPEN_IN_DIFF THEN
    ASM_SIMP_TAC[OPEN_IN_DELETE] THEN
    MATCH_MP_TAC CLOSED_SUBSET THEN
    (CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC]) THEN
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_SCF_SC_CLOSED; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `?V:real^N->bool. open_in (subtopology euclidean (UNIONS L)) V /\
                                w IN V /\ V SUBSET st /\ connected (V DELETE w)`
  (X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) THENL
   [USE_THEN "punct" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN L /\ aff_dim t = &2 /\ w IN t
                ==> ?y. y IN V /\ ~(y = w) /\ y IN st /\ y IN t`
  (LABEL_TAC "near") THENL
   [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `w:real^N`; `t:real^N->bool`;
                   `V:real^N->bool`] MOI_SCF_NEAR_VERTEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim {w:real^N} = &2` THEN
      REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]] THEN
    EXPAND_TAC "st" THEN REWRITE_TAC[IN_ELIM_THM; IN_UNIONS] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `t:real^N->bool` THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      X_GEN_TAC `u:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) SUBSET u` MP_TAC THENL
       [MATCH_MP_TAC MOI_SCF_RELINT_SUBSET THEN
        MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `y:real^N`] THEN
        ASM_REWRITE_TAC[];
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS L:real^N->bool`; `V DELETE (w:real^N)`;
                 `A1:real^N->bool`; `A2:real^N->bool`]
    MOI_SCF_NOT_CONNECTED_OPEN_IN) THEN
  ANTS_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET o check (fun th ->
      can (find_term ((=) `V:real^N->bool`)) (concl th))) THEN SET_TAC[];
    REWRITE_TAC[SUBSET; IN_DELETE; IN_UNION] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN st` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MAP_EVERY EXPAND_TAC ["A1"; "A2"] THEN
    REWRITE_TAC[IN_INTER; IN_DELETE; IN_UNIONS] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "cover" (MP_TAC o SPEC `x:real^N`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "split" (MP_TAC o SPEC `t:real^N->bool`) THEN
    UNDISCH_TAC `(x:real^N) IN t` THEN
    UNDISCH_TAC `(t:real^N->bool) IN L` THEN
    UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
    UNDISCH_TAC `(w:real^N) IN t` THEN
    MESON_TAC[];
    MAP_EVERY EXPAND_TAC ["A1"; "A2"] THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_DELETE; IN_UNIONS; NOT_IN_EMPTY] THEN
    USE_THEN "disj" MP_TAC THEN MESON_TAC[];
    USE_THEN "near" (MP_TAC o SPEC `t1:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
    EXPAND_TAC "A1" THEN REWRITE_TAC[IN_INTER; IN_DELETE; IN_UNIONS] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `t1:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    USE_THEN "near" (MP_TAC o SPEC `t2:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
    EXPAND_TAC "A2" THEN REWRITE_TAC[IN_INTER; IN_DELETE; IN_UNIONS] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `t2:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The link of a vertex w of a 2-complex: its simplices have dimension      *)
(* at most 1; a link vertex a gives the edge [w,a]; the link edges at a     *)
(* correspond to the triangles on [w,a] (e |-> the join of w and e); every  *)
(* link simplex lies in a link edge (purity).                               *)
(* ------------------------------------------------------------------------- *)

(* The faces of a triangle at w that miss w are in the link.                 *)

let MOI_S8TB_TRI_OPP = prove
 (`!d (w:real^N) a b.
     simplicial_complex d /\ convex hull {w,a,b} IN d /\ ~affine_dependent {w,a,b} /\
     ~(a = w) /\ ~(b = w) /\ ~(a = b)
     ==> segment[a,b] IN simplicial_link d w /\
         {a} IN simplicial_link d w /\ {b} IN simplicial_link d w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!c:real^N->bool. c SUBSET {w,a,b} /\ ~(w IN c)
                ==> convex hull c IN simplicial_link d w`
  (LABEL_TAC "hull") THENL
   [X_GEN_TAC `c:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    SUBGOAL_THEN `(convex hull c:real^N->bool) face_of convex hull {w,a,b}`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `c:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex];
      DISCH_TAC THEN UNDISCH_TAC `~affine_dependent {w:real^N,a,b}` THEN
      REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `w:real^N` THEN
      REWRITE_TAC[IN_INSERT] THEN
      MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `c:real^N->bool`;
                     `{w:real^N,a,b} DELETE w`] HULL_MONO) THEN
      MP_TAC(ISPEC `c:real^N->bool` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      ASM SET_TAC[];
      EXISTS_TAC `convex hull {w:real^N,a,b}` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN USE_THEN "hull" MATCH_MP_TAC THEN
    ASM SET_TAC[];
    USE_THEN "hull" (MP_TAC o SPEC `{a:real^N}`) THEN
    REWRITE_TAC[CONVEX_HULL_SING] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[];
    USE_THEN "hull" (MP_TAC o SPEC `{b:real^N}`) THEN
    REWRITE_TAC[CONVEX_HULL_SING] THEN DISCH_THEN MATCH_MP_TAC THEN ASM SET_TAC[]]);;

(* A triangle at a vertex w: its two other vertices, the opposite edge and   *)
(* the two vertices in the link, and every vertex of d in it other than w   *)
(* is one of the two.                                                        *)

let MOI_S8TB_TRI_AT = prove
 (`!d (w:real^N) t.
     simplicial_complex d /\ {w} IN d /\ t IN d /\ aff_dim t = &2 /\ w IN t
     ==> ?a b. ~(a = w) /\ ~(b = w) /\ ~(a = b) /\ ~affine_dependent {w,a,b} /\
               t = convex hull {w,a,b} /\
               segment[a,b] IN simplicial_link d w /\
               {a} IN simplicial_link d w /\ {b} IN simplicial_link d w /\
               (!c. {c} IN d /\ c IN t /\ ~(c = w) ==> c = a \/ c = b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `t:real^N->bool`; `w:real^N`]
    MOI_SCF_TRIANGLE_AT_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `a:real^N`; `b:real^N`]
    MOI_S8TB_TRI_OPP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `c:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(c:real^N) extreme_point_of convex hull {w,a,b}` MP_TAC THENL
   [MATCH_MP_TAC MOI_SCF_VERTEX_EXTREME THEN EXISTS_TAC `d:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; IN_INSERT;
                 NOT_IN_EMPTY]]);;

let MOI_S8TB_LINK_DIM = prove
 (`!d (w:real^N) s.
     simplicial_complex d /\ (!s. s IN d ==> aff_dim s <= &2) /\ {w} IN d /\
     s IN simplicial_link d w
     ==> aff_dim s <= &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `s:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(convex hull ((w:real^N) INSERT s)) <= &2` MP_TAC THENL
   [ASM_MESON_TAC[]; ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

let MOI_S8TB_LINK_VERTEX = prove
 (`!d (w:real^N) a.
     simplicial_complex d /\ {w} IN d /\ {a} IN simplicial_link d w
     ==> ~(a = w) /\ {a} IN d /\ convex hull {w,a} IN d /\
         aff_dim(convex hull {w,a}) = &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `{a:real^N}`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[AFF_DIM_SING; IN_SING] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [ASM_MESON_TAC[];
    UNDISCH_TAC `{a:real^N} IN simplicial_link d w` THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN SIMP_TAC[];
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

(* The link edges at a link vertex a and the triangles on the edge [w,a].    *)

let MOI_S8TB_LINK_DEGREE = prove
 (`!d (w:real^N) a.
     simplicial_complex d /\ {w} IN d /\ {a} IN simplicial_link d w
     ==> CARD {e | e IN simplicial_link d w /\ aff_dim e = &1 /\ a IN e} =
         CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `a:real^N`]
    MOI_S8TB_LINK_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} =
    IMAGE (\e. convex hull ((w:real^N) INSERT e))
          {e | e IN simplicial_link d w /\ aff_dim e = &1 /\ a IN e}`
  SUBST1_TAC THENL
   [ALL_TAC;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MOI_SCF_LINK_JOIN_INJ THEN
      MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `w:real^N`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `d:(real^N->bool)->bool` THEN
      CONJ_TAC THENL [ASM_MESON_TAC[MOI_SCF_SC_FINITE]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM; simplicial_link] THEN MESON_TAC[]]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `(w:real^N) IN t /\ a IN t` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `{w:real^N,a}`] HULL_SUBSET) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `t:real^N->bool`]
      MOI_SCF_LINK_OPP) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `s:real^N->bool`]
      MOI_SCF_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL [ASM_INT_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^N) extreme_point_of convex hull (w INSERT s)` MP_TAC THENL
     [MATCH_MP_TAC MOI_SCF_VERTEX_EXTREME THEN
      EXISTS_TAC `d:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[extreme_point_of] THEN SIMP_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool`
      (CONJUNCTS_THEN2 SUBST1_TAC STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `e:real^N->bool`]
      MOI_SCF_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY INT_ARITH_TAC THEN
    MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]]);;

(* Every link simplex lies in a link edge (purity of d).                    *)

let MOI_S8TB_LINK_COVER = prove
 (`!d (w:real^N) s.
     simplicial_complex d /\
     (!s. s IN d /\ ~(s = {}) ==> ?t. t IN d /\ aff_dim t = &2 /\ s SUBSET t) /\
     {w} IN d /\ s IN simplicial_link d w
     ==> ?e. e IN simplicial_link d w /\ aff_dim e = &1 /\ s SUBSET e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pure")
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `s:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "pure" (MP_TAC o SPEC `convex hull ((w:real^N) INSERT s)`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `t:real^N->bool`]
    MOI_SCF_LINK_OPP) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `e:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_INT_ARITH_TAC;
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `s:real^N->bool`;
                   `e:real^N->bool`] MOI_SCF_LINK_JOIN_SUBSET) THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The link of a vertex w is connected: a set P of link vertices closed     *)
(* under link edges and nonempty is everything (the triangles at w with a   *)
(* vertex in P are closed under adjacency, so they are all triangles at w   *)
(* by MOI_S8TB_VERTEX_CONNECTED); hence the polyhedron of the link is       *)
(* connected and nonempty.                                                   *)
(* ------------------------------------------------------------------------- *)

let MOI_S8TB_LINK_GRAPH_CONN = prove
 (`!d (w:real^N) P.
     simplicial_complex d /\
     (!s. s IN d /\ ~(s = {}) ==> ?t. t IN d /\ aff_dim t = &2 /\ s SUBSET t) /\
     (!u0. open_in (subtopology euclidean (UNIONS d)) u0 /\ w IN u0
           ==> ?v. open_in (subtopology euclidean (UNIONS d)) v /\ w IN v /\
                   v SUBSET u0 /\ connected (v DELETE w)) /\
     {w} IN d /\
     (!a. a IN P ==> {a} IN simplicial_link d w) /\ ~(P = {}) /\
     (!a b. a IN P /\ ~(a = b) /\ segment[a,b] IN simplicial_link d w ==> b IN P)
     ==> !b. {b} IN simplicial_link d w ==> b IN P`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pure")
    (CONJUNCTS_THEN2 (LABEL_TAC "punct") (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "PK") (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "clos"))))))) THEN
  (* in a triangle at w meeting P, all link vertices are in P *)
  SUBGOAL_THEN
   `!t a c. t IN d /\ aff_dim t = &2 /\ (w:real^N) IN t /\ a IN P /\ a IN t /\
            {c} IN simplicial_link d w /\ c IN t
            ==> c IN P`
  (LABEL_TAC "B") THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `t:real^N->bool`]
      MOI_S8TB_TRI_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a1:real^N` (X_CHOOSE_THEN `b1:real^N`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      concl th = `t:real^N->bool = convex hull {w,a1,b1}`)) THEN
    SUBGOAL_THEN `{a:real^N} IN simplicial_link d w` ASSUME_TAC THENL
     [USE_THEN "PK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `a:real^N`]
      MOI_S8TB_LINK_VERTEX) THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `c:real^N`]
      MOI_S8TB_LINK_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(a = a1 \/ a = b1) /\ (c:real^N = a1 \/ c = b1)` MP_TAC THENL
     [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `c:real^N = a` THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN USE_THEN "clos" MATCH_MP_TAC THEN EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SEGMENT_SYM];
    ALL_TAC] THEN
  ABBREV_TAC `U = {t | t IN d /\ aff_dim t = &2 /\ (w:real^N) IN t /\
                       ?a. a IN P /\ a IN t}` THEN
  SUBGOAL_THEN `U = {t | t IN d /\ aff_dim t = &2 /\ (w:real^N) IN t}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TB_VERTEX_CONNECTED THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "U" THEN SET_TAC[];
      UNDISCH_TAC `~(P:real^N->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
      SUBGOAL_THEN `{a:real^N} IN simplicial_link d w` ASSUME_TAC THENL
       [USE_THEN "PK" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `a:real^N`]
        MOI_S8TB_LINK_VERTEX) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      USE_THEN "pure" (MP_TAC o SPEC `convex hull {w:real^N,a}`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(w:real^N) IN t /\ a IN t` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `{w:real^N,a}`] HULL_SUBSET) THEN
        ASM SET_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `t:real^N->bool` THEN EXPAND_TAC "U" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `t':real^N->bool`] THEN
      EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `t:real^N->bool`]
        MOI_S8TB_TRI_AT) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `a1:real^N` (X_CHOOSE_THEN `b1:real^N`
        STRIP_ASSUME_TAC)) THEN
      FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
        concl th = `t:real^N->bool = convex hull {w,a1,b1}`)) THEN
      SUBGOAL_THEN `(a1:real^N) IN convex hull {w,a1,b1} /\
                    b1 IN convex hull {w,a1,b1}` STRIP_ASSUME_TAC THENL
       [SIMP_TAC[HULL_INC; IN_INSERT]; ALL_TAC] THEN
      SUBGOAL_THEN `(a1:real^N) IN P /\ b1 IN P` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN USE_THEN "B" MATCH_MP_TAC THEN
        MAP_EVERY EXISTS_TAC [`convex hull {w:real^N,a1,b1}`; `a:real^N`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`w:real^N`; `a1:real^N`; `b1:real^N`;
                     `convex hull {w:real^N,a1,b1} INTER t'`] MOI_SCF_EDGE_AT_VERTEX) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[MOI_CON_SC_INTER];
        ALL_TAC] THEN
      DISCH_THEN DISJ_CASES_TAC THENL
       [EXISTS_TAC `a1:real^N` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `{w:real^N,a1}`] HULL_SUBSET) THEN
        ASM SET_TAC[];
        EXISTS_TAC `b1:real^N` THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `{w:real^N,b1}`] HULL_SUBSET) THEN
        ASM SET_TAC[]]];
    ALL_TAC] THEN
  X_GEN_TAC `b:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `b:real^N`]
    MOI_S8TB_LINK_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "pure" (MP_TAC o SPEC `convex hull {w:real^N,b}`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N) IN t /\ b IN t` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex:(real^N->bool)->bool`; `{w:real^N,b}`] HULL_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(t:real^N->bool) IN U` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  EXPAND_TAC "U" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC o last o CONJUNCTS) THEN
  USE_THEN "B" MATCH_MP_TAC THEN
  MAP_EVERY EXISTS_TAC [`t:real^N->bool`; `a:real^N`] THEN ASM_REWRITE_TAC[]);;

(* A connected subset of a set split by two open sets lies on one side.     *)

let MOI_S8TB_SIDE = prove
 (`!c s e1 e2:real^N->bool.
     connected c /\ c SUBSET s /\ open e1 /\ open e2 /\ s SUBSET e1 UNION e2 /\
     e1 INTER e2 INTER s = {} /\ ~(c INTER e1 = {})
     ==> c SUBSET e1`,
  REWRITE_TAC[connected; NOT_EXISTS_THM] THEN REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`e1:real^N->bool`; `e2:real^N->bool`]) THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_S8TB_LINK_CONNECTED = prove
 (`!d (w:real^N).
     simplicial_complex d /\
     (!s. s IN d /\ ~(s = {}) ==> ?t. t IN d /\ aff_dim t = &2 /\ s SUBSET t) /\
     (!u0. open_in (subtopology euclidean (UNIONS d)) u0 /\ w IN u0
           ==> ?v. open_in (subtopology euclidean (UNIONS d)) v /\ w IN v /\
                   v SUBSET u0 /\ connected (v DELETE w)) /\
     {w} IN d
     ==> connected (UNIONS (simplicial_link d w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ABBREV_TAC `K = simplicial_link d (w:real^N)` THEN
  SUBGOAL_THEN `simplicial_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "K" THEN MATCH_MP_TAC MOI_SCF_LINK_SC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K ==> connected s` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_CON_SC_CONVEX; CONVEX_CONNECTED]; ALL_TAC] THEN
  REWRITE_TAC[connected] THEN
  DISCH_THEN(X_CHOOSE_THEN `e1:real^N->bool` (X_CHOOSE_THEN `e2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K /\ ~(s INTER e1 = {}) ==> s SUBSET e1`
  (LABEL_TAC "S1") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_SIDE THEN
    MAP_EVERY EXISTS_TAC [`UNIONS K:real^N->bool`; `e2:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN K /\ ~(s INTER e2 = {}) ==> s SUBSET e2`
  (LABEL_TAC "S2") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_SIDE THEN
    MAP_EVERY EXISTS_TAC [`UNIONS K:real^N->bool`; `e1:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v:real^N. {v} IN K /\ v IN e1` ASSUME_TAC THENL
   [SUBGOAL_THEN `?x:real^N s. x IN e1 /\ s IN K /\ x IN s` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_SC_VERTEX) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^N` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "S1" (MP_TAC o SPEC `s:real^N->bool`) THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b:real^N. {a} IN K /\ a IN e1 /\ ~(a = b) /\ segment[a,b] IN K
                             ==> {b} IN K /\ b IN e1`
  ASSUME_TAC THENL
   [MAP_EVERY X_GEN_TAC [`a:real^N`; `b:real^N`] THEN STRIP_TAC THEN CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_complex (K:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      EXISTS_TAC `segment[a:real^N,b]` THEN
      ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT];
      USE_THEN "S1" (MP_TAC o SPEC `segment[a:real^N,b]`) THEN
      MP_TAC(ISPECL [`a:real^N`; `b:real^N`] ENDS_IN_SEGMENT) THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`;
                 `{a:real^N | {a} IN K /\ a IN e1}`] MOI_S8TB_LINK_GRAPH_CONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(LABEL_TAC "ALL" o REWRITE_RULE[IN_ELIM_THM;
    ASSUME `simplicial_link d (w:real^N) = K`]) THEN
  SUBGOAL_THEN `?x:real^N s. x IN e2 /\ s IN K /\ x IN s` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_SC_VERTEX) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  USE_THEN "ALL" (MP_TAC o SPEC `v:real^N`) THEN
  USE_THEN "S2" (MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM SET_TAC[]);;

let MOI_S8TB_LINK_NONEMPTY = prove
 (`!d (w:real^N).
     simplicial_complex d /\
     (!s. s IN d /\ ~(s = {}) ==> ?t. t IN d /\ aff_dim t = &2 /\ s SUBSET t) /\
     {w} IN d
     ==> ?t. t IN d /\ aff_dim t = &2 /\ w IN t /\
             ~(UNIONS (simplicial_link d w) = {})`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "pure")
    ASSUME_TAC)) THEN
  USE_THEN "pure" (MP_TAC o SPEC `{w:real^N}`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[NOT_INSERT_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[SING_SUBSET] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `t:real^N->bool`]
    MOI_S8TB_TRI_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `{a:real^N}`] THEN
  ASM_REWRITE_TAC[IN_SING]);;

(* ------------------------------------------------------------------------- *)
(* A finite connected graph in which every vertex has at most two           *)
(* neighbours and x0 at most one is a path from x0: a longest injective     *)
(* path from x0 (moi_scf_path of pc_moi_smo_cf) visits every vertex, and    *)
(* its only edges join consecutive vertices.                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S8TB_GRAPH_PATH = prove
 (`!(V:A->bool) R x0.
     FINITE V /\ x0 IN V /\ (!x y. R x y ==> R y x) /\ (!x. ~R x x) /\
     (!x u1 u2 u3. x IN V /\ u1 IN V /\ u2 IN V /\ u3 IN V /\
                   R x u1 /\ R x u2 /\ R x u3
                   ==> u1 = u2 \/ u1 = u3 \/ u2 = u3) /\
     (!u1 u2. u1 IN V /\ u2 IN V /\ R x0 u1 /\ R x0 u2 ==> u1 = u2) /\
     (!U. U SUBSET V /\ ~(U = {}) /\ (!x y. x IN U /\ y IN V /\ R x y ==> y IN U)
          ==> U = V)
     ==> ?k W. moi_scf_path V R x0 k W /\
               (!x. x IN V ==> ?i. i <= k /\ W i = x) /\
               (!i j. i <= k /\ j <= k /\ R (W i) (W j) ==> j = SUC i \/ i = SUC j)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "sym") (CONJUNCTS_THEN2 (LABEL_TAC "irr")
      (CONJUNCTS_THEN2 (LABEL_TAC "deg2") (CONJUNCTS_THEN2 (LABEL_TAC "deg1")
        (LABEL_TAC "conn"))))))) THEN
  MP_TAC(ISPEC `\k. ?W:num->A. moi_scf_path V R x0 k W` num_MAX) THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `a /\ (b ==> c) ==> (a <=> b) ==> c`) THEN CONJ_TAC THENL
   [CONJ_TAC THENL
     [EXISTS_TAC `0` THEN EXISTS_TAC `\i:num. (x0:A)` THEN
      REWRITE_TAC[moi_scf_path; LE; LT] THEN ASM_MESON_TAC[];
      EXISTS_TAC `CARD(V:A->bool)` THEN X_GEN_TAC `k:num` THEN
      DISCH_THEN(X_CHOOSE_TAC `W:num->A`) THEN
      MATCH_MP_TAC LT_IMP_LE THEN MATCH_MP_TAC MOI_SCF_PATH_BOUND THEN
      MAP_EVERY EXISTS_TAC [`R:A->A->bool`; `x0:A`; `W:num->A`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (CONJUNCTS_THEN2
    (X_CHOOSE_TAC `W:num->A`) (LABEL_TAC "max"))) THEN
  EXISTS_TAC `k:num` THEN EXISTS_TAC `W:num->A` THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_scf_path]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W0") (CONJUNCTS_THEN2
    (LABEL_TAC "WV") (CONJUNCTS_THEN2 (LABEL_TAC "WR") (LABEL_TAC "Winj")))) THEN
  (* neighbours of the last vertex are on the path (maximality) *)
  SUBGOAL_THEN `!u:A. u IN V /\ R ((W:num->A) k) u ==> ?i. i <= k /\ W i = u`
  (LABEL_TAC "onpath") THENL
   [X_GEN_TAC `u:A` THEN STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(ASSUME_TAC o
      REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`]) THEN
    USE_THEN "max" (MP_TAC o SPEC `SUC k`) THEN
    REWRITE_TAC[ARITH_RULE `~(SUC k <= k)`; NOT_CLAUSES; IMP_CLAUSES] THEN
    EXISTS_TAC `\i. if i <= k then (W:num->A) i else u` THEN
    MATCH_MP_TAC MOI_SCF_PATH_EXTEND THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* steps back along the path *)
  SUBGOAL_THEN `!i. 0 < i /\ i <= k ==> R ((W:num->A) i) (W(i - 1))`
  (LABEL_TAC "Wback") THENL
   [X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    USE_THEN "sym" MATCH_MP_TAC THEN
    SUBGOAL_THEN `(W:num->A) i = W(SUC(i - 1))` SUBST1_TAC THENL
     [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  (* the vertex set of the path is closed under adjacency *)
  SUBGOAL_THEN `!j v:A. j <= k /\ v IN V /\ R ((W:num->A) j) v
                        ==> ?i. i <= k /\ W i = v`
  (LABEL_TAC "closed") THENL
   [REPEAT STRIP_TAC THEN
    ASM_CASES_TAC `j:num = k` THENL
     [USE_THEN "onpath" MATCH_MP_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(LABEL_TAC "off" o
      REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ b) <=> a ==> ~b`]) THEN
    SUBGOAL_THEN `R ((W:num->A) j) (W(SUC j)):bool` ASSUME_TAC THENL
     [USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(W:num->A) (SUC j) IN V /\ W j IN V` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `j = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "deg1" (MP_TAC o SPECL [`(W:num->A) (SUC 0)`; `v:A`]) THEN
      ANTS_TAC THENL
       [USE_THEN "W0" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN USE_THEN "off" (MP_TAC o SPEC `SUC 0`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `R ((W:num->A) j) (W(j - 1)):bool /\ W(j - 1) IN V`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "Wback" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "deg2" (MP_TAC o SPECL [`(W:num->A) j`; `(W:num->A)(j - 1)`;
                                     `(W:num->A)(SUC j)`; `v:A`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [USE_THEN "Winj" (MP_TAC o SPECL [`j - 1`; `SUC j`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      USE_THEN "off" (MP_TAC o SPEC `j - 1`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      USE_THEN "off" (MP_TAC o SPEC `SUC j`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [(* every vertex is on the path *)
    SUBGOAL_THEN `{x:A | ?i. i <= k /\ (W:num->A) i = x} = V` MP_TAC THENL
     [USE_THEN "conn" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
        MAP_EVERY EXISTS_TAC [`(W:num->A) 0`; `0`] THEN REWRITE_TAC[LE_0];
        REWRITE_TAC[IN_ELIM_THM] THEN MAP_EVERY X_GEN_TAC [`x:A`; `y:A`] THEN
        DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)
          STRIP_ASSUME_TAC) THEN
        USE_THEN "closed" MATCH_MP_TAC THEN EXISTS_TAC `j:num` THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  (* only consecutive vertices are adjacent *)
  SUBGOAL_THEN `!i j. i < j /\ j <= k /\ R ((W:num->A) i) (W j) ==> j = SUC i`
  (LABEL_TAC "lt") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `R ((W:num->A) i) (W(SUC i)):bool` ASSUME_TAC THENL
     [USE_THEN "WR" MATCH_MP_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(W:num->A) (SUC i) IN V /\ W j IN V /\ W i IN V`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `i = 0` THENL
     [FIRST_X_ASSUM SUBST_ALL_TAC THEN
      USE_THEN "deg1" (MP_TAC o SPECL [`(W:num->A) (SUC 0)`; `(W:num->A) j`]) THEN
      ANTS_TAC THENL
       [USE_THEN "W0" (SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_TAC THEN USE_THEN "Winj" (MP_TAC o SPECL [`SUC 0`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `R ((W:num->A) i) (W(i - 1)):bool /\ W(i - 1) IN V`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [USE_THEN "Wback" MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "WV" MATCH_MP_TAC THEN ASM_ARITH_TAC];
      ALL_TAC] THEN
    USE_THEN "deg2" (MP_TAC o SPECL [`(W:num->A) i`; `(W:num->A)(i - 1)`;
                                     `(W:num->A)(SUC i)`; `(W:num->A) j`]) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    STRIP_TAC THENL
     [USE_THEN "Winj" (MP_TAC o SPECL [`i - 1`; `SUC i`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      USE_THEN "Winj" (MP_TAC o SPECL [`i - 1`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]];
      USE_THEN "Winj" (MP_TAC o SPECL [`SUC i`; `j:num`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
  ASM_CASES_TAC `i:num = j` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `i < j \/ j < i:num` DISJ_CASES_TAC THENL
   [ASM_ARITH_TAC;
    DISJ1_TAC THEN USE_THEN "lt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN USE_THEN "lt" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "sym" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Recognising the link.  A 1-complex whose vertices are on at most two     *)
(* edges, with one vertex on exactly one edge, and whose vertex graph is    *)
(* connected, is a polygonal arc (MOI_S8TB_GRAPH_PATH, MOI_SLV_POLY_ARC),   *)
(* hence a PL 1-ball (MOI_SFR_ARC_PL_BALL).                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S8TB_EDGES_GE = prove
 (`!(K:(real^N->bool)->bool) x u1 u2 u3.
     FINITE K /\
     segment[x,u1] IN K /\ segment[x,u2] IN K /\ segment[x,u3] IN K /\
     ~(x = u1) /\ ~(x = u2) /\ ~(x = u3) /\
     ~(u1 = u2) /\ ~(u1 = u3) /\ ~(u2 = u3)
     ==> 3 <= CARD {e | e IN K /\ aff_dim e = &1 /\ x IN e}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD {segment[x:real^N,u1], segment[x,u2], segment[x,u3]} = 3`
  (SUBST1_TAC o SYM) THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[SEGMENT_EQ; SET_RULE `{a:real^N,b} = {a,c} <=> b = c`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT];
      MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]]]);;

let MOI_S8TB_EDGES_GE2 = prove
 (`!(K:(real^N->bool)->bool) x u1 u2.
     FINITE K /\ segment[x,u1] IN K /\ segment[x,u2] IN K /\
     ~(x = u1) /\ ~(x = u2) /\ ~(u1 = u2)
     ==> 2 <= CARD {e | e IN K /\ aff_dim e = &1 /\ x IN e}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `CARD {segment[x:real^N,u1], segment[x,u2]} = 2`
  (SUBST1_TAC o SYM) THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[SEGMENT_EQ; SET_RULE `{a:real^N,b} = {a,c} <=> b = c`] THEN
    CONV_TAC NUM_REDUCE_CONV;
    MATCH_MP_TAC CARD_SUBSET THEN CONJ_TAC THENL
     [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT; ENDS_IN_SEGMENT];
      MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[]]]);;

let MOI_S8TB_SEG_ENDS = prove
 (`!(K:(real^N->bool)->bool) a b.
     simplicial_complex K /\ segment[a,b] IN K ==> {a} IN K /\ {b} IN K`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  EXISTS_TAC `segment[a:real^N,b]` THEN
  ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT]);;

let MOI_S8TB_K1_ARC = prove
 (`!(K:(real^N->bool)->bool) a0.
     simplicial_complex K /\ (!s. s IN K ==> aff_dim s <= &1) /\
     (!s. s IN K /\ ~(s = {}) ==> ?e. e IN K /\ aff_dim e = &1 /\ s SUBSET e) /\
     (!v. {v} IN K ==> CARD {e | e IN K /\ aff_dim e = &1 /\ v IN e} <= 2) /\
     {a0} IN K /\ CARD {e | e IN K /\ aff_dim e = &1 /\ a0 IN e} = 1 /\
     (!P. (!a. a IN P ==> {a} IN K) /\ ~(P = {}) /\
          (!a b. a IN P /\ ~(a = b) /\ segment[a,b] IN K ==> b IN P)
          ==> !b. {b} IN K ==> b IN P)
     ==> pl_ball 1 (UNIONS K)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "cover") (CONJUNCTS_THEN2 (LABEL_TAC "deg")
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (LABEL_TAC "gconn"))))))) THEN
  SUBGOAL_THEN `FINITE (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SCF_SC_FINITE]; ALL_TAC] THEN
  ABBREV_TAC `V = {a:real^N | {a} IN K}` THEN
  ABBREV_TAC `R = \a b:real^N. ~(a = b) /\ segment[a,b] IN K` THEN
  SUBGOAL_THEN `!a b:real^N. R a b <=> ~(a = b) /\ segment[a,b] IN K`
  (LABEL_TAC "Rdef") THENL
   [EXPAND_TAC "R" THEN REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^N. a IN V <=> {a} IN K` (LABEL_TAC "Vdef") THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  (* the hypotheses of MOI_S8TB_GRAPH_PATH *)
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN
    MP_TAC(ISPECL [`\a:real^N. {a}`; `K:(real^N->bool)->bool`] FINITE_IMAGE_INJ) THEN
    REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a0:real^N) IN V` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x y:real^N. R x y ==> R y x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN MESON_TAC[SEGMENT_SYM]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. ~R x x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x u1 u2 u3:real^N. x IN V /\ u1 IN V /\ u2 IN V /\ u3 IN V /\
                        R x u1 /\ R x u2 /\ R x u3
                        ==> u1 = u2 \/ u1 = u3 \/ u2 = u3`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
    DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE[DE_MORGAN_THM]) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`; `u1:real^N`; `u2:real^N`;
                   `u3:real^N`] MOI_S8TB_EDGES_GE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    USE_THEN "deg" (MP_TAC o C MATCH_MP (ASSUME `{x:real^N} IN K`)) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `!u1 u2:real^N. u1 IN V /\ u2 IN V /\ R (a0:real^N) u1 /\ R a0 u2 ==> u1 = u2`
  ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `a0:real^N`; `u1:real^N`; `u2:real^N`]
      MOI_S8TB_EDGES_GE2) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!U:real^N->bool. U SUBSET V /\ ~(U = {}) /\
                     (!x y. x IN U /\ y IN V /\ R x y ==> y IN U)
                     ==> U = V`
  ASSUME_TAC THENL
   [X_GEN_TAC `U:real^N->bool` THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET] THEN USE_THEN "Vdef" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "gconn" MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [UNDISCH_TAC `(U:real^N->bool) SUBSET V` THEN
      USE_THEN "Vdef" (fun th -> REWRITE_TAC[SUBSET; th]);
      ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[MOI_S8TB_SEG_ENDS]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `R:real^N->real^N->bool`; `a0:real^N`]
    MOI_S8TB_GRAPH_PATH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` (X_CHOOSE_THEN `W:num->real^N`
    (CONJUNCTS_THEN2 MP_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ham") (LABEL_TAC "cons"))))) THEN
  REWRITE_TAC[moi_scf_path] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "W0") (CONJUNCTS_THEN2
    (LABEL_TAC "WV") (CONJUNCTS_THEN2 (LABEL_TAC "WR") (LABEL_TAC "Winj")))) THEN
  (* the path has at least one edge *)
  SUBGOAL_THEN `1 <= k` ASSUME_TAC THENL
   [SUBGOAL_THEN `~({e | e IN K /\ aff_dim e = &1 /\ (a0:real^N) IN e} = {})`
    MP_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `CARD {e | e IN K /\ aff_dim e = &1 /\ (a0:real^N) IN e} = 1` THEN
      ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `a0:real^N`; `e:real^N->bool`]
      MOI_S4L_K1_EDGE_AT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC) THEN
    USE_THEN "ham" (MP_TAC o C MATCH_MP (ASSUME `{b:real^N} IN K`)) THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(i = 0)` MP_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~(b:real^N = a0)` THEN
      USE_THEN "W0" (SUBST1_TAC o SYM) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
        concl th = `(W:num->real^N) i = b`)) THEN
      ASM_REWRITE_TAC[];
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `k:num`; `W:num->real^N`]
    MOI_SLV_POLY_ARC) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[];
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      USE_THEN "WR" (MP_TAC o C MP (ASSUME `(i:num) < k`) o SPEC `i:num`) THEN
      USE_THEN "Rdef" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `UNIONS K = path_image(polygonal_path(list_of_seq (W:num->real^N) (SUC k)))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      USE_THEN "cover" (MP_TAC o SPEC `s:real^N->bool`) THEN
      ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `e:real^N->bool`] MOI_S4L_K1_CASES) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_EMPTY; INT_ARITH `~(-- &1:int = &1)`];
        UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
        ASM_REWRITE_TAC[AFF_DIM_SING; INT_ARITH `~(&0:int = &1)`];
        ALL_TAC] THEN
      USE_THEN "ham" (MP_TAC o C MATCH_MP (ASSUME `{a:real^N} IN K`)) THEN
      USE_THEN "ham" (MP_TAC o C MATCH_MP (ASSUME `{b:real^N} IN K`)) THEN
      DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
      DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
      USE_THEN "cons" (MP_TAC o SPECL [`i:num`; `j:num`]) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN USE_THEN "Rdef" (fun th -> REWRITE_TAC[th]) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THENL
       [EXISTS_TAC `segment[(W:num->real^N) i,W(SUC i)]` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
         [EXISTS_TAC `i:num` THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
          FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `j = SUC i`)) THEN
          ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
        EXISTS_TAC `segment[(W:num->real^N) j,W(SUC j)]` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
         [EXISTS_TAC `j:num` THEN REWRITE_TAC[] THEN ASM_ARITH_TAC;
          FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> concl th = `i = SUC j`)) THEN
          ONCE_REWRITE_TAC[SEGMENT_SYM] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]];
      REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `i:num` THEN DISCH_TAC THEN
      MATCH_MP_TAC(SET_RULE `!s:real^N->bool. s IN K ==> s SUBSET UNIONS K`) THEN
      USE_THEN "WR" (MP_TAC o C MP (ASSUME `(i:num) < k`) o SPEC `i:num`) THEN
      USE_THEN "Rdef" (fun th -> REWRITE_TAC[th]) THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SFR_ARC_PL_BALL THEN
  ASM_REWRITE_TAC[MOI_PL2_PL_POLYGONAL_PATH]);;

(* ------------------------------------------------------------------------- *)
(* The link of every vertex of a charted complex is a PL 1-sphere (all      *)
(* edges at the vertex on two triangles: a connected 1-complex with all     *)
(* vertices of degree 2, MOI_S4L_CM1_CIRCLES) or a PL 1-ball (an edge on    *)
(* one triangle gives a link vertex of degree 1, MOI_S8TB_K1_ARC).  Then    *)
(* SURF_LOCAL: the complex is a combinatorial 2-manifold with boundary, its *)
(* boundary is the set of points without plane chart (SURF_CHARTS), and an  *)
(* empty boundary leaves only sphere links.                                 *)
(* ------------------------------------------------------------------------- *)

let MOI_S8TB_VERTEX_LINK = prove
 (`!d (w:real^N).
     simplicial_complex d /\
     (!y. y IN UNIONS d
          ==> moi_s28_locally_r2 (UNIONS d) y \/ moi_s28_locally_half (UNIONS d) y) /\
     {w} IN d
     ==> (pl_sphere 1 (UNIONS (simplicial_link d w)) \/
          pl_ball 1 (UNIONS (simplicial_link d w))) /\
         ((!a. {a} IN simplicial_link d w
               ==> CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 2)
          ==> pl_sphere 1 (UNIONS (simplicial_link d w)))`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "ch") ASSUME_TAC)) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN d ==> aff_dim s <= &2` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TB_DIM THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN d /\ ~(s = {})
                ==> ?t. t IN d /\ aff_dim t = &2 /\ s SUBSET t`
  (LABEL_TAC "pure") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_PURE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!u0. open_in (subtopology euclidean (UNIONS d)) u0 /\ (w:real^N) IN u0
         ==> ?v. open_in (subtopology euclidean (UNIONS d)) v /\ w IN v /\
                 v SUBSET u0 /\ connected (v DELETE w)`
  (LABEL_TAC "punct") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_PUNCT THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "ch" MATCH_MP_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (simplicial_link d (w:real^N))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LINK_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN simplicial_link d w ==> aff_dim s <= &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_LINK_DIM THEN
    MAP_EVERY EXISTS_TAC [`d:(real^N->bool)->bool`; `w:real^N`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!s:real^N->bool. s IN simplicial_link d w /\ ~(s = {})
                     ==> ?e. e IN simplicial_link d w /\ aff_dim e = &1 /\ s SUBSET e`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_LINK_COVER THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!a:real^N. {a} IN simplicial_link d w
     ==> CARD {e | e IN simplicial_link d w /\ aff_dim e = &1 /\ a IN e} =
         CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} /\
         (CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 1 \/
          CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 2)`
  (LABEL_TAC "degs") THENL
   [X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_S8TB_LINK_DEGREE THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`; `a:real^N`]
        MOI_S8TB_LINK_VERTEX) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_S8TB_EDGE_CARD THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `connected (UNIONS (simplicial_link d (w:real^N)))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S8TB_LINK_CONNECTED THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `w:real^N`] MOI_S8TB_LINK_NONEMPTY) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN
    MP_TAC(ISPEC `t0:real^N->bool` AFF_DIM_LE_UNIV) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  (* all link vertices of degree 2: a PL 1-sphere *)
  SUBGOAL_THEN
   `(!a:real^N. {a} IN simplicial_link d w
                ==> CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 2)
    ==> pl_sphere 1 (UNIONS (simplicial_link d w))`
  ASSUME_TAC THENL
   [DISCH_THEN(LABEL_TAC "allTwo") THEN
    MP_TAC(ISPEC `simplicial_link d (w:real^N)` MOI_S4L_CM1_CIRCLES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      USE_THEN "degs" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN simplicial_link d w`)) THEN
      USE_THEN "allTwo" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN simplicial_link d w`)) THEN
      ARITH_TAC;
      ALL_TAC] THEN
    STRIP_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    SUBGOAL_THEN `components(UNIONS (simplicial_link d (w:real^N))) =
                  {UNIONS (simplicial_link d w)}`
    SUBST1_TAC THENL
     [ASM_REWRITE_TAC[COMPONENTS_EQ_SING]; REWRITE_TAC[IN_SING]];
    ALL_TAC] THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  ASM_CASES_TAC
   `!a:real^N. {a} IN simplicial_link d w
               ==> CARD {t | t IN d /\ aff_dim t = &2 /\ convex hull {w,a} SUBSET t} = 2`
  THENL [DISJ1_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISJ2_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_THEN `a0:real^N` STRIP_ASSUME_TAC o
    REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
  (* a link vertex of degree 1: a PL 1-ball *)
  SUBGOAL_THEN `!v:real^N. {v} IN simplicial_link d w
                ==> CARD {e | e IN simplicial_link d w /\ aff_dim e = &1 /\ v IN e} <= 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    USE_THEN "degs" (MP_TAC o C MATCH_MP (ASSUME `{v:real^N} IN simplicial_link d w`)) THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {e | e IN simplicial_link d w /\ aff_dim e = &1 /\ (a0:real^N) IN e}
                = 1`
  ASSUME_TAC THENL
   [USE_THEN "degs" (MP_TAC o C MATCH_MP (ASSUME `{a0:real^N} IN simplicial_link d w`)) THEN
    UNDISCH_TAC `~(CARD {t | t IN d /\ aff_dim t = &2 /\
                             convex hull {w:real^N,a0} SUBSET t} = 2)` THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!P. (!a. a IN P ==> {a} IN simplicial_link d w) /\ ~(P = {}) /\
        (!a b. a IN P /\ ~(a = b) /\ segment[a,b] IN simplicial_link d w ==> b IN P)
        ==> !b:real^N. {b} IN simplicial_link d w ==> b IN P`
  ASSUME_TAC THENL
   [GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC MOI_S8TB_LINK_GRAPH_CONN THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S8TB_K1_ARC THEN EXISTS_TAC `a0:real^N` THEN
  ASM_REWRITE_TAC[]);;

(* The target.                                                               *)

let SURF_LOCAL = prove
 (MOI_S28_SURF_LOCAL,
  GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ch"))) THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 2 (d:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF];
      REPEAT STRIP_TAC THEN
      MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `v:real^N`] MOI_S8TB_VERTEX_LINK) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(MATCH_MP SURF_CHARTS (CONJ (ASSUME `FINITE (d:(real^N->bool)->bool)`)
    (ASSUME `combinatorial_manifold_with_boundary 2 (d:(real^N->bool)->bool)`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1") (CONJUNCTS_THEN2 (LABEL_TAC "C2")
    (LABEL_TAC "C3"))) THEN
  SUBGOAL_THEN `surface_boundary d SUBSET UNIONS (d:(real^N->bool)->bool)` ASSUME_TAC THENL
   [REWRITE_TAC[surface_boundary; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^N` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[IN_DIFF; SUBSET];
    DISCH_TAC THEN REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `v:real^N`] MOI_S8TB_VERTEX_LINK) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    X_GEN_TAC `a:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `v:real^N`; `a:real^N`]
      MOI_S8TB_LINK_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`d:(real^N->bool)->bool`; `convex hull {v:real^N,a}`]
      MOI_S8TB_EDGE_CARD) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(TAUT `~p ==> p \/ q ==> q`) THEN DISCH_TAC THEN
    SUBGOAL_THEN `convex hull {v:real^N,a} SUBSET surface_boundary d` MP_TAC THENL
     [REWRITE_TAC[surface_boundary] THEN
      MATCH_MP_TAC(SET_RULE `!x:real^N->bool s. x IN s ==> x SUBSET UNIONS s`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM];
      ASM_REWRITE_TAC[SUBSET_EMPTY; CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY]]]);;

(* ------------------------------------------------------------------------- *)
(* SURF_INVARIANT by transport: a homeomorphism of polyhedra carries        *)
(* plane and half-plane charts (MOI_S8TB_TRANSPORT), so a triangulation d   *)
(* of |c| with c a combinatorial surface satisfies the hypotheses of        *)
(* SURF_LOCAL; the boundaries are the points without plane chart on both   *)
(* sides (SURF_CHARTS for c, SURF_LOCAL for d), so f maps one onto the      *)
(* other, and an empty boundary of c gives an empty boundary of d.          *)
(* ------------------------------------------------------------------------- *)

let MOI_S8TB_TRANSPORT = prove
 (`!(x:real^M->bool) (x':real^N->bool) f g y.
     homeomorphism (x,x') (f,g) /\ y IN x
     ==> (moi_s28_locally_r2 x y ==> moi_s28_locally_r2 x' (f y)) /\
         (moi_s28_locally_half x y ==> moi_s28_locally_half x' (f y))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN
   `!u. open_in (subtopology euclidean x) u
        ==> open_in (subtopology euclidean x') (IMAGE (f:real^M->real^N) u) /\
            homeomorphism (IMAGE f u,u) (g,f)`
  (LABEL_TAC "img") THENL
   [GEN_TAC THEN DISCH_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
      MAP_EVERY EXISTS_TAC [`g:real^N->real^M`; `x:real^M->bool`] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
      MAP_EVERY EXISTS_TAC [`x':real^N->bool`; `x:real^M->bool`] THEN
      ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MP_TAC o MATCH_MP OPEN_IN_IMP_SUBSET) THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[moi_s28_locally_r2; moi_s28_locally_half] THEN CONJ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "img" (MP_TAC o C MATCH_MP
      (ASSUME `open_in (subtopology euclidean x) (u:real^M->bool)`)) THEN
    STRIP_TAC THEN EXISTS_TAC `IMAGE (f:real^M->real^N) u` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC(INST_TYPE [`:N`,`:M`; `:M`,`:N`; `:2`,`:P`] HOMEOMORPHIC_TRANS) THEN
      EXISTS_TAC `u:real^M->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[homeomorphic] THEN
      MAP_EVERY EXISTS_TAC [`g:real^N->real^M`; `f:real^M->real^N`] THEN
      ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `u:real^M->bool` (X_CHOOSE_THEN `h:real^M->real^2`
      (X_CHOOSE_THEN `k:real^2->real^M` STRIP_ASSUME_TAC))) THEN
    USE_THEN "img" (MP_TAC o C MATCH_MP
      (ASSUME `open_in (subtopology euclidean x) (u:real^M->bool)`)) THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`IMAGE (f:real^M->real^N) u`;
                          `(h:real^M->real^2) o (g:real^N->real^M)`;
                          `(f:real^M->real^N) o (k:real^2->real^M)`] THEN
    ASM_REWRITE_TAC[o_THM] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      MATCH_MP_TAC HOMEOMORPHISM_COMPOSE THEN EXISTS_TAC `u:real^M->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[]]]);;

(* The target.                                                               *)

let SURF_INVARIANT = prove
 (MOI_S28_SURF_INVARIANT,
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "CH") (LABEL_TAC "LOC")) THEN
  MAP_EVERY X_GEN_TAC [`c:(real^M->bool)->bool`; `d:(real^N->bool)->bool`;
                       `f:real^M->real^N`; `g:real^N->real^M`] THEN
  STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  USE_THEN "CH" (MP_TAC o C MATCH_MP
    (CONJ (ASSUME `FINITE (c:(real^M->bool)->bool)`)
          (ASSUME `combinatorial_manifold_with_boundary 2 (c:(real^M->bool)->bool)`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "C1") (CONJUNCTS_THEN2 (LABEL_TAC "C2")
    (LABEL_TAC "C3"))) THEN
  (* charts on |d| *)
  SUBGOAL_THEN
   `!z:real^N. z IN UNIONS d
               ==> moi_s28_locally_r2 (UNIONS d) z \/ moi_s28_locally_half (UNIONS d) z`
  ASSUME_TAC THENL
   [X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(g:real^N->real^M) z IN UNIONS c /\ f (g z) = z` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`UNIONS c:real^M->bool`; `UNIONS d:real^N->bool`;
                   `f:real^M->real^N`; `g:real^N->real^M`; `(g:real^N->real^M) z`]
      MOI_S8TB_TRANSPORT) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(g:real^N->real^M) z IN surface_boundary c` THENL
     [USE_THEN "C2" (MP_TAC o C MATCH_MP
        (ASSUME `(g:real^N->real^M) z IN surface_boundary c`)) THEN
      MESON_TAC[];
      USE_THEN "C1" (MP_TAC o SPEC `(g:real^N->real^M) z`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
      MESON_TAC[]];
    ALL_TAC] THEN
  USE_THEN "LOC" (MP_TAC o SPEC `d:(real^N->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "D3"))) THEN
  (* plane charts correspond *)
  SUBGOAL_THEN
   `!y:real^M. y IN UNIONS c
               ==> (moi_s28_locally_r2 (UNIONS c) y <=>
                    moi_s28_locally_r2 (UNIONS d) ((f:real^M->real^N) y))`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^M` THEN DISCH_TAC THEN EQ_TAC THENL
     [MP_TAC(ISPECL [`UNIONS c:real^M->bool`; `UNIONS d:real^N->bool`;
                     `f:real^M->real^N`; `g:real^N->real^M`; `y:real^M`]
        MOI_S8TB_TRANSPORT) THEN
      ASM_SIMP_TAC[];
      MP_TAC(ISPECL [`UNIONS d:real^N->bool`; `UNIONS c:real^M->bool`;
                     `g:real^N->real^M`; `f:real^M->real^N`; `(f:real^M->real^N) y`]
        MOI_S8TB_TRANSPORT) THEN
      ANTS_TAC THENL
       [CONJ_TAC THENL
         [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
          ASM SET_TAC[]];
        ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `surface_boundary c =
    {y:real^M | y IN UNIONS c /\ ~moi_s28_locally_r2 (UNIONS c) y}`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `y:real^M` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    SUBGOAL_THEN `surface_boundary c SUBSET UNIONS (c:(real^M->bool)->bool)`
    ASSUME_TAC THENL
     [REWRITE_TAC[surface_boundary; SUBSET; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    ASM_MESON_TAC[IN_DIFF; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (f:real^M->real^N) (surface_boundary c) = surface_boundary d`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(fun th -> REWRITE_TAC[check (fun th ->
      aconv (concl th) `surface_boundary c =
                  {y:real^M | y IN UNIONS c /\ ~moi_s28_locally_r2 (UNIONS c) y}`) th]) THEN
    FIRST_X_ASSUM(fun th -> REWRITE_TAC[check (fun th ->
      aconv (concl th) `surface_boundary d =
                  {y:real^N | y IN UNIONS d /\ ~moi_s28_locally_r2 (UNIONS d) y}`) th]) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^N` THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `y:real^M` STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      STRIP_TAC THEN EXISTS_TAC `(g:real^N->real^M) z` THEN
      SUBGOAL_THEN `(g:real^N->real^M) z IN UNIONS c /\ f (g z) = z`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [FIRST_ASSUM ACCEPT_TAC;
    FIRST_ASSUM ACCEPT_TAC;
    DISCH_TAC THEN USE_THEN "D3" MATCH_MP_TAC THEN
    SUBGOAL_THEN `surface_boundary c = {}:real^M->bool` ASSUME_TAC THENL
     [USE_THEN "C3" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      concl th = `IMAGE (f:real^M->real^N) (surface_boundary c) = surface_boundary d`)) THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
      concl th = `surface_boundary c = {}:real^M->bool`)) THEN
    REWRITE_TAC[IMAGE_CLAUSES]]);;

