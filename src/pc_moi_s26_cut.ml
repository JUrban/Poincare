(* ========================================================================= *)
(* pc_moi_s26_cut: Case 3 of Moise 26.4 (GTM 47, p.193).  A finite           *)
(* combinatorial 3-manifold with boundary w in real^3 is cut along a closed  *)
(* connected surface subcomplex s missing Bd w into the parts on the two     *)
(* sides of |s| (26.6), both combinatorial 3-manifolds with boundary.  Main  *)
(* theorem CUT : |- MOI_S26_CUT (pc_moi_s2628_stmt.ml).  s need not be full  *)
(* in w.                                                                     *)
(* ========================================================================= *)

needs "src/pc_moi_s2628_stmt.ml";;
needs "src/pc_moi_fnd_bicol.ml";;
needs "src/pc_moi_fnd_tubed.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* The setting of the cut, and the relative interior of a simplex of w not   *)
(* in s misses |s| (used for sides, links and cones).                        *)
(* ------------------------------------------------------------------------- *)

let moi_s6ct_setting = new_definition
 `moi_s6ct_setting (w:(real^3->bool)->bool) s <=>
    FINITE w /\ combinatorial_manifold_with_boundary 3 w /\
    simplicial_subcomplex s w /\ combinatorial_manifold 2 s /\
    connected (UNIONS s) /\ ~(UNIONS s = {}) /\
    DISJOINT (UNIONS s) (complex_boundary w)`;;

let MOI_S6CT_SETTING_FACTS = prove
 (`!(w:(real^3->bool)->bool) s.
     moi_s6ct_setting w s
     ==> lf_simplicial_complex w /\ FINITE s /\ s SUBSET w /\
         (!q. q IN w ==> compact q /\ convex q /\ closed q) /\
         compact (UNIONS s) /\ closed (UNIONS s) /\
         UNIONS s SUBSET UNIONS w /\ ({}:real^3->bool) IN s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s6ct_setting] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (w:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:(real^3->bool)->bool) SUBSET w` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  SUBGOAL_THEN `!q:real^3->bool. q IN w ==> compact q /\ convex q /\ closed q`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_COMPACT; MOI_FM3_LF_CONVEX; COMPACT_IMP_CLOSED];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (s:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[FINITE_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (UNIONS (s:(real^3->bool)->bool))` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `({}:real^3->bool) IN s` ASSUME_TAC THENL
   [UNDISCH_TAC `~(UNIONS (s:(real^3->bool)->bool) = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^3` (X_CHOOSE_THEN `r:real^3->bool`
      STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `simplicial_subcomplex (s:(real^3->bool)->bool) w` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    EXISTS_TAC `r:real^3->bool` THEN ASM_REWRITE_TAC[EMPTY_FACE_OF];
    ALL_TAC] THEN
  ASM_SIMP_TAC[COMPACT_IMP_CLOSED; SUBSET_UNIONS]);;

(* Moise 26.6 (MOISE_266_STATEMENT) for the surface |s|: the two           *)
(* complementary components are inside and outside, both with frontier |s|. *)

let MOI_S6CT_SIDES = prove
 (`!(w:(real^3->bool)->bool) s.
     MOISE_266_STATEMENT /\ moi_s6ct_setting w s
     ==> components ((:real^3) DIFF UNIONS s) =
           {inside (UNIONS s), outside (UNIONS s)} /\
         ~(inside (UNIONS s) = outside (UNIONS s)) /\
         frontier (inside (UNIONS s)) = UNIONS s /\
         frontier (outside (UNIONS s)) = UNIONS s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SETTING_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_setting]) THEN
  UNDISCH_TAC `MOISE_266_STATEMENT` THEN REWRITE_TAC[MOISE_266_STATEMENT] THEN
  DISCH_THEN(MP_TAC o SPEC `s:(real^3->bool)->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `b:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `b = inside (UNIONS (s:(real^3->bool)->bool))` SUBST_ALL_TAC THENL
   [SUBGOAL_THEN `b INTER outside (UNIONS (s:(real^3->bool)->bool)) = {}` MP_TAC THENL
     [MP_TAC(ISPECL [`(:real^3) DIFF UNIONS (s:(real^3->bool)->bool)`; `b:real^3->bool`;
                     `outside (UNIONS (s:(real^3->bool)->bool))`] COMPONENTS_NONOVERLAP) THEN
      ASM_REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    MP_TAC(ISPEC `(:real^3) DIFF UNIONS (s:(real^3->bool)->bool)` UNIONS_COMPONENTS) THEN
    ASM_REWRITE_TAC[UNIONS_2] THEN
    MP_TAC(ISPEC `UNIONS (s:(real^3->bool)->bool)` INSIDE_UNION_OUTSIDE) THEN
    MP_TAC(ISPEC `UNIONS (s:(real^3->bool)->bool)` INSIDE_INTER_OUTSIDE) THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

let MOI_S6CT_RELINT_OFF = prove
 (`!(w:(real^N->bool)->bool) s q.
     lf_simplicial_complex w /\ simplicial_subcomplex s w /\ q IN w /\ ~(q IN s)
     ==> DISJOINT (relative_interior q) (UNIONS s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(r:real^N->bool) IN w` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^N->bool) SUBSET r` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`w:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^N->bool) face_of r` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
    EXISTS_TAC `w:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~((q:real^N->bool) IN s)` THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[simplicial_subcomplex]);;

(* ------------------------------------------------------------------------- *)
(* A side C of |s| with complementary side C' (C, C' are inside and         *)
(* outside of |s| in either order), and the side of a simplex of w not in s *)
(* (its relative interior is connected and misses |s|).                     *)
(* ------------------------------------------------------------------------- *)

let moi_s6ct_side = new_definition
 `moi_s6ct_side (w:(real^3->bool)->bool) s (C:real^3->bool) C' <=>
    moi_s6ct_setting w s /\
    components ((:real^3) DIFF UNIONS s) = {C, C'} /\ ~(C = C') /\
    frontier C = UNIONS s /\ frontier C' = UNIONS s`;;

let MOI_S6CT_SIDE_SYM = prove
 (`!(w:(real^3->bool)->bool) s C C'.
     moi_s6ct_side w s C C' ==> moi_s6ct_side w s C' C`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s6ct_side] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [ASM_REWRITE_TAC[] THEN SET_TAC[];
    ASM_MESON_TAC[]]);;

let MOI_S6CT_SIDE_FACTS = prove
 (`!(w:(real^3->bool)->bool) s C C'.
     moi_s6ct_side w s C C'
     ==> C IN components ((:real^3) DIFF UNIONS s) /\
         C' IN components ((:real^3) DIFF UNIONS s) /\
         open C /\ open C' /\ ~(C = {}) /\ ~(C' = {}) /\
         DISJOINT C C' /\ DISJOINT C (UNIONS s) /\ DISJOINT C' (UNIONS s) /\
         C UNION C' = (:real^3) DIFF UNIONS s /\
         closure C = C UNION UNIONS s /\ closure C' = C' UNION UNIONS s`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_s6ct_side] THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SETTING_FACTS) THEN
  SUBGOAL_THEN `(C:real^3->bool) IN components ((:real^3) DIFF UNIONS s) /\
                (C':real^3->bool) IN components ((:real^3) DIFF UNIONS s)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `open ((:real^3) DIFF UNIONS (s:(real^3->bool)->bool))` ASSUME_TAC THENL
   [REWRITE_TAC[GSYM closed] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THENL
   [ASM_MESON_TAC[OPEN_COMPONENTS];
    ASM_MESON_TAC[OPEN_COMPONENTS];
    ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
    ASM_MESON_TAC[IN_COMPONENTS_NONEMPTY];
    REWRITE_TAC[DISJOINT] THEN ASM_MESON_TAC[COMPONENTS_NONOVERLAP];
    MP_TAC(ISPECL [`(:real^3) DIFF UNIONS (s:(real^3->bool)->bool)`; `C:real^3->bool`]
      IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MP_TAC(ISPECL [`(:real^3) DIFF UNIONS (s:(real^3->bool)->bool)`; `C':real^3->bool`]
      IN_COMPONENTS_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MP_TAC(ISPEC `(:real^3) DIFF UNIONS (s:(real^3->bool)->bool)` UNIONS_COMPONENTS) THEN
    ASM_REWRITE_TAC[UNIONS_2] THEN DISCH_THEN(ACCEPT_TAC o SYM);
    REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[CLOSURE_UNION_FRONTIER] THEN ASM_REWRITE_TAC[]]);;

let MOI_S6CT_SIDE_IO = prove
 (`!(w:(real^3->bool)->bool) s.
     MOISE_266_STATEMENT /\ moi_s6ct_setting w s
     ==> moi_s6ct_side w s (inside (UNIONS s)) (outside (UNIONS s)) /\
         moi_s6ct_side w s (outside (UNIONS s)) (inside (UNIONS s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`] MOI_S6CT_SIDES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_s6ct_side (w:(real^3->bool)->bool) s
                  (inside (UNIONS s)) (outside (UNIONS s))` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s6ct_side]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_S6CT_SIDE_SYM]);;

let MOI_S6CT_SIDE_CONN = prove
 (`!(w:(real^3->bool)->bool) s C C' k.
     moi_s6ct_side w s C C' /\ connected k /\ ~(k = {}) /\ DISJOINT k (UNIONS s)
     ==> k SUBSET C \/ k SUBSET C'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SIDE_FACTS) THEN
  SUBGOAL_THEN `(k:real^3->bool) SUBSET (:real^3) DIFF UNIONS s` ASSUME_TAC THENL
   [UNDISCH_TAC `DISJOINT (k:real^3->bool) (UNIONS s)` THEN SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~(k:real^3->bool = {})` THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `x:real^3`) THEN
  SUBGOAL_THEN `(x:real^3) IN C \/ x IN C'` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(x:real^3) IN k`; `(k:real^3->bool) SUBSET (:real^3) DIFF UNIONS s`;
      `(C:real^3->bool) UNION C' = (:real^3) DIFF UNIONS s`] THEN
    SET_TAC[];
    DISJ1_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `(:real^3) DIFF UNIONS (s:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN MATCH_MP_TAC COMPONENTS_MAXIMAL THEN
    EXISTS_TAC `(:real^3) DIFF UNIONS (s:(real^3->bool)->bool)` THEN
    ASM_REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:real^3` THEN ASM_REWRITE_TAC[]]);;

let MOI_S6CT_INTERIOR_S = prove
 (`!(w:(real^3->bool)->bool) s C C'.
     moi_s6ct_side w s C C' ==> interior (UNIONS s) = {}`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SIDE_FACTS) THEN
  MP_TAC(ISPECL [`interior (UNIONS (s:(real^3->bool)->bool))`; `C:real^3->bool`]
    OPEN_INTER_CLOSURE_EQ_EMPTY) THEN
  REWRITE_TAC[OPEN_INTERIOR] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `UNIONS (s:(real^3->bool)->bool)` INTERIOR_SUBSET) THEN
  UNDISCH_TAC `DISJOINT (C:real^3->bool) (UNIONS s)` THEN
  SET_TAC[]);;

let MOI_S6CT_TET_NOT_S = prove
 (`!(w:(real^3->bool)->bool) s C C' q.
     moi_s6ct_side w s C C' /\ q IN w /\ aff_dim q = &3 ==> ~(q IN s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S6CT_INTERIOR_S) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_side]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SETTING_FACTS) THEN
  SUBGOAL_THEN `convex (q:real^3->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(interior (q:real^3->bool) = {})` MP_TAC THENL
   [MP_TAC(ISPEC `q:real^3->bool` AFF_DIM_NONEMPTY_INTERIOR_EQ) THEN
    ASM_REWRITE_TAC[DIMINDEX_3];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  MATCH_MP_TAC(SET_RULE `!a b:real^3->bool. a SUBSET b /\ b = {} ==> a = {}`) THEN
  EXISTS_TAC `interior (UNIONS (s:(real^3->bool)->bool))` THEN
  CONJ_TAC THENL [ALL_TAC; FIRST_ASSUM ACCEPT_TAC] THEN
  MATCH_MP_TAC SUBSET_INTERIOR THEN
  UNDISCH_TAC `(q:real^3->bool) IN s` THEN SET_TAC[]);;

let MOI_S6CT_SIMPLEX_SIDE = prove
 (`!(w:(real^3->bool)->bool) s C C' q.
     moi_s6ct_side w s C C' /\ q IN w /\ ~(q IN s)
     ==> ~(relative_interior q = {}) /\
         ((relative_interior q SUBSET C /\ q SUBSET C UNION UNIONS s) \/
          (relative_interior q SUBSET C' /\ q SUBSET C' UNION UNIONS s))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SIDE_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_side]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SETTING_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_setting]) THEN
  SUBGOAL_THEN `convex (q:real^3->bool) /\ closed q` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(q:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior (q:real^3->bool) = {})` ASSUME_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `relative_interior (q:real^3->bool)`]
    MOI_S6CT_SIDE_CONN) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CONNECTED; CONVEX_RELATIVE_INTERIOR] THEN
    MATCH_MP_TAC MOI_S6CT_RELINT_OFF THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3->bool) SUBSET closure (relative_interior q)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_SUBSET]; ALL_TAC] THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC SUBSET_TRANS `closure (relative_interior (q:real^3->bool))` THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC SUBSET_TRANS `closure (C:real^3->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[SUBSET_REFL]];
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    TRANS_TAC SUBSET_TRANS `closure (relative_interior (q:real^3->bool))` THEN
    ASM_REWRITE_TAC[] THEN
    TRANS_TAC SUBSET_TRANS `closure (C':real^3->bool)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_CLOSURE THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[SUBSET_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* The part of w on the side C: the simplices missing C'.  A                *)
(* subcomplex with polyhedron UNIONS w DIFF C', containing s; at a vertex  *)
(* off |s| (then in C) its link is the link in w.                          *)
(* ------------------------------------------------------------------------- *)

let moi_s6ct_part = new_definition
 `moi_s6ct_part (w:(real^3->bool)->bool) (C':real^3->bool) =
    {q | q IN w /\ DISJOINT q C'}`;;

let MOI_S6CT_IN_PART = prove
 (`!(w:(real^3->bool)->bool) C' q.
     q IN moi_s6ct_part w C' <=> q IN w /\ DISJOINT q C'`,
  REWRITE_TAC[moi_s6ct_part; IN_ELIM_THM]);;

let MOI_S6CT_PART_BASIC = prove
 (`!(w:(real^3->bool)->bool) s C C'.
     moi_s6ct_side w s C C'
     ==> simplicial_subcomplex (moi_s6ct_part w C') w /\
         lf_simplicial_complex (moi_s6ct_part w C') /\
         FINITE (moi_s6ct_part w C') /\
         s SUBSET moi_s6ct_part w C' /\
         moi_s6ct_part w C' SUBSET w /\
         UNIONS (moi_s6ct_part w C') = UNIONS w DIFF C'`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SIDE_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_side]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SETTING_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_setting]) THEN
  SUBGOAL_THEN `moi_s6ct_part (w:(real^3->bool)->bool) C' SUBSET w` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_S6CT_IN_PART] THEN MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!q f:real^3->bool. q IN moi_s6ct_part w C' /\ f face_of q
                                   ==> f IN moi_s6ct_part w C'` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S6CT_IN_PART] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[MOI_FM3_LF_FACE];
      FIRST_ASSUM(ASSUME_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
      UNDISCH_TAC `DISJOINT (q:real^3->bool) C'` THEN
      UNDISCH_TAC `(f:real^3->bool) SUBSET q` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:(real^3->bool)->bool) SUBSET moi_s6ct_part w C'` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; MOI_S6CT_IN_PART] THEN X_GEN_TAC `q:real^3->bool` THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^3->bool) SUBSET UNIONS s` MP_TAC THENL
     [UNDISCH_TAC `(q:real^3->bool) IN s` THEN SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (C':real^3->bool) (UNIONS s)` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[simplicial_subcomplex] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBCOMPLEX THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; IN_DIFF; MOI_S6CT_IN_PART] THEN
    X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `DISJOINT (q:real^3->bool) C'` THEN
    UNDISCH_TAC `(x:real^3) IN q` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC ASSUME_TAC) THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `DISJOINT (q:real^3->bool) C'` THENL
   [EXISTS_TAC `q:real^3->bool` THEN ASM_REWRITE_TAC[MOI_S6CT_IN_PART]; ALL_TAC] THEN
  SUBGOAL_THEN `~((q:real^3->bool) IN s)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~DISJOINT (q:real^3->bool) C'` THEN REWRITE_TAC[] THEN
    ASM_MESON_TAC[MOI_S6CT_IN_PART; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `q:real^3->bool`] MOI_S6CT_SIMPLEX_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [MATCH_MP_TAC(TAUT `F ==> p`) THEN
    UNDISCH_TAC `~DISJOINT (q:real^3->bool) C'` THEN
    UNDISCH_TAC `(q:real^3->bool) SUBSET C UNION UNIONS s` THEN
    UNDISCH_TAC `DISJOINT (C:real^3->bool) C'` THEN
    UNDISCH_TAC `DISJOINT (C':real^3->bool) (UNIONS s)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^3) IN UNIONS s` MP_TAC THENL
   [UNDISCH_TAC `(q:real^3->bool) SUBSET C' UNION UNIONS s` THEN
    UNDISCH_TAC `(x:real^3) IN q` THEN UNDISCH_TAC `~((x:real^3) IN C')` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS] THEN MATCH_MP_TAC MONO_EXISTS THEN
  X_GEN_TAC `r:real^3->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[SUBSET]);;

let MOI_S6CT_LINK_OFF = prove
 (`!(w:(real^3->bool)->bool) s C C' v.
     moi_s6ct_side w s C C' /\ {v} IN moi_s6ct_part w C' /\ ~(v IN UNIONS s)
     ==> simplicial_link (moi_s6ct_part w C') v = simplicial_link w v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SIDE_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_PART_BASIC) THEN
  SUBGOAL_THEN `(v:real^3) IN C` ASSUME_TAC THENL
   [UNDISCH_TAC `{v:real^3} IN moi_s6ct_part w C'` THEN REWRITE_TAC[MOI_S6CT_IN_PART] THEN
    UNDISCH_TAC `~((v:real^3) IN UNIONS s)` THEN
    UNDISCH_TAC `(C:real^3->bool) UNION C' = (:real^3) DIFF UNIONS s` THEN SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FBC_LINK_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; simplicial_link; IN_ELIM_THM] THEN
  X_GEN_TAC `q:real^3->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(t:real^3->bool) IN moi_s6ct_part w C'` ASSUME_TAC THENL
   [REWRITE_TAC[MOI_S6CT_IN_PART] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((t:real^3->bool) IN s)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((v:real^3) IN UNIONS s)` THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                   `C':real^3->bool`; `t:real^3->bool`] MOI_S6CT_SIMPLEX_SIDE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [UNDISCH_TAC `(t:real^3->bool) SUBSET C UNION UNIONS s` THEN
      UNDISCH_TAC `DISJOINT (C:real^3->bool) C'` THEN
      UNDISCH_TAC `DISJOINT (C':real^3->bool) (UNIONS s)` THEN SET_TAC[];
      UNDISCH_TAC `(t:real^3->bool) SUBSET C' UNION UNIONS s` THEN
      UNDISCH_TAC `(v:real^3) IN t` THEN UNDISCH_TAC `(v:real^3) IN C` THEN
      UNDISCH_TAC `~((v:real^3) IN UNIONS s)` THEN
      UNDISCH_TAC `DISJOINT (C:real^3->bool) C'` THEN SET_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex];
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Triangles of s: a point of the relative interior is interior in |w|      *)
(* (not on Bd w) and in the frontier of both sides, so the tetrahedra of w  *)
(* at the triangle (one or two, MOI_FTD_TRIANGLE_COFACES) are exactly two,  *)
(* one on each side.  Off s the tetrahedra of the part are those of w.      *)
(* ------------------------------------------------------------------------- *)

let MOI_S6CT_LOCAL_TETS = prove
 (`!(w:(real^3->bool)->bool) x.
     FINITE w /\ combinatorial_manifold_with_boundary 3 w
     ==> ?e. &0 < e /\
             !y. y IN UNIONS w /\ dist(x,y) < e
                 ==> ?R. R IN w /\ aff_dim R = &3 /\ x IN R /\ y IN R`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (w:(real^3->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary]; ALL_TAC] THEN
  SUBGOAL_THEN
   `closed (UNIONS {R:real^3->bool | R IN w /\ aff_dim R = &3 /\ ~(x IN R)})`
  MP_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN
      ASM_MESON_TAC[MOI_FM3_LF_COMPACT; COMPACT_IMP_CLOSED]];
    ALL_TAC] THEN
  REWRITE_TAC[closed; OPEN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `e:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `y:real^3` THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^3) IN UNIONS w` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `q:real^3->bool`] MOI_FBC_CMWB3_PURE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(y:real^3) IN q` THEN SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `R:real^3->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^3) IN R` ASSUME_TAC THENL
   [UNDISCH_TAC `(y:real^3) IN q` THEN UNDISCH_TAC `(q:real^3->bool) SUBSET R` THEN
    SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  UNDISCH_TAC `ball(x:real^3,e) SUBSET
               (:real^3) DIFF UNIONS {R | R IN w /\ aff_dim R = &3 /\ ~(x IN R)}` THEN
  REWRITE_TAC[SUBSET; IN_BALL; IN_DIFF; IN_UNIV; IN_UNIONS; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `y:real^3`) THEN ASM_REWRITE_TAC[] THEN
  EXISTS_TAC `R:real^3->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S6CT_TRI_TET_AT = prove
 (`!(w:(real^3->bool)->bool) s C C' t.
     moi_s6ct_side w s C C' /\ t IN s /\ aff_dim t = &2
     ==> ?R. R IN w /\ aff_dim R = &3 /\ t SUBSET R /\
             ~(relative_interior R = {}) /\
             relative_interior R SUBSET C /\ R SUBSET C UNION UNIONS s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SIDE_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_side]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SETTING_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_setting]) THEN
  SUBGOAL_THEN `(t:real^3->bool) IN w` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `convex (t:real^3->bool) /\ ~(t = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim({}:real^3->bool) = &2` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?p:real^3. p IN relative_interior t` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEMBER_NOT_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN t /\ p IN UNIONS s /\ p IN UNIONS w` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(p:real^3) IN relative_interior t` THEN
    UNDISCH_TAC `(t:real^3->bool) IN s` THEN
    UNDISCH_TAC `UNIONS s SUBSET UNIONS (w:(real^3->bool)->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3) IN interior (UNIONS w)` MP_TAC THENL
   [MATCH_MP_TAC MOI_FM3_NOT_CB_INTERIOR THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `DISJOINT (UNIONS s) (complex_boundary (w:(real^3->bool)->bool))` THEN
    UNDISCH_TAC `(p:real^3) IN UNIONS s` THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[IN_INTERIOR] THEN DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `p:real^3`] MOI_S6CT_LOCAL_TETS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "loc"))) THEN
  SUBGOAL_THEN `(p:real^3) IN closure C` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_UNION]; ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN DISCH_THEN(MP_TAC o SPEC `min r e:real`) THEN
  ASM_REWRITE_TAC[REAL_LT_MIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^3) IN UNIONS w` ASSUME_TAC THENL
   [UNDISCH_TAC `ball(p:real^3,r) SUBSET UNIONS w` THEN REWRITE_TAC[SUBSET; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "loc" (MP_TAC o SPEC `y:real^3`) THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[DIST_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `R:real^3->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(t:real^3->bool) SUBSET R` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`w:(real^3->bool)->bool`; `p:real^3`] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `R:real^3->bool`] MOI_S6CT_SIMPLEX_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S6CT_TET_NOT_S THEN
    MAP_EVERY EXISTS_TAC [`w:(real^3->bool)->bool`; `C:real^3->bool`; `C':real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(R:real^3->bool) SUBSET C' UNION UNIONS s` THEN
  UNDISCH_TAC `(y:real^3) IN R` THEN UNDISCH_TAC `(y:real^3) IN C` THEN
  UNDISCH_TAC `DISJOINT (C:real^3->bool) C'` THEN
  UNDISCH_TAC `DISJOINT (C:real^3->bool) (UNIONS s)` THEN SET_TAC[]);;

let MOI_S6CT_TRI_SIDES = prove
 (`!(w:(real^3->bool)->bool) s C C' t.
     moi_s6ct_side w s C C' /\ t IN s /\ aff_dim t = &2
     ==> ?R R'. R IN w /\ aff_dim R = &3 /\ t SUBSET R /\
                ~(relative_interior R = {}) /\
                relative_interior R SUBSET C /\ R SUBSET C UNION UNIONS s /\
                R' IN w /\ aff_dim R' = &3 /\ t SUBSET R' /\
                ~(relative_interior R' = {}) /\
                relative_interior R' SUBSET C' /\ R' SUBSET C' UNION UNIONS s /\
                ~(R = R') /\
                {r | r IN w /\ aff_dim r = &3 /\ t SUBSET r} = {R, R'}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S6CT_SIDE_SYM) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `t:real^3->bool`] MOI_S6CT_TRI_TET_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C':real^3->bool`;
                 `C:real^3->bool`; `t:real^3->bool`] MOI_S6CT_TRI_TET_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R':real^3->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`R:real^3->bool`; `R':real^3->bool`] THEN ASM_REWRITE_TAC[] THEN
  STRIP_ASSUME_TAC(MATCH_MP MOI_S6CT_SIDE_FACTS
    (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C C'`)) THEN
  STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [moi_s6ct_side]
    (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C C'`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_setting]) THEN
  SUBGOAL_THEN `~(R:real^3->bool = R')` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `~(relative_interior (R':real^3->bool) = {})` THEN
    UNDISCH_TAC `relative_interior (R':real^3->bool) SUBSET C` THEN
    UNDISCH_TAC `relative_interior (R':real^3->bool) SUBSET C'` THEN
    UNDISCH_TAC `DISJOINT (C:real^3->bool) C'` THEN SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `t:real^3->bool`] MOI_FTD_TRIANGLE_COFACES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `{R:real^3->bool, R'} SUBSET {r | r IN w /\ aff_dim r = &3 /\ t SUBSET r}`
  ASSUME_TAC THENL
   [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {R:real^3->bool, R'} = 2` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD {R:real^3->bool, R'} <=
    CARD {r | r IN w /\ aff_dim (r:real^3->bool) = &3 /\ t SUBSET r}`
  ASSUME_TAC THENL [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN ASM_REWRITE_TAC[] THEN
  ASM_ARITH_TAC);;

let MOI_S6CT_TRI_PART = prove
 (`!(w:(real^3->bool)->bool) s C C' t.
     moi_s6ct_side w s C C' /\ t IN s /\ aff_dim t = &2
     ==> CARD {r | r IN moi_s6ct_part w C' /\ aff_dim r = &3 /\ t SUBSET r} = 1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `t:real^3->bool`] MOI_S6CT_TRI_SIDES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->bool` (X_CHOOSE_THEN `R':real^3->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SIDE_FACTS) THEN
  SUBGOAL_THEN
   `{r | r IN moi_s6ct_part w C' /\ aff_dim r = &3 /\ t SUBSET r} = {R:real^3->bool}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING; MOI_S6CT_IN_PART] THEN
    X_GEN_TAC `r:real^3->bool` THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(r:real^3->bool) = R \/ r = R'` MP_TAC THENL
       [MP_TAC(SPEC `r:real^3->bool` (GEN_REWRITE_RULE I [EXTENSION]
          (ASSUME `{r | r IN w /\ aff_dim r = &3 /\ t SUBSET r} = {R:real^3->bool, R'}`))) THEN
        ASM_REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY];
        ALL_TAC] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `DISJOINT (r:real^3->bool) C'` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `R':real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `~(relative_interior (R':real^3->bool) = {})` THEN
      UNDISCH_TAC `relative_interior (R':real^3->bool) SUBSET C'` THEN SET_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(R:real^3->bool) SUBSET C UNION UNIONS s` THEN
      UNDISCH_TAC `DISJOINT (C:real^3->bool) C'` THEN
      UNDISCH_TAC `DISJOINT (C':real^3->bool) (UNIONS s)` THEN SET_TAC[]];
    REWRITE_TAC[CARD_SING]]);;

let MOI_S6CT_TRI_OFF = prove
 (`!(w:(real^3->bool)->bool) s C C' t.
     moi_s6ct_side w s C C' /\ t IN moi_s6ct_part w C' /\ ~(t IN s)
     ==> {r | r IN moi_s6ct_part w C' /\ aff_dim r = &3 /\ t SUBSET r} =
         {r | r IN w /\ aff_dim r = &3 /\ t SUBSET r}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SIDE_FACTS) THEN
  UNDISCH_TAC `(t:real^3->bool) IN moi_s6ct_part w C'` THEN
  REWRITE_TAC[MOI_S6CT_IN_PART] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `t:real^3->bool`] MOI_S6CT_SIMPLEX_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    UNDISCH_TAC `DISJOINT (t:real^3->bool) C'` THEN
    MP_TAC(ISPEC `t:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `relative_interior (t:real^3->bool) SUBSET C'` THEN
    UNDISCH_TAC `~(relative_interior (t:real^3->bool) = {})` THEN SET_TAC[]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; MOI_S6CT_IN_PART] THEN
  X_GEN_TAC `r:real^3->bool` THEN EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `r:real^3->bool`] MOI_S6CT_SIMPLEX_SIDE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S6CT_TET_NOT_S THEN
    MAP_EVERY EXISTS_TAC [`w:(real^3->bool)->bool`; `C:real^3->bool`; `C':real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `(r:real^3->bool) SUBSET C UNION UNIONS s` THEN
    UNDISCH_TAC `DISJOINT (C:real^3->bool) C'` THEN
    UNDISCH_TAC `DISJOINT (C':real^3->bool) (UNIONS s)` THEN SET_TAC[];
    MATCH_MP_TAC(TAUT `F ==> p`) THEN
    MP_TAC(ISPEC `t:real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(t:real^3->bool) SUBSET r` THEN
    UNDISCH_TAC `(r:real^3->bool) SUBSET C' UNION UNIONS s` THEN
    UNDISCH_TAC `relative_interior (t:real^3->bool) SUBSET C` THEN
    UNDISCH_TAC `~(relative_interior (t:real^3->bool) = {})` THEN
    UNDISCH_TAC `DISJOINT (C:real^3->bool) C'` THEN
    UNDISCH_TAC `DISJOINT (C:real^3->bool) (UNIONS s)` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The link of a vertex v of |s| in the part on the side C: a PL disk.      *)
(* The link S of v in w is a PL 2-sphere (v is not on Bd w), the link J of  *)
(* v in s a PL circle in it; S is covered by the links on the two sides,    *)
(* which meet inside J (a point of both lies in the relative interior of a  *)
(* link simplex whose cone from v lies on both sides, hence in s); each     *)
(* side has a point off the other (the tetrahedra at a triangle of s at v). *)
(* MOI_S4O_SPHERE_PIECE then makes the link on the side C a PL disk.        *)
(* ------------------------------------------------------------------------- *)

let MOI_S6CT_VERTEX_S = prove
 (`!(w:(real^3->bool)->bool) s v.
     lf_simplicial_complex w /\ simplicial_subcomplex s w /\ {v} IN w /\
     v IN UNIONS s
     ==> {v} IN s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(v:real^3) IN UNIONS s` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(r:real^3->bool) IN w` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `{v:real^3}`; `r:real^3->bool`]
    MOI_FM3_LF_INTER) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{v:real^3} INTER r = {v}` SUBST1_TAC THENL
   [UNDISCH_TAC `(v:real^3) IN r` THEN SET_TAC[]; ALL_TAC] THEN
  STRIP_TAC THEN
  UNDISCH_TAC `simplicial_subcomplex (s:(real^3->bool)->bool) w` THEN
  REWRITE_TAC[simplicial_subcomplex] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
  EXISTS_TAC `r:real^3->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_S6CT_JOIN_PART = prove
 (`!(w:(real^3->bool)->bool) C' v q.
     lf_simplicial_complex w /\ q IN simplicial_link (moi_s6ct_part w C') v
     ==> DISJOINT (convex hull (v INSERT q)) C'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FM3_LINK_IN) THEN
  UNDISCH_TAC `(t:real^3->bool) IN moi_s6ct_part w C'` THEN
  REWRITE_TAC[MOI_S6CT_IN_PART] THEN STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE
   `!a b c:real^3->bool. a SUBSET b /\ DISJOINT b c ==> DISJOINT a c`) THEN
  EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HULL_MINIMAL THEN
  REWRITE_TAC[INSERT_SUBSET] THEN ASM_SIMP_TAC[FACE_OF_IMP_SUBSET] THEN
  MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
  ASM_REWRITE_TAC[]);;

let MOI_S6CT_PART_LINK_IN = prove
 (`!(w:(real^3->bool)->bool) C' v q.
     lf_simplicial_complex w /\ {v} IN w /\ q IN simplicial_link w v /\
     DISJOINT (convex hull (v INSERT q)) C'
     ==> q IN simplicial_link (moi_s6ct_part w C') v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `v:real^3`; `q:real^3->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FM3_LINK_IN) THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM; MOI_S6CT_IN_PART] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `DISJOINT (convex hull (v INSERT q)) (C':real^3->bool)` THEN
    UNDISCH_TAC `(q:real^3->bool) SUBSET convex hull (v INSERT q)` THEN SET_TAC[];
    EXISTS_TAC `convex hull (v INSERT q):real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_S6CT_S_LINK_IN = prove
 (`!(w:(real^3->bool)->bool) s v q.
     lf_simplicial_complex w /\ simplicial_subcomplex s w /\ {v} IN w /\
     q IN simplicial_link w v /\ convex hull (v INSERT q) IN s
     ==> q IN simplicial_link s v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `v:real^3`; `q:real^3->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FM3_LINK_IN) THEN
  SUBGOAL_THEN `(q:real^3->bool) face_of convex hull (v INSERT q)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex];
    EXISTS_TAC `convex hull (v INSERT q):real^3->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_S6CT_S_LINK_JOIN = prove
 (`!(w:(real^3->bool)->bool) s v q.
     lf_simplicial_complex w /\ simplicial_subcomplex s w /\
     q IN simplicial_link s v
     ==> convex hull (v INSERT q) SUBSET UNIONS s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FM3_LINK_IN) THEN
  TRANS_TAC SUBSET_TRANS `t:real^3->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[INSERT_SUBSET] THEN ASM_SIMP_TAC[FACE_OF_IMP_SUBSET] THEN
    MATCH_MP_TAC MOI_FM3_LF_CONVEX THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
    UNDISCH_TAC `(t:real^3->bool) IN s` THEN SET_TAC[]]);;

let MOI_S6CT_LINK_COVER = prove
 (`!(w:(real^3->bool)->bool) s C C' v.
     moi_s6ct_side w s C C' /\ {v} IN w
     ==> !q. q IN simplicial_link w v
             ==> q IN simplicial_link (moi_s6ct_part w C') v \/
                 q IN simplicial_link (moi_s6ct_part w C) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN
  STRIP_ASSUME_TAC(MATCH_MP MOI_S6CT_SIDE_FACTS
    (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C C'`)) THEN
  STRIP_ASSUME_TAC(MATCH_MP MOI_S6CT_PART_BASIC
    (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C C'`)) THEN
  STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [moi_s6ct_side]
    (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C C'`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SETTING_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_setting]) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `v:real^3`; `q:real^3->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  ASM_CASES_TAC `convex hull (v INSERT q) IN (s:(real^3->bool)->bool)` THENL
   [DISJ1_TAC THEN
    MATCH_MP_TAC(SET_RULE
     `!a b (x:real^3->bool). a SUBSET b /\ x IN a ==> x IN b`) THEN
    EXISTS_TAC `simplicial_link (s:(real^3->bool)->bool) v` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FBC_LINK_SUBSET THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC MOI_S6CT_S_LINK_IN THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `convex hull (v INSERT q):real^3->bool`]
    MOI_S6CT_SIMPLEX_SIDE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN MATCH_MP_TAC MOI_S6CT_PART_LINK_IN THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `convex hull (v INSERT q) SUBSET (C:real^3->bool) UNION UNIONS s` THEN
    UNDISCH_TAC `DISJOINT (C:real^3->bool) C'` THEN
    UNDISCH_TAC `DISJOINT (C':real^3->bool) (UNIONS s)` THEN SET_TAC[];
    DISJ2_TAC THEN MATCH_MP_TAC MOI_S6CT_PART_LINK_IN THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `convex hull (v INSERT q) SUBSET (C':real^3->bool) UNION UNIONS s` THEN
    UNDISCH_TAC `DISJOINT (C:real^3->bool) C'` THEN
    UNDISCH_TAC `DISJOINT (C:real^3->bool) (UNIONS s)` THEN SET_TAC[]]);;

let MOI_S6CT_LINK_MEET = prove
 (`!(w:(real^3->bool)->bool) s C C' v.
     moi_s6ct_side w s C C' /\ {v} IN w
     ==> UNIONS (simplicial_link (moi_s6ct_part w C') v) INTER
         UNIONS (simplicial_link (moi_s6ct_part w C) v)
         SUBSET UNIONS (simplicial_link s v)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(MATCH_MP MOI_S6CT_SIDE_FACTS
    (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C C'`)) THEN
  STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [moi_s6ct_side]
    (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C C'`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SETTING_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_setting]) THEN
  SUBGOAL_THEN
   `simplicial_link (moi_s6ct_part w C') (v:real^3) SUBSET simplicial_link w v /\
    simplicial_link (moi_s6ct_part w C) (v:real^3) SUBSET simplicial_link w v`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FBC_LINK_SUBSET THEN
    REWRITE_TAC[SUBSET; MOI_S6CT_IN_PART] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS] THEN X_GEN_TAC `y:real^3` THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:real^3->bool` STRIP_ASSUME_TAC)
                             (X_CHOOSE_THEN `p:real^3->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(q:real^3->bool) IN simplicial_link w v /\
                (p:real^3->bool) IN simplicial_link w v` STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`(q:real^3->bool) IN simplicial_link (moi_s6ct_part w C') v`;
      `(p:real^3->bool) IN simplicial_link (moi_s6ct_part w C) v`;
      `simplicial_link (moi_s6ct_part w C') (v:real^3) SUBSET simplicial_link w v`;
      `simplicial_link (moi_s6ct_part w C) (v:real^3) SUBSET simplicial_link w v`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^3->bool) IN w` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LINK_IN]; ALL_TAC] THEN
  STRIP_ASSUME_TAC(MATCH_MP MOI_FM3_LINK_IN
    (ASSUME `(q:real^3->bool) IN simplicial_link w v`)) THEN
  MP_TAC(ISPECL [`q:real^3->bool`; `y:real^3`] IN_RELATIVE_INTERIOR_OF_FACE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^3->bool) SUBSET q` ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^3) IN f` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->bool) IN w` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LF_FACE]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->bool) IN simplicial_link w v` ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `~((v:real^3) IN q)` THEN UNDISCH_TAC `(f:real^3->bool) SUBSET q` THEN
      SET_TAC[];
      EXISTS_TAC `t:real^3->bool` THEN ASM_MESON_TAC[FACE_OF_TRANS]];
    ALL_TAC] THEN
  ASM_CASES_TAC `convex hull (v INSERT f) IN (s:(real^3->bool)->bool)` THENL
   [EXISTS_TAC `f:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_S6CT_S_LINK_IN THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `F ==> p`) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `v:real^3`; `f:real^3->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `DISJOINT (convex hull (v INSERT f)) (C':real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!a b c:real^3->bool. a SUBSET b /\ DISJOINT b c ==> DISJOINT a c`) THEN
    EXISTS_TAC `convex hull (v INSERT q):real^3->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN
      UNDISCH_TAC `(f:real^3->bool) SUBSET q` THEN SET_TAC[];
      MATCH_MP_TAC MOI_S6CT_JOIN_PART THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^3->bool) SUBSET p` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`w:(real^3->bool)->bool`; `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (convex hull (v INSERT f)) (C:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `!a b c:real^3->bool. a SUBSET b /\ DISJOINT b c ==> DISJOINT a c`) THEN
    EXISTS_TAC `convex hull (v INSERT p):real^3->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN
      UNDISCH_TAC `(f:real^3->bool) SUBSET p` THEN SET_TAC[];
      MATCH_MP_TAC MOI_S6CT_JOIN_PART THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `convex hull (v INSERT f):real^3->bool`]
    MOI_S6CT_SIMPLEX_SIDE) THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPEC `convex hull (v INSERT f):real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC `DISJOINT (convex hull (v INSERT f)) (C:real^3->bool)` THEN
  UNDISCH_TAC `DISJOINT (convex hull (v INSERT f)) (C':real^3->bool)` THEN
  SET_TAC[]);;

let MOI_S6CT_LINK_TET = prove
 (`!(w:(real^3->bool)->bool) s C C' v.
     moi_s6ct_side w s C C' /\ {v} IN w /\ v IN UNIONS s
     ==> ?y. y IN UNIONS (simplicial_link (moi_s6ct_part w C') v) /\
             ~(y IN UNIONS (simplicial_link (moi_s6ct_part w C) v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  STRIP_ASSUME_TAC(MATCH_MP MOI_S6CT_SIDE_FACTS
    (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C C'`)) THEN
  STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [moi_s6ct_side]
    (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C C'`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SETTING_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_setting]) THEN
  SUBGOAL_THEN `{v:real^3} IN s` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S6CT_VERTEX_S THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(real^3->bool)->bool`; `{v:real^3}`] MOI_FSA_CM_PURE) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `t:real^3->bool`] MOI_S6CT_TRI_TET_AT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `R:real^3->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^3) IN R` ASSUME_TAC THENL
   [UNDISCH_TAC `{v:real^3} SUBSET t` THEN UNDISCH_TAC `(t:real^3->bool) SUBSET R` THEN
    SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `v:real^3`; `R:real^3->bool`]
    MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^3->bool` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `v:real^3`; `q:real^3->bool`]
    MOI_FM3_LINK_JOIN) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(q:real^3->bool) IN simplicial_link (moi_s6ct_part w C') v` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S6CT_PART_LINK_IN THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `convex hull (v INSERT q) SUBSET (C:real^3->bool) UNION UNIONS s` THEN
    UNDISCH_TAC `DISJOINT (C:real^3->bool) C'` THEN
    UNDISCH_TAC `DISJOINT (C':real^3->bool) (UNIONS s)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3->bool) IN w /\ convex q` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FM3_LINK_IN]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (q:real^3->bool) = &2` ASSUME_TAC THENL
   [UNDISCH_TAC `aff_dim (convex hull (v INSERT q)) = aff_dim (q:real^3->bool) + &1` THEN
    UNDISCH_TAC `aff_dim (convex hull (v INSERT q:real^3->bool)) = &3` THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(q:real^3->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim ({}:real^3->bool) = &2` THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^3. y IN relative_interior q` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MEMBER_NOT_EMPTY; RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  EXISTS_TAC `y:real^3` THEN CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `q:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; NOT_EXISTS_THM] THEN X_GEN_TAC `p:real^3->bool` THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(p:real^3->bool) IN w` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`moi_s6ct_part w (C:real^3->bool)`; `v:real^3`; `p:real^3->bool`]
      MOI_FM3_LINK_IN) THEN
    ASM_REWRITE_TAC[MOI_S6CT_IN_PART] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^3->bool) SUBSET p` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC [`w:(real^3->bool)->bool`; `y:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `DISJOINT (convex hull (v INSERT p)) (C:real^3->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S6CT_JOIN_PART THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull (v INSERT q) SUBSET convex hull (v INSERT (p:real^3->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN UNDISCH_TAC `(q:real^3->bool) SUBSET p` THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `convex hull (v INSERT q):real^3->bool` RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC `~(relative_interior (convex hull (v INSERT q)) = ({}:real^3->bool))` THEN
  UNDISCH_TAC `relative_interior (convex hull (v INSERT q)) SUBSET (C:real^3->bool)` THEN
  UNDISCH_TAC `convex hull (v INSERT q) SUBSET convex hull (v INSERT (p:real^3->bool))` THEN
  UNDISCH_TAC `DISJOINT (convex hull (v INSERT p)) (C:real^3->bool)` THEN
  SET_TAC[]);;

let MOI_S6CT_LINK_ON = prove
 (`!(w:(real^3->bool)->bool) s C C' v.
     moi_s6ct_side w s C C' /\ {v} IN moi_s6ct_part w C' /\ v IN UNIONS s
     ==> pl_ball 2 (UNIONS (simplicial_link (moi_s6ct_part w C') v))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_S6CT_SIDE_SYM) THEN
  STRIP_ASSUME_TAC(MATCH_MP MOI_S6CT_SIDE_FACTS
    (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C C'`)) THEN
  STRIP_ASSUME_TAC(GEN_REWRITE_RULE I [moi_s6ct_side]
    (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C C'`)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SETTING_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_setting]) THEN
  SUBGOAL_THEN `moi_s6ct_part w C' SUBSET (w:(real^3->bool)->bool) /\
                moi_s6ct_part w C SUBSET w /\
                s SUBSET moi_s6ct_part w C' /\ s SUBSET moi_s6ct_part w C`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(MATCH_MP MOI_S6CT_PART_BASIC
      (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C C'`)) THEN
    MP_TAC(MATCH_MP MOI_S6CT_PART_BASIC
      (ASSUME `moi_s6ct_side (w:(real^3->bool)->bool) s C' C`)) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^3} IN w` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^3} IN s` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_S6CT_VERTEX_S THEN EXISTS_TAC `w:(real^3->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (simplicial_link w (v:real^3)))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `v:real^3`] MOI_FM3_CB_VERTEX_CLASSIFY) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    UNDISCH_TAC `DISJOINT (UNIONS s) (complex_boundary (w:(real^3->bool)->bool))` THEN
    UNDISCH_TAC `(v:real^3) IN UNIONS s` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_sphere 1 (UNIONS (simplicial_link s (v:real^3)))` ASSUME_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold 2 (s:(real^3->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `simplicial_link s (v:real^3) SUBSET simplicial_link (moi_s6ct_part w C') v /\
    simplicial_link s (v:real^3) SUBSET simplicial_link (moi_s6ct_part w C) v /\
    simplicial_link (moi_s6ct_part w C') (v:real^3) SUBSET simplicial_link w v /\
    simplicial_link (moi_s6ct_part w C) (v:real^3) SUBSET simplicial_link w v`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_FBC_LINK_SUBSET THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (simplicial_link w (v:real^3))` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LINK_FINITE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `closed (UNIONS (simplicial_link (moi_s6ct_part w C') (v:real^3))) /\
    closed (UNIONS (simplicial_link (moi_s6ct_part w C) (v:real^3)))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THEN
    TRY(MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `simplicial_link w (v:real^3)` THEN
        ASM_REWRITE_TAC[] THEN NO_TAC) THEN
    X_GEN_TAC `q:real^3->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(q:real^3->bool) IN w` (fun th -> ASM_SIMP_TAC[th]) THEN
    ASM_MESON_TAC[SUBSET; MOI_FM3_LINK_IN];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `v:real^3`] MOI_S6CT_LINK_COVER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `v:real^3`] MOI_S6CT_LINK_MEET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `v:real^3`] MOI_S6CT_LINK_TET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y1:real^3` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C':real^3->bool`;
                 `C:real^3->bool`; `v:real^3`] MOI_S6CT_LINK_TET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y2:real^3` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `UNIONS (simplicial_link w (v:real^3)) SUBSET
    UNIONS (simplicial_link (moi_s6ct_part w C') v) UNION
    UNIONS (simplicial_link (moi_s6ct_part w C) v)`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `!q. q IN simplicial_link w (v:real^3)
          ==> q IN simplicial_link (moi_s6ct_part w C') v \/
              q IN simplicial_link (moi_s6ct_part w C) v` THEN
    REWRITE_TAC[SUBSET; IN_UNION; IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (simplicial_link s (v:real^3)) SUBSET
      UNIONS (simplicial_link (moi_s6ct_part w C') v) /\
    UNIONS (simplicial_link s (v:real^3)) SUBSET
      UNIONS (simplicial_link (moi_s6ct_part w C) v) /\
    UNIONS (simplicial_link (moi_s6ct_part w C') (v:real^3)) SUBSET
      UNIONS (simplicial_link w v) /\
    UNIONS (simplicial_link (moi_s6ct_part w C) (v:real^3)) SUBSET
      UNIONS (simplicial_link w v)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Lw = UNIONS (simplicial_link w (v:real^3))` THEN
  ABBREV_TAC `LP = UNIONS (simplicial_link (moi_s6ct_part w C') (v:real^3))` THEN
  ABBREV_TAC `LQ = UNIONS (simplicial_link (moi_s6ct_part w C) (v:real^3))` THEN
  ABBREV_TAC `J = UNIONS (simplicial_link s (v:real^3))` THEN
  SUBGOAL_THEN `closure (Lw DIFF LP) INTER LP SUBSET (J:real^3->bool)` ASSUME_TAC THENL
   [TRANS_TAC SUBSET_TRANS `LQ INTER LP:real^3->bool` THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `!a b c:real^3->bool. a SUBSET b ==> a INTER c SUBSET b INTER c`) THEN
      MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `Lw SUBSET LP UNION (LQ:real^3->bool)` THEN SET_TAC[];
      UNDISCH_TAC `LP INTER LQ SUBSET (J:real^3->bool)` THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(LP SUBSET (J:real^3->bool))` ASSUME_TAC THENL
   [UNDISCH_TAC `(y1:real^3) IN LP` THEN UNDISCH_TAC `~((y1:real^3) IN LQ)` THEN
    UNDISCH_TAC `J SUBSET (LQ:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(Lw SUBSET (LP:real^3->bool))` ASSUME_TAC THENL
   [UNDISCH_TAC `(y2:real^3) IN LQ` THEN UNDISCH_TAC `~((y2:real^3) IN LP)` THEN
    UNDISCH_TAC `LQ SUBSET (Lw:real^3->bool)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_cell_with_boundary 2 LP (J:real^3->bool)` MP_TAC THENL
   [MATCH_MP_TAC MOI_S4O_SPHERE_PIECE THEN EXISTS_TAC `Lw:real^3->bool` THEN
    ASM_REWRITE_TAC[];
    REWRITE_TAC[pl_cell_with_boundary; pl_ball] THEN MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The part on the side C is a combinatorial 3-manifold with boundary,      *)
(* its boundary is |s| together with the part of Bd w off C', and the cut.  *)
(* ------------------------------------------------------------------------- *)

let MOI_S6CT_PART_CMWB = prove
 (`!(w:(real^3->bool)->bool) s C C'.
     moi_s6ct_side w s C C'
     ==> combinatorial_manifold_with_boundary 3 (moi_s6ct_part w C')`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_PART_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_side]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_setting]) THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^3` THEN DISCH_TAC THEN
  ASM_CASES_TAC `(v:real^3) IN UNIONS s` THENL
   [DISJ2_TAC THEN MATCH_MP_TAC MOI_S6CT_LINK_ON THEN
    MAP_EVERY EXISTS_TAC [`s:(real^3->bool)->bool`; `C:real^3->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `v:real^3`] MOI_S6CT_LINK_OFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (w:(real^3->bool)->bool)` THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[SUBSET]);;

let MOI_S6CT_PART_BOUNDARY = prove
 (`!(w:(real^3->bool)->bool) s C C'.
     moi_s6ct_side w s C C'
     ==> complex_boundary (moi_s6ct_part w C') =
         (complex_boundary w DIFF C') UNION UNIONS s`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SIDE_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_PART_BASIC) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_side]) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_S6CT_SETTING_FACTS) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_s6ct_setting]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC LAND_CONV [complex_boundary] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^3` THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(t:real^3->bool) IN s` THENL
     [REWRITE_TAC[IN_UNION] THEN DISJ2_TAC THEN REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                   `C':real^3->bool`; `t:real^3->bool`] MOI_S6CT_TRI_OFF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> RULE_ASSUM_TAC(REWRITE_RULE[th])) THEN
    UNDISCH_TAC `(t:real^3->bool) IN moi_s6ct_part w C'` THEN
    REWRITE_TAC[MOI_S6CT_IN_PART] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_UNION; IN_DIFF] THEN DISJ1_TAC THEN CONJ_TAC THENL
     [REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `DISJOINT (t:real^3->bool) C'` THEN
      UNDISCH_TAC `(x:real^3) IN t` THEN SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_UNION; IN_DIFF] THEN X_GEN_TAC `x:real^3` THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `(x:real^3) IN complex_boundary w` THEN
    REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(t:real^3->bool) SUBSET complex_boundary w` ASSUME_TAC THENL
     [REWRITE_TAC[complex_boundary] THEN
      MATCH_MP_TAC(SET_RULE `!a:real^3->bool f. a IN f ==> a SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `DISJOINT (t:real^3->bool) (UNIONS s)` ASSUME_TAC THENL
     [UNDISCH_TAC `(t:real^3->bool) SUBSET complex_boundary w` THEN
      UNDISCH_TAC `DISJOINT (UNIONS s) (complex_boundary (w:(real^3->bool)->bool))` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((t:real^3->bool) IN s)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `DISJOINT (t:real^3->bool) (UNIONS s)` THEN
      UNDISCH_TAC `(x:real^3) IN t` THEN UNDISCH_TAC `(t:real^3->bool) IN s` THEN
      SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(t:real^3->bool) IN moi_s6ct_part w C'` ASSUME_TAC THENL
     [REWRITE_TAC[MOI_S6CT_IN_PART] THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                     `C':real^3->bool`; `t:real^3->bool`] MOI_S6CT_SIMPLEX_SIDE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [UNDISCH_TAC `(t:real^3->bool) SUBSET C UNION UNIONS s` THEN
        UNDISCH_TAC `DISJOINT (C:real^3->bool) C'` THEN
        UNDISCH_TAC `DISJOINT (C':real^3->bool) (UNIONS s)` THEN SET_TAC[];
        MATCH_MP_TAC(TAUT `F ==> p`) THEN
        UNDISCH_TAC `(t:real^3->bool) SUBSET C' UNION UNIONS s` THEN
        UNDISCH_TAC `DISJOINT (t:real^3->bool) (UNIONS s)` THEN
        UNDISCH_TAC `(x:real^3) IN t` THEN UNDISCH_TAC `~((x:real^3) IN C')` THEN
        SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                   `C':real^3->bool`; `t:real^3->bool`] MOI_S6CT_TRI_OFF) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^3) IN UNIONS s` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:(real^3->bool)->bool`; `r:real^3->bool`] MOI_FSA_CM_PURE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(x:real^3) IN r` THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `t:real^3->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`; `C:real^3->bool`;
                 `C':real^3->bool`; `t:real^3->bool`] MOI_S6CT_TRI_PART) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REWRITE_TAC[complex_boundary; IN_UNIONS; IN_ELIM_THM] THEN
  EXISTS_TAC `t:real^3->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[SUBSET];
    UNDISCH_TAC `(x:real^3) IN r` THEN UNDISCH_TAC `(r:real^3->bool) SUBSET t` THEN
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The cut (Case 3 of Moise 26.4): the parts on the two sides of |s|.  The  *)
(* antecedent MOI_S26_SPHERE_SPLIT of the statement is not needed: the      *)
(* disk in the link comes from MOI_S4O_SPHERE_PIECE.                        *)
(* ------------------------------------------------------------------------- *)

let CUT = prove
 (MOI_S26_CUT,
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (K ALL_TAC)) THEN
  MAP_EVERY X_GEN_TAC [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `moi_s6ct_setting (w:(real^3->bool)->bool) s` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[moi_s6ct_setting]; ALL_TAC] THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`] MOI_S6CT_SIDE_IO) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `moi_s6ct_part w (outside (UNIONS (s:(real^3->bool)->bool)))` THEN
  EXISTS_TAC `moi_s6ct_part w (inside (UNIONS (s:(real^3->bool)->bool)))` THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`;
                 `inside (UNIONS (s:(real^3->bool)->bool))`;
                 `outside (UNIONS (s:(real^3->bool)->bool))`] MOI_S6CT_PART_BASIC) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`;
                 `outside (UNIONS (s:(real^3->bool)->bool))`;
                 `inside (UNIONS (s:(real^3->bool)->bool))`] MOI_S6CT_PART_BASIC) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`;
                 `inside (UNIONS (s:(real^3->bool)->bool))`;
                 `outside (UNIONS (s:(real^3->bool)->bool))`] MOI_S6CT_PART_CMWB) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`;
                 `outside (UNIONS (s:(real^3->bool)->bool))`;
                 `inside (UNIONS (s:(real^3->bool)->bool))`] MOI_S6CT_PART_CMWB) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`;
                 `inside (UNIONS (s:(real^3->bool)->bool))`;
                 `outside (UNIONS (s:(real^3->bool)->bool))`] MOI_S6CT_PART_BOUNDARY) THEN
  MP_TAC(ISPECL [`w:(real^3->bool)->bool`; `s:(real^3->bool)->bool`;
                 `outside (UNIONS (s:(real^3->bool)->bool))`;
                 `inside (UNIONS (s:(real^3->bool)->bool))`] MOI_S6CT_PART_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[]);;

