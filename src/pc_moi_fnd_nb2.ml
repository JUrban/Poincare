(* ========================================================================= *)
(* pc_moi_fnd_nb2: second-derived neighbourhoods of polygons in finite       *)
(* closed combinatorial surfaces (Moise p.155, 21.10, 28.19 as used by the   *)
(* split of MOI_FND_SPLIT_DISK_R3). Main theorem MOI_FN2_POLYGON_2_COND: the *)
(* statement term of pc_moi_fnd_stmt3.ml                                     *)
(*   DERIVED_NBHD_POLYGON_2 = MOI_FND_DERIVED_NBHD_POLYGON_2                 *)
(* from the planar surface theorem and the boundary-circles theorem as       *)
(* hypotheses (pc_moi_fnd_nb2f discharges both), and the generic trace       *)
(* identity MOI_FN2_DERIVED_TRACE (sub-complexes of a complex: the derived   *)
(* neighbourhood and frontier of l in t meet UNIONS m in those of l INTER m  *)
(* in m).                                                                    *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt3.ml";;
needs "src/pc_moi_fnd_cm2.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* The trace identity (chains of the first derived, minima of chains, the    *)
(* interior and frontier of N in UNIONS t in terms of the second-derived     *)
(* simplices through a point).                                               *)
(* ========================================================================= *)

let MOI_FN2_BSD_INTER = prove
 (`!(t:(real^N->bool)->bool) l m.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ simplicial_subcomplex m t
     ==> barycentric_subdivision (l INTER m) =
         barycentric_subdivision l INTER barycentric_subdivision m`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `(l:(real^N->bool)->bool) SUBSET t /\ m SUBSET t` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
  REWRITE_TAC[IN_INTER; MOI_BAR_IN_SUBDIVISION] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    CONJ_TAC THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN EXISTS_TAC `(l:(real^N->bool)->bool) INTER m` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC)
      (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(f:(real^N->bool)->bool) = g` SUBST_ALL_TAC THENL
     [MATCH_MP_TAC MOI_FRN_CHAIN_HULL_INJ THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[MOI_BAR_CHAIN_MONO];
      ALL_TAC] THEN
    EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_bar_chain (l:(real^N->bool)->bool) g` THEN
    UNDISCH_TAC `moi_bar_chain (m:(real^N->bool)->bool) g` THEN
    REWRITE_TAC[moi_bar_chain] THEN SET_TAC[]]);;

let MOI_FN2_SUBCOMPLEX_INTER = prove
 (`!(t:(real^N->bool)->bool) l m.
     simplicial_subcomplex l t /\ simplicial_subcomplex m t
     ==> simplicial_subcomplex (l INTER m) t /\ simplicial_subcomplex (l INTER m) m /\
         simplicial_subcomplex (l INTER m) l`,
  REWRITE_TAC[simplicial_subcomplex; IN_INTER; SUBSET] THEN MESON_TAC[]);;

let MOI_FN2_UNIONS_INTER = prove
 (`!(t:(real^N->bool)->bool) l m.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ simplicial_subcomplex m t
     ==> UNIONS (l INTER m) = UNIONS l INTER UNIONS m`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS t` ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN UNIONS l` THEN
    UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) t` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `x:real^N`] MOI_FRN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `m:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `(l:(real^N->bool)->bool) INTER m`]
                MOI_FRN_SETUP) THEN
  ASM_SIMP_TAC[MOI_FN2_SUBCOMPLEX_INTER] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision l /\
                r IN barycentric_subdivision m` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
    MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision (l INTER m)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FN2_BSD_INTER; IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS (barycentric_subdivision (l INTER m))` MP_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ASM_REWRITE_TAC[]]);;

(* Chains of the first derived and their minima. *)

let MOI_FN2_CHAIN_MIN_IN = prove
 (`!(c:(real^N->bool)->bool) f k.
     moi_bar_complex c /\ simplicial_subcomplex k c /\ moi_bar_chain c f /\
     ~(f INTER k = {})
     ==> INTERS f IN f /\ INTERS f IN k`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(f:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`] MOI_FRN_CHAIN_MIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((f:(real^N->bool)->bool) INTER k = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `simplicial_subcomplex (k:(real^N->bool)->bool) c` THEN
  REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_SIMP_TAC[] THEN
  ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]);;

let MOI_FN2_CHAIN_INSERT_MIN = prove
 (`!(c:(real^N->bool)->bool) f r.
     moi_bar_chain c f /\ ~(f = {}) /\ r IN c /\ ~(r = {}) /\ r SUBSET INTERS f
     ==> moi_bar_chain c (r INSERT f)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN f ==> r SUBSET s` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `INTERS (f:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `moi_bar_chain (c:(real^N->bool)->bool) f` THEN
  REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; FINITE_INSERT; IN_INSERT] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
  ASM_MESON_TAC[]);;

let MOI_FN2_NC_CHAIN = prove
 (`!(t:(real^N->bool)->bool) l f.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     moi_bar_chain (barycentric_subdivision t) f /\ ~(f = {})
     ==> (convex hull (IMAGE simplex_barycentre f) IN derived_nbhd_complex t l <=>
          ?r. r IN barycentric_subdivision l /\ ~(r = {}) /\ r SUBSET INTERS f)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FRN_IN_NBHD_COMPLEX] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `r0:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    SUBGOAL_THEN `(f:(real^N->bool)->bool) SUBSET g` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`IMAGE simplex_barycentre (g:(real^N->bool)->bool)`;
                     `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))`]
                    FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_BAR_CHAIN_AFFINE_INDEPENDENT]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `S:real^N->bool` STRIP_ASSUME_TAC) THEN
      ABBREV_TAC `g' = {r:real^N->bool | r IN g /\ simplex_barycentre r IN S}` THEN
      SUBGOAL_THEN `S = IMAGE simplex_barycentre (g':(real^N->bool)->bool)` ASSUME_TAC THENL
       [EXPAND_TAC "g'" THEN
        UNDISCH_TAC `S SUBSET IMAGE simplex_barycentre (g:(real^N->bool)->bool)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool)) g'`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "g'" THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(f:(real^N->bool)->bool) = g'` SUBST1_TAC THENL
       [MATCH_MP_TAC MOI_FRN_CHAIN_HULL_INJ THEN
        EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
        ASM_MESON_TAC[];
        EXPAND_TAC "g'" THEN SET_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `g:(real^N->bool)->bool`; `barycentric_subdivision (l:(real^N->bool)->bool)`]
                  MOI_FN2_CHAIN_MIN_IN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN STRIP_TAC THEN
    EXISTS_TAC `INTERS (g:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool))
                    (r INSERT f)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FN2_CHAIN_INSERT_MIN THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision (l:(real^N->bool)->bool))
                     (barycentric_subdivision t)` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `(r:real^N->bool) INSERT f` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[IN_INSERT];
      MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
      EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[]]]);;

(* Interior and frontier of N in UNIONS t through the second-derived        *)
(* simplices containing a point.                                             *)

let MOI_FN2_INTERIOR_NC = prove
 (`!(t:(real^N->bool)->bool) l x.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> (x IN (subtopology euclidean (UNIONS t)) interior_of (derived_nbhd t l) <=>
          x IN derived_nbhd t l /\
          !s. s IN barycentric_subdivision (barycentric_subdivision t) /\ x IN s
              ==> s IN derived_nbhd_complex t l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision
                  (t:(real^N->bool)->bool))) /\
                UNIONS (barycentric_subdivision (barycentric_subdivision t)) = UNIONS t /\
                moi_bar_complex (barycentric_subdivision (barycentric_subdivision t)) /\
                simplicial_subcomplex (derived_nbhd_complex t l)
                  (barycentric_subdivision (barycentric_subdivision t)) /\
                UNIONS (derived_nbhd_complex t l) = derived_nbhd t (l:(real^N->bool)->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF; UNIONS_BARYCENTRIC_SUBDIVISION;
                 MOI_FDN_DERIVED_NBHD_COMPLEX_SUBCOMPLEX; MOI_FDN_UNIONS_DERIVED_NBHD_COMPLEX] THEN
    MATCH_MP_TAC MOI_FRN_LF_BAR_COMPLEX THEN
    ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN CONJ_TAC THENL
     [ASM_MESON_TAC[INTERIOR_OF_SUBSET; SUBSET]; ALL_TAC] THEN
    X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN (subtopology euclidean (UNIONS t)) interior_of
                   (derived_nbhd t l)` THEN
    REWRITE_TAC[interior_of; IN_ELIM_THM; OPEN_IN_SUBTOPOLOGY; OPEN_IN_EUCLIDEAN] THEN
    DISCH_THEN(X_CHOOSE_THEN `U:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `V:real^N->bool` STRIP_ASSUME_TAC) STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:real^N) IN closure (relative_interior s)` MP_TAC THENL
     [SUBGOAL_THEN `convex (s:real^N->bool) /\ closed s` STRIP_ASSUME_TAC THENL
       [SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
         [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
        ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT; COMPACT_IMP_CLOSED];
        ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]];
      ALL_TAC] THEN
    REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
    SUBGOAL_THEN `(x:real^N) IN V` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `open (V:real^N->bool)` THEN REWRITE_TAC[OPEN_CONTAINS_BALL] THEN
    DISCH_THEN(fun th -> DISCH_THEN(MP_TAC o MATCH_MP th)) THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    DISCH_THEN(MP_TAC o SPEC `e:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^N) IN derived_nbhd t l` ASSUME_TAC THENL
     [SUBGOAL_THEN `(y:real^N) IN U` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
         [UNDISCH_TAC `ball(x:real^N,e) SUBSET V` THEN
          REWRITE_TAC[SUBSET; IN_BALL] THEN DISCH_THEN MATCH_MP_TAC THEN
          ASM_MESON_TAC[DIST_SYM];
          SUBGOAL_THEN `(y:real^N) IN s` MP_TAC THENL
           [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
          SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS (barycentric_subdivision (barycentric_subdivision t))` MP_TAC THENL
           [ASM SET_TAC[]; ASM_REWRITE_TAC[] THEN SET_TAC[]]];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `~((s:real^N->bool) IN derived_nbhd_complex t l)` THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
    MAP_EVERY EXISTS_TAC [`barycentric_subdivision (barycentric_subdivision (t:(real^N->bool)->bool))`; `y:real^N`] THEN
    ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (t:(real^N->bool)->bool))`; `x:real^N`] MOI_CMB_STAR_NBHD) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^N) IN derived_nbhd t l` THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
                    MOI_FDN_DERIVED_NBHD_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[interior_of; IN_ELIM_THM] THEN
    EXISTS_TAC `UNIONS t INTER ball(x:real^N,e)` THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
      REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(x:real^N) IN derived_nbhd t l` THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
                    MOI_FDN_DERIVED_NBHD_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N` o check (is_forall o concl)) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(s:real^N->bool) IN derived_nbhd_complex t l` ASSUME_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(y:real^N) IN UNIONS (derived_nbhd_complex t l)` MP_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]]]]);;

let MOI_FN2_FRONTIER_NC = prove
 (`!(t:(real^N->bool)->bool) l x.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> (x IN derived_frontier t l <=>
          x IN derived_nbhd t l /\
          ?s. s IN barycentric_subdivision (barycentric_subdivision t) /\ x IN s /\
              ~(s IN derived_nbhd_complex t l))`,
  REPEAT STRIP_TAC THEN
  REWRITE_TAC[derived_frontier; frontier_of; IN_DIFF] THEN
  ASM_SIMP_TAC[CLOSURE_OF_CLOSED_IN; MOI_FDN_DERIVED_NBHD_CLOSED_IN] THEN
  ASM_SIMP_TAC[MOI_FN2_INTERIOR_NC] THEN MESON_TAC[]);;

let MOI_FN2_MIN_RESTRICT = prove
 (`!(c:(real^N->bool)->bool) f k.
     moi_bar_complex c /\ simplicial_subcomplex k c /\ moi_bar_chain c f /\
     ~(f INTER k = {})
     ==> INTERS (f INTER k) = INTERS f /\ INTERS f IN f INTER k`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FN2_CHAIN_MIN_IN) THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTERS] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(MP_TAC o SPEC `INTERS (f:(real^N->bool)->bool)`) THEN
    ASM_REWRITE_TAC[IN_INTER; IN_INTERS];
    REWRITE_TAC[SUBSET; IN_INTERS; IN_INTER] THEN MESON_TAC[]]);;

let MOI_FN2_TRACE_SETUP = prove
 (`!(t:(real^N->bool)->bool) l m.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ simplicial_subcomplex m t
     ==> lf_simplicial_complex m /\ simplicial_subcomplex (l INTER m) m /\
         moi_bar_complex (barycentric_subdivision t) /\
         simplicial_subcomplex (barycentric_subdivision l) (barycentric_subdivision t) /\
         simplicial_subcomplex (barycentric_subdivision m) (barycentric_subdivision t) /\
         UNIONS (barycentric_subdivision m) = UNIONS m /\
         barycentric_subdivision (l INTER m) =
         barycentric_subdivision l INTER barycentric_subdivision m /\
         simplicial_subcomplex (barycentric_subdivision (barycentric_subdivision m))
                               (barycentric_subdivision (barycentric_subdivision t))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SUBCOMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_subcomplex ((l:(real^N->bool)->bool) INTER m) m` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FN2_SUBCOMPLEX_INTER]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FN2_BSD_INTER] THEN
  SUBGOAL_THEN `barycentric_subdivision ((l:(real^N->bool)->bool) INTER m) =
                barycentric_subdivision l INTER barycentric_subdivision m`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[MOI_FN2_BSD_INTER]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `m:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `barycentric_subdivision (m:(real^N->bool)->bool)`]
                BARYCENTRIC_SUBDIVISION_SUBCOMPLEX) THEN
  ASM_SIMP_TAC[]);;

let MOI_FN2_NBHD_TRACE = prove
 (`!(t:(real^N->bool)->bool) l m.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ simplicial_subcomplex m t
     ==> derived_nbhd t l INTER UNIONS m = derived_nbhd m (l INTER m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FN2_TRACE_SETUP) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN
  ASM_SIMP_TAC[MOI_FRN_IN_NBHD] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC) THEN
    EXISTS_TAC `f INTER barycentric_subdivision (m:(real^N->bool)->bool)` THEN
    SUBGOAL_THEN
     `(x:real^N) IN convex hull IMAGE simplex_barycentre
                      (f INTER barycentric_subdivision m)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                     `barycentric_subdivision (m:(real^N->bool)->bool)`;
                     `f:(real^N->bool)->bool`] MOI_FRN_FULL_CHAIN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[IN_INTER];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((f:(real^N->bool)->bool) INTER barycentric_subdivision m = {})`
    ASSUME_TAC THENL
     [DISCH_THEN(fun th -> UNDISCH_TAC
        `(x:real^N) IN convex hull IMAGE simplex_barycentre
                         (f INTER barycentric_subdivision m)` THEN
        REWRITE_TAC[th; IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY]);
      ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `f:(real^N->bool)->bool`; `barycentric_subdivision (m:(real^N->bool)->bool)`]
                  MOI_FN2_MIN_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `f:(real^N->bool)->bool`; `barycentric_subdivision (l:(real^N->bool)->bool)`]
                  MOI_FN2_CHAIN_MIN_IN) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; STRIP_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool)) f` THEN
      REWRITE_TAC[moi_bar_chain] THEN SIMP_TAC[FINITE_INTER] THEN SET_TAC[];
      EXISTS_TAC `INTERS (f:(real^N->bool)->bool)` THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
        EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN
        ASM_MESON_TAC[simplicial_subcomplex];
        EXISTS_TAC `s:real^N->bool` THEN ASM SET_TAC[]];
      SUBGOAL_THEN `(x:real^N) IN derived_nbhd m (l INTER m)` MP_TAC THENL
       [ASM_SIMP_TAC[MOI_FRN_IN_NBHD] THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
        MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `(l:(real^N->bool)->bool) INTER m`]
                      MOI_FDN_DERIVED_NBHD_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[]]]]);;

let MOI_FN2_FRONTIER_TRACE = prove
 (`!(t:(real^N->bool)->bool) l m.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ simplicial_subcomplex m t
     ==> derived_frontier t l INTER UNIONS m = derived_frontier m (l INTER m)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o MATCH_MP MOI_FN2_TRACE_SETUP) THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_FN2_NBHD_TRACE) THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_INTER] THEN
  ASM_SIMP_TAC[MOI_FN2_FRONTIER_NC] THEN
  SUBGOAL_THEN `(x:real^N) IN derived_nbhd t l /\ x IN UNIONS m <=>
                x IN derived_nbhd m (l INTER m)`
  (fun th -> REWRITE_TAC[GSYM th]) THENL
   [UNDISCH_TAC `derived_nbhd t l INTER UNIONS m =
                 derived_nbhd m ((l:(real^N->bool)->bool) INTER m)` THEN
    SET_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC)) ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(sg:real^N->bool) IN barycentric_subdivision (barycentric_subdivision t)` THEN
    REWRITE_TAC[ISPEC `barycentric_subdivision (t:(real^N->bool)->bool)`
                  MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `(x:real^N) IN convex hull IMAGE simplex_barycentre
                      (f INTER barycentric_subdivision m)`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                     `barycentric_subdivision (m:(real^N->bool)->bool)`;
                     `f:(real^N->bool)->bool`] MOI_FRN_FULL_CHAIN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_REWRITE_TAC[IN_INTER] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((f:(real^N->bool)->bool) INTER barycentric_subdivision m = {})`
    ASSUME_TAC THENL
     [DISCH_THEN(fun th -> UNDISCH_TAC
        `(x:real^N) IN convex hull IMAGE simplex_barycentre
                         (f INTER barycentric_subdivision m)` THEN
        REWRITE_TAC[th; IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY]);
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision (m:(real^N->bool)->bool))
                    (f INTER barycentric_subdivision m)` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool)) f` THEN
      REWRITE_TAC[moi_bar_chain] THEN SIMP_TAC[FINITE_INTER] THEN SET_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `convex hull IMAGE simplex_barycentre
                  (f INTER barycentric_subdivision (m:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[ISPEC `barycentric_subdivision (m:(real^N->bool)->bool)`
                    MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `f INTER barycentric_subdivision (m:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `(l:(real^N->bool)->bool) INTER m`;
                   `f INTER barycentric_subdivision (m:(real^N->bool)->bool)`]
                  MOI_FN2_NC_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~((sg:real^N->bool) IN derived_nbhd_complex t l)` THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `f:(real^N->bool)->bool`] MOI_FN2_NC_CHAIN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN EXISTS_TAC `r:real^N->bool` THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `f:(real^N->bool)->bool`; `barycentric_subdivision (m:(real^N->bool)->bool)`]
                  MOI_FN2_MIN_RESTRICT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    UNDISCH_TAC `(r:real^N->bool) SUBSET INTERS (f INTER barycentric_subdivision m)` THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[IN_INTER];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `sg:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex
                     (barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool)))
                     (barycentric_subdivision (barycentric_subdivision t))` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(sg:real^N->bool) IN barycentric_subdivision (barycentric_subdivision m)` THEN
    REWRITE_TAC[ISPEC `barycentric_subdivision (m:(real^N->bool)->bool)`
                  MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(x:real^N) IN sg` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool)) g`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
      EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN
      ASM_MESON_TAC[simplicial_subcomplex];
      ALL_TAC] THEN
    UNDISCH_TAC `~((sg:real^N->bool) IN derived_nbhd_complex m (l INTER m))` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `(l:(real^N->bool)->bool) INTER m`;
                   `g:(real^N->bool)->bool`] MOI_FN2_NC_CHAIN) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `g:(real^N->bool)->bool`] MOI_FN2_NC_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC I [GSYM CONTRAPOS_THM] THEN REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                   `g:(real^N->bool)->bool`] MOI_FRN_CHAIN_MIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `INTERS g IN barycentric_subdivision (m:(real^N->bool)->bool)` ASSUME_TAC
    THENL [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
    UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision (m:(real^N->bool)->bool))
                   (barycentric_subdivision t)` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `INTERS (g:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
    EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision (l:(real^N->bool)->bool))
                     (barycentric_subdivision t)` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN ASM SET_TAC[];
      ASM SET_TAC[]]]);;

let MOI_FN2_DERIVED_TRACE = prove
 (`!(t:(real^N->bool)->bool) (l:(real^N->bool)->bool) (m:(real^N->bool)->bool).
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\ simplicial_subcomplex m t
     ==> UNIONS (l INTER m) = UNIONS l INTER UNIONS m /\
         derived_nbhd t l INTER UNIONS m = derived_nbhd m (l INTER m) /\
         derived_frontier t l INTER UNIONS m = derived_frontier m (l INTER m)`,
  MESON_TAC[MOI_FN2_UNIONS_INTER; MOI_FN2_NBHD_TRACE; MOI_FN2_FRONTIER_TRACE]);;

(* ========================================================================= *)
(* The second-derived neighbourhood as a                                    *)
(* union of closed stars.  With c = bsd m and k = bsd l: N(l) is the union *)
(* of the closed stars in bsd c of the vertices of k; two such stars are    *)
(* disjoint unless their vertices span an edge e of k, and then they meet  *)
(* in the dual cell moi_fn2_dual c e of e; the trace of a star on UNIONS l *)
(* is the union of the half-edges from its vertex.                          *)
(* ========================================================================= *)

let moi_fn2_dual = new_definition
 `moi_fn2_dual (c:(real^N->bool)->bool) e =
    UNIONS {convex hull (IMAGE simplex_barycentre h) | h |
            moi_bar_chain c h /\ ~(h = {}) /\ !r. r IN h ==> e SUBSET r}`;;

let MOI_FN2_SIMPLEX_HAS_VERTEX = prove
 (`!(c:(real^N->bool)->bool) s.
     moi_bar_complex c /\ s IN c /\ ~(s = {}) ==> ?v. {v} IN c /\ v IN s`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  DISCH_THEN(MP_TAC o CONJUNCT2) THEN
  ASM_CASES_TAC `{v:real^N | v extreme_point_of s} = {}` THEN
  ASM_REWRITE_TAC[CONVEX_HULL_EMPTY] THEN DISCH_TAC THEN
  UNDISCH_TAC `~({v:real^N | v extreme_point_of s} = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN EXISTS_TAC `v:real^N` THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_FC2_EXTREME_VERTEX]; ASM_MESON_TAC[extreme_point_of]]);;

let MOI_FN2_NBHD_STARS = prove
 (`!(m:(real^N->bool)->bool) l.
     lf_simplicial_complex m /\ simplicial_subcomplex l m
     ==> derived_nbhd m l =
         UNIONS {UNIONS (moi_fm3_cstar (barycentric_subdivision (barycentric_subdivision m)) w) |
                 w | {w} IN barycentric_subdivision l}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    ASM_SIMP_TAC[MOI_FRN_IN_NBHD] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                   `f:(real^N->bool)->bool`; `barycentric_subdivision (l:(real^N->bool)->bool)`]
                  MOI_FN2_CHAIN_MIN_IN) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; STRIP_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (l:(real^N->bool)->bool)`;
                   `INTERS (f:(real^N->bool)->bool)`] MOI_FN2_SIMPLEX_HAS_VERTEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `{w:real^N} IN barycentric_subdivision m` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision (l:(real^N->bool)->bool))
                     (barycentric_subdivision m)` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision (m:(real^N->bool)->bool))
                    ({w} INSERT f)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FN2_CHAIN_INSERT_MIN THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[SING_SUBSET]];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `UNIONS (moi_fm3_cstar (barycentric_subdivision
                  (barycentric_subdivision (m:(real^N->bool)->bool))) w)` THEN
    CONJ_TAC THENL [EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; moi_fm3_cstar; IN_ELIM_THM] THEN
    EXISTS_TAC `convex hull IMAGE simplex_barycentre ({w:real^N} INSERT f)` THEN
    CONJ_TAC THENL
     [EXISTS_TAC `convex hull IMAGE simplex_barycentre ({w:real^N} INSERT f)` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE; IN_INSERT] THEN
        EXISTS_TAC `{w:real^N}` THEN REWRITE_TAC[MOI_FRN_BARYCENTRE_SING];
        MATCH_MP_TAC FACE_OF_REFL THEN REWRITE_TAC[CONVEX_CONVEX_HULL]];
      UNDISCH_TAC `(x:real^N) IN convex hull IMAGE simplex_barycentre f` THEN
      SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; moi_fm3_cstar] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `(x:real^N) IN S` THEN ASM_REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    REWRITE_TAC[derived_nbhd; IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `w:real^N` THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(w:real^N) IN UNIONS (barycentric_subdivision l)` MP_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^N}` THEN
        ASM_REWRITE_TAC[IN_SING];
        ASM_REWRITE_TAC[]];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]]]);;

let MOI_FN2_STAR_CHAINS = prove
 (`!(c:(real^N->bool)->bool) w.
     moi_bar_complex c /\ {w} IN c
     ==> UNIONS (moi_fm3_cstar (barycentric_subdivision c) w) =
         UNIONS {convex hull (IMAGE simplex_barycentre f) | f |
                 moi_bar_chain c f /\ {w} IN f}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; moi_fm3_cstar; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `(s:real^N->bool) IN barycentric_subdivision c` THEN
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN CONJ_TAC THENL
     [EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FC2_BARY_IN_HULL THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY; MOI_FRN_BARYCENTRE_SING] THEN
      ASM_MESON_TAC[];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]];
    REWRITE_TAC[SUBSET; IN_UNIONS; moi_fm3_cstar; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `s:real^N->bool` THEN REPEAT CONJ_TAC THENL
     [ASM_REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[MOI_FRN_BARYCENTRE_SING];
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC FACE_OF_REFL THEN
      REWRITE_TAC[CONVEX_CONVEX_HULL]]]);;

(* Elements of a chain through {u} and through {w} contain both u and w. *)

let MOI_FN2_CHAIN_PAIR_CONTAINS = prove
 (`!(c:(real^N->bool)->bool) f g u w r.
     moi_bar_chain c f /\ moi_bar_chain c g /\ {u} IN f /\ {w} IN g /\ ~(u = w) /\
     r IN f INTER g
     ==> u IN r /\ w IN r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(r:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `({u:real^N} SUBSET r \/ r SUBSET {u}) /\ ({w:real^N} SUBSET r \/ r SUBSET {w})`
  MP_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `!a:real^N. r SUBSET {a} ==> r = {a}` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~({u:real^N} IN g) /\ ~({w:real^N} IN f)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [SUBGOAL_THEN `{u:real^N} SUBSET {w} \/ {w} SUBSET {u}` MP_TAC THENL
       [ASM_MESON_TAC[moi_bar_chain]; ASM SET_TAC[]];
      SUBGOAL_THEN `{u:real^N} SUBSET {w} \/ {w} SUBSET {u}` MP_TAC THENL
       [ASM_MESON_TAC[moi_bar_chain]; ASM SET_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[SING_SUBSET] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REPEAT(FIRST_X_ASSUM(fun th -> if is_imp (concl th) then NO_TAC else
     (try (let th' = MATCH_MP (ASSUME `!a:real^N. r SUBSET {a} ==> r = {a}`) th in
           SUBST_ALL_TAC th') with Failure _ -> NO_TAC))) THEN
  ASM SET_TAC[]);;

let MOI_FN2_STAR_INTER = prove
 (`!(c:(real^N->bool)->bool) u w.
     moi_bar_complex c /\ {u} IN c /\ {w} IN c /\ ~(u = w)
     ==> UNIONS (moi_fm3_cstar (barycentric_subdivision c) u) INTER
         UNIONS (moi_fm3_cstar (barycentric_subdivision c) w) =
         moi_fn2_dual c (segment[u,w])`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_FN2_STAR_CHAINS] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM; moi_fn2_dual] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `s1:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC))
      (X_CHOOSE_THEN `s2:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER g))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                     `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_MESON_TAC[IN_INTER];
      ALL_TAC] THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre ((f:(real^N->bool)->bool) INTER g))` THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `(f:(real^N->bool)->bool) INTER g` THEN
    REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      DISCH_TAC THEN UNDISCH_TAC
        `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER g))` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                     `g:(real^N->bool)->bool`; `u:real^N`; `w:real^N`; `r:real^N->bool`]
                    MOI_FN2_CHAIN_PAIR_CONTAINS) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM SUBSET; SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
      ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
      SUBGOAL_THEN `(r:real^N->bool) IN c` ASSUME_TAC THENL
       [ASM_MESON_TAC[moi_bar_chain; SUBSET; IN_INTER]; ALL_TAC] THEN
      ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]];
    REWRITE_TAC[SUBSET_INTER] THEN
    SUBGOAL_THEN
     `!a:real^N. a IN segment[u,w] /\ {a} IN c
                 ==> moi_fn2_dual c (segment[u,w]) SUBSET
                     UNIONS {convex hull (IMAGE simplex_barycentre f) | f |
                             moi_bar_chain c f /\ {a} IN f}`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; moi_fn2_dual; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre ({a:real^N} INSERT h))` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `{a:real^N} INSERT h` THEN REWRITE_TAC[IN_INSERT] THEN
        MATCH_MP_TAC MOI_FN2_CHAIN_INSERT_MIN THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
        REWRITE_TAC[SING_SUBSET; IN_INTERS] THEN ASM_MESON_TAC[];
        UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
        SPEC_TAC(`x:real^N`,`x:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
      CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT]]]);;

(* Two simplices of a complex, one inside the other, of the same dimension, *)
(* coincide.                                                                *)

let MOI_FN2_SUBSET_DIM_EQ = prove
 (`!(c:(real^N->bool)->bool) s r.
     moi_bar_complex c /\ s IN c /\ r IN c /\ s SUBSET r /\ aff_dim s = aff_dim r
     ==> s = r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) face_of r` ASSUME_TAC THENL
   [SUBGOAL_THEN `s:real^N->bool = s INTER r` SUBST1_TAC THENL
     [ASM SET_TAC[]; ASM_MESON_TAC[moi_bar_complex]];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (r:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`s:real^N->bool`; `r:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ASM_REWRITE_TAC[INT_LT_REFL] THEN MESON_TAC[]);;

(* The dual cell of a set contained in no simplex is empty.                  *)

let MOI_FN2_DUAL_EMPTY = prove
 (`!(c:(real^N->bool)->bool) e.
     ~(?r. r IN c /\ e SUBSET r) ==> moi_fn2_dual c e = {}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fn2_dual; EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
  X_GEN_TAC `h:(real^N->bool)->bool` THEN STRIP_TAC THEN
  UNDISCH_TAC `~(h:(real^N->bool)->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `r:real^N->bool`) THEN
  UNDISCH_TAC `~(?r:real^N->bool. r IN c /\ e SUBSET r)` THEN
  REWRITE_TAC[TAUT `~p ==> q <=> p \/ q`] THEN DISJ1_TAC THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_MESON_TAC[moi_bar_chain; SUBSET]);;

(* The closed stars of three distinct vertices lying in no common simplex   *)
(* have no common point.                                                     *)

let MOI_FN2_STAR_INTER3 = prove
 (`!(c:(real^N->bool)->bool) u v w.
     moi_bar_complex c /\ {u} IN c /\ {v} IN c /\ {w} IN c /\
     ~(u = v) /\ ~(u = w) /\ ~(v = w) /\
     ~(?r. r IN c /\ u IN r /\ v IN r /\ w IN r)
     ==> UNIONS (moi_fm3_cstar (barycentric_subdivision c) u) INTER
         UNIONS (moi_fm3_cstar (barycentric_subdivision c) v) INTER
         UNIONS (moi_fm3_cstar (barycentric_subdivision c) w) = {}`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_FN2_STAR_INTER] THEN
  ASM_SIMP_TAC[MOI_FN2_STAR_CHAINS] THEN
  MATCH_MP_TAC(SET_RULE `(!x:real^N. x IN s /\ x IN t ==> F) ==> s INTER t = {}`) THEN
  REWRITE_TAC[moi_fn2_dual; IN_UNIONS; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `s1:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC))
    (X_CHOOSE_THEN `s2:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `h:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER h))`
  MP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `h:(real^N->bool)->bool`] MOI_BAR_CHAIN_HULL_INTER) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_MESON_TAC[IN_INTER];
    ALL_TAC] THEN
  ASM_CASES_TAC `(f:(real^N->bool)->bool) INTER h = {}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY]) THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` MP_TAC) THEN REWRITE_TAC[IN_INTER] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN r /\ w IN r` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `segment[v:real^N,w] SUBSET r` MP_TAC THENL
     [ASM_MESON_TAC[]; MESON_TAC[SUBSET; ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N) IN r` ASSUME_TAC THENL
   [SUBGOAL_THEN `{u:real^N} SUBSET r \/ r SUBSET {u}` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
    REWRITE_TAC[SING_SUBSET] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(v:real^N) IN r` THEN UNDISCH_TAC `(r:real^N->bool) SUBSET {u}` THEN
    UNDISCH_TAC `~(u:real^N = v)` THEN SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `~(?r:real^N->bool. r IN c /\ u IN r /\ v IN r /\ w IN r)` THEN
  REWRITE_TAC[] THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[moi_bar_chain; SUBSET]);;

let MOI_FN2_SUBSET3_CASES = prove
 (`!(h:A->bool) e t1 t2.
     (!r. r IN h ==> r = e \/ r = t1 \/ r = t2) /\ ~(t1 IN h /\ t2 IN h)
     ==> h SUBSET {e,t1} \/ h SUBSET {e,t2}`,
  SET_TAC[]);;

(* The dual cell of an edge e of a finite combinatorial surface: the union  *)
(* of the two segments from the barycentre of e to the barycentres of the   *)
(* two triangles at e.                                                       *)

let MOI_FN2_DUAL_EDGE = prove
 (`!(c:(real^N->bool)->bool) e.
     FINITE c /\ combinatorial_manifold 2 c /\ e IN c /\ aff_dim e = &1
     ==> ?t1 t2. ~(t1 = t2) /\
                 {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = {t1,t2} /\
                 moi_fn2_dual c e =
                 segment[simplex_barycentre e,simplex_barycentre t1] UNION
                 segment[simplex_barycentre e,simplex_barycentre t2]`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSA_CM_EDGE2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE {t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t}`
               MOI_FC2_CARD_EQ_2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`t1:real^N->bool`; `t2:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `!r:real^N->bool. r IN c /\ aff_dim r = &2 /\ e SUBSET r <=> r = t1 \/ r = t2`
  (LABEL_TAC "T12") THENL
   [UNDISCH_TAC `{t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = {t1,t2}` THEN
    DISCH_THEN(fun th -> X_GEN_TAC `r:real^N->bool` THEN
      MP_TAC(SPEC `r:real^N->bool` (GEN_REWRITE_RULE I [EXTENSION] th))) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(t1:real^N->bool) IN c /\ aff_dim t1 = &2 /\ e SUBSET t1 /\
    (t2:real^N->bool) IN c /\ aff_dim t2 = &2 /\ e SUBSET t2`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "T12" (MP_TAC o SPEC `t1:real^N->bool`) THEN
    USE_THEN "T12" (MP_TAC o SPEC `t2:real^N->bool`) THEN
    REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(e:real^N->bool = {}) /\ ~(t1:real^N->bool = {}) /\ ~(t2:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
                    lhs (concl th) = `-- &1:int`)) THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r:real^N->bool. r IN c /\ e SUBSET r ==> r = e \/ r = t1 \/ r = t2`
  (LABEL_TAC "CL") THENL
   [X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `aff_dim (r:real^N->bool) = &1 \/ aff_dim r = &2` STRIP_ASSUME_TAC THENL
     [MP_TAC(ISPECL [`e:real^N->bool`; `r:real^N->bool`] AFF_DIM_SUBSET) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`] MOI_FSA_CM_DIM) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      DISJ1_TAC THEN CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FN2_SUBSET_DIM_EQ THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN USE_THEN "T12" (fun th -> REWRITE_TAC[GSYM th]) THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  REMOVE_THEN "T12" (K ALL_TAC) THEN
  REWRITE_TAC[moi_fn2_dual] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `h:(real^N->bool)->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `!r:real^N->bool. r IN h ==> r = e \/ r = t1 \/ r = t2` ASSUME_TAC THENL
     [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN USE_THEN "CL" MATCH_MP_TAC THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `moi_bar_chain c (h:(real^N->bool)->bool)` THEN
        REWRITE_TAC[moi_bar_chain; SUBSET] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `~((t1:real^N->bool) IN h /\ t2 IN h)` ASSUME_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(t1:real^N->bool) SUBSET t2 \/ t2 SUBSET t1` MP_TAC THENL
       [UNDISCH_TAC `moi_bar_chain c (h:(real^N->bool)->bool)` THEN
        REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      STRIP_TAC THENL
       [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t1:real^N->bool`; `t2:real^N->bool`]
                      MOI_FN2_SUBSET_DIM_EQ);
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t2:real^N->bool`; `t1:real^N->bool`]
                      MOI_FN2_SUBSET_DIM_EQ)] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`h:(real^N->bool)->bool`; `e:real^N->bool`; `t1:real^N->bool`;
                   `t2:real^N->bool`] MOI_FN2_SUBSET3_CASES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `segment[simplex_barycentre e:real^N,simplex_barycentre t1]` THEN
      REWRITE_TAC[SUBSET_UNION; SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE simplex_barycentre {e:real^N->bool,t1}` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET] THEN REWRITE_TAC[IMAGE_CLAUSES; SUBSET_REFL];
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `segment[simplex_barycentre e:real^N,simplex_barycentre t2]` THEN
      REWRITE_TAC[SUBSET_UNION; SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
      MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `IMAGE simplex_barycentre {e:real^N->bool,t2}` THEN
      ASM_SIMP_TAC[IMAGE_SUBSET] THEN REWRITE_TAC[IMAGE_CLAUSES; SUBSET_REFL]];
    REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s:real^N->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[IN_ELIM_THM] THENL
     [EXISTS_TAC `{e:real^N->bool,t1}`; EXISTS_TAC `{e:real^N->bool,t2}`] THEN
    REWRITE_TAC[IMAGE_CLAUSES; SEGMENT_CONVEX_HULL; NOT_INSERT_EMPTY; MOI_FRN_CHAIN_PAIR;
                FORALL_IN_INSERT; NOT_IN_EMPTY; SUBSET_REFL] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FN2_PAIR_INTER = prove
 (`!(k:A->bool) e t. e IN k /\ ~(t IN k) ==> {e,t} INTER k = {e}`,
  SET_TAC[]);;

(* The dual cell of an edge e of a 1-dimensional subcomplex k of a finite   *)
(* combinatorial surface meets |k| only in the barycentre of e.             *)

let MOI_FN2_DUAL_TRACE = prove
 (`!(c:(real^N->bool)->bool) k e.
     FINITE c /\ combinatorial_manifold 2 c /\ simplicial_subcomplex k c /\
     (!s. s IN k ==> aff_dim s <= &1) /\ e IN k /\ aff_dim e = &1
     ==> moi_fn2_dual c e INTER UNIONS k = {simplex_barycentre e}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `(e:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim ({}:real^N->bool) = &1` THEN
    REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FN2_DUAL_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(t1:real^N->bool) IN c /\ aff_dim t1 = &2 /\ e SUBSET t1 /\
    (t2:real^N->bool) IN c /\ aff_dim t2 = &2 /\ e SUBSET t2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = {t1,t2}` THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `t1:real^N->bool` (GEN_REWRITE_RULE I [EXTENSION] th)) THEN
      MP_TAC(SPEC `t2:real^N->bool` (GEN_REWRITE_RULE I [EXTENSION] th))) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((t1:real^N->bool) IN k) /\ ~((t2:real^N->bool) IN k)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `!s:real^N->bool. s IN k ==> aff_dim s <= &1` THEN
      DISCH_THEN(MP_TAC o SPEC `t1:real^N->bool`);
      UNDISCH_TAC `!s:real^N->bool. s IN k ==> aff_dim s <= &1` THEN
      DISCH_THEN(MP_TAC o SPEC `t2:real^N->bool`)] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^N->bool.
      t IN c /\ ~(t IN k) /\ e SUBSET t
      ==> segment[simplex_barycentre e,simplex_barycentre t] INTER UNIONS k =
          {simplex_barycentre e}`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~(t:real^N->bool = {})` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                   `{e:real^N->bool,t}`] MOI_FRN_FULL_CHAIN) THEN
    ASM_SIMP_TAC[MOI_FRN_CHAIN_PAIR; MOI_FN2_PAIR_INTER; IMAGE_CLAUSES;
                 CONVEX_HULL_SING; GSYM SEGMENT_CONVEX_HULL];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SET_RULE `((a:real^N->bool) UNION b) INTER u = (a INTER u) UNION (b INTER u)`] THEN
  REWRITE_TAC[UNION_IDEMPOT]);;

let MOI_FN2_SING_IN = prove
 (`!(g:A->bool) a. a IN g /\ (!r. r IN g ==> r = a) ==> g = {a}`,
  SET_TAC[]);;

let MOI_FN2_PAIR_IN = prove
 (`!(g:A->bool) a b. a IN g /\ b IN g /\ (!r. r IN g ==> r = a \/ r = b) ==> g = {a,b}`,
  SET_TAC[]);;

(* Chains through a vertex w in a 1-dimensional subcomplex: {w} alone or   *)
(* {w} with one edge at w.                                                   *)

let MOI_FN2_K1_CHAIN = prove
 (`!(c:(real^N->bool)->bool) k g w.
     moi_bar_complex c /\ simplicial_subcomplex k c /\
     (!s. s IN k ==> aff_dim s <= &1) /\
     moi_bar_chain c g /\ g SUBSET k /\ {w} IN g
     ==> g = {{w}} \/ ?e. e IN k /\ aff_dim e = &1 /\ w IN e /\ g = {{w},e}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!r:real^N->bool. r IN g ==> r = {w} \/ (aff_dim r = &1 /\ w IN r)`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `~(r:real^N->bool = {}) /\ (r SUBSET {w} \/ {w} SUBSET r) /\ r IN k`
    MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
    STRIP_TAC THENL
     [DISJ1_TAC THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `r:real^N->bool = {w}` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]] THEN
    MP_TAC(ISPEC `r:real^N->bool` AFF_DIM_GE) THEN
    SUBGOAL_THEN `aff_dim (r:real^N->bool) <= &1` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim (r:real^N->bool) = -- &1)` MP_TAC THENL
     [ASM_REWRITE_TAC[AFF_DIM_EQ_MINUS1]; ALL_TAC] THEN
    SUBGOAL_THEN `~(aff_dim (r:real^N->bool) = &0)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
      UNDISCH_TAC `~(r:real^N->bool = {w})` THEN
      UNDISCH_TAC `{w:real^N} SUBSET r` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      INT_ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `?e:real^N->bool. e IN g /\ ~(e = {w})` THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
    DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
    SUBGOAL_THEN `aff_dim (e:real^N->bool) = &1 /\ w IN e` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FN2_PAIR_IN THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    ASM_CASES_TAC `r:real^N->bool = {w}` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `aff_dim (r:real^N->bool) = &1` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(r:real^N->bool) SUBSET e \/ e SUBSET r` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
    SUBGOAL_THEN `(r:real^N->bool) IN c /\ (e:real^N->bool) IN c` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
    STRIP_TAC THENL
     [MATCH_MP_TAC MOI_FN2_SUBSET_DIM_EQ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FN2_SUBSET_DIM_EQ THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
    DISJ1_TAC THEN MATCH_MP_TAC MOI_FN2_SING_IN THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[]]);;

(* The trace of the closed star of a vertex w of k on |k| (k as above): the *)
(* half edges from w to the barycentres of the edges of k at w.             *)

let MOI_FN2_STAR_TRACE = prove
 (`!(c:(real^N->bool)->bool) k w.
     moi_bar_complex c /\ simplicial_subcomplex k c /\
     (!s. s IN k ==> aff_dim s <= &1) /\ {w} IN k /\
     (?e. e IN k /\ aff_dim e = &1 /\ w IN e)
     ==> UNIONS (moi_fm3_cstar (barycentric_subdivision c) w) INTER UNIONS k =
         UNIONS {segment[w,simplex_barycentre e] | e |
                 e IN k /\ aff_dim e = &1 /\ w IN e}`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `e0:real^N->bool` STRIP_ASSUME_TAC))))) THEN
  SUBGOAL_THEN `{w:real^N} IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FN2_STAR_CHAINS] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    UNDISCH_TAC
     `(x:real^N) IN UNIONS {convex hull (IMAGE simplex_barycentre f) | f |
                            moi_bar_chain c f /\ {w} IN f}` THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER k))`
    ASSUME_TAC THENL
     [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                     `f:(real^N->bool)->bool`] MOI_FRN_FULL_CHAIN) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
      ASM_MESON_TAC[IN_INTER];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `k:(real^N->bool)->bool`;
                   `(f:(real^N->bool)->bool) INTER k`; `w:real^N`] MOI_FN2_K1_CHAIN) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[INTER_SUBSET; IN_INTER] THEN
      MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[INTER_SUBSET];
      ALL_TAC] THEN
    DISCH_THEN(DISJ_CASES_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)) THENL
     [UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER k))` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FRN_BARYCENTRE_SING; CONVEX_HULL_SING;
                      IN_SING] THEN
      DISCH_THEN SUBST1_TAC THEN
      EXISTS_TAC `segment[w:real^N,simplex_barycentre e0]` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `e0:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre (f INTER k))` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; MOI_FRN_BARYCENTRE_SING; GSYM SEGMENT_CONVEX_HULL] THEN
      DISCH_TAC THEN EXISTS_TAC `segment[w:real^N,simplex_barycentre e]` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e:real^N->bool) IN c /\ ~(e = {})` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET; MEMBER_NOT_EMPTY]; ALL_TAC] THEN
    SUBGOAL_THEN `?n. n simplex (e:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE `!s:real^N->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `{{w:real^N},e}` THEN
      REWRITE_TAC[IMAGE_CLAUSES; MOI_FRN_BARYCENTRE_SING; GSYM SEGMENT_CONVEX_HULL;
                  IN_INSERT; MOI_FRN_CHAIN_PAIR; NOT_INSERT_EMPTY; SING_SUBSET] THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `e:real^N->bool` THEN CONJ_TAC THENL
       [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
        ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
        ASM_MESON_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_IN; SIMPLEX_IMP_CONVEX];
        MATCH_MP_TAC(SET_RULE `!s:real^N->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
        ASM_REWRITE_TAC[]]]]);;

(* Each simplex of the closed star in bsd c of a vertex w of c lies in a    *)
(* simplex of c containing w.                                                *)

let MOI_FN2_CSTAR_IN_SIMPLEX = prove
 (`!(c:(real^N->bool)->bool) w s.
     moi_bar_complex c /\ s IN moi_fm3_cstar (barycentric_subdivision c) w
     ==> ?t. t IN c /\ w IN t /\ s SUBSET t`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fm3_cstar; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `(r:real^N->bool) IN barycentric_subdivision c` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(f:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(w:real^N) IN r` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  EXISTS_TAC `UNIONS f:real^N->bool` THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
                MOI_BAR_CHAIN_HULL_SUBSET_MAX) THEN
  ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET];
    ASM_MESON_TAC[SUBSET];
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_SIMP_TAC[FACE_OF_IMP_SUBSET] THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* The cycle of the polygon.  The first                                     *)
(* derived k = bsd l of a triangulated PL circle is a cycle of vertices     *)
(* S 0, ..., S(n-1) (moi_fn2_kcyc); it is full in c = bsd m, so a simplex  *)
(* of c contains at most two vertices of k, and then they span an edge of  *)
(* k.  Consequently the closed stars in bsd c of S i and S j are disjoint  *)
(* unless i and j are cyclic neighbours, and three such stars never meet.  *)
(* ========================================================================= *)

let moi_fn2_kcyc = new_definition
 `moi_fn2_kcyc (k:(real^N->bool)->bool) n (S:num->real^N) <=>
    3 <= n /\ (!i. S(i + n) = S i) /\
    (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
    (!i. {S i} IN k /\ segment[S i,S(SUC i)] IN k) /\
    (!v. {v} IN k ==> ?i. i < n /\ v = S i) /\
    (!e. e IN k /\ aff_dim e = &1 ==> ?i. i < n /\ e = segment[S i,S(SUC i)]) /\
    UNIONS k = UNIONS {segment[S i,S(SUC i)] | i < n}`;;

let MOI_FN2_CYC_N = prove
 (`!n (S:num->A). (!i. S(i + n) = S i) ==> S n = S 0`,
  REPEAT STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `0`) THEN
  REWRITE_TAC[ADD_CLAUSES]);;

let MOI_FN2_CYC_NEQ_SUC = prove
 (`!n (S:num->A) p.
     3 <= n /\ (!i. S(i + n) = S i) /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\ p < n
     ==> ~(S p = S(SUC p))`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `SUC p < n` THENL
   [SUBGOAL_THEN `p = SUC p` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `SUC p = n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(S:num->A) p = S 0` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`n:num`; `S:num->A`] MOI_FN2_CYC_N) THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `p = 0` MP_TAC THENL
   [FIRST_X_ASSUM MATCH_MP_TAC THEN REPEAT CONJ_TAC THENL
     [ASM_ARITH_TAC; ASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
    ASM_ARITH_TAC]);;

(* A triangulated circle (1-dimensional, every vertex of degree 2,         *)
(* connected and nonempty) is a cycle.                                       *)

let MOI_FN2_KCYC_EXISTS = prove
 (`!k:(real^N->bool)->bool.
     simplicial_complex k /\ (!s. s IN k ==> aff_dim s <= &1) /\
     (!v. {v} IN k ==> CARD {e | e IN k /\ aff_dim e = &1 /\ v IN e} = 2) /\
     connected (UNIONS k) /\ ~(UNIONS k = {})
     ==> ?n S. moi_fn2_kcyc k n S`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`k:(real^N->bool)->bool`; `UNIONS k:real^N->bool`]
                MOI_S4L_CM1_CYCLE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[COMPONENTS_EQ_SING; IN_SING];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `S:num->real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `S:num->real^N`] THEN
  REWRITE_TAC[moi_fn2_kcyc] THEN
  SUBGOAL_THEN `moi_bar_complex (k:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_SIMPLICIAL_COMPLEX]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    ASM_REWRITE_TAC[];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    CONJ_TAC THENL
     [ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{v:real^N}` THEN
      ASM_REWRITE_TAC[IN_SING]];
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`k:(real^N->bool)->bool`; `e:real^N->bool`] MOI_S4L_K1_CASES) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY; INT_ARITH `~(-- &1:int = &1)`];
      UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[AFF_DIM_SING; INT_ARITH `~(&0:int = &1)`];
      ALL_TAC] THEN
    UNDISCH_TAC `e = segment[a:real^N,b]` THEN DISCH_THEN SUBST_ALL_TAC THEN
    SUBGOAL_THEN
     `midpoint(a:real^N,b) IN UNIONS {segment[(S:num->real^N) i,S(SUC i)] | i < n}`
    MP_TAC THENL
     [UNDISCH_TAC `UNIONS k = UNIONS {segment[(S:num->real^N) i,S(SUC i)] | i < n}` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `segment[a:real^N,b]` THEN
      ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT];
      ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    EXISTS_TAC `p:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((S:num->real^N) p = S(SUC p))` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[(S:num->real^N) p,S(SUC p)] IN k` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `segment[a:real^N,b] INTER segment[(S:num->real^N) p,S(SUC p)] = segment[a,b]`
    ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`segment[a:real^N,b] INTER segment[(S:num->real^N) p,S(SUC p)]`;
                     `segment[a:real^N,b]`] FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
      ASM_REWRITE_TAC[RELATIVE_INTERIOR_SEGMENT] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `midpoint(a:real^N,b)` THEN
      ASM_REWRITE_TAC[MIDPOINT_IN_SEGMENT] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FN2_SUBSET_DIM_EQ THEN EXISTS_TAC `k:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The setting of the main theorem: m a finite closed combinatorial surface, *)
(* l a subcomplex whose polyhedron is a PL circle.                           *)

let MOI_FN2_CONTEXT = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> lf_simplicial_complex m /\ FINITE l /\
         FINITE (barycentric_subdivision m) /\
         combinatorial_manifold 2 (barycentric_subdivision m) /\
         moi_bar_complex (barycentric_subdivision m) /\
         simplicial_subcomplex (barycentric_subdivision l) (barycentric_subdivision m) /\
         UNIONS (barycentric_subdivision l) = UNIONS l /\
         simplicial_complex (barycentric_subdivision l) /\
         (!s. s IN barycentric_subdivision l ==> aff_dim s <= &1) /\
         (!v. {v} IN barycentric_subdivision l
              ==> CARD {e | e IN barycentric_subdivision l /\ aff_dim e = &1 /\ v IN e} = 2) /\
         connected (UNIONS l) /\ ~(UNIONS l = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; FINITE_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPEC `m:(real^N->bool)->bool` MOI_FC2_BARYCENTRIC_CM2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `moi_bar_complex (barycentric_subdivision (m:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
                BARYCENTRIC_SUBDIVISION_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `simplicial_complex (barycentric_subdivision (l:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_BAR_SIMPLICIAL_COMPLEX] THEN
    ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE] THEN
    MATCH_MP_TAC MOI_BAR_SUBDIVISION_COMPLEX THEN
    MATCH_MP_TAC MOI_FRN_LF_BAR_COMPLEX THEN
    ASM_MESON_TAC[MOI_FDN_LF_SUBCOMPLEX];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `pl_sphere 1 (UNIONS (l:(real^N->bool)->bool))` THEN
  REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `homeomorphism (relative_frontier k,
                   UNIONS (barycentric_subdivision (l:(real^N->bool)->bool)))
                  (f:real^N->real^N,g)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  SUBGOAL_THEN `!s. s IN barycentric_subdivision (l:(real^N->bool)->bool)
                    ==> aff_dim s <= &1`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`barycentric_subdivision (l:(real^N->bool)->bool)`;
                         `k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`]
                        MOI_FSA_LK_DIM) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `complex_euler (barycentric_subdivision (l:(real^N->bool)->bool)) = &0`
  ASSUME_TAC THENL
   [MP_TAC(ISPEC `barycentric_subdivision (l:(real^N->bool)->bool)`
                 COMPLEX_EULER_VALUES) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC(INT_ARITH `x <= &1 ==> x:int <= &2`) THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[pl_sphere] THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    MATCH_MP_TAC(ISPECL [`barycentric_subdivision (l:(real^N->bool)->bool)`;
                         `k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`]
                        MOI_FSA_LK_DEG2) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`barycentric_subdivision (l:(real^N->bool)->bool)`;
                   `k:real^N->bool`; `f:real^N->real^N`; `g:real^N->real^N`]
                  MOI_FSA_LK_CONNECTED) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    MP_TAC(ISPEC `k:real^N->bool` MOI_FSA_RF_TWO_POINTS) THEN ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN
    UNDISCH_TAC
     `homeomorphism (relative_frontier k,
                     UNIONS (barycentric_subdivision (l:(real^N->bool)->bool)))
                    (f:real^N->real^N,g)` THEN
    ASM_REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(f:real^N->real^N) a` THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^N) (relative_frontier k) = UNIONS l` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE]]);;

(* Fullness of k = bsd l in c = bsd m: two vertices of k lying in a common  *)
(* simplex of c span an edge of k; three never lie in a common simplex.     *)

let MOI_FN2_FULL_TRACE_SEG = prove
 (`!(m:(real^N->bool)->bool) l r.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     simplicial_complex (barycentric_subdivision l) /\
     (!s. s IN barycentric_subdivision l ==> aff_dim s <= &1) /\
     r IN barycentric_subdivision m
     ==> r INTER UNIONS l IN barycentric_subdivision l /\
         (!u. {u} IN barycentric_subdivision l /\ u IN r ==> u IN r INTER UNIONS l)`,
  REPEAT STRIP_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_FULL]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
                BARYCENTRIC_SUBDIVISION_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT2) THEN
  REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^N}` THEN ASM_REWRITE_TAC[IN_SING]);;

let MOI_FN2_FULL_EDGE = prove
 (`!(m:(real^N->bool)->bool) l r u w.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     simplicial_complex (barycentric_subdivision l) /\
     (!s. s IN barycentric_subdivision l ==> aff_dim s <= &1) /\
     r IN barycentric_subdivision m /\
     {u} IN barycentric_subdivision l /\ {w} IN barycentric_subdivision l /\
     ~(u = w) /\ u IN r /\ w IN r
     ==> segment[u,w] IN barycentric_subdivision l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
                MOI_FN2_FULL_TRACE_SEG) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = (r:real^N->bool) INTER UNIONS l` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^N) IN q /\ (w:real^N) IN q` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (l:(real^N->bool)->bool)`; `q:real^N->bool`]
                MOI_S4L_K1_CASES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[NOT_IN_EMPTY];
    UNDISCH_TAC `~(u:real^N = w)` THEN UNDISCH_TAC `(u:real^N) IN q` THEN
    UNDISCH_TAC `(w:real^N) IN q` THEN ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u = a \/ u = b) /\ (w = a \/ w = (b:real^N))` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_S4L_K1_ENDPOINT THEN
    EXISTS_TAC `barycentric_subdivision (l:(real^N->bool)->bool)` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_MESON_TAC[SEGMENT_SYM]);;

let MOI_FN2_FULL_TRIPLE = prove
 (`!(m:(real^N->bool)->bool) l r u v w.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     simplicial_complex (barycentric_subdivision l) /\
     (!s. s IN barycentric_subdivision l ==> aff_dim s <= &1) /\
     r IN barycentric_subdivision m /\
     {u} IN barycentric_subdivision l /\ {v} IN barycentric_subdivision l /\
     {w} IN barycentric_subdivision l /\
     ~(u = v) /\ ~(u = w) /\ ~(v = w) /\ u IN r /\ v IN r /\ w IN r
     ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
                MOI_FN2_FULL_TRACE_SEG) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q = (r:real^N->bool) INTER UNIONS l` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(u:real^N) IN q /\ (v:real^N) IN q /\ (w:real^N) IN q`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (l:(real^N->bool)->bool)`; `q:real^N->bool`]
                MOI_S4L_K1_CASES) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
   [ASM_MESON_TAC[NOT_IN_EMPTY];
    UNDISCH_TAC `~(u:real^N = w)` THEN UNDISCH_TAC `(u:real^N) IN q` THEN
    UNDISCH_TAC `(w:real^N) IN q` THEN ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(u = a \/ u = b) /\ (v = a \/ v = b) /\ (w = a \/ w = (b:real^N))`
  MP_TAC THENL
   [REPEAT CONJ_TAC THEN MATCH_MP_TAC MOI_S4L_K1_ENDPOINT THEN
    EXISTS_TAC `barycentric_subdivision (l:(real^N->bool)->bool)` THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* In a cycle, an edge of k between S i and S j (i < j < n) joins cyclic     *)
(* neighbours.                                                               *)

let MOI_FN2_KCYC_ADJ = prove
 (`!(k:(real^N->bool)->bool) n S i j.
     moi_fn2_kcyc k n S /\ i < j /\ j < n /\ segment[S i,S j] IN k
     ==> j = SUC i \/ (i = 0 /\ j = n - 1)`,
  REWRITE_TAC[moi_fn2_kcyc] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~((S:num->real^N) i = S j)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `i:num = j` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `segment[(S:num->real^N) i,S j]` o
    check (fun th -> can (find_term (fun t -> t = `&1:int`)) (concl th) &&
                     is_forall (concl th))) THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `segment[(S:num->real^N) i,S j] = segment[S a,S(SUC a)]` THEN
  REWRITE_TAC[SEGMENT_EQ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
    `{x:real^N,y} = {z,w} ==> (x = z /\ y = w) \/ (x = w /\ y = z)`)) THEN
  SUBGOAL_THEN `(S:num->real^N) n = S 0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FN2_CYC_N THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `SUC a < n` THENL
   [STRIP_TAC THENL
     [SUBGOAL_THEN `i:num = a /\ j = SUC a` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      SUBGOAL_THEN `i:num = SUC a /\ j = a` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        ASM_ARITH_TAC]];
    SUBGOAL_THEN `SUC a = n` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [SUBGOAL_THEN `j = 0` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      SUBGOAL_THEN `i = 0 /\ j:num = a` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        ASM_ARITH_TAC;
        ASM_ARITH_TAC]]]);;

(* The closed stars of the cycle vertices in the second derived of m.        *)

let MOI_FN2_KSTARS = prove
 (`!(m:(real^N->bool)->bool) l n S.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ moi_fn2_kcyc (barycentric_subdivision l) n S
     ==> (!i j. i < j /\ j < n /\ ~(j = SUC i) /\ ~(i = 0 /\ j = n - 1)
                ==> UNIONS (moi_fm3_cstar (barycentric_subdivision
                              (barycentric_subdivision m)) (S i)) INTER
                    UNIONS (moi_fm3_cstar (barycentric_subdivision
                              (barycentric_subdivision m)) (S j)) = {}) /\
         (!i. i < n
              ==> UNIONS (moi_fm3_cstar (barycentric_subdivision
                            (barycentric_subdivision m)) (S i)) INTER
                  UNIONS (moi_fm3_cstar (barycentric_subdivision
                            (barycentric_subdivision m)) (S(SUC i))) =
                  moi_fn2_dual (barycentric_subdivision m) (segment[S i,S(SUC i)])) /\
         (!u v w. {u} IN barycentric_subdivision l /\ {v} IN barycentric_subdivision l /\
                  {w} IN barycentric_subdivision l /\
                  ~(u = v) /\ ~(u = w) /\ ~(v = w)
                  ==> UNIONS (moi_fm3_cstar (barycentric_subdivision
                                (barycentric_subdivision m)) u) INTER
                      UNIONS (moi_fm3_cstar (barycentric_subdivision
                                (barycentric_subdivision m)) v) INTER
                      UNIONS (moi_fm3_cstar (barycentric_subdivision
                                (barycentric_subdivision m)) w) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v:real^N. {v} IN barycentric_subdivision l
                           ==> {v} IN barycentric_subdivision m`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fn2_kcyc]) THEN
  REPEAT CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `~((S:num->real^N) i = S j)` ASSUME_TAC THENL
     [DISCH_TAC THEN SUBGOAL_THEN `i:num = j` MP_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                   `(S:num->real^N) i`; `(S:num->real^N) j`] MOI_FN2_STAR_INTER) THEN
    ASM_SIMP_TAC[] THEN DISCH_THEN(K ALL_TAC) THEN
    MATCH_MP_TAC MOI_FN2_DUAL_EMPTY THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `segment[(S:num->real^N) i,S j] IN barycentric_subdivision l`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FN2_FULL_EDGE THEN
      MAP_EVERY EXISTS_TAC [`m:(real^N->bool)->bool`; `r:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (l:(real^N->bool)->bool)`; `n:num`;
                   `S:num->real^N`; `i:num`; `j:num`] MOI_FN2_KCYC_ADJ) THEN
    ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FN2_STAR_INTER THEN
    ASM_SIMP_TAC[] THEN MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC THEN
    EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FN2_STAR_INTER3 THEN
    ASM_SIMP_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`;
                   `u:real^N`; `v:real^N`; `w:real^N`] MOI_FN2_FULL_TRIPLE) THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* N = derived_nbhd m l is connected and                                    *)
(* has Euler characteristic 0.  N is the union of the closed stars St(S i)  *)
(* of the cycle vertices (each a PL 2-ball, Euler characteristic 1);        *)
(* consecutive stars meet in the dual arc of their edge (two segments with  *)
(* a common end, Euler characteristic 1), other pairs are disjoint; adding  *)
(* the stars one by one gives 1 + (n - 2)(1 - 1) + (1 - 2) = 0.            *)
(* ========================================================================= *)

let MOI_FN2_CONE_CONNECTED = prove
 (`!(w:real^N) L. connected (UNIONS {segment[w,y] | y | y IN L})`,
  REPEAT GEN_TAC THEN MATCH_MP_TAC CONNECTED_UNIONS THEN
  REWRITE_TAC[FORALL_IN_GSPEC; CONNECTED_SEGMENT] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `w:real^N` THEN
  REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; ENDS_IN_SEGMENT]);;

(* The closed star in bsd c of a vertex of a finite combinatorial surface c *)
(* is the cone over its (nonempty) link, hence connected.                   *)

let MOI_FN2_STAR_CONE = prove
 (`!(c:(real^N->bool)->bool) w.
     FINITE c /\ combinatorial_manifold 2 c /\ {w} IN c
     ==> UNIONS (moi_fm3_cstar (barycentric_subdivision c) w) =
         UNIONS {segment[w,y] | y | y IN UNIONS (simplicial_link
                                                  (barycentric_subdivision c) w)} /\
         ~(UNIONS (simplicial_link (barycentric_subdivision c) w) = {}) /\
         connected (UNIONS (moi_fm3_cstar (barycentric_subdivision c) w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `~(UNIONS (simplicial_link (barycentric_subdivision c) (w:real^N)) = {})`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{w:real^N}`] MOI_FC2_LINK_CONNECTED) THEN
    ASM_REWRITE_TAC[NOT_INSERT_EMPTY; MOI_FRN_BARYCENTRE_SING] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `UNIONS (moi_fm3_cstar (barycentric_subdivision c) (w:real^N)) =
    UNIONS {segment[w,y] | y | y IN UNIONS (simplicial_link (barycentric_subdivision c) w)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_UNIONS_CSTAR THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FC2_BARYCENTRIC_CM2) THEN
      ASM_MESON_TAC[combinatorial_manifold];
      MATCH_MP_TAC MOI_FRN_SING_IN_BARY THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[MOI_FN2_CONE_CONNECTED]);;

let MOI_FN2_NBHD_CONNECTED = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> connected (derived_nbhd m l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS l SUBSET derived_nbhd m (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
                  DERIVED_NBHD_BASIC) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `(subtopology euclidean (UNIONS (m:(real^N->bool)->bool))) interior_of
                (derived_nbhd m l)` THEN
    ASM_REWRITE_TAC[INTERIOR_OF_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_NBHD_STARS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "ST") THEN
  SUBGOAL_THEN
   `derived_nbhd m (l:(real^N->bool)->bool) =
    UNIONS {UNIONS (moi_fm3_cstar (barycentric_subdivision (barycentric_subdivision m)) w)
            UNION UNIONS l | w | {w} IN barycentric_subdivision l}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [USE_THEN "ST" (fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
      MATCH_MP_TAC UNIONS_MONO THEN REWRITE_TAC[FORALL_IN_GSPEC; EXISTS_IN_GSPEC] THEN
      X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN EXISTS_TAC `w:real^N` THEN
      ASM_REWRITE_TAC[SUBSET_UNION];
      GEN_REWRITE_TAC I [UNIONS_SUBSET] THEN REWRITE_TAC[FORALL_IN_GSPEC; UNION_SUBSET] THEN
      X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
       [USE_THEN "ST" (fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
        MATCH_MP_TAC(SET_RULE `!s:real^N->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `w:real^N` THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  REMOVE_THEN "ST" (K ALL_TAC) THEN
  MATCH_MP_TAC CONNECTED_UNIONS THEN REWRITE_TAC[FORALL_IN_GSPEC] THEN CONJ_TAC THENL
   [X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN MATCH_MP_TAC CONNECTED_UNION THEN
    SUBGOAL_THEN `{w:real^N} IN barycentric_subdivision m` ASSUME_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `w:real^N`]
                  MOI_FN2_STAR_CONE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `w:real^N` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `~(UNIONS (simplicial_link
                     (barycentric_subdivision (barycentric_subdivision m)) (w:real^N)) = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `segment[w:real^N,y]` THEN
      REWRITE_TAC[ENDS_IN_SEGMENT] THEN EXISTS_TAC `y:real^N` THEN
      ASM_REWRITE_TAC[GSYM IN_UNIONS];
      UNDISCH_TAC `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING]];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    UNDISCH_TAC `~(UNIONS l:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
    EXISTS_TAC `x:real^N` THEN REWRITE_TAC[IN_INTERS; FORALL_IN_GSPEC; IN_UNION] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FN2_EULER_SEGMENT = prove
 (`!a b:real^N. moi_feu_euler (segment[a,b]) (&1)`,
  REPEAT GEN_TAC THEN
  X_CHOOSE_TAC `n:int` (ISPECL [`a:real^N`; `b:real^N`] SIMPLEX_SEGMENT) THEN
  MATCH_MP_TAC MOI_FEU_EULER_SIMPLEX THEN EXISTS_TAC `n:int` THEN
  ASM_REWRITE_TAC[SEGMENT_EQ_EMPTY]);;

let MOI_FN2_EULER_SING = prove
 (`!a:real^N. moi_feu_euler {a} (&1)`,
  MESON_TAC[MOI_FN2_EULER_SEGMENT; SEGMENT_REFL]);;

(* The closed star of a vertex in the barycentric subdivision of a finite   *)
(* combinatorial surface has Euler characteristic 1 (it is a PL 2-ball).    *)

let MOI_FN2_EULER_STAR = prove
 (`!(c:(real^N->bool)->bool) w.
     FINITE c /\ combinatorial_manifold 2 c /\ {w} IN c
     ==> moi_feu_euler (UNIONS (moi_fm3_cstar (barycentric_subdivision c) w)) (&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_FC2_BARYCENTRIC_CM2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision (c:(real^N->bool)->bool))`
  ASSUME_TAC THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^N} IN barycentric_subdivision c` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_SING_IN_BARY THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (c:(real^N->bool)->bool)`; `w:real^N`]
                MOI_FM3_CSTAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `complex_euler (moi_fm3_cstar (barycentric_subdivision c) (w:real^N)) = &1`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision (c:(real^N->bool)->bool)`; `w:real^N`]
                  MOI_FC2_STAR_CIRCLE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `combinatorial_manifold 2 (barycentric_subdivision (c:(real^N->bool)->bool))` THEN
      REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^2->bool` (X_CHOOSE_THEN `p:real^N->real^2`
      (X_CHOOSE_THEN `q:real^2->real^N` STRIP_ASSUME_TAC))) THEN
    MATCH_MP_TAC(ISPEC `S:real^2->bool` MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
    MAP_EVERY EXISTS_TAC [`q:real^2->real^N`; `p:real^N->real^2`] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FEU_EULER_SIMPLEX THEN EXISTS_TAC `&2:int` THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SIMPLEX_EMPTY; INT_ARITH `~(&2:int = -- &1)`];
      ASM_MESON_TAC[SIMPLEX_IMP_COMPACT];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`] MOI_FN2_STAR_CONE) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `moi_fm3_cstar (barycentric_subdivision c) (w:real^N)`
               MOI_FEU_EULER_SIMPLICIAL_COMPLEX) THEN
  ASM_REWRITE_TAC[]);;

(* The dual arc of an edge of a finite combinatorial surface has Euler      *)
(* characteristic 1.                                                         *)

let MOI_FN2_EULER_DUAL = prove
 (`!(c:(real^N->bool)->bool) e.
     FINITE c /\ combinatorial_manifold 2 c /\ e IN c /\ aff_dim e = &1
     ==> moi_feu_euler (moi_fn2_dual c e) (&1)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FN2_DUAL_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `(t1:real^N->bool) IN c /\ aff_dim t1 = &2 /\ e SUBSET t1 /\
    (t2:real^N->bool) IN c /\ aff_dim t2 = &2 /\ e SUBSET t2`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{t:real^N->bool | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = {t1,t2}` THEN
    DISCH_THEN(fun th ->
      MP_TAC(SPEC `t1:real^N->bool` (GEN_REWRITE_RULE I [EXTENSION] th)) THEN
      MP_TAC(SPEC `t2:real^N->bool` (GEN_REWRITE_RULE I [EXTENSION] th))) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(e:real^N->bool = {}) /\ ~(t1:real^N->bool = {}) /\ ~(t2:real^N->bool = {}) /\
                ~(e = t1) /\ ~(e = t2)`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th ->
      let c = concl th in is_eq c && (lhs c = `-- &1:int` || lhs c = `&1:int`)))) THEN
    TRY INT_ARITH_TAC THEN ASM_MESON_TAC[INT_ARITH `~(&1:int = &2)`];
    ALL_TAC] THEN
  ABBREV_TAC `be = simplex_barycentre (e:real^N->bool)` THEN
  ABBREV_TAC `b1 = simplex_barycentre (t1:real^N->bool)` THEN
  ABBREV_TAC `b2 = simplex_barycentre (t2:real^N->bool)` THEN
  SUBGOAL_THEN `~(be:real^N = b1) /\ ~(be = b2) /\ ~(b1 = b2)` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["be"; "b1"; "b2"] THEN
    ASM_MESON_TAC[MOI_FRN_BARYCENTRE_INJ];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[be:real^N,b1] IN barycentric_subdivision c /\
    segment[be:real^N,b2] IN barycentric_subdivision c`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN CONJ_TAC THENL
     [EXISTS_TAC `{e:real^N->bool,t1}`; EXISTS_TAC `{e:real^N->bool,t2}`] THEN
    MAP_EVERY EXPAND_TAC ["be"; "b1"; "b2"] THEN
    REWRITE_TAC[MOI_FRN_CHAIN_PAIR; IMAGE_CLAUSES; SEGMENT_CONVEX_HULL] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (barycentric_subdivision (c:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_BAR_SIMPLICIAL_COMPLEX] THEN
    ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE; MOI_BAR_SUBDIVISION_COMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[be:real^N,b1] INTER segment[be,b2] = {be}` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [MATCH_MP_TAC SUBSET_TRANS THEN
      EXISTS_TAC `{be:real^N,b1} INTER {be,b2}` THEN CONJ_TAC THENL
       [MATCH_MP_TAC MOI_SLV_SEGMENTS_INTER THEN
        EXISTS_TAC `barycentric_subdivision (c:(real^N->bool)->bool)` THEN
        ASM_REWRITE_TAC[SEGMENT_EQ] THEN
        UNDISCH_TAC `~(b1:real^N = b2)` THEN UNDISCH_TAC `~(be:real^N = b1)` THEN
        SET_TAC[];
        UNDISCH_TAC `~(b1:real^N = b2)` THEN UNDISCH_TAC `~(be:real^N = b2)` THEN
        UNDISCH_TAC `~(be:real^N = b1)` THEN SET_TAC[]];
      REWRITE_TAC[SING_SUBSET; IN_INTER; ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 = &1 + &1 - &1` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FEU_EULER_UNION THEN
  ASM_REWRITE_TAC[MOI_FN2_EULER_SEGMENT; MOI_FN2_EULER_SING]);;

let MOI_FN2_GSPEC_LE_SUC = prove
 (`!(f:num->A) j. {f i | i <= SUC j} = f(SUC j) INSERT {f i | i <= j}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; LE] THEN MESON_TAC[]);;

let MOI_FN2_GSPEC_LE_0 = prove
 (`!(f:num->A). {f i | i <= 0} = {f 0}`,
  REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_SING; LE] THEN MESON_TAC[]);;

(* The union of the first j + 1 stars (j < n - 1) has Euler characteristic  *)
(* 1, and so N has Euler characteristic 0.                                   *)

let MOI_FN2_EULER_CHAIN = prove
 (`!(m:(real^N->bool)->bool) l n S.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ moi_fn2_kcyc (barycentric_subdivision l) n S
     ==> !j. j < n - 1
             ==> moi_feu_euler
                   (UNIONS {UNIONS (moi_fm3_cstar (barycentric_subdivision
                              (barycentric_subdivision m)) (S i)) | i | i <= j})
                   (&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `n:num`;
                 `S:num->real^N`] MOI_FN2_KSTARS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "K1") (CONJUNCTS_THEN2 (LABEL_TAC "K2")
    (LABEL_TAC "K3"))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fn2_kcyc]) THEN
  SUBGOAL_THEN `!i. {(S:num->real^N) i} IN barycentric_subdivision m` ASSUME_TAC THENL
   [GEN_TAC THEN
    UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                   (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  INDUCT_TAC THENL
   [DISCH_TAC THEN REWRITE_TAC[MOI_FN2_GSPEC_LE_0; UNIONS_1] THEN
    MATCH_MP_TAC MOI_FN2_EULER_STAR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o check (is_imp o concl)) THEN
  ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_TAC] THEN
  REWRITE_TAC[MOI_FN2_GSPEC_LE_SUC; UNIONS_INSERT] THEN
  SUBGOAL_THEN
   `UNIONS (moi_fm3_cstar (barycentric_subdivision (barycentric_subdivision m))
              ((S:num->real^N)(SUC j))) INTER
    UNIONS {UNIONS (moi_fm3_cstar (barycentric_subdivision
              (barycentric_subdivision m)) (S i)) | i | i <= j} =
    moi_fn2_dual (barycentric_subdivision m) (segment[S j,S(SUC j)])`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_UNIONS] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      UNDISCH_TAC `(x:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_CASES_TAC `i:num = j` THENL
       [UNDISCH_THEN `i:num = j` SUBST_ALL_TAC THEN
        USE_THEN "K2" (MP_TAC o SPEC `j:num`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN
        CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
        USE_THEN "K1" (MP_TAC o SPECL [`i:num`; `SUC j`]) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
        DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[]];
      USE_THEN "K2" (MP_TAC o SPEC `j:num`) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(SET_RULE
       `!(a:real^N->bool) b u. a SUBSET u ==> a INTER b SUBSET b INTER u`) THEN
      MATCH_MP_TAC(SET_RULE `!s:real^N->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `j:num` THEN REWRITE_TAC[LE_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&1 = &1 + &1 - &1` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FEU_EULER_UNION THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FN2_EULER_STAR THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FN2_EULER_DUAL THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                     (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
      REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[AFF_DIM_SEGMENT] THEN
      SUBGOAL_THEN `~((S:num->real^N) j = S(SUC j))` (fun th -> REWRITE_TAC[th]) THEN
      MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC THEN EXISTS_TAC `n:num` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]]);;

let MOI_FN2_GSPEC_VERTEX_ENUM = prove
 (`!(K:(real^N->bool)->bool) (f:real^N->B) n (S:num->real^N).
     (!i. {S i} IN K) /\ (!v. {v} IN K ==> ?i. i < n /\ v = S i) /\ 1 <= n
     ==> {f w | w | {w} IN K} = {f (S i) | i | i <= n - 1}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `y:B` THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `w:real^N`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `(S:num->real^N) i` THEN ASM_REWRITE_TAC[]]);;

let MOI_FN2_NBHD_EULER = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> complex_euler (derived_nbhd_complex m l) = &0`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `barycentric_subdivision (l:(real^N->bool)->bool)` MOI_FN2_KCYC_EXISTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_TAC `S:num->real^N`)) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `n:num`;
                 `S:num->real^N`] MOI_FN2_KSTARS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "K1") (CONJUNCTS_THEN2 (LABEL_TAC "K2")
    (LABEL_TAC "K3"))) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `n:num`;
                 `S:num->real^N`] MOI_FN2_EULER_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "CH") THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fn2_kcyc]) THEN
  SUBGOAL_THEN `!i. {(S:num->real^N) i} IN barycentric_subdivision m` ASSUME_TAC THENL
   [GEN_TAC THEN
    UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                   (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. segment[(S:num->real^N) i,S(SUC i)] IN barycentric_subdivision m`
  ASSUME_TAC THENL
   [GEN_TAC THEN
    UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                   (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. i < n ==> aff_dim(segment[(S:num->real^N) i,S(SUC i)]) = &1`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[AFF_DIM_SEGMENT] THEN
    SUBGOAL_THEN `~((S:num->real^N) i = S(SUC i))` (fun th -> REWRITE_TAC[th]) THEN
    MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC THEN EXISTS_TAC `n:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(S:num->real^N) n = S 0` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FN2_CYC_N THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `SUC(n - 1) = n /\ n - 1 = SUC(n - 2)`
  (CONJUNCTS_THEN2 (LABEL_TAC "A1") (LABEL_TAC "A2")) THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  (* N as the union of the stars *)
  SUBGOAL_THEN
   `derived_nbhd m (l:(real^N->bool)->bool) =
    UNIONS (moi_fm3_cstar (barycentric_subdivision (barycentric_subdivision m))
              ((S:num->real^N)(n - 1))) UNION
    UNIONS {UNIONS (moi_fm3_cstar (barycentric_subdivision
              (barycentric_subdivision m)) (S i)) | i | i <= n - 2}`
  (LABEL_TAC "NE") THENL
   [ASM_SIMP_TAC[MOI_FN2_NBHD_STARS] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (l:(real^N->bool)->bool)`;
                   `\w:real^N. UNIONS (moi_fm3_cstar (barycentric_subdivision
                                 (barycentric_subdivision m)) w)`;
                   `n:num`; `S:num->real^N`] MOI_FN2_GSPEC_VERTEX_ENUM) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `n - 1 = SUC(n - 2)` THEN DISCH_THEN(fun th ->
      GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o ONCE_DEPTH_CONV) [th]) THEN
    REWRITE_TAC[MOI_FN2_GSPEC_LE_SUC; UNIONS_INSERT] THEN
    UNDISCH_TAC `n - 1 = SUC(n - 2)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    REWRITE_TAC[];
    ALL_TAC] THEN
  (* the last intersection *)
  SUBGOAL_THEN
   `UNIONS (moi_fm3_cstar (barycentric_subdivision (barycentric_subdivision m))
              ((S:num->real^N)(n - 1))) INTER
    UNIONS {UNIONS (moi_fm3_cstar (barycentric_subdivision
              (barycentric_subdivision m)) (S i)) | i | i <= n - 2} =
    moi_fn2_dual (barycentric_subdivision m) (segment[S(n - 2),S(SUC(n - 2))]) UNION
    moi_fn2_dual (barycentric_subdivision m) (segment[S(n - 1),S(SUC(n - 1))])`
  (LABEL_TAC "LI") THENL
   [USE_THEN "K2" (MP_TAC o SPEC `n - 2`) THEN
    USE_THEN "K2" (MP_TAC o SPEC `n - 1`) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
    UNDISCH_TAC `SUC(n - 1) = n` THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `n - 1 = SUC(n - 2)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER; IN_UNION] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
      GEN_REWRITE_TAC (LAND_CONV o ONCE_DEPTH_CONV) [IN_UNIONS] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool`
        (CONJUNCTS_THEN2 (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      UNDISCH_TAC `(x:real^N) IN t` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_CASES_TAC `i = n - 2` THENL
       [DISJ1_TAC THEN UNDISCH_THEN `i = n - 2` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_CASES_TAC `i = 0` THENL
       [DISJ2_TAC THEN UNDISCH_THEN `i = 0` SUBST_ALL_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      USE_THEN "K1" (MP_TAC o SPECL [`i:num`; `n - 1`]) THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THENL
       [MATCH_MP_TAC(SET_RULE
         `!(a:real^N->bool) b u. a SUBSET u ==> a INTER b SUBSET b INTER u`) THEN
        MATCH_MP_TAC(SET_RULE `!s:real^N->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `n - 2` THEN REWRITE_TAC[LE_REFL];
        MATCH_MP_TAC(SET_RULE
         `!(a:real^N->bool) b u. b SUBSET u ==> a INTER b SUBSET a INTER u`) THEN
        MATCH_MP_TAC(SET_RULE `!s:real^N->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
        REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `0` THEN REWRITE_TAC[LE_0]]];
    ALL_TAC] THEN
  (* Euler characteristic of N *)
  REMOVE_THEN "A1" (K ALL_TAC) THEN REMOVE_THEN "A2" (K ALL_TAC) THEN
  SUBGOAL_THEN `moi_feu_euler (derived_nbhd m (l:(real^N->bool)->bool)) (&0)` ASSUME_TAC THENL
   [REMOVE_THEN "NE" SUBST1_TAC THEN
    SUBGOAL_THEN `&0 = &1 + &1 - (&1 + &1)` SUBST1_TAC THENL [REAL_ARITH_TAC; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FEU_EULER_UNION THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FN2_EULER_STAR THEN ASM_REWRITE_TAC[];
      USE_THEN "CH" MATCH_MP_TAC THEN ASM_ARITH_TAC;
      REMOVE_THEN "LI" SUBST1_TAC THEN
      MATCH_MP_TAC MOI_FEU_EULER_UNION_DISJOINT THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FN2_EULER_DUAL THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        MATCH_MP_TAC MOI_FN2_EULER_DUAL THEN ASM_REWRITE_TAC[] THEN
        FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_ARITH_TAC;
        USE_THEN "K2" (MP_TAC o SPEC `n - 2`) THEN
        USE_THEN "K2" (MP_TAC o SPEC `n - 1`) THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
        ANTS_TAC THENL [ASM_ARITH_TAC; DISCH_THEN(SUBST1_TAC o SYM)] THEN
        SUBGOAL_THEN `(S:num->real^N)(SUC(n - 2)) = S(n - 1)` SUBST1_TAC THENL
         [AP_TERM_TAC THEN ASM_ARITH_TAC; ALL_TAC] THEN
        SUBGOAL_THEN `(S:num->real^N)(SUC(n - 1)) = S 0` SUBST1_TAC THENL
         [SUBGOAL_THEN `SUC(n - 1) = n` SUBST1_TAC THENL
           [ASM_ARITH_TAC; FIRST_ASSUM ACCEPT_TAC];
          ALL_TAC] THEN
        USE_THEN "K3" (MP_TAC o SPECL [`(S:num->real^N)(n - 2)`; `(S:num->real^N)(n - 1)`;
                                       `(S:num->real^N) 0`]) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN DISCH_TAC THENL
           [SUBGOAL_THEN `n - 2 = n - 1` MP_TAC THENL
             [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
                check (fun th -> can (find_term (fun t -> t = `i:num < n`)) (concl th))) THEN
              ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
              ASM_ARITH_TAC];
            SUBGOAL_THEN `n - 2 = 0` MP_TAC THENL
             [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
                check (fun th -> can (find_term (fun t -> t = `i:num < n`)) (concl th))) THEN
              ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
              ASM_ARITH_TAC];
            SUBGOAL_THEN `n - 1 = 0` MP_TAC THENL
             [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl) o
                check (fun th -> can (find_term (fun t -> t = `i:num < n`)) (concl th))) THEN
              ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
              ASM_ARITH_TAC]];
          ALL_TAC] THEN
        REWRITE_TAC[DISJOINT] THEN SET_TAC[]]];
    ALL_TAC] THEN
  REMOVE_THEN "NE" (K ALL_TAC) THEN REMOVE_THEN "LI" (K ALL_TAC) THEN
  MATCH_MP_TAC MOI_FEU_COMPLEX_EULER_EQ_EULER THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] DERIVED_NBHD_BASIC) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[MOI_BAR_SIMPLICIAL_COMPLEX] THEN ASM_SIMP_TAC[MOI_FRN_LF_BAR_COMPLEX]);;

(* ========================================================================= *)
(* Links of subcomplexes generated by                                       *)
(* triangles of a finite combinatorial surface K.  At a vertex y of K the  *)
(* link is a cycle U 0, ..., U(d-1) and the triangles at y are the hulls    *)
(* of y, U i, U(i+1) (the rotation at y).  For a set P of triangles of K   *)
(* and the subcomplex KP they generate, the link of y in KP is the union of *)
(* the link edges of the triangles of P at y; it is the whole circle when  *)
(* P contains all triangles at y and an arc when these triangles form a    *)
(* proper cyclic interval.                                                   *)
(* ========================================================================= *)

let MOI_FN2_CYC_PERIOD = prove
 (`!n (S:num->A). (!i. S(i + n) = S i) ==> !k q. S(q + k * n) = S q`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN INDUCT_TAC THEN
  REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN GEN_TAC THEN
  ONCE_REWRITE_TAC[ARITH_RULE `q + k * n + n = (q + k * n) + n:num`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_FN2_CYC_NEQ_SUC_ALL = prove
 (`!n (S:num->A) p.
     3 <= n /\ (!i. S(i + n) = S i) /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j)
     ==> ~(S p = S(SUC p))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `S:num->A`] MOI_FN2_CYC_PERIOD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(S:num->A) p = S(p MOD n) /\ (S:num->A)(SUC p) = S(SUC(p MOD n))`
  STRIP_ASSUME_TAC THENL
   [ASSUME_TAC(CONJUNCT1(MP (SPECL [`p:num`; `n:num`] DIVISION)
                              (ASSUME `~(n = 0)`))) THEN CONJ_TAC THENL
     [TRANS_TAC EQ_TRANS `(S:num->A)(p MOD n + p DIV n * n)` THEN CONJ_TAC THENL
       [AP_TERM_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[ASSUME `!k q. (S:num->A)(q + k * n) = S q`]];
      TRANS_TAC EQ_TRANS `(S:num->A)(SUC(p MOD n) + p DIV n * n)` THEN CONJ_TAC THENL
       [AP_TERM_TAC THEN ASM_ARITH_TAC;
        REWRITE_TAC[ASSUME `!k q. (S:num->A)(q + k * n) = S q`]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `S:num->A`; `p MOD n`] MOI_FN2_CYC_NEQ_SUC) THEN
  ASM_REWRITE_TAC[MOD_LT_EQ] THEN ASM_MESON_TAC[]);;

let MOI_FN2_TRI_FROM_LINK_EDGE = prove
 (`!(K:(real^N->bool)->bool) y a b.
     moi_bar_complex K /\ {y} IN K /\ segment[a,b] IN simplicial_link K y /\ ~(a = b)
     ==> ~affine_dependent {y,a,b} /\ convex hull {y,a,b} IN K`,
  REPEAT GEN_TAC THEN REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
  DISCH_THEN STRIP_ASSUME_TAC THEN
  SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  SUBGOAL_THEN `{y:real^N,a,b} SUBSET {v | v extreme_point_of t}` ASSUME_TAC THENL
   [REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FC2_VERTEX_EXTREME THEN
      EXISTS_TAC `K:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`segment[a:real^N,b]`; `t:real^N->bool`; `a:real^N`]
                    EXTREME_POINT_OF_FACE) THEN
      ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT; ENDS_IN_SEGMENT];
      MP_TAC(ISPECL [`segment[a:real^N,b]`; `t:real^N->bool`; `b:real^N`]
                    EXTREME_POINT_OF_FACE) THEN
      ASM_REWRITE_TAC[EXTREME_POINT_OF_SEGMENT; ENDS_IN_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~affine_dependent {y:real^N,a,b}` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_SUBSET]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(convex hull {y:real^N,a,b}) face_of t` ASSUME_TAC THENL
   [UNDISCH_TAC `t:real^N->bool = convex hull {v | v extreme_point_of t}` THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{y:real^N,a,b}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[moi_bar_complex]);;

(* The rotation at a vertex y of a finite combinatorial surface.             *)

let MOI_FN2_ROT = prove
 (`!(K:(real^N->bool)->bool) y.
     FINITE K /\ combinatorial_manifold 2 K /\ {y} IN K
     ==> ?d U. moi_fn2_kcyc (simplicial_link K y) d U /\
               (!i. ~(U i = y)) /\
               (!i. ~affine_dependent {y, U i, U(SUC i)} /\
                    convex hull {y, U i, U(SUC i)} IN K) /\
               (!tr. tr IN K /\ aff_dim tr = &2 /\ y IN tr
                    ==> ?i. i < d /\ tr = convex hull {y, U i, U(SUC i)})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `y:real^N`] MOI_FSA_CM_LINK) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPEC `simplicial_link K (y:real^N)` MOI_FN2_KCYC_EXISTS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ISPECL [`simplicial_link K (y:real^N)`; `k:real^N->bool`;
                           `f:real^N->real^N`; `g:real^N->real^N`] MOI_FSA_LK_DIM) THEN
      ASM_REWRITE_TAC[];
      X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC(ISPECL [`simplicial_link K (y:real^N)`; `k:real^N->bool`;
                           `f:real^N->real^N`; `g:real^N->real^N`] MOI_FSA_LK_DEG2) THEN
      ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`simplicial_link K (y:real^N)`; `k:real^N->bool`;
                     `f:real^N->real^N`; `g:real^N->real^N`] MOI_FSA_LK_CONNECTED) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      MP_TAC(ISPEC `k:real^N->bool` MOI_FSA_RF_TWO_POINTS) THEN ASM_REWRITE_TAC[] THEN
      STRIP_TAC THEN
      UNDISCH_TAC `homeomorphism (relative_frontier k,UNIONS (simplicial_link K y))
                                 (f:real^N->real^N,g)` THEN
      REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `(f:real^N->real^N) a` THEN
      UNDISCH_TAC `IMAGE (f:real^N->real^N) (relative_frontier k) =
                   UNIONS (simplicial_link K y)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_SIMP_TAC[FUN_IN_IMAGE]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_TAC `U:num->real^N`)) THEN
  MAP_EVERY EXISTS_TAC [`d:num`; `U:num->real^N`] THEN ASM_REWRITE_TAC[] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fn2_kcyc]) THEN
  SUBGOAL_THEN `!i. ~((U:num->real^N) i = U(SUC i))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC_ALL THEN
    EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN DISCH_TAC THEN
    UNDISCH_TAC `!i. {(U:num->real^N) i} IN simplicial_link K y /\
                     segment[U i,U(SUC i)] IN simplicial_link K y` THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `i:num`) THEN
    ASM_REWRITE_TAC[simplicial_link; IN_ELIM_THM; IN_SING];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_FN2_TRI_FROM_LINK_EDGE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `tr:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `tr:real^N->bool`; `y:real^N`]
                MOI_FRN_TRI_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `segment[x:real^N,z] IN simplicial_link K y` ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    SUBGOAL_THEN `segment[x:real^N,z] face_of tr` ASSUME_TAC THENL
     [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `{x:real^N,z}` THEN REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex];
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
      UNDISCH_TAC `~affine_dependent {y:real^N,x,z}` THEN
      REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `y:real^N` THEN
      REWRITE_TAC[IN_INSERT] THEN
      SUBGOAL_THEN `{y:real^N,x,z} DELETE y = {x,z}` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPEC `{x:real^N,z}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN ASM SET_TAC[];
      EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `!e. e IN simplicial_link K y /\ aff_dim e = &1
                   ==> ?i. i < d /\ e = segment[(U:num->real^N) i,U(SUC i)]` THEN
  DISCH_THEN(MP_TAC o SPEC `segment[x:real^N,z]`) THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `segment[x:real^N,z] = segment[U i,U(SUC i)]` THEN
  REWRITE_TAC[SEGMENT_EQ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
    `{x:real^N,y} = {z,w} ==> (x = z /\ y = w) \/ (x = w /\ y = z)`)) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  AP_TERM_TAC THEN SET_TAC[]);;

let MOI_FN2_CYC_MOD = prove
 (`!n (S:num->A). (!i. S(i + n) = S i) /\ ~(n = 0) ==> !p. S p = S(p MOD n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_TAC THEN
  MP_TAC(ISPECL [`n:num`; `S:num->A`] MOI_FN2_CYC_PERIOD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_TAC THEN
  TRANS_TAC EQ_TRANS `(S:num->A)(p MOD n + p DIV n * n)` THEN CONJ_TAC THENL
   [AP_TERM_TAC THEN
    MP_TAC(CONJUNCT1(MP (SPECL [`p:num`; `n:num`] DIVISION) (ASSUME `~(n = 0)`))) THEN
    ARITH_TAC;
    ASM_REWRITE_TAC[]]);;

(* A cycle is injective on every window of n consecutive indices.            *)

let MOI_FN2_CYC_INJ_WINDOW = prove
 (`!n (S:num->A) x e.
     3 <= n /\ (!i. S(i + n) = S i) /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\
     e < n /\ S(x + e) = S x
     ==> e = 0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `S:num->A`] MOI_FN2_CYC_MOD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `x + e:num` th) THEN MP_TAC(SPEC `x:num` th)) THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `(x + e) MOD n = x MOD n` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      is_imp (snd (strip_forall (concl th))))) THEN
    REWRITE_TAC[MOD_LT_EQ] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN ASM_SIMP_TAC[MOD_LT] THEN
  MP_TAC(SPECL [`x MOD n`; `e:num`; `n:num`] MOD_ADD_CASES) THEN
  ASM_REWRITE_TAC[MOD_LT_EQ] THEN DISCH_THEN SUBST1_TAC THEN
  COND_CASES_TAC THEN ASM_ARITH_TAC);;

(* A proper run of consecutive edges of a cycle is a PL arc.                *)

let MOI_FN2_CYC_ARC = prove
 (`!(L:(real^N->bool)->bool) d U a r.
     simplicial_complex L /\ moi_fn2_kcyc L d U /\ r + 2 <= d
     ==> pl_ball 1 (UNIONS {segment[U(a + j),U(SUC(a + j))] | j | j <= r})`,
  REWRITE_TAC[moi_fn2_kcyc] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `SUC r`; `\j. (U:num->real^N)(a + j)`]
                MOI_SLV_POLY_ARC) THEN
  REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_REWRITE_TAC[ARITH_RULE `1 <= SUC r`] THEN CONJ_TAC THENL
     [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN STRIP_TAC THEN
      DISJ_CASES_TAC (ARITH_RULE `i <= j \/ j <= i:num`) THENL
       [MP_TAC(ISPECL [`d:num`; `U:num->real^N`; `a + i:num`; `j - i:num`]
                      MOI_FN2_CYC_INJ_WINDOW) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(a + i) + (j - i) = a + j:num` SUBST1_TAC THENL
         [UNDISCH_TAC `i <= j:num` THEN ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [UNDISCH_TAC `r + 2 <= d` THEN UNDISCH_TAC `j <= SUC r` THEN ARITH_TAC;
          UNDISCH_TAC `i <= j:num` THEN ARITH_TAC];
        MP_TAC(ISPECL [`d:num`; `U:num->real^N`; `a + j:num`; `i - j:num`]
                      MOI_FN2_CYC_INJ_WINDOW) THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `(a + j) + (i - j) = a + i:num` SUBST1_TAC THENL
         [UNDISCH_TAC `j <= i:num` THEN ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
         [UNDISCH_TAC `r + 2 <= d` THEN UNDISCH_TAC `i <= SUC r` THEN ARITH_TAC;
          UNDISCH_TAC `j <= i:num` THEN ARITH_TAC]];
      GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[ADD_CLAUSES] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN
   `UNIONS {segment[(U:num->real^N)(a + j),U(SUC(a + j))] | j | j <= r} =
    path_image(polygonal_path(list_of_seq (\j. (U:num->real^N)(a + j)) (SUC (SUC r))))`
  SUBST1_TAC THENL
   [ASM_REWRITE_TAC[LT_SUC_LE; ADD_CLAUSES];
    MATCH_MP_TAC MOI_SFR_ARC_PL_BALL THEN ASM_REWRITE_TAC[MOI_PL2_PL_POLYGONAL_PATH]]);;

(* The link of y in the subcomplex generated by a set P of triangles.        *)

let MOI_FN2_SUBLINK = prove
 (`!(K:(real^N->bool)->bool) P y d U.
     moi_bar_complex K /\ {y} IN K /\ P SUBSET K /\
     (!tr. tr IN P ==> aff_dim tr = &2) /\
     (!i. ~(U i = y)) /\
     (!i. ~affine_dependent {y, U i, U(SUC i)} /\
          convex hull {y, U i, U(SUC i)} IN K) /\
     (!tr. tr IN K /\ aff_dim tr = &2 /\ y IN tr
           ==> ?i. i < d /\ tr = convex hull {y, U i, U(SUC i)})
     ==> UNIONS (simplicial_link {s | ?tr. tr IN P /\ s face_of tr} y) =
         UNIONS {segment[U i,U(SUC i)] | i |
                 i < d /\ convex hull {y,U i,U(SUC i)} IN P}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; simplicial_link; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      ASSUME_TAC)) THEN
    SUBGOAL_THEN `(y:real^N) IN tr'` ASSUME_TAC THENL
     [UNDISCH_TAC `(t':real^N->bool) face_of tr'` THEN
      DISCH_THEN(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
      UNDISCH_TAC `(y:real^N) IN t'` THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(tr':real^N->bool) IN K /\ aff_dim tr' = &2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(P:(real^N->bool)->bool) SUBSET K` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `!tr:real^N->bool. tr IN P ==> aff_dim tr = &2` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `!tr. tr IN K /\ aff_dim tr = &2 /\ (y:real^N) IN tr
                      ==> ?i. i < d /\ tr = convex hull {y, U i, U(SUC i)}` THEN
    DISCH_THEN(MP_TAC o SPEC `tr':real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    EXISTS_TAC `segment[(U:num->real^N) i,U(SUC i)]` THEN CONJ_TAC THENL
     [EXISTS_TAC `i:num` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) face_of convex hull {y, U i, U(SUC i)}` MP_TAC THENL
     [MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `t':real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `cc:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~((y:real^N) IN cc)` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `~((y:real^N) IN s)` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) SUBSET segment[U i,U(SUC i)]` MP_TAC THENL
     [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN
      UNDISCH_TAC `(cc:real^N->bool) SUBSET {y, U i, U(SUC i)}` THEN
      UNDISCH_TAC `~((y:real^N) IN cc)` THEN SET_TAC[];
      UNDISCH_TAC `(x:real^N) IN s` THEN SET_TAC[]];
    REWRITE_TAC[UNIONS_SUBSET; FORALL_IN_GSPEC] THEN
    X_GEN_TAC `i:num` THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s:real^N->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    SUBGOAL_THEN `segment[(U:num->real^N) i,U(SUC i)] face_of convex hull {y, U i, U(SUC i)}`
    ASSUME_TAC THENL
     [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `{(U:num->real^N) i,U(SUC i)}` THEN REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [EXISTS_TAC `convex hull {y:real^N, U i, U(SUC i)}` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN DISCH_TAC THEN
      UNDISCH_TAC `!i. ~affine_dependent {y:real^N, U i, U(SUC i)} /\
                       convex hull {y, U i, U(SUC i)} IN K` THEN
      DISCH_THEN(MP_TAC o CONJUNCT1 o SPEC `i:num`) THEN
      REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `y:real^N` THEN
      REWRITE_TAC[IN_INSERT] THEN
      SUBGOAL_THEN `{y:real^N, U i, U(SUC i)} DELETE y = {U i, U(SUC i)}` SUBST1_TAC THENL
       [MP_TAC(SPEC `i:num` (ASSUME `!i. ~((U:num->real^N) i = y)`)) THEN
        MP_TAC(SPEC `SUC i` (ASSUME `!i. ~((U:num->real^N) i = y)`)) THEN SET_TAC[];
        ALL_TAC] THEN
      MATCH_MP_TAC(SET_RULE `!t u. (y:real^N) IN t /\ t SUBSET u ==> y IN u`) THEN
      EXISTS_TAC `convex hull {(U:num->real^N) i, U(SUC i)}` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL];
      EXISTS_TAC `convex hull {y:real^N, U i, U(SUC i)}` THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [EXISTS_TAC `convex hull {y:real^N, U i, U(SUC i)}` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FACE_OF_REFL THEN REWRITE_TAC[CONVEX_CONVEX_HULL];
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]]]]);;

(* Index arithmetic for cycles: equal values exactly at congruent indices.  *)

let MOI_FN2_CYC_MODEQ = prove
 (`!n (S:num->A) a b.
     3 <= n /\ (!i. S(i + n) = S i) /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j)
     ==> (S a = S b <=> a MOD n = b MOD n)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `S:num->A`] MOI_FN2_CYC_MOD) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `a:num` th) THEN MP_TAC(SPEC `b:num` th)) THEN
  REPEAT DISCH_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall (concl th) &&
      is_imp (snd (strip_forall (concl th))))) THEN
    REWRITE_TAC[MOD_LT_EQ] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    DISCH_TAC THEN ASM_MESON_TAC[]]);;

let MOI_FN2_CYC_SUC_EQ = prove
 (`!n (S:num->A) a b.
     3 <= n /\ (!i. S(i + n) = S i) /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\ S a = S b
     ==> S(SUC a) = S(SUC b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`n:num`; `S:num->A`; `a:num`; `b:num`] MOI_FN2_CYC_MODEQ) THEN
  MP_TAC(ISPECL [`n:num`; `S:num->A`; `SUC a`; `SUC b`] MOI_FN2_CYC_MODEQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(SUC a) MOD n = (a MOD n + 1) MOD n /\ (SUC b) MOD n = (b MOD n + 1) MOD n`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_EQ THENL
   [EXISTS_TAC `a DIV n`; EXISTS_TAC `b DIV n`] THEN
  MP_TAC(SPECL [`a:num`; `n:num`] DIVISION) THEN
  MP_TAC(SPECL [`b:num`; `n:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let MOI_FN2_CYC_PRE_EQ = prove
 (`!n (S:num->A) a b.
     3 <= n /\ (!i. S(i + n) = S i) /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j) /\ S(SUC a) = S(SUC b)
     ==> S a = S b`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(S:num->A) a = S(SUC a + (n - 1)) /\ (S:num->A) b = S(SUC b + (n - 1))`
  (fun th -> REWRITE_TAC[th]) THENL
   [SUBGOAL_THEN `SUC a + (n - 1) = a + n /\ SUC b + (n - 1) = b + n`
    (fun th -> ASM_REWRITE_TAC[th]) THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:num`; `S:num->A`; `SUC a + (n - 1)`; `SUC b + (n - 1)`]
                MOI_FN2_CYC_MODEQ) THEN
  MP_TAC(ISPECL [`n:num`; `S:num->A`; `SUC a`; `SUC b`] MOI_FN2_CYC_MODEQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(SUC a + (n - 1)) MOD n = ((SUC a) MOD n + (n - 1)) MOD n /\
                (SUC b + (n - 1)) MOD n = ((SUC b) MOD n + (n - 1)) MOD n`
  (fun th -> ASM_REWRITE_TAC[th]) THEN
  CONJ_TAC THEN MATCH_MP_TAC MOD_EQ THENL
   [EXISTS_TAC `(SUC a) DIV n`; EXISTS_TAC `(SUC b) DIV n`] THEN
  MP_TAC(SPECL [`SUC a`; `n:num`] DIVISION) THEN
  MP_TAC(SPECL [`SUC b`; `n:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN ARITH_TAC);;

let MOI_FN2_CYC_REP = prove
 (`!n (S:num->A) c i.
     3 <= n /\ (!i. S(i + n) = S i) /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j)
     ==> ?r. r < n /\ S i = S(c + r)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  EXISTS_TAC `(i + n * c - c) MOD n` THEN ASM_REWRITE_TAC[MOD_LT_EQ] THEN
  MP_TAC(ISPECL [`n:num`; `S:num->A`; `i:num`; `c + (i + n * c - c) MOD n`]
                MOI_FN2_CYC_MODEQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN `c <= n * c:num` ASSUME_TAC THENL
   [MATCH_MP_TAC(ARITH_RULE `1 * c <= n * c ==> c <= n * c:num`) THEN
    REWRITE_TAC[LE_MULT_RCANCEL] THEN ASM_ARITH_TAC;
    ALL_TAC] THEN
  TRANS_TAC EQ_TRANS `(c + (i + n * c - c)) MOD n` THEN CONJ_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOD_EQ THEN EXISTS_TAC `c:num` THEN
    ASM_ARITH_TAC;
    MATCH_MP_TAC MOD_EQ THEN EXISTS_TAC `(i + n * c - c) DIV n` THEN
    MP_TAC(SPECL [`i + n * c - c:num`; `n:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC]);;

(* When the triangles of P at y are those with a link vertex in X, and the  *)
(* link vertices in X form the run U c, ..., U(c+q), the triangles of P at  *)
(* y are all of them (d <= q + 2) or the run from U(c - 1), and those not   *)
(* in P are the complementary run.                                           *)

let MOI_FN2_LINK_INTERVAL = prove
 (`!(L:(real^N->bool)->bool) d (U:num->real^N) (y:real^N) P X c q.
     moi_fn2_kcyc L d U /\
     (!i. convex hull {y, U i, U(SUC i)} IN P <=> U i IN X \/ U(SUC i) IN X) /\
     (!i. U i IN X <=> ?j. j <= q /\ U i = U(c + j))
     ==> (d <= q + 2 ==> !i. convex hull {y, U i, U(SUC i)} IN P) /\
         (q + 3 <= d
          ==> {segment[U i,U(SUC i)] | i | i < d /\ convex hull {y, U i, U(SUC i)} IN P} =
              {segment[U((c + d - 1) + j),U(SUC((c + d - 1) + j))] | j | j <= q + 1} /\
              {segment[U i,U(SUC i)] | i |
               i < d /\ ~(convex hull {y, U i, U(SUC i)} IN P)} =
              {segment[U((c + q + 1) + j),U(SUC((c + q + 1) + j))] | j | j <= d - q - 3})`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fn2_kcyc] THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
    (CONJUNCTS_THEN2 (LABEL_TAC "PX") (LABEL_TAC "VX"))) THEN
  SUBGOAL_THEN `!a b. (U:num->real^N) a = U b ==> U(SUC a) = U(SUC b)` (LABEL_TAC "SE") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FN2_CYC_SUC_EQ THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. (U:num->real^N)(SUC a) = U(SUC b) ==> U a = U b` (LABEL_TAC "PE") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FN2_CYC_PRE_EQ THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e i. (U:num->real^N)(i + e * d) = U i` (LABEL_TAC "PER") THENL
   [MP_TAC(ISPECL [`d:num`; `U:num->real^N`] MOI_FN2_CYC_PERIOD) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a i. ?r. r < d /\ (U:num->real^N) i = U(a + r)` (LABEL_TAC "REP") THENL
   [REPEAT GEN_TAC THEN MATCH_MP_TAC MOI_FN2_CYC_REP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x e. e < d /\ (U:num->real^N)(x + e) = U x ==> e = 0` (LABEL_TAC "WIN") THENL
   [REPEAT STRIP_TAC THEN
    MATCH_MP_TAC(ISPECL [`d:num`; `U:num->real^N`; `x:num`] MOI_FN2_CYC_INJ_WINDOW) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!a b. a < d /\ b < d /\ (U:num->real^N)(c + a) = U(c + b) ==> a = b`
  (LABEL_TAC "CAN") THENL
   [REPEAT STRIP_TAC THEN DISJ_CASES_TAC (ARITH_RULE `a <= b \/ b <= a:num`) THENL
     [USE_THEN "WIN" (MP_TAC o SPECL [`c + a:num`; `b - a:num`]) THEN
      ASM_SIMP_TAC[ARITH_RULE `a <= b ==> (c + a) + (b - a) = c + b:num`] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC];
      USE_THEN "WIN" (MP_TAC o SPECL [`c + b:num`; `a - b:num`]) THEN
      ASM_SIMP_TAC[ARITH_RULE `b <= a ==> (c + b) + (a - b) = c + a:num`] THEN
      ANTS_TAC THENL [ASM_ARITH_TAC; ASM_ARITH_TAC]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN X_GEN_TAC `i:num` THEN USE_THEN "PX" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "REP" (X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC o SPECL [`c:num`; `i:num`]) THEN
    ASM_CASES_TAC `r <= q:num` THENL
     [DISJ1_TAC THEN USE_THEN "VX" (fun th -> REWRITE_TAC[th]) THEN
      EXISTS_TAC `r:num` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN USE_THEN "VX" (fun th -> REWRITE_TAC[th]) THEN
      EXISTS_TAC `0` THEN REWRITE_TAC[LE_0; ADD_CLAUSES] THEN
      SUBGOAL_THEN `(U:num->real^N)(SUC i) = U(SUC(c + r))` SUBST1_TAC THENL
       [USE_THEN "SE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `SUC(c + r) = c + 1 * d` SUBST1_TAC THENL
       [ASM_ARITH_TAC; USE_THEN "PER" (fun th -> REWRITE_TAC[th])]];
    ALL_TAC] THEN
  DISCH_TAC THEN CONJ_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `sg:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [(* P side, forward *)
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `convex hull {y:real^N, U i, U(SUC i)} IN P` THEN
    USE_THEN "PX" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "VX" (fun th -> REWRITE_TAC[th]) THEN
    DISCH_THEN(DISJ_CASES_THEN (X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC)) THENL
     [EXISTS_TAC `SUC j` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(U:num->real^N)((c + d - 1) + SUC j) = U i` ASSUME_TAC THENL
       [SUBGOAL_THEN `(c + d - 1) + SUC j = (c + j) + 1 * d` SUBST1_TAC THENL
         [ASM_ARITH_TAC; USE_THEN "PER" (fun th -> REWRITE_TAC[th])] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(U:num->real^N)(SUC((c + d - 1) + SUC j)) = U(SUC i)` ASSUME_TAC THENL
       [USE_THEN "SE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `j:num` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(U:num->real^N)(SUC((c + d - 1) + j)) = U(SUC i)` ASSUME_TAC THENL
       [SUBGOAL_THEN `SUC((c + d - 1) + j) = (c + j) + 1 * d` SUBST1_TAC THENL
         [ASM_ARITH_TAC; USE_THEN "PER" (fun th -> REWRITE_TAC[th])] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(U:num->real^N)((c + d - 1) + j) = U i` ASSUME_TAC THENL
       [USE_THEN "PE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[]];
    (* P side, backward *)
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "REP" (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o
      SPECL [`0`; `(c + d - 1) + j:num`]) THEN
    EXISTS_TAC `i:num` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    SUBGOAL_THEN `(U:num->real^N)(SUC i) = U(SUC((c + d - 1) + j))` ASSUME_TAC THENL
     [USE_THEN "SE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `convex hull {y:real^N, U i, U(SUC i)} IN P` ASSUME_TAC THENL
     [USE_THEN "PX" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "VX" (fun th -> REWRITE_TAC[th]) THEN
      ASM_CASES_TAC `j = 0` THENL
       [DISJ2_TAC THEN EXISTS_TAC `0` THEN REWRITE_TAC[LE_0; ADD_CLAUSES] THEN
        TRANS_TAC EQ_TRANS `(U:num->real^N)(SUC((c + d - 1) + j))` THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          SUBGOAL_THEN `SUC((c + d - 1) + j) = c + 1 * d` SUBST1_TAC THENL
           [ASM_ARITH_TAC; USE_THEN "PER" (fun th -> REWRITE_TAC[th])]];
        DISJ1_TAC THEN EXISTS_TAC `j - 1:num` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
        TRANS_TAC EQ_TRANS `(U:num->real^N)((c + d - 1) + j)` THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          SUBGOAL_THEN `(c + d - 1) + j = (c + (j - 1)) + 1 * d:num` SUBST1_TAC THENL
           [ASM_ARITH_TAC; USE_THEN "PER" (fun th -> REWRITE_TAC[th])]]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    (* complement side, forward *)
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `~(convex hull {y:real^N, U i, U(SUC i)} IN P)` THEN
    USE_THEN "PX" (fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "VX" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN STRIP_TAC THEN
    USE_THEN "REP" (X_CHOOSE_THEN `r:num` STRIP_ASSUME_TAC o SPECL [`c:num`; `i:num`]) THEN
    SUBGOAL_THEN `q + 1 <= r:num` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:num` o check (fun th ->
        can (find_term (fun t -> t = `(U:num->real^N) i`)) (concl th) &&
        is_forall (concl th))) THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(U:num->real^N)(SUC i) = U(c + SUC r)` ASSUME_TAC THENL
     [REWRITE_TAC[ADD_CLAUSES] THEN USE_THEN "SE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `SUC r < d` ASSUME_TAC THENL
     [REWRITE_TAC[GSYM NOT_LE] THEN DISCH_TAC THEN
      SUBGOAL_THEN `SUC r = d` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      SUBGOAL_THEN `(U:num->real^N)(SUC i) = U(c + 0)` MP_TAC THENL
       [TRANS_TAC EQ_TRANS `(U:num->real^N)(c + SUC r)` THEN CONJ_TAC THENL
         [FIRST_ASSUM ACCEPT_TAC;
          SUBGOAL_THEN `c + SUC r = (c + 0) + 1 * d` SUBST1_TAC THENL
           [ASM_ARITH_TAC; USE_THEN "PER" (fun th -> REWRITE_TAC[th])]];
        ASM_MESON_TAC[LE_0]];
      ALL_TAC] THEN
    EXISTS_TAC `r - (q + 1):num` THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(c + q + 1) + r - (q + 1) = c + r:num` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[ADD_CLAUSES];
    (* complement side, backward *)
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "REP" (X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC o
      SPECL [`0`; `(c + q + 1) + j:num`]) THEN
    EXISTS_TAC `i:num` THEN
    RULE_ASSUM_TAC(REWRITE_RULE[ADD_CLAUSES]) THEN
    SUBGOAL_THEN `(U:num->real^N)(SUC i) = U(SUC((c + q + 1) + j))` ASSUME_TAC THENL
     [USE_THEN "SE" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(convex hull {y:real^N, U i, U(SUC i)} IN P)` ASSUME_TAC THENL
     [USE_THEN "PX" (fun th -> REWRITE_TAC[th]) THEN
      USE_THEN "VX" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[DE_MORGAN_THM; NOT_EXISTS_THM] THEN
      CONJ_TAC THEN X_GEN_TAC `jj:num` THEN
      REWRITE_TAC[TAUT `~p \/ ~q <=> p ==> ~q`] THEN DISCH_TAC THEN DISCH_TAC THENL
       [SUBGOAL_THEN `q + 1 + j = jj:num` MP_TAC THENL
         [USE_THEN "CAN" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[ARITH_RULE `c + q + 1 + j = (c + q + 1) + j:num`] THEN ASM_MESON_TAC[];
          ASM_ARITH_TAC];
        SUBGOAL_THEN `q + 2 + j = jj:num` MP_TAC THENL
         [USE_THEN "CAN" MATCH_MP_TAC THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
          REWRITE_TAC[ARITH_RULE `c + q + 2 + j = SUC((c + q + 1) + j)`] THEN ASM_MESON_TAC[];
          ASM_ARITH_TAC]];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FN2_CARD2_EQ = prove
 (`!(s:A->bool) a b. FINITE s /\ CARD s = 2 /\ a IN s /\ b IN s /\ ~(a = b) ==> s = {a,b}`,
  REPEAT STRIP_TAC THEN MP_TAC(ISPEC `s:A->bool` MOI_FC2_CARD_EQ_2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THEN
  ASM SET_TAC[]);;

(* Edges at y in the rotation: [y, U(i+1)] lies exactly in the triangles   *)
(* of indices i and i + 1.                                                   *)

let MOI_FN2_ROT_EDGE = prove
 (`!(K:(real^N->bool)->bool) y d U i.
     FINITE K /\ combinatorial_manifold 2 K /\ {y} IN K /\
     moi_fn2_kcyc (simplicial_link K y) d U /\
     (!i. ~(U i = y)) /\
     (!i. ~affine_dependent {y, U i, U(SUC i)} /\ convex hull {y, U i, U(SUC i)} IN K)
     ==> segment[y,U(SUC i)] IN K /\ aff_dim(segment[y,U(SUC i)]) = &1 /\
         ~(convex hull {y, U i, U(SUC i)} = convex hull {y, U(SUC i), U(SUC(SUC i))}) /\
         {t | t IN K /\ aff_dim t = &2 /\ segment[y,U(SUC i)] SUBSET t} =
         {convex hull {y, U i, U(SUC i)}, convex hull {y, U(SUC i), U(SUC(SUC i))}}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fn2_kcyc]) THEN
  SUBGOAL_THEN `!j. ~((U:num->real^N) j = U(SUC j))` ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_FN2_CYC_NEQ_SUC_ALL THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!j. aff_dim(convex hull {y:real^N, U j, U(SUC j)}) = &2` ASSUME_TAC THENL
   [GEN_TAC THEN
    SUBGOAL_THEN `~affine_dependent {y:real^N, U j, U(SUC j)}` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    SUBGOAL_THEN `CARD {y:real^N, U j, U(SUC j)} = 3` (fun th -> REWRITE_TAC[th]) THENL
     [MATCH_MP_TAC MOI_FC2_CARD_3 THEN ASM_MESON_TAC[]; INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[y:real^N,U(SUC i)] face_of convex hull {y, U i, U(SUC i)}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SUBGOAL_THEN `~affine_dependent {y:real^N, U i, U(SUC i)}` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{y:real^N, U(SUC i)}` THEN REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[y:real^N,U(SUC i)] face_of
                convex hull {y, U(SUC i), U(SUC(SUC i))}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    SUBGOAL_THEN `~affine_dependent {y:real^N, U(SUC i), U(SUC(SUC i))}` ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{y:real^N, U(SUC i)}` THEN REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `segment[y:real^N,U(SUC i)] IN K` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(segment[y:real^N,U(SUC i)]) = &1` ASSUME_TAC THENL
   [REWRITE_TAC[AFF_DIM_SEGMENT] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `~(convex hull {y:real^N, U i, U(SUC i)} = convex hull {y, U(SUC i), U(SUC(SUC i))})`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(U:num->real^N) i IN {y, U(SUC i), U(SUC(SUC i))}` MP_TAC THENL
     [SUBGOAL_THEN `~affine_dependent {y:real^N, U i, U(SUC i)} /\
                    ~affine_dependent {y:real^N, U(SUC i), U(SUC(SUC i))}`
      STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`{y:real^N, U(SUC i), U(SUC(SUC i))}`; `(U:num->real^N) i`]
                    EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      MP_TAC(ISPECL [`{y:real^N, U i, U(SUC i)}`; `(U:num->real^N) i`]
                    EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INSERT] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    SUBGOAL_THEN `~((U:num->real^N) i = U(SUC(SUC i)))` ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`d:num`; `U:num->real^N`; `i:num`; `2`] MOI_FN2_CYC_INJ_WINDOW) THEN
      ASM_REWRITE_TAC[ARITH_RULE `i + 2 = SUC(SUC i)`] THEN ASM_ARITH_TAC;
      ALL_TAC] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FN2_CARD2_EQ THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    MATCH_MP_TAC MOI_FSA_CM_EDGE2 THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET];
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]);;

(* Links in the subcomplexes generated by P and by the other triangles.      *)

let MOI_FN2_KP_LINK = prove
 (`!(K:(real^N->bool)->bool) P y d U X c q.
     FINITE K /\ combinatorial_manifold 2 K /\ {y} IN K /\ P SUBSET K /\
     (!tr. tr IN P ==> aff_dim tr = &2) /\
     moi_fn2_kcyc (simplicial_link K y) d U /\ (!i. ~(U i = y)) /\
     (!i. ~affine_dependent {y, U i, U(SUC i)} /\ convex hull {y, U i, U(SUC i)} IN K) /\
     (!tr. tr IN K /\ aff_dim tr = &2 /\ y IN tr
           ==> ?i. i < d /\ tr = convex hull {y, U i, U(SUC i)}) /\
     (!i. convex hull {y, U i, U(SUC i)} IN P <=> U i IN X \/ U(SUC i) IN X) /\
     (!i. U i IN X <=> ?j. j <= q /\ U i = U(c + j))
     ==> (d <= q + 2
          ==> pl_sphere 1 (UNIONS (simplicial_link {s | ?tr. tr IN P /\ s face_of tr} y)) /\
              UNIONS (simplicial_link
                {s | ?tr. tr IN {t | t IN K /\ aff_dim t = &2 /\ ~(t IN P)} /\
                          s face_of tr} y) = {}) /\
         (q + 3 <= d
          ==> pl_ball 1 (UNIONS (simplicial_link {s | ?tr. tr IN P /\ s face_of tr} y)) /\
              pl_ball 1 (UNIONS (simplicial_link
                {s | ?tr. tr IN {t | t IN K /\ aff_dim t = &2 /\ ~(t IN P)} /\
                          s face_of tr} y)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `P:(real^N->bool)->bool`; `y:real^N`;
                 `d:num`; `U:num->real^N`] MOI_FN2_SUBLINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`;
                 `{t:real^N->bool | t IN K /\ aff_dim t = &2 /\ ~(t IN P)}`; `y:real^N`;
                 `d:num`; `U:num->real^N`] MOI_FN2_SUBLINK) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  SUBGOAL_THEN
   `!i. convex hull {y:real^N, U i, U(SUC i)} IN
        {t | t IN K /\ aff_dim t = &2 /\ ~(t IN P)} <=>
        ~(convex hull {y, U i, U(SUC i)} IN P)`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `y:real^N`; `d:num`; `U:num->real^N`;
                   `i:num`] MOI_FN2_ROT_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `aff_dim (convex hull {y:real^N, U i, U(SUC i)}) = &2` ASSUME_TAC THENL
     [UNDISCH_TAC `{t | t IN K /\ aff_dim t = &2 /\ segment[y:real^N,U(SUC i)] SUBSET t} =
                   {convex hull {y, U i, U(SUC i)}, convex hull {y, U(SUC i), U(SUC(SUC i))}}` THEN
      DISCH_THEN(MP_TAC o SPEC `convex hull {y:real^N, U i, U(SUC i)}` o
                 GEN_REWRITE_RULE I [EXTENSION]) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN SIMP_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`simplicial_link K (y:real^N)`; `d:num`; `U:num->real^N`; `y:real^N`;
                 `P:(real^N->bool)->bool`; `X:real^N->bool`; `c:num`; `q:num`]
                MOI_FN2_LINK_INTERVAL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "I1") (LABEL_TAC "I2")) THEN
  SUBGOAL_THEN `simplicial_complex (simplicial_link K (y:real^N))` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `y:real^N`] MOI_FSA_CM_LINK) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN USE_THEN "I1" (MP_TAC o C MP (ASSUME `d <= q + 2`)) THEN
    DISCH_TAC THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `UNIONS {segment[(U:num->real^N) i,U(SUC i)] | i |
                i < d /\ convex hull {y,U i,U(SUC i)} IN P} =
        UNIONS (simplicial_link K y)` SUBST1_TAC THENL
       [REWRITE_TAC[ASSUME `!i. convex hull {y:real^N, U i, U(SUC i)} IN P`] THEN
        UNDISCH_TAC `moi_fn2_kcyc (simplicial_link K y) d (U:num->real^N)` THEN
        REWRITE_TAC[moi_fn2_kcyc] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `combinatorial_manifold 2 (K:(real^N->bool)->bool)` THEN
        REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[EMPTY_UNIONS; FORALL_IN_GSPEC] THEN
      REWRITE_TAC[ASSUME `!i. convex hull {y:real^N, U i, U(SUC i)} IN P`]];
    DISCH_TAC THEN USE_THEN "I2" (MP_TAC o C MP (ASSUME `q + 3 <= d`)) THEN
    DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN CONJ_TAC THEN
    MATCH_MP_TAC MOI_FN2_CYC_ARC THEN
    EXISTS_TAC `simplicial_link K (y:real^N)` THEN EXISTS_TAC `d:num` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* Triangles and surface boundaries of the subcomplex generated by a set P  *)
(* of triangles of K.                                                        *)

let MOI_FN2_KP_TRIANGLES = prove
 (`!(K:(real^N->bool)->bool) P r.
     moi_bar_complex K /\ P SUBSET K /\ (!tr. tr IN P ==> aff_dim tr = &2)
     ==> ((r IN {s | ?tr. tr IN P /\ s face_of tr} /\ aff_dim r = &2) <=> r IN P)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    SUBGOAL_THEN `r:real^N->bool = tr` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r:real^N->bool`; `tr:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `convex (tr:real^N->bool) /\ aff_dim tr = &2` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC `(P:(real^N->bool)->bool) SUBSET K` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN(MP_TAC o SPEC `tr:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX];
        UNDISCH_TAC `!tr:real^N->bool. tr IN P ==> aff_dim tr = &2` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[INT_LT_REFL]];
    DISCH_TAC THEN CONJ_TAC THENL
     [EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FACE_OF_REFL THEN
      UNDISCH_TAC `(P:(real^N->bool)->bool) SUBSET K` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `r:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX];
      UNDISCH_TAC `!tr:real^N->bool. tr IN P ==> aff_dim tr = &2` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]]);;

let MOI_FN2_KP_SURFACE_BOUNDARY = prove
 (`!(K:(real^N->bool)->bool) P.
     moi_bar_complex K /\ P SUBSET K /\ (!tr. tr IN P ==> aff_dim tr = &2)
     ==> surface_boundary {s | ?tr. tr IN P /\ s face_of tr} =
         UNIONS {e | e IN K /\ aff_dim e = &1 /\
                     CARD {t | t IN P /\ e SUBSET t} = 1}`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[surface_boundary] THEN AP_TERM_TAC THEN
  SUBGOAL_THEN
   `!e. {r | r IN {s | ?tr. tr IN P /\ s face_of tr} /\ aff_dim r = &2 /\ e SUBSET r} =
        {t:real^N->bool | t IN P /\ e SUBSET t}`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `r:real^N->bool` THEN
    GEN_REWRITE_TAC BINOP_CONV [IN_ELIM_THM] THEN REWRITE_TAC[CONJ_ASSOC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `P:(real^N->bool)->bool`; `r:real^N->bool`]
                  MOI_FN2_KP_TRIANGLES) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN REWRITE_TAC[];
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
  GEN_REWRITE_TAC BINOP_CONV [IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
    REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_bar_complex (K:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_complex] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(P:(real^N->bool)->bool) SUBSET K` THEN REWRITE_TAC[SUBSET] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~({t:real^N->bool | t IN P /\ e SUBSET t} = {})` MP_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `CARD {t:real^N->bool | t IN P /\ e SUBSET t} = 1` THEN
      ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `e:real^N->bool = e INTER t` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(t:real^N->bool) IN K` ASSUME_TAC THENL
     [UNDISCH_TAC `(P:(real^N->bool)->bool) SUBSET K` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_bar_complex (K:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`e:real^N->bool`; `t:real^N->bool`] o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[]]);;

let MOI_FN2_CARD_PAIR_SPLIT = prove
 (`!(a:A) b P.
     ~(a = b)
     ==> (CARD {x | x IN {a,b} /\ x IN P} = 1 <=> CARD {x | x IN {a,b} /\ ~(x IN P)} = 1)`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `(a:A) IN P` THEN ASM_CASES_TAC `(b:A) IN P` THENL
   [SUBGOAL_THEN `{x:A | x IN {a,b} /\ x IN P} = {a,b} /\
                  {x:A | x IN {a,b} /\ ~(x IN P)} = {}` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                                  NOT_IN_EMPTY] THEN ARITH_TAC];
    SUBGOAL_THEN `{x:A | x IN {a,b} /\ x IN P} = {a} /\
                  {x:A | x IN {a,b} /\ ~(x IN P)} = {b}` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; REWRITE_TAC[CARD_SING]];
    SUBGOAL_THEN `{x:A | x IN {a,b} /\ x IN P} = {b} /\
                  {x:A | x IN {a,b} /\ ~(x IN P)} = {a}` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; REWRITE_TAC[CARD_SING]];
    SUBGOAL_THEN `{x:A | x IN {a,b} /\ x IN P} = {} /\
                  {x:A | x IN {a,b} /\ ~(x IN P)} = {a,b}` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                                  NOT_IN_EMPTY] THEN ARITH_TAC]]);;

(* The subcomplexes generated by P and by the other triangles have the same *)
(* surface boundary.                                                          *)

let MOI_FN2_SB_PQ = prove
 (`!(K:(real^N->bool)->bool) P.
     FINITE K /\ combinatorial_manifold 2 K /\ P SUBSET K /\
     (!tr. tr IN P ==> aff_dim tr = &2)
     ==> surface_boundary {s | ?tr. tr IN {t | t IN K /\ aff_dim t = &2 /\ ~(t IN P)} /\
                                    s face_of tr} =
         surface_boundary {s | ?tr. tr IN P /\ s face_of tr}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `P:(real^N->bool)->bool`]
                MOI_FN2_KP_SURFACE_BOUNDARY) THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`;
                 `{t:real^N->bool | t IN K /\ aff_dim t = &2 /\ ~(t IN P)}`]
                MOI_FN2_KP_SURFACE_BOUNDARY) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
    DISCH_THEN SUBST1_TAC] THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `e:real^N->bool` THEN
  GEN_REWRITE_TAC BINOP_CONV [IN_ELIM_THM] THEN
  ASM_CASES_TAC `(e:real^N->bool) IN K /\ aff_dim e = &1` THENL
   [FIRST_X_ASSUM(CONJUNCTS_THEN ASSUME_TAC) THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[]] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `e:real^N->bool`] MOI_FSA_CM_EDGE2) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `FINITE {t:real^N->bool | t IN K /\ aff_dim t = &2 /\ e SUBSET t}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `{t:real^N->bool | t IN K /\ aff_dim t = &2 /\ e SUBSET t}`
               MOI_FC2_CARD_EQ_2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `{t:real^N->bool | t IN P /\ e SUBSET t} = {x | x IN {t1,t2} /\ x IN P} /\
    {t:real^N->bool | t IN {t | t IN K /\ aff_dim t = &2 /\ ~(t IN P)} /\ e SUBSET t} =
    {x | x IN {t1,t2} /\ ~(x IN P)}`
  (fun th -> REWRITE_TAC[th]) THENL
   [UNDISCH_TAC `{t:real^N->bool | t IN K /\ aff_dim t = &2 /\ e SUBSET t} = {t1,t2}` THEN
    DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN CONJ_TAC THEN X_GEN_TAC `x:real^N->bool` THENL
     [ASM_CASES_TAC `(x:real^N->bool) IN P` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^N->bool) IN K /\ aff_dim x = &2`
      (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
       [UNDISCH_TAC `(P:(real^N->bool)->bool) SUBSET K` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `!tr:real^N->bool. tr IN P ==> aff_dim tr = &2` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      CONV_TAC TAUT];
    ALL_TAC] THEN
  MATCH_MP_TAC(GSYM MOI_FN2_CARD_PAIR_SPLIT) THEN ASM_REWRITE_TAC[]);;

(* A periodic predicate that is somewhere true and somewhere false changes  *)
(* from true to false somewhere.                                              *)

let MOI_FN2_CYC_TRANSITION = prove
 (`!d (p:num->bool) a b.
     1 <= d /\ (!i. p(i + d) <=> p i) /\ ~p a /\ p b ==> ?i. p i /\ ~p(SUC i)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `!k i. (p:num->bool)(i + k * d) <=> p i` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN GEN_TAC THEN
    ONCE_REWRITE_TAC[ARITH_RULE `i + k * d + d = (i + k * d) + d:num`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?k. ~(p:num->bool)(b + k)` MP_TAC THENL
   [EXISTS_TAC `a + b * d - b:num` THEN
    SUBGOAL_THEN `b + a + b * d - b = a + b * d:num` SUBST1_TAC THENL
     [SUBGOAL_THEN `b <= b * d:num` MP_TAC THENL
       [MATCH_MP_TAC(ARITH_RULE `b * 1 <= b * d ==> b <= b * d:num`) THEN
        REWRITE_TAC[LE_MULT_LCANCEL] THEN ASM_ARITH_TAC;
        ARITH_TAC];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  GEN_REWRITE_TAC LAND_CONV [num_WOP] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:num` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `k = 0` THENL
   [UNDISCH_TAC `~(p:num->bool)(b + k)` THEN ASM_REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
  EXISTS_TAC `b + k - 1` THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `k - 1` o check (is_forall o concl)) THEN
    ANTS_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `b + k - 1 = b + (k - 1):num` (fun th -> REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC;
    SUBGOAL_THEN `SUC(b + k - 1) = b + k:num` (fun th -> ASM_REWRITE_TAC[th]) THEN
    ASM_ARITH_TAC]);;

(* The relative frontier points of |KP| (those lying in some simplex of K   *)
(* outside KP) are exactly its surface boundary.                             *)

let MOI_FN2_KP_FRONTIER = prove
 (`!(K:(real^N->bool)->bool) P.
     FINITE K /\ combinatorial_manifold 2 K /\ P SUBSET K /\
     (!tr. tr IN P ==> aff_dim tr = &2)
     ==> {x | x IN UNIONS P /\
              ?s. s IN K /\ x IN s /\ ~(s IN {s | ?tr. tr IN P /\ s face_of tr})} =
         surface_boundary {s | ?tr. tr IN P /\ s face_of tr}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FN2_KP_SURFACE_BOUNDARY] THEN
  SUBGOAL_THEN
   `!r:real^N->bool. r IN K /\ aff_dim r = &2 /\ ~(r IN P)
                     ==> ~(r IN {s | ?tr. tr IN P /\ s face_of tr})`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `P:(real^N->bool)->bool`; `r:real^N->bool`]
                  MOI_FN2_KP_TRIANGLES) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!e. e IN K /\ aff_dim e = &1
        ==> ?t1 t2. ~(t1 = t2) /\
                    {t | t IN K /\ aff_dim t = &2 /\ e SUBSET t} = {t1:real^N->bool,t2}`
  (LABEL_TAC "E2") THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM MOI_FC2_CARD_EQ_2] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      MATCH_MP_TAC MOI_FSA_CM_EDGE2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ALL_TAC;
    GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
    GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (CONJUNCTS_THEN2 MP_TAC ASSUME_TAC)) THEN
    GEN_REWRITE_TAC LAND_CONV [IN_ELIM_THM] THEN STRIP_TAC THEN
    GEN_REWRITE_TAC I [IN_ELIM_THM] THEN
    USE_THEN "E2" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(e:real^N->bool) IN K`) (ASSUME `aff_dim(e:real^N->bool) = &1`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN
     `{t:real^N->bool | t IN P /\ e SUBSET t} = {x | x IN {t1,t2} /\ x IN P}`
    ASSUME_TAC THENL
     [UNDISCH_TAC `{t | t IN K /\ aff_dim t = &2 /\ e SUBSET t} = {t1:real^N->bool,t2}` THEN
      DISCH_THEN(fun th -> REWRITE_TAC[GSYM th]) THEN
      REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `y:real^N->bool` THEN
      ASM_CASES_TAC `(y:real^N->bool) IN P` THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(y:real^N->bool) IN K /\ aff_dim y = &2`
      (fun th -> REWRITE_TAC[th]) THEN CONJ_TAC THENL
       [UNDISCH_TAC `(P:(real^N->bool)->bool) SUBSET K` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `!tr:real^N->bool. tr IN P ==> aff_dim tr = &2` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(t1:real^N->bool) IN K /\ aff_dim t1 = &2 /\ e SUBSET t1 /\
                  (t2:real^N->bool) IN K /\ aff_dim t2 = &2 /\ e SUBSET t2`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `{t | t IN K /\ aff_dim t = &2 /\ e SUBSET t} = {t1:real^N->bool,t2}` THEN
      DISCH_THEN(fun th ->
        MP_TAC(SPEC `t1:real^N->bool` (GEN_REWRITE_RULE I [EXTENSION] th)) THEN
        MP_TAC(SPEC `t2:real^N->bool` (GEN_REWRITE_RULE I [EXTENSION] th))) THEN
      REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `CARD {t:real^N->bool | t IN P /\ e SUBSET t} = 1` THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `(t1:real^N->bool) IN P` THEN ASM_CASES_TAC `(t2:real^N->bool) IN P` THENL
     [SUBGOAL_THEN `{x:real^N->bool | x IN {t1,t2} /\ x IN P} = {t1,t2}` SUBST1_TAC THENL
       [ASM SET_TAC[];
        ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
        ARITH_TAC];
      DISCH_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t1:real^N->bool` THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(e:real^N->bool) SUBSET t1` THEN UNDISCH_TAC `(x:real^N) IN e` THEN
        SET_TAC[];
        EXISTS_TAC `t2:real^N->bool` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `(e:real^N->bool) SUBSET t2` THEN UNDISCH_TAC `(x:real^N) IN e` THEN
          SET_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
      DISCH_TAC THEN CONJ_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t2:real^N->bool` THEN
        CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        UNDISCH_TAC `(e:real^N->bool) SUBSET t2` THEN UNDISCH_TAC `(x:real^N) IN e` THEN
        SET_TAC[];
        EXISTS_TAC `t1:real^N->bool` THEN CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
        CONJ_TAC THENL
         [UNDISCH_TAC `(e:real^N->bool) SUBSET t1` THEN UNDISCH_TAC `(x:real^N) IN e` THEN
          SET_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]]];
      SUBGOAL_THEN `{x:real^N->bool | x IN {t1,t2} /\ x IN P} = {}` SUBST1_TAC THENL
       [ASM SET_TAC[]; REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC]]] THEN
  GEN_REWRITE_TAC I [SUBSET] THEN X_GEN_TAC `x:real^N` THEN
  GEN_REWRITE_TAC LAND_CONV [IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
  GEN_REWRITE_TAC LAND_CONV [IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `tp:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(tp:real^N->bool) IN K /\ aff_dim tp = &2` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `(P:(real^N->bool)->bool) SUBSET K` THEN REWRITE_TAC[SUBSET] THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `!tr:real^N->bool. tr IN P ==> aff_dim tr = &2` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FSA_CM_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tn:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~((tn:real^N->bool) IN P)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~((s:real^N->bool) IN {s | ?tr. tr IN P /\ s face_of tr})` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN EXISTS_TAC `tn:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `s:real^N->bool = s INTER tn` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `moi_bar_complex (K:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_complex] THEN
    DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `tn:real^N->bool`] o
               CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(tn:real^N->bool = tp)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~((tn:real^N->bool) IN P)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `sg = (tn:real^N->bool) INTER tp` THEN
  SUBGOAL_THEN `(sg:real^N->bool) face_of tn /\ sg face_of tp /\ sg IN K /\ (x:real^N) IN sg`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_complex (K:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_complex] THEN STRIP_TAC THEN EXPAND_TAC "sg" THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex (tn:real^N->bool) /\ convex (tp:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `~(sg:real^N->bool = tn)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(tn:real^N->bool) = tp` MP_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`tn:real^N->bool`; `tp:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
      ASM_REWRITE_TAC[INT_LT_REFL] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(sg:real^N->bool) = &0 \/ aff_dim sg = &1` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`sg:real^N->bool`; `tn:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~(aff_dim(sg:real^N->bool) = -- &1)` MP_TAC THENL
     [REWRITE_TAC[AFF_DIM_EQ_MINUS1] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPEC `sg:real^N->bool` AFF_DIM_GE) THEN INT_ARITH_TAC;
    (* a vertex *)
    UNDISCH_TAC `aff_dim(sg:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` SUBST_ALL_TAC) THEN
    SUBGOAL_THEN `y:real^N = x` SUBST_ALL_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`] MOI_FN2_ROT) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `U:num->real^N`
      (CONJUNCTS_THEN2 (LABEL_TAC "KC") (CONJUNCTS_THEN2 (LABEL_TAC "UY")
        (CONJUNCTS_THEN2 (LABEL_TAC "AI") (LABEL_TAC "TR")))))) THEN
    USE_THEN "KC" (STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fn2_kcyc]) THEN
    SUBGOAL_THEN `?a. ~(convex hull {x:real^N, U a, U(SUC a)} IN P)` STRIP_ASSUME_TAC THENL
     [USE_THEN "TR" (MP_TAC o SPEC `tn:real^N->bool`) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN UNDISCH_TAC `(s:real^N->bool) SUBSET tn` THEN
        UNDISCH_TAC `(x:real^N) IN s` THEN SET_TAC[];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `a:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `a:num` THEN
      UNDISCH_TAC `~((tn:real^N->bool) IN P)` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?b. convex hull {x:real^N, U b, U(SUC b)} IN P` STRIP_ASSUME_TAC THENL
     [USE_THEN "TR" (MP_TAC o SPEC `tp:real^N->bool`) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `b:num` STRIP_ASSUME_TAC) THEN EXISTS_TAC `b:num` THEN
      UNDISCH_TAC `(tp:real^N->bool) IN P` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`d:num`; `\i. convex hull {x:real^N, U i, U(SUC i)} IN P`;
                   `a:num`; `b:num`] MOI_FN2_CYC_TRANSITION) THEN
    REWRITE_TAC[] THEN ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
      GEN_TAC THEN ONCE_REWRITE_TAC[ARITH_RULE `SUC(i + d) = SUC i + d`] THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `i:num` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `x:real^N`; `d:num`; `U:num->real^N`;
                   `i:num`] MOI_FN2_ROT_EDGE) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `segment[x:real^N,U(SUC i)]` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT] THEN
    SUBGOAL_THEN `{t:real^N->bool | t IN P /\ segment[x,U(SUC i)] SUBSET t} =
                  {convex hull {x, U i, U(SUC i)}}` (fun th -> REWRITE_TAC[th; CARD_SING]) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) IN {t | t IN K /\ aff_dim t = &2 /\
                                             segment[x,U(SUC i)] SUBSET t}` MP_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
         [UNDISCH_TAC `(P:(real^N->bool)->bool) SUBSET K` THEN REWRITE_TAC[SUBSET] THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `!tr:real^N->bool. tr IN P ==> aff_dim tr = &2` THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
      UNDISCH_TAC `(t:real^N->bool) IN P` THEN ASM_REWRITE_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    (* an edge *)
    USE_THEN "E2" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(sg:real^N->bool) IN K`) (ASSUME `aff_dim(sg:real^N->bool) = &1`)))) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN EXISTS_TAC `sg:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{t:real^N->bool | t IN P /\ sg SUBSET t} = {tp}`
    (fun th -> REWRITE_TAC[th; CARD_SING]) THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `!r:real^N->bool. r IN K /\ aff_dim r = &2 /\ sg SUBSET r
                                     ==> r = t1 \/ r = t2` (LABEL_TAC "TT") THENL
       [UNDISCH_TAC `{t | t IN K /\ aff_dim t = &2 /\ sg SUBSET t} = {t1:real^N->bool,t2}` THEN
        DISCH_THEN(fun th -> X_GEN_TAC `r:real^N->bool` THEN
          MP_TAC(SPEC `r:real^N->bool` (GEN_REWRITE_RULE I [EXTENSION] th))) THEN
        REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(t:real^N->bool) IN K /\ aff_dim t = &2` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `(P:(real^N->bool)->bool) SUBSET K` THEN REWRITE_TAC[SUBSET] THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          UNDISCH_TAC `!tr:real^N->bool. tr IN P ==> aff_dim tr = &2` THEN
          DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(sg:real^N->bool) SUBSET tn /\ sg SUBSET tp` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "sg" THEN SET_TAC[]; ALL_TAC] THEN
      REMOVE_THEN "TT" (fun th -> MP_TAC(SPEC `t:real^N->bool` th) THEN
                                  MP_TAC(SPEC `tn:real^N->bool` th) THEN
                                  MP_TAC(SPEC `tp:real^N->bool` th)) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `~((tn:real^N->bool) IN P)` THEN UNDISCH_TAC `(t:real^N->bool) IN P` THEN
      UNDISCH_TAC `~(tn:real^N->bool = tp)` THEN MESON_TAC[];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "sg" THEN SET_TAC[]]]);;

(* ========================================================================= *)
(* The two sides of the frontier.  With                                     *)
(* K = bsd(bsd m) and P = moi_fn2_ptri m l (its triangles meeting UNIONS l), *)
(* the derived neighbourhood complex is generated by P and the closure of   *)
(* the complement by the other triangles.  A triangle meets UNIONS l iff    *)
(* one of its vertices lies in it (fullness), and at a vertex b(tau) off    *)
(* UNIONS l the link vertices in UNIONS l are the barycentres of the faces  *)
(* of tau INTER UNIONS l: one point or three consecutive ones.  So the      *)
(* generic links of the previous section apply: both complexes are          *)
(* combinatorial surfaces with boundary, with the derived frontier as       *)
(* common surface boundary.                                                 *)
(* ========================================================================= *)

let moi_fn2_ptri = new_definition
 `moi_fn2_ptri (m:(real^N->bool)->bool) (l:(real^N->bool)->bool) =
    {t | t IN barycentric_subdivision (barycentric_subdivision m) /\ aff_dim t = &2 /\
         ~(t INTER UNIONS l = {})}`;;

let MOI_FN2_C2_CONTEXT = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> FINITE (barycentric_subdivision (barycentric_subdivision m)) /\
         combinatorial_manifold 2 (barycentric_subdivision (barycentric_subdivision m)) /\
         moi_bar_complex (barycentric_subdivision (barycentric_subdivision m)) /\
         lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision m)) /\
         UNIONS (barycentric_subdivision (barycentric_subdivision m)) = UNIONS m /\
         moi_fn2_ptri m l SUBSET barycentric_subdivision (barycentric_subdivision m) /\
         (!tr. tr IN moi_fn2_ptri m l ==> aff_dim tr = &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `barycentric_subdivision (m:(real^N->bool)->bool)` MOI_FC2_BARYCENTRIC_CM2) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision
                  (barycentric_subdivision (m:(real^N->bool)->bool)))` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FRN_LF_BAR_COMPLEX] THEN
  REWRITE_TAC[moi_fn2_ptri; SUBSET; IN_ELIM_THM] THEN SIMP_TAC[] THEN
  MP_TAC(ISPEC `m:(real^N->bool)->bool` MOI_FDN_BAR2_LF) THEN ASM_SIMP_TAC[]);;

(* Fullness in the second derived: a simplex of bsd(bsd m) meeting          *)
(* UNIONS l has a vertex in it.                                              *)

let MOI_FN2_C2_MEETS = prove
 (`!(m:(real^N->bool)->bool) l s.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\
     s IN barycentric_subdivision (barycentric_subdivision m) /\ ~(s INTER UNIONS l = {})
     ==> ?v. v extreme_point_of s /\ v IN UNIONS l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                 `barycentric_subdivision (l:(real^N->bool)->bool)`; `s:real^N->bool`]
                MOI_FRN_FULL) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
                  MOI_FN2_C2_CONTEXT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_MESON_TAC[moi_bar_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (s INTER UNIONS l:real^N->bool) /\ convex (s INTER UNIONS l)`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC FACE_OF_IMP_COMPACT THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT];
      ASM_MESON_TAC[FACE_OF_IMP_CONVEX]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s INTER UNIONS l:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN
  EXISTS_TAC `v:real^N` THEN
  MP_TAC(ISPECL [`s INTER UNIONS l:real^N->bool`; `s:real^N->bool`; `v:real^N`]
                EXTREME_POINT_OF_FACE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FN2_NESTED_FACE = prove
 (`!(c:(real^N->bool)->bool) s t.
     moi_bar_complex c /\ s IN c /\ t IN c /\ s SUBSET t ==> s face_of t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `s:real^N->bool = s INTER t` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[moi_bar_complex]]);;

(* The derived neighbourhood (complex) is generated by the triangles of     *)
(* bsd(bsd m) meeting UNIONS l.                                              *)

let MOI_FN2_NC_KP = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> derived_nbhd_complex m l = {s | ?tr. tr IN moi_fn2_ptri m l /\ s face_of tr} /\
         derived_nbhd m l = UNIONS (moi_fn2_ptri m l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_C2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!r. r IN barycentric_subdivision (barycentric_subdivision m) /\
        ~(r INTER UNIONS l = {})
        ==> ?tr:real^N->bool. tr IN moi_fn2_ptri m l /\ r face_of tr`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))`;
                   `r:real^N->bool`] MOI_FSA_CM_PURE) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `tr:real^N->bool` THEN CONJ_TAC THENL
     [REWRITE_TAC[moi_fn2_ptri; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MATCH_MP_TAC MOI_FN2_NESTED_FACE THEN
      EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[derived_nbhd_complex] THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    X_GEN_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `tr:real^N->bool` THEN ASM_MESON_TAC[FACE_OF_TRANS];
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(tr:real^N->bool) IN moi_fn2_ptri m l` THEN
      REWRITE_TAC[moi_fn2_ptri; IN_ELIM_THM] THEN SIMP_TAC[]];
    REWRITE_TAC[derived_nbhd] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `r:real^N->bool` THEN
      DISCH_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `tr:real^N->bool` THEN
      ASM_SIMP_TAC[FACE_OF_IMP_SUBSET] THEN
      MATCH_MP_TAC(SET_RULE `!s:real^N->bool f. s IN f ==> s SUBSET UNIONS f`) THEN
      ASM_REWRITE_TAC[];
      MATCH_MP_TAC UNIONS_MONO THEN X_GEN_TAC `tr:real^N->bool` THEN
      DISCH_TAC THEN EXISTS_TAC `tr:real^N->bool` THEN REWRITE_TAC[SUBSET_REFL] THEN
      UNDISCH_TAC `(tr:real^N->bool) IN moi_fn2_ptri m l` THEN
      REWRITE_TAC[moi_fn2_ptri; IN_ELIM_THM] THEN SIMP_TAC[]]]);;

(* Barycentres of simplices of bsd m in UNIONS l (fullness).                 *)

let MOI_FN2_BARY_IN_L = prove
 (`!(m:(real^N->bool)->bool) l r.
     lf_simplicial_complex m /\ simplicial_subcomplex l m /\
     r IN barycentric_subdivision m /\ ~(r = {})
     ==> (simplex_barycentre r IN UNIONS l <=> r SUBSET UNIONS l)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex; MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
                  MOI_FRN_FULL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MATCH_MP_TAC(SET_RULE `r INTER u = r ==> (r:real^N->bool) SUBSET u`) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`r INTER UNIONS l:real^N->bool`; `r:real^N->bool`]
                  FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `simplex_barycentre r:real^N` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR; MOI_BAR_SIMPLEX_BARYCENTRE_IN];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`n:int`; `r:real^N->bool`] MOI_BAR_SIMPLEX_BARYCENTRE_IN) THEN
    ASM SET_TAC[]]);;

(* At a vertex b(tau) of bsd(bsd m) off UNIONS l, the link vertices in      *)
(* UNIONS l are the barycentres of the nonempty faces of tau INTER UNIONS l. *)

let MOI_FN2_LINKV = prove
 (`!(m:(real^N->bool)->bool) l tau x.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\
     tau IN barycentric_subdivision m /\ ~(tau = {}) /\
     ~(simplex_barycentre tau IN UNIONS l) /\
     {x} IN simplicial_link (barycentric_subdivision (barycentric_subdivision m))
                            (simplex_barycentre tau)
     ==> (x IN UNIONS l <=>
          ?r. r IN barycentric_subdivision m /\ ~(r = {}) /\ r SUBSET tau INTER UNIONS l /\
              x = simplex_barycentre r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `tau:real^N->bool`;
                 `x:real^N`] MOI_FC2_LINK_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `simplex_barycentre r IN UNIONS l <=> (r:real^N->bool) SUBSET UNIONS l`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FN2_BARY_IN_L THEN EXISTS_TAC `m:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(r:real^N->bool) SUBSET UNIONS l` ASSUME_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN UNIONS l` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(r:real^N->bool) SUBSET tau \/ tau SUBSET r` MP_TAC THENL
     [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision m) {tau:real^N->bool,r}` THEN
      REWRITE_TAC[MOI_FRN_CHAIN_PAIR] THEN MESON_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [UNDISCH_TAC `(r:real^N->bool) SUBSET tau` THEN
      UNDISCH_TAC `(r:real^N->bool) SUBSET UNIONS l` THEN SET_TAC[];
      UNDISCH_TAC `~(simplex_barycentre tau IN UNIONS (l:(real^N->bool)->bool))` THEN
      MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
      MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `tau:real^N->bool`] MOI_FN2_BARY_IN_L) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
      UNDISCH_TAC `(tau:real^N->bool) SUBSET r` THEN
      UNDISCH_TAC `(r:real^N->bool) SUBSET UNIONS l` THEN SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `r':real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `x = simplex_barycentre (r':real^N->bool)` THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `r':real^N->bool`] MOI_FN2_BARY_IN_L) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `(r':real^N->bool) SUBSET tau INTER UNIONS l` THEN SET_TAC[]]);;

let MOI_FN2_LINK_SING = prove
 (`!(c:(real^N->bool)->bool) s r.
     moi_bar_complex c /\ s IN c /\ ~(s = {}) /\ r IN c /\ ~(r = {}) /\ ~(r = s) /\
     (r SUBSET s \/ s SUBSET r)
     ==> {simplex_barycentre r} IN
         simplicial_link (barycentric_subdivision c) (simplex_barycentre s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_SIMP_TAC[MOI_FC2_LINK_CHAIN] THEN
  EXISTS_TAC `{r:real^N->bool}` THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; IN_SING] THEN
  REWRITE_TAC[MOI_FRN_CHAIN_PAIR] THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

(* The two cycle neighbours of U c' are U(c'+1) and U(c'+d-1).               *)

let MOI_FN2_CYC_NBR = prove
 (`!(L:(real^N->bool)->bool) d U c' z.
     moi_fn2_kcyc L d U /\ segment[U c',z] IN L /\ ~(z = U c')
     ==> z = U(SUC c') \/ z = U(c' + d - 1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [moi_fn2_kcyc]) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `segment[(U:num->real^N) c',z]` o check (fun th ->
    is_forall (concl th) && can (find_term (fun t -> t = `&1:int`)) (concl th))) THEN
  ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `segment[(U:num->real^N) c',z] = segment[U j,U(SUC j)]` THEN
  REWRITE_TAC[SEGMENT_EQ] THEN
  DISCH_THEN(MP_TAC o MATCH_MP (SET_RULE
    `{x:real^N,y} = {z,w} ==> (x = z /\ y = w) \/ (x = w /\ y = z)`)) THEN
  STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_FN2_CYC_SUC_EQ THEN EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[];
    DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FN2_CYC_PRE_EQ THEN EXISTS_TAC `d:num` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `SUC(c' + d - 1) = c' + d` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_REWRITE_TAC[]]]);;

(* The link vertices of b(tau) (off UNIONS l, tau meeting UNIONS l) lying  *)
(* in UNIONS l form a run of one or three consecutive cycle vertices.       *)

let MOI_FN2_VX = prove
 (`!(m:(real^N->bool)->bool) l tau d U.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\
     tau IN barycentric_subdivision m /\ ~(tau = {}) /\
     ~(simplex_barycentre tau IN UNIONS l) /\ ~(tau INTER UNIONS l = {}) /\
     moi_fn2_kcyc (simplicial_link (barycentric_subdivision (barycentric_subdivision m))
                                   (simplex_barycentre tau)) d U
     ==> ?c q. (q = 0 \/ q = 2) /\
               !i. U i IN UNIONS l <=> ?j. j <= q /\ U i = U(c + j)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN barycentric_subdivision l
                                 ==> r IN barycentric_subdivision m`
  (LABEL_TAC "LM") THENL
   [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                   (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN SIMP_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [moi_fn2_kcyc] o check (fun th ->
    is_comb (concl th) && is_const (fst(strip_comb (concl th))) &&
    fst(dest_const(fst(strip_comb (concl th)))) = "moi_fn2_kcyc")) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "VE") (CONJUNCTS_THEN2 (LABEL_TAC "EE") ASSUME_TAC)))))) THEN
  SUBGOAL_THEN
   `!i. (U:num->real^N) i IN UNIONS l <=>
        ?r. r IN barycentric_subdivision m /\ ~(r = {}) /\ r SUBSET tau INTER UNIONS l /\
            U i = simplex_barycentre r`
  (LABEL_TAC "LV") THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_FN2_LINKV THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `tau:real^N->bool`]
                MOI_FRN_FULL) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (l:(real^N->bool)->bool)`;
                 `tau INTER UNIONS l:real^N->bool`] MOI_S4L_K1_CASES) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `sg = tau INTER UNIONS (l:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(sg:real^N->bool) SUBSET tau` ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(sg:real^N->bool) IN barycentric_subdivision m` ASSUME_TAC THENL
   [USE_THEN "LM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~(sg:real^N->bool = tau)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(simplex_barycentre tau IN UNIONS (l:(real^N->bool)->bool))` THEN
    REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `tau:real^N->bool`] MOI_FN2_BARY_IN_L) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `sg:real^N->bool = tau` THEN EXPAND_TAC "sg" THEN SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(DISJ_CASES_THEN2 (fun th -> ASM_MESON_TAC[th])
   (DISJ_CASES_THEN2 (X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC)
    (X_CHOOSE_THEN `w:real^N` (X_CHOOSE_THEN `w':real^N` STRIP_ASSUME_TAC)))) THENL
   [(* a single vertex *)
    SUBGOAL_THEN `{w:real^N} IN barycentric_subdivision m` ASSUME_TAC THENL
     [USE_THEN "LM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `tau:real^N->bool`;
                   `{w:real^N}`] MOI_FN2_LINK_SING) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
      UNDISCH_TAC `~(sg:real^N->bool = tau)` THEN UNDISCH_TAC `(sg:real^N->bool) SUBSET tau` THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      REWRITE_TAC[MOI_FRN_BARYCENTRE_SING] THEN DISCH_TAC] THEN
    USE_THEN "VE" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `{w:real^N} IN simplicial_link (barycentric_subdivision (barycentric_subdivision m))
                                     (simplex_barycentre tau)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `c:num` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`c:num`; `0`] THEN REWRITE_TAC[LE; ADD_CLAUSES; UNWIND_THM2] THEN
    X_GEN_TAC `i:num` THEN USE_THEN "LV" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `w:real^N = U(c:num)` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `r:real^N->bool = {w}` SUBST_ALL_TAC THENL
       [UNDISCH_TAC `(r:real^N->bool) SUBSET sg` THEN ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `~(r:real^N->bool = {})` THEN SET_TAC[];
        ASM_REWRITE_TAC[MOI_FRN_BARYCENTRE_SING]];
      DISCH_TAC THEN EXISTS_TAC `{w:real^N}` THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY; SUBSET_REFL; MOI_FRN_BARYCENTRE_SING]];
    (* an edge *)
    SUBGOAL_THEN
     `(w:real^N) IN sg /\ w' IN sg /\ aff_dim (sg:real^N->bool) = &1 /\ ~(sg = {}) /\
      (!a. {a} IN barycentric_subdivision l /\ a IN sg ==> a = w \/ a = w')`
    STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[ENDS_IN_SEGMENT; AFF_DIM_SEGMENT; SEGMENT_EQ_EMPTY] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S4L_K1_ENDPOINT THEN
      EXISTS_TAC `barycentric_subdivision (l:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(sg:real^N->bool) IN barycentric_subdivision l` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_THEN `sg = segment[w:real^N,w']` (K ALL_TAC) THEN
    SUBGOAL_THEN `{w:real^N} IN barycentric_subdivision m /\
                  {w':real^N} IN barycentric_subdivision m`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN USE_THEN "LM" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN
     `!z. z = w \/ z = w'
          ==> {z:real^N} IN barycentric_subdivision m /\ {z} SUBSET sg /\
              ~({z} = tau) /\ ~(sg = {z})`
    (LABEL_TAC "ZZ") THENL
     [GEN_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `(z:real^N) IN sg` ASSUME_TAC THENL
       [UNDISCH_TAC `z:real^N = w \/ z = w'` THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `~(sg = {z:real^N})` ASSUME_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `~(w:real^N = w')` THEN REWRITE_TAC[] THEN
        UNDISCH_TAC `(w:real^N) IN sg` THEN UNDISCH_TAC `(w':real^N) IN sg` THEN
        ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[SING_SUBSET] THEN CONJ_TAC THENL
       [UNDISCH_TAC `z:real^N = w \/ z = w'` THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `(sg:real^N->bool) SUBSET tau` THEN
        UNDISCH_TAC `~(sg:real^N->bool = {z})` THEN UNDISCH_TAC `(z:real^N) IN sg` THEN
        UNDISCH_TAC `{z:real^N} = tau` THEN SET_TAC[]];
      ALL_TAC] THEN
    (* the faces of sg: its two vertices and itself *)
    SUBGOAL_THEN
     `!r. r IN barycentric_subdivision m /\ ~(r = {}) /\ r SUBSET sg
          ==> r = {w:real^N} \/ r = {w'} \/ r = sg`
    (LABEL_TAC "FS") THENL
     [REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision l` ASSUME_TAC THENL
       [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                       (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
        REWRITE_TAC[simplicial_subcomplex] THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN EXISTS_TAC `sg:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FN2_NESTED_FACE THEN
        EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`barycentric_subdivision (l:(real^N->bool)->bool)`; `r:real^N->bool`]
                    MOI_S4L_K1_CASES) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN2 (fun th -> ASM_MESON_TAC[th])
       (DISJ_CASES_THEN2 (X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC)
        (X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)))) THENL
       [SUBGOAL_THEN `a:real^N = w \/ a = w'` MP_TAC THENL
         [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
            can (find_term (fun t -> t = `w':real^N`)) (concl th) && is_forall (concl th))) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `(r:real^N->bool) SUBSET sg` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
          STRIP_TAC THEN ASM_REWRITE_TAC[]];
        DISJ2_TAC THEN DISJ2_TAC THEN MATCH_MP_TAC MOI_FN2_SUBSET_DIM_EQ THEN
        EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN
        ASM_REWRITE_TAC[AFF_DIM_SEGMENT]];
      ALL_TAC] THEN
    (* b sg is a cycle vertex U c' *)
    MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `tau:real^N->bool`;
                   `sg:real^N->bool`] MOI_FN2_LINK_SING) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
    USE_THEN "VE" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `{simplex_barycentre sg:real^N} IN
       simplicial_link (barycentric_subdivision (barycentric_subdivision m))
                       (simplex_barycentre tau)`))) THEN
    DISCH_THEN(X_CHOOSE_THEN `c':num` STRIP_ASSUME_TAC) THEN
    (* w and w' are its two neighbours *)
    SUBGOAL_THEN
     `!z. z = w \/ z = w'
          ==> z = U(SUC c') \/ z = (U:num->real^N)(c' + d - 1)`
    (LABEL_TAC "NB") THENL
     [GEN_TAC THEN DISCH_TAC THEN
      USE_THEN "ZZ" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `z:real^N = w \/ z = w'`))) THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_FN2_CYC_NBR THEN
      EXISTS_TAC `simplicial_link (barycentric_subdivision (barycentric_subdivision m))
                    (simplex_barycentre (tau:real^N->bool))` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `simplex_barycentre sg = (U:num->real^N) c'` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `tau:real^N->bool`;
                       `sg:real^N->bool`; `{z:real^N}`] MOI_FC2_FLAG_LINK_EDGE) THEN
        REWRITE_TAC[MOI_FRN_BARYCENTRE_SING; SEGMENT_CONVEX_HULL] THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC MOI_FC2_CHAIN3 THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
        UNDISCH_TAC `{z:real^N} SUBSET sg` THEN UNDISCH_TAC `(sg:real^N->bool) SUBSET tau` THEN
        SET_TAC[];
        DISCH_TAC THEN
        MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                       `{z:real^N}`; `sg:real^N->bool`] MOI_FRN_BARYCENTRE_INJ) THEN
        ASM_REWRITE_TAC[MOI_FRN_BARYCENTRE_SING; NOT_INSERT_EMPTY] THEN
        UNDISCH_TAC `~(sg = {z:real^N})` THEN MESON_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `!x:real^N. x IN {w, w', simplex_barycentre sg} <=>
                 x IN {U(c' + d - 1), U(c' + d), U(c' + d + 1)}`
    (LABEL_TAC "SET3") THENL
     [SUBGOAL_THEN `(U:num->real^N)(c' + d) = U c' /\ U(c' + d + 1) = U(SUC c')`
      (fun th -> REWRITE_TAC[th]) THENL
       [CONJ_TAC THENL
         [ASM_REWRITE_TAC[];
          REWRITE_TAC[ARITH_RULE `c' + d + 1 = SUC c' + d`] THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      USE_THEN "NB" (MP_TAC o SPEC `w:real^N`) THEN
      USE_THEN "NB" (MP_TAC o SPEC `w':real^N`) THEN REWRITE_TAC[] THEN
      UNDISCH_TAC `~(w:real^N = w')` THEN
      UNDISCH_TAC `simplex_barycentre sg = (U:num->real^N) c'` THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`c' + d - 1`; `2`] THEN REWRITE_TAC[] THEN
    X_GEN_TAC `i:num` THEN USE_THEN "LV" (fun th -> REWRITE_TAC[th]) THEN
    TRANS_TAC EQ_TRANS `(U:num->real^N) i IN {w, w', simplex_barycentre sg}` THEN
    CONJ_TAC THENL
     [REMOVE_THEN "SET3" (K ALL_TAC) THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
        USE_THEN "FS" (fun th -> MP_TAC(MATCH_MP th
          (CONJ (ASSUME `(r:real^N->bool) IN barycentric_subdivision m`)
                (CONJ (ASSUME `~(r:real^N->bool = {})`)
                      (ASSUME `(r:real^N->bool) SUBSET sg`))))) THEN
        STRIP_TAC THEN ASM_REWRITE_TAC[MOI_FRN_BARYCENTRE_SING; IN_INSERT];
        REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
         [EXISTS_TAC `{w:real^N}`; EXISTS_TAC `{w':real^N}`; EXISTS_TAC `sg:real^N->bool`] THEN
        ASM_REWRITE_TAC[MOI_FRN_BARYCENTRE_SING; NOT_INSERT_EMPTY; SUBSET_REFL; SING_SUBSET]];
      USE_THEN "SET3" (fun th -> REWRITE_TAC[th]) THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[ARITH_RULE `j <= 2 <=> j = 0 \/ j = 1 \/ j = 2`] THEN
      REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
      SUBGOAL_THEN `(c' + d - 1) + 0 = c' + d - 1 /\ (c' + d - 1) + 1 = c' + d /\
                    (c' + d - 1) + 2 = c' + d + 1`
      (fun th -> REWRITE_TAC[th]) THEN
      ASM_ARITH_TAC]]);;


let MOI_FN2_ROT_TRI_DIM = prove
 (`!(K:(real^N->bool)->bool) y d U i.
     FINITE K /\ combinatorial_manifold 2 K /\ {y} IN K /\
     moi_fn2_kcyc (simplicial_link K y) d U /\
     (!i. ~(U i = y)) /\
     (!i. ~affine_dependent {y, U i, U(SUC i)} /\ convex hull {y, U i, U(SUC i)} IN K)
     ==> aff_dim (convex hull {y, U i, U(SUC i)}) = &2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `y:real^N`; `d:num`; `U:num->real^N`;
                 `i:num`] MOI_FN2_ROT_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `convex hull {y:real^N, U i, U(SUC i)}` o
             GEN_REWRITE_RULE I [EXTENSION] o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN SIMP_TAC[]);;

(* Which triangles at a vertex y of bsd(bsd m) meet UNIONS l.                 *)

let MOI_FN2_PX = prove
 (`!(m:(real^N->bool)->bool) l y d U.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\
     {y} IN barycentric_subdivision (barycentric_subdivision m) /\
     moi_fn2_kcyc (simplicial_link (barycentric_subdivision (barycentric_subdivision m)) y)
                  d U /\
     (!i. ~(U i = y)) /\
     (!i. ~affine_dependent {y, U i, U(SUC i)} /\
          convex hull {y, U i, U(SUC i)} IN
          barycentric_subdivision (barycentric_subdivision m))
     ==> (!i. convex hull {y, U i, U(SUC i)} IN moi_fn2_ptri m l <=>
              y IN UNIONS l \/ U i IN UNIONS l \/ U(SUC i) IN UNIONS l)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_C2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[moi_fn2_ptri; IN_ELIM_THM] THEN
  SUBGOAL_THEN `~affine_dependent {y:real^N, U i, U(SUC i)} /\
                convex hull {y:real^N, U i, U(SUC i)} IN
                barycentric_subdivision (barycentric_subdivision m)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))`;
                 `y:real^N`; `d:num`; `U:num->real^N`; `i:num`] MOI_FN2_ROT_TRI_DIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `convex hull {y:real^N, U i, U(SUC i)}`] MOI_FN2_C2_MEETS) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN STRIP_TAC THENL
     [EXISTS_TAC `y:real^N`; EXISTS_TAC `(U:num->real^N) i`;
      EXISTS_TAC `(U:num->real^N)(SUC i)`] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]]);;

let MOI_FN2_KP_LINK_ALL = prove
 (`!(K:(real^N->bool)->bool) P y d U.
     FINITE K /\ combinatorial_manifold 2 K /\ {y} IN K /\ P SUBSET K /\
     (!tr. tr IN P ==> aff_dim tr = &2) /\
     moi_fn2_kcyc (simplicial_link K y) d U /\ (!i. ~(U i = y)) /\
     (!i. ~affine_dependent {y, U i, U(SUC i)} /\ convex hull {y, U i, U(SUC i)} IN K) /\
     (!tr. tr IN K /\ aff_dim tr = &2 /\ y IN tr
           ==> ?i. i < d /\ tr = convex hull {y, U i, U(SUC i)}) /\
     (!i. convex hull {y, U i, U(SUC i)} IN P)
     ==> pl_sphere 1 (UNIONS (simplicial_link {s | ?tr. tr IN P /\ s face_of tr} y))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `P:(real^N->bool)->bool`; `y:real^N`;
                 `d:num`; `U:num->real^N`] MOI_FN2_SUBLINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
  REWRITE_TAC[ASSUME `!i. convex hull {y:real^N, U i, U(SUC i)} IN P`] THEN
  SUBGOAL_THEN `UNIONS {segment[(U:num->real^N) i,U(SUC i)] | i | i < d} =
                UNIONS (simplicial_link K y)` SUBST1_TAC THENL
   [UNDISCH_TAC `moi_fn2_kcyc (simplicial_link K y) d (U:num->real^N)` THEN
    REWRITE_TAC[moi_fn2_kcyc] THEN STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `combinatorial_manifold 2 (K:(real^N->bool)->bool)` THEN
  REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_REWRITE_TAC[]);;

(* The three situations at a vertex of bsd(bsd m): all triangles at it      *)
(* meet UNIONS l, none does, or they are decided by a run of link vertices. *)

let MOI_FN2_VERTEX_CASES = prove
 (`!(m:(real^N->bool)->bool) l y.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\
     {y} IN barycentric_subdivision (barycentric_subdivision m)
     ==> ?d U. moi_fn2_kcyc
                 (simplicial_link (barycentric_subdivision (barycentric_subdivision m)) y)
                 d U /\
               (!i. ~(U i = y)) /\
               (!i. ~affine_dependent {y, U i, U(SUC i)} /\
                    convex hull {y, U i, U(SUC i)} IN
                    barycentric_subdivision (barycentric_subdivision m)) /\
               (!tr. tr IN barycentric_subdivision (barycentric_subdivision m) /\
                     aff_dim tr = &2 /\ y IN tr
                     ==> ?i. i < d /\ tr = convex hull {y, U i, U(SUC i)}) /\
               ((!i. convex hull {y, U i, U(SUC i)} IN moi_fn2_ptri m l) \/
                (!i. ~(convex hull {y, U i, U(SUC i)} IN moi_fn2_ptri m l)) \/
                ?c q. (q = 0 \/ q = 2) /\
                      (!i. convex hull {y, U i, U(SUC i)} IN moi_fn2_ptri m l <=>
                           U i IN UNIONS l \/ U(SUC i) IN UNIONS l) /\
                      (!i. U i IN UNIONS l <=> ?j. j <= q /\ U i = U(c + j)))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_C2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))`;
                 `y:real^N`] MOI_FN2_ROT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `U:num->real^N` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`d:num`; `U:num->real^N`] THEN ASM_REWRITE_TAC[] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`;
                 `d:num`; `U:num->real^N`] MOI_FN2_PX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_TAC] THEN
  ASM_CASES_TAC `(y:real^N) IN UNIONS l` THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `y:real^N`]
                MOI_FC2_BSD_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real^N->bool` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `y:real^N = simplex_barycentre tau` THEN DISCH_THEN SUBST_ALL_TAC THEN
  SUBGOAL_THEN
   `!i. (U:num->real^N) i IN UNIONS l <=>
        ?r. r IN barycentric_subdivision m /\ ~(r = {}) /\ r SUBSET tau INTER UNIONS l /\
            U i = simplex_barycentre r`
  ASSUME_TAC THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_FN2_LINKV THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_fn2_kcyc
                 (simplicial_link (barycentric_subdivision (barycentric_subdivision m))
                    (simplex_barycentre tau)) d (U:num->real^N)` THEN
    REWRITE_TAC[moi_fn2_kcyc] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `tau INTER UNIONS (l:(real^N->bool)->bool) = {}` THENL
   [DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[SUBSET_EMPTY] THEN MESON_TAC[];
    DISJ2_TAC THEN DISJ2_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `tau:real^N->bool`;
                 `d:num`; `U:num->real^N`] MOI_FN2_VX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `q:num` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`c:num`; `q:num`] THEN ASM_REWRITE_TAC[]);;

(* Subcomplexes generated by sets of triangles of bsd(bsd m).               *)

let MOI_FN2_GEN_SUBCOMPLEX = prove
 (`!(K:(real^N->bool)->bool) R.
     lf_simplicial_complex K /\ R SUBSET K
     ==> lf_simplicial_complex {s | ?tr. tr IN R /\ s face_of tr} /\
         (!v. {v} IN {s | ?tr. tr IN R /\ s face_of tr} ==> {v} IN K /\ ?tr. tr IN R /\ v IN tr)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (K:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[simplicial_subcomplex; SUBSET; IN_ELIM_THM] THEN CONJ_TAC THENL
     [X_GEN_TAC `s:real^N->bool` THEN
      DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `moi_bar_complex (K:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_complex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      MAP_EVERY X_GEN_TAC [`s:real^N->bool`; `f:real^N->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)
        ASSUME_TAC) THEN
      EXISTS_TAC `tr:real^N->bool` THEN ASM_MESON_TAC[FACE_OF_TRANS]];
    X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [UNDISCH_TAC `moi_bar_complex (K:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_complex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET o check (fun th ->
        can (term_match [] `{v:real^N} face_of tr`) (concl th))) THEN SET_TAC[]]]);;

(* The derived neighbourhood side is a combinatorial surface with boundary.  *)

let MOI_FN2_NC_CMWB = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> combinatorial_manifold_with_boundary 2
           {s | ?tr. tr IN moi_fn2_ptri m l /\ s face_of tr}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_C2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))`;
                 `moi_fn2_ptri (m:(real^N->bool)->bool) l`] MOI_FN2_GEN_SUBCOMPLEX) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GV")) THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  USE_THEN "GV" (fun th -> MP_TAC(MATCH_MP th (ASSUME
    `{v:real^N} IN {s | ?tr. tr IN moi_fn2_ptri m l /\ s face_of tr}`))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
                MOI_FN2_VERTEX_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `U:num->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "TR")
        (DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC
          (X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `q:num`
            (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))))))))))) THENL
   [DISJ1_TAC THEN
    MATCH_MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision
                            (m:(real^N->bool)->bool))`;
                         `moi_fn2_ptri (m:(real^N->bool)->bool) l`; `v:real^N`; `d:num`;
                         `U:num->real^N`] MOI_FN2_KP_LINK_ALL) THEN
    ASM_REWRITE_TAC[];
    USE_THEN "TR" (MP_TAC o SPEC `tr:real^N->bool`) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [UNDISCH_TAC `moi_fn2_ptri m l SUBSET
                     barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `!tr:real^N->bool. tr IN moi_fn2_ptri m l ==> aff_dim tr = &2` THEN
        DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `(tr:real^N->bool) IN moi_fn2_ptri m l` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision
                      (m:(real^N->bool)->bool))`;
                   `moi_fn2_ptri (m:(real^N->bool)->bool) l`; `v:real^N`; `d:num`;
                   `U:num->real^N`; `UNIONS (l:(real^N->bool)->bool)`; `c:num`; `q:num`]
                  MOI_FN2_KP_LINK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `d <= q + 2` THEN ASM_SIMP_TAC[] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(d <= q + 2) ==> q + 3 <= d`]]);;

(* The complement side is a combinatorial surface with boundary.             *)

let MOI_FN2_CC_CMWB = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> combinatorial_manifold_with_boundary 2
           {s | ?tr. tr IN {t | t IN barycentric_subdivision (barycentric_subdivision m) /\
                                aff_dim t = &2 /\ ~(t IN moi_fn2_ptri m l)} /\
                     s face_of tr}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_C2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))`;
                 `{t:real^N->bool | t IN barycentric_subdivision (barycentric_subdivision m) /\
                                    aff_dim t = &2 /\ ~(t IN moi_fn2_ptri m l)}`]
                MOI_FN2_GEN_SUBCOMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "GV")) THEN
  REWRITE_TAC[combinatorial_manifold_with_boundary] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  USE_THEN "GV" (fun th -> MP_TAC(MATCH_MP th (ASSUME
    `{v:real^N} IN {s | ?tr. tr IN {t | t IN barycentric_subdivision
                                             (barycentric_subdivision m) /\
                                         aff_dim t = &2 /\ ~(t IN moi_fn2_ptri m l)} /\
                             s face_of tr}`))) THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[IN_ELIM_THM]) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `v:real^N`]
                MOI_FN2_VERTEX_CASES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `U:num->real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 (LABEL_TAC "TR") (LABEL_TAC "TRI"))))))) THEN
  USE_THEN "TR" (MP_TAC o SPEC `tr:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `j:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(convex hull {v:real^N, U j, U(SUC j)} IN moi_fn2_ptri m l)` ASSUME_TAC THENL
   [UNDISCH_TAC `~((tr:real^N->bool) IN moi_fn2_ptri m l)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REMOVE_THEN "TRI" (DISJ_CASES_THEN2 ASSUME_TAC (DISJ_CASES_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `c:num` (X_CHOOSE_THEN `q:num`
      (CONJUNCTS_THEN2 ASSUME_TAC STRIP_ASSUME_TAC))))) THENL
   [UNDISCH_TAC `~(convex hull {v:real^N, U j, U(SUC j)} IN moi_fn2_ptri m l)` THEN
    ASM_REWRITE_TAC[];
    DISJ1_TAC THEN
    MATCH_MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision
                            (m:(real^N->bool)->bool))`;
                         `{t:real^N->bool | t IN barycentric_subdivision
                                                   (barycentric_subdivision m) /\
                                            aff_dim t = &2 /\ ~(t IN moi_fn2_ptri m l)}`;
                         `v:real^N`; `d:num`; `U:num->real^N`] MOI_FN2_KP_LINK_ALL) THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[];
      SIMP_TAC[IN_ELIM_THM];
      GEN_TAC THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FN2_ROT_TRI_DIM THEN
      MAP_EVERY EXISTS_TAC [`barycentric_subdivision (barycentric_subdivision
                                (m:(real^N->bool)->bool))`; `d:num`] THEN
      ASM_REWRITE_TAC[]];
    MP_TAC(ISPECL [`simplicial_link (barycentric_subdivision (barycentric_subdivision m))
                      (v:real^N)`; `d:num`; `U:num->real^N`; `v:real^N`;
                   `moi_fn2_ptri (m:(real^N->bool)->bool) l`; `UNIONS (l:(real^N->bool)->bool)`;
                   `c:num`; `q:num`] MOI_FN2_LINK_INTERVAL) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(LABEL_TAC "LI1" o CONJUNCT1) THEN
    ASM_CASES_TAC `d <= q + 2` THENL
     [UNDISCH_TAC `~(convex hull {v:real^N, U j, U(SUC j)} IN moi_fn2_ptri m l)` THEN
      USE_THEN "LI1" (fun th -> REWRITE_TAC[SPEC `j:num` (MATCH_MP th (ASSUME `d <= q + 2`))]);
      ALL_TAC] THEN
    DISJ2_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision
                      (m:(real^N->bool)->bool))`;
                   `moi_fn2_ptri (m:(real^N->bool)->bool) l`; `v:real^N`; `d:num`;
                   `U:num->real^N`; `UNIONS (l:(real^N->bool)->bool)`; `c:num`; `q:num`]
                  MOI_FN2_KP_LINK) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[ARITH_RULE `~(d <= q + 2) ==> q + 3 <= d`]]);;

(* The simplices of the polygon l have dimension at most one.                *)

let MOI_FN2_L_DIM = prove
 (`!(m:(real^N->bool)->bool) l s.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ s IN l
     ==> aff_dim s <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (l:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[MOI_BAR_SIMPLICIAL_COMPLEX] THEN
    MATCH_MP_TAC MOI_FRN_LF_BAR_COMPLEX THEN
    ASM_MESON_TAC[MOI_FDN_LF_SUBCOMPLEX];
    ALL_TAC] THEN
  UNDISCH_TAC `pl_sphere 1 (UNIONS (l:(real^N->bool)->bool))` THEN
  REWRITE_TAC[pl_sphere; pl_homeomorphism] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MATCH_MP_TAC(ISPECL [`l:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                       `g:real^N->real^N`] MOI_FSA_LK_DIM) THEN
  ASM_REWRITE_TAC[]);;

(* Two triangles of a complex sharing a relative interior point coincide.     *)

let MOI_FN2_TRI_RELINT = prove
 (`!(K:(real^N->bool)->bool) t p x.
     lf_simplicial_complex K /\ t IN K /\ p IN K /\ aff_dim t = &2 /\ aff_dim p = &2 /\
     x IN relative_interior t /\ x IN p
     ==> p = t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t INTER p:real^N->bool) face_of t /\ (t INTER p) face_of p`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `t INTER p:real^N->bool = t` ASSUME_TAC THENL
   [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t INTER p:real^N->bool`; `t:real^N->bool`]
                  FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:real^N->bool`; `p:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[lf_simplicial_complex; SIMPLEX_IMP_CONVEX];
      UNDISCH_TAC `(t INTER p:real^N->bool) face_of p` THEN ASM_REWRITE_TAC[];
      ASM_MESON_TAC[]];
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]);;

(* Some triangle of the second derived subdivision avoids the polygon.       *)

let MOI_FN2_Q_NONEMPTY = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> ?tr. tr IN barycentric_subdivision (barycentric_subdivision m) /\
              aff_dim tr = &2 /\ ~(tr IN moi_fn2_ptri m l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_C2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?T0:real^N->bool. T0 IN m /\ aff_dim T0 = &2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~(UNIONS l = {}:real^N->bool)` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FRN_CM_PURE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ASM_MESON_TAC[MEMBER_NOT_EMPTY]];
      MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(T0:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim (T0:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre (T0:real^N->bool) IN UNIONS l)` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS; NOT_EXISTS_THM] THEN X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?n. n simplex (T0:real^N->bool)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (m:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) IN m` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) m` THEN
      REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(T0 INTER s:real^N->bool) face_of T0` ASSUME_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (m:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`T0:real^N->bool`; `s:real^N->bool`] o
                 CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[] THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `T0 INTER s:real^N->bool = T0` ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`T0 INTER s:real^N->bool`; `T0:real^N->bool`]
                    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `simplex_barycentre (T0:real^N->bool)` THEN REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN EXISTS_TAC `n:int` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN EXISTS_TAC `n:int` THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `s:real^N->bool`]
                  MOI_FN2_L_DIM) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`T0:real^N->bool`; `s:real^N->bool`] AFF_DIM_SUBSET) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `tau = {simplex_barycentre (T0:real^N->bool)}` THEN
  SUBGOAL_THEN `~(tau:real^N->bool = {})` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(tau:real^N->bool) INTER UNIONS l = {}` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN UNDISCH_TAC
     `~(simplex_barycentre (T0:real^N->bool) IN UNIONS l)` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(tau:real^N->bool) IN barycentric_subdivision m` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `simplex_barycentre (T0:real^N->bool)`]
                  MOI_FC2_BSD_VERTEX) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX]; DISCH_THEN SUBST1_TAC] THEN
    EXISTS_TAC `T0:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(simplex_barycentre (tau:real^N->bool) IN UNIONS l)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `tau:real^N->bool`]
                  MOI_FN2_BARY_IN_L) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `(tau:real^N->bool) INTER UNIONS l = {}` THEN
    UNDISCH_TAC `~(tau:real^N->bool = {})` THEN SET_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `y = simplex_barycentre (tau:real^N->bool)` THEN
  SUBGOAL_THEN `{y:real^N} IN barycentric_subdivision (barycentric_subdivision m)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `y:real^N`]
                  MOI_FC2_BSD_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `tau:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))`;
                 `y:real^N`] MOI_FN2_ROT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `d:num` (X_CHOOSE_THEN `U:num->real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!i. {(U:num->real^N) i} IN
                    simplicial_link (barycentric_subdivision (barycentric_subdivision m)) y`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_fn2_kcyc (simplicial_link (barycentric_subdivision
                   (barycentric_subdivision (m:(real^N->bool)->bool))) y) d U` THEN
    REWRITE_TAC[moi_fn2_kcyc] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. ~((U:num->real^N) i IN UNIONS l)` ASSUME_TAC THENL
   [X_GEN_TAC `i:num` THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `tau:real^N->bool`;
                   `(U:num->real^N) i`] MOI_FN2_LINKV) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    ASM_REWRITE_TAC[SUBSET_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `y:real^N`; `d:num`;
                 `U:num->real^N`] MOI_FN2_PX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  EXISTS_TAC `convex hull {y:real^N, U 0, U(SUC 0)}` THEN ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FN2_ROT_TRI_DIM THEN
  MAP_EVERY EXISTS_TAC [`barycentric_subdivision (barycentric_subdivision
                            (m:(real^N->bool)->bool))`; `d:num`] THEN
  ASM_REWRITE_TAC[]);;

(* The faces of a family of convex sets cover the same set.                  *)

let MOI_FN2_UNIONS_FACES = prove
 (`!R:(real^N->bool)->bool.
     (!tr. tr IN R ==> convex tr)
     ==> UNIONS {s | ?tr. tr IN R /\ s face_of tr} = UNIONS R`,
  GEN_TAC THEN DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(MATCH_MP FACE_OF_IMP_SUBSET (ASSUME `(s:real^N->bool) face_of tr`)) THEN
    UNDISCH_TAC `(tr:real^N->bool) IN R` THEN SET_TAC[];
    MATCH_MP_TAC SUBSET_UNIONS THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
    X_GEN_TAC `tr:real^N->bool` THEN DISCH_TAC THEN EXISTS_TAC `tr:real^N->bool` THEN
    ASM_SIMP_TAC[FACE_OF_REFL]]);;

(* The closure of the complement of N is the union of the other triangles.   *)

let MOI_FN2_CLOSURE_Q = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> closure (UNIONS m DIFF derived_nbhd m l) =
         UNIONS {t | t IN barycentric_subdivision (barycentric_subdivision m) /\
                     aff_dim t = &2 /\ ~(t IN moi_fn2_ptri m l)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_C2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_NC_KP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  UNDISCH_TAC `UNIONS (barycentric_subdivision (barycentric_subdivision
                 (m:(real^N->bool)->bool))) = UNIONS m` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `K = barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
  ABBREV_TAC `P = moi_fn2_ptri (m:(real^N->bool)->bool) l` THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN K ==> closed t /\ convex t` ASSUME_TAC THENL
   [X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (K:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SIMPLEX_IMP_CLOSED; SIMPLEX_IMP_CONVEX]];
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS K = UNIONS P UNION
                UNIONS {t:real^N->bool | t IN K /\ aff_dim t = &2 /\ ~(t IN P)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FRN_CM_PURE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MEMBER_NOT_EMPTY]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `(t:real^N->bool) IN P` THENL
       [DISJ1_TAC THEN EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[SUBSET];
        DISJ2_TAC THEN EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[SUBSET]];
      REWRITE_TAC[UNION_SUBSET] THEN CONJ_TAC THEN MATCH_MP_TAC SUBSET_UNIONS THENL
       [ASM_REWRITE_TAC[]; SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!t:real^N->bool. t IN K /\ aff_dim t = &2 /\ ~(t IN P)
                                 ==> relative_interior t INTER UNIONS P = {}`
  (LABEL_TAC "RI") THENL
   [X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `p:real^N->bool` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(p:real^N->bool) IN K /\ aff_dim p = &2` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
    MP_TAC(ISPECL [`K:(real^N->bool)->bool`; `t:real^N->bool`; `p:real^N->bool`; `x:real^N`]
                  MOI_FN2_TRI_RELINT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `closed (UNIONS {t:real^N->bool | t IN K /\ aff_dim t = &2 /\ ~(t IN P)})`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `K:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MATCH_MP_TAC CLOSURE_MINIMAL THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[UNIONS_SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `t:real^N->bool = closure(relative_interior t)` SUBST1_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_CLOSURE THEN
  SUBGOAL_THEN `relative_interior t INTER UNIONS P = {}:real^N->bool` MP_TAC THENL
   [USE_THEN "RI" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `t:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC `(t:real^N->bool) IN K` THEN SET_TAC[]);;

(* The complement complex: simplices of the second derived subdivision in   *)
(* the closure of the complement of N are the faces of the other triangles.  *)

let MOI_FN2_CC_EQ = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> {s | s IN barycentric_subdivision (barycentric_subdivision m) /\
              s SUBSET closure (UNIONS m DIFF derived_nbhd m l)} =
         {s | ?tr. tr IN {t | t IN barycentric_subdivision (barycentric_subdivision m) /\
                              aff_dim t = &2 /\ ~(t IN moi_fn2_ptri m l)} /\
                   s face_of tr}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CLOSURE_Q) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_Q_NONEMPTY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_C2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `K = barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
  ABBREV_TAC `P = moi_fn2_ptri (m:(real^N->bool)->bool) l` THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THENL
   [STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
     [EXISTS_TAC `t0:real^N->bool` THEN ASM_REWRITE_TAC[EMPTY_FACE_OF]; ALL_TAC] THEN
    SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (K:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `?x:real^N. x IN relative_interior s` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_EQ_EMPTY; SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    SUBGOAL_THEN `?tr:real^N->bool. (tr IN K /\ aff_dim tr = &2 /\ ~(tr IN P)) /\ x IN tr`
    (X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THENL
     [UNDISCH_TAC `s SUBSET UNIONS {t:real^N->bool | t IN K /\ aff_dim t = &2 /\ ~(t IN P)}` THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
      ALL_TAC] THEN
    EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(s INTER tr:real^N->bool) face_of s /\ (s INTER tr) face_of tr`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (K:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`s:real^N->bool`; `tr:real^N->bool`] o
                 CONJUNCT1 o CONJUNCT2 o CONJUNCT2) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `s INTER tr:real^N->bool = s`
     (fun th -> UNDISCH_TAC `(s INTER tr:real^N->bool) face_of tr` THEN REWRITE_TAC[th]) THEN
    MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`s INTER tr:real^N->bool`; `s:real^N->bool`]
                  FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN CONJ_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (K:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
      EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(MATCH_MP FACE_OF_IMP_SUBSET (ASSUME `(s:real^N->bool) face_of tr`)) THEN
      MATCH_MP_TAC(SET_RULE `(tr:real^N->bool) IN Q ==> s SUBSET tr ==> s SUBSET UNIONS Q`) THEN
      ASM_REWRITE_TAC[IN_ELIM_THM]]]);;

(* Conclusion (3): the surface boundary of N is its frontier.                *)

let MOI_FN2_BOUNDARY_NC = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> surface_boundary (derived_nbhd_complex m l) = derived_frontier m l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (m:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_C2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  ASM_SIMP_TAC[MOI_FN2_FRONTIER_NC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_NC_KP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))`;
                 `moi_fn2_ptri (m:(real^N->bool)->bool) l`] MOI_FN2_KP_FRONTIER) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[IN_ELIM_THM]);;

(* Conclusions (11)-(13): the complement side.                               *)

let MOI_FN2_CC_PROPS = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> combinatorial_manifold_with_boundary 2
           {s | s IN barycentric_subdivision (barycentric_subdivision m) /\
                s SUBSET closure (UNIONS m DIFF derived_nbhd m l)} /\
         UNIONS {s | s IN barycentric_subdivision (barycentric_subdivision m) /\
                     s SUBSET closure (UNIONS m DIFF derived_nbhd m l)} =
         closure (UNIONS m DIFF derived_nbhd m l) /\
         surface_boundary
           {s | s IN barycentric_subdivision (barycentric_subdivision m) /\
                s SUBSET closure (UNIONS m DIFF derived_nbhd m l)} =
         derived_frontier m l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CC_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_C2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FN2_CC_CMWB THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CLOSURE_Q) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC MOI_FN2_UNIONS_FACES THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `tr:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?n. n simplex (tr:real^N->bool)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (barycentric_subdivision
                     (barycentric_subdivision (m:(real^N->bool)->bool)))` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      ASM_REWRITE_TAC[];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]];
    MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))`;
                   `moi_fn2_ptri (m:(real^N->bool)->bool) l`] MOI_FN2_SB_PQ) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_NC_KP) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
    MATCH_MP_TAC MOI_FN2_BOUNDARY_NC THEN ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* The frontier of N as a graph.  Its edges are the second-derived          *)
(* segments from the barycentre of an edge f of the first derived that      *)
(* meets UNIONS l without lying in it (moi_frn_vp of pc_moi_fnd_rn) to the  *)
(* barycentre of a triangle containing f.                                   *)
(* ========================================================================= *)

(* Facts about the first and second derived subdivisions used below.        *)

let MOI_FN2_F7_CONTEXT = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> lf_simplicial_complex m /\
         lf_simplicial_complex (barycentric_subdivision m) /\
         moi_bar_complex (barycentric_subdivision m) /\
         FINITE (barycentric_subdivision m) /\
         combinatorial_manifold 2 (barycentric_subdivision m) /\
         (!r. r IN barycentric_subdivision m ==> aff_dim r <= &2) /\
         simplicial_subcomplex (barycentric_subdivision l) (barycentric_subdivision m) /\
         UNIONS (barycentric_subdivision l) = UNIONS l /\
         simplicial_complex (barycentric_subdivision l) /\
         (!s. s IN barycentric_subdivision l ==> aff_dim s <= &1) /\
         (!r. r IN barycentric_subdivision m /\ r SUBSET UNIONS l
              ==> r IN barycentric_subdivision l) /\
         FINITE (barycentric_subdivision (barycentric_subdivision m)) /\
         combinatorial_manifold 2 (barycentric_subdivision (barycentric_subdivision m)) /\
         moi_bar_complex (barycentric_subdivision (barycentric_subdivision m)) /\
         lf_simplicial_complex (barycentric_subdivision (barycentric_subdivision m)) /\
         UNIONS (barycentric_subdivision (barycentric_subdivision m)) = UNIONS m /\
         moi_fn2_ptri m l SUBSET barycentric_subdivision (barycentric_subdivision m) /\
         (!tr. tr IN moi_fn2_ptri m l ==> aff_dim tr = &2)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_C2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision (m:(real^N->bool)->bool))`
  ASSUME_TAC THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN barycentric_subdivision m ==> aff_dim r <= &2`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN MATCH_MP_TAC MOI_FRN_SA_CM_DIM THEN
    EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN barycentric_subdivision m /\ r SUBSET UNIONS l
                                 ==> r IN barycentric_subdivision l`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_FULL_SUBSET THEN
    EXISTS_TAC `m:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[]);;

(* A vertex of the first derived lies on the polygon iff it is a vertex of   *)
(* the first derived of l.                                                  *)

let MOI_FN2_VERT_L = prove
 (`!(m:(real^N->bool)->bool) l x.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ {x} IN barycentric_subdivision m
     ==> (x IN UNIONS l <=> {x} IN barycentric_subdivision l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!r:real^N->bool. r IN barycentric_subdivision m /\
                                           r SUBSET UNIONS l
                                           ==> r IN barycentric_subdivision l`) (concl th))) THEN
    ASM_REWRITE_TAC[SING_SUBSET];
    DISCH_TAC THEN UNDISCH_TAC
     `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `{x:real^N}` THEN ASM_REWRITE_TAC[IN_SING]]);;

(* A simplex of the first derived meeting the polygon without lying in it  *)
(* is not a vertex.                                                         *)

let MOI_FN2_VP_NOT_VERTEX = prove
 (`!(m:(real^N->bool)->bool) l r.
     moi_frn_vp m l r ==> ~(aff_dim r = &0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_frn_vp; AFF_DIM_EQ_0] THEN
  STRIP_TAC THEN DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `~({a:real^N} SUBSET UNIONS l)` THEN
  UNDISCH_TAC `~({a:real^N} INTER UNIONS l = {})` THEN SET_TAC[]);;

(* Such an edge has exactly one end on the polygon.                          *)

let MOI_FN2_VP_EDGE = prove
 (`!(m:(real^N->bool)->bool) l f.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ moi_frn_vp m l f /\ aff_dim f = &1
     ==> ?x y. ~(x = y) /\ f = segment[x,y] /\
               {x} IN barycentric_subdivision m /\ {y} IN barycentric_subdivision m /\
               x IN UNIONS l /\ ~(y IN UNIONS l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_frn_vp m l (f:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `f:real^N->bool`]
                MOI_FRN_SEG_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!u:real^N. {u} IN barycentric_subdivision m /\ u IN f ==> u = x \/ u = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `{u:real^N} face_of f` MP_TAC THENL
     [SUBGOAL_THEN `{u:real^N} = {u} INTER f` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `moi_bar_complex (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
      REWRITE_TAC[moi_bar_complex] THEN
      DISCH_THEN(MP_TAC o SPECL [`{u:real^N}`; `f:real^N->bool`] o
                 CONJUNCT2 o CONJUNCT2) THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[FACE_OF_SING; GSYM SEGMENT_CONVEX_HULL; EXTREME_POINT_OF_SEGMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS l \/ y IN UNIONS l` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
                  MOI_FRN_FULL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (l:(real^N->bool)->bool)`;
                   `f INTER UNIONS l:real^N->bool`] MOI_FN2_SIMPLEX_HAS_VERTEX) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `simplicial_complex (barycentric_subdivision (l:(real^N->bool)->bool))` THEN
      SIMP_TAC[MOI_BAR_SIMPLICIAL_COMPLEX];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `u:real^N` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `{u:real^N} IN barycentric_subdivision m` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                     (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
      REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(u:real^N) = x \/ u = y` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `(u:real^N) IN f INTER UNIONS l` THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^N) IN UNIONS l /\ y IN UNIONS l)` ASSUME_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `{x:real^N} IN barycentric_subdivision l /\
                  {y:real^N} IN barycentric_subdivision l` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FN2_VERT_L]; ALL_TAC] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`;
                   `x:real^N`; `y:real^N`] MOI_FN2_FULL_EDGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_REWRITE_TAC[HULL_INC; IN_INSERT; NOT_IN_EMPTY] THEN
      CONJ_TAC THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    UNDISCH_TAC `f = convex hull {x:real^N,y}` THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    DISCH_TAC THEN UNDISCH_TAC `~(f SUBSET UNIONS (l:(real^N->bool)->bool))` THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(f:real^N->bool) IN k ==> f SUBSET UNIONS k`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THENL
   [MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    UNDISCH_TAC `~((x:real^N) IN UNIONS l /\ y IN UNIONS l)` THEN ASM_REWRITE_TAC[];
    MAP_EVERY EXISTS_TAC [`y:real^N`; `x:real^N`] THEN
    ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN CONJ_TAC THENL
     [REWRITE_TAC[INSERT_AC];
      UNDISCH_TAC `~((x:real^N) IN UNIONS l /\ y IN UNIONS l)` THEN ASM_REWRITE_TAC[]]]);;

(* Chains of two and three simplices; the hull of a two-chain.               *)

let MOI_FN2_CHAIN2 = prove
 (`!(c:(real^N->bool)->bool) r r'.
     r IN c /\ r' IN c /\ ~(r = {}) /\ r SUBSET r' ==> moi_bar_chain c {r,r'}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_bar_chain] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    CONJ_TAC THEN DISCH_THEN(ASSUME_TAC o SYM) THEN
    UNDISCH_TAC `~(r:real^N->bool = {})` THEN UNDISCH_TAC `(r:real^N->bool) SUBSET r'` THEN
    ASM_REWRITE_TAC[SUBSET_EMPTY];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (DISJ_CASES_THEN SUBST1_TAC)) THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

let MOI_FN2_CHAIN3 = prove
 (`!(c:(real^N->bool)->bool) x r r'.
     {x} IN c /\ r IN c /\ r' IN c /\ x IN r /\ r SUBSET r'
     ==> moi_bar_chain c {{x},r,r'}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `{x:real^N} SUBSET r /\ {x} SUBSET r'` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_bar_chain] THEN REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET];
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[NOT_EMPTY_INSERT];
      DISCH_TAC THEN UNDISCH_TAC `{x:real^N} SUBSET r` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUBSET_EMPTY; NOT_INSERT_EMPTY];
      DISCH_TAC THEN UNDISCH_TAC `{x:real^N} SUBSET r'` THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN REWRITE_TAC[SUBSET_EMPTY; NOT_INSERT_EMPTY]];
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT GEN_TAC THEN
    DISCH_THEN(CONJUNCTS_THEN (DISJ_CASES_THEN2 SUBST1_TAC (DISJ_CASES_THEN SUBST1_TAC))) THEN
    ASM_REWRITE_TAC[SUBSET_REFL]]);;

let MOI_FN2_HULL2 = prove
 (`!(r:real^N->bool) r'.
     convex hull (IMAGE simplex_barycentre {r,r'}) =
     segment[simplex_barycentre r,simplex_barycentre r']`,
  REWRITE_TAC[IMAGE_CLAUSES; SEGMENT_CONVEX_HULL]);;

let MOI_FN2_BARY_IN_C = prove
 (`!(c:(real^N->bool)->bool) r.
     moi_bar_complex c /\ r IN c /\ ~(r = {}) ==> simplex_barycentre r IN r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN EXISTS_TAC `n:int` THEN
  ASM_REWRITE_TAC[]);;

(* A second-derived simplex meets the polygon iff its chain contains a      *)
(* simplex of the first derived of l.                                       *)

let MOI_FN2_CHAIN_MEETS_L = prove
 (`!(m:(real^N->bool)->bool) l g.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ moi_bar_chain (barycentric_subdivision m) g
     ==> (~(convex hull (IMAGE simplex_barycentre g) INTER UNIONS l = {}) <=>
          ?s. s IN g /\ s IN barycentric_subdivision l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                 `barycentric_subdivision (l:(real^N->bool)->bool)`; `g:(real^N->bool)->bool`]
                MOI_FRN_CHAIN_HULL_MEETS) THEN
  ASM_REWRITE_TAC[]);;

(* The second-derived edge from the barycentre of rho to that of rho' lies in *)
(* exactly one triangle of N iff rho meets the polygon without lying in it.    *)

let MOI_FN2_FR_EDGE = prove
 (`!(m:(real^N->bool)->bool) l rho rho'.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\
     rho IN barycentric_subdivision m /\ rho' IN barycentric_subdivision m /\
     ~(rho = {}) /\ rho SUBSET rho' /\ ~(rho = rho')
     ==> (CARD {t | t IN moi_fn2_ptri m l /\
                    segment[simplex_barycentre rho,simplex_barycentre rho'] SUBSET t} = 1 <=>
          moi_frn_vp m l rho)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision m) {rho:real^N->bool,rho'}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FN2_CHAIN2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[simplex_barycentre rho:real^N,simplex_barycentre rho'] IN
    barycentric_subdivision (barycentric_subdivision m) /\
    aff_dim(segment[simplex_barycentre rho:real^N,simplex_barycentre rho']) = &1`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_FN2_HULL2] THEN CONJ_TAC THENL
     [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `{rho:real^N->bool,rho'}` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                     `{rho:real^N->bool,rho'}`] MOI_FRN_BARY_AFF_DIM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  ABBREV_TAC `e = segment[simplex_barycentre rho:real^N,simplex_barycentre rho']` THEN
  SUBGOAL_THEN
   `CARD {t | t IN barycentric_subdivision (barycentric_subdivision m) /\
              aff_dim t = &2 /\ (e:real^N->bool) SUBSET t} = 2`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_SA_CM_EDGE2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!t:real^N->bool. t IN moi_fn2_ptri m l <=>
                     t IN barycentric_subdivision (barycentric_subdivision m) /\
                     aff_dim t = &2 /\ ~(t INTER UNIONS l = {})`
  (LABEL_TAC "PT") THENL
   [REWRITE_TAC[moi_fn2_ptri; IN_ELIM_THM]; ALL_TAC] THEN
  ASM_CASES_TAC `(rho:real^N->bool) IN barycentric_subdivision l` THENL
   [SUBGOAL_THEN `(rho:real^N->bool) SUBSET UNIONS l` ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(SET_RULE `(r:real^N->bool) IN k ==> r SUBSET UNIONS k`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~moi_frn_vp m l (rho:real^N->bool)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[moi_frn_vp]; ALL_TAC] THEN
    SUBGOAL_THEN
     `{t | t IN moi_fn2_ptri m l /\ (e:real^N->bool) SUBSET t} =
      {t | t IN barycentric_subdivision (barycentric_subdivision m) /\
           aff_dim t = &2 /\ e SUBSET t}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN X_GEN_TAC `t:real^N->bool` THEN
      USE_THEN "PT" (fun th -> REWRITE_TAC[th]) THEN
      EQ_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `simplex_barycentre rho:real^N` THEN CONJ_TAC THENL
       [UNDISCH_TAC `(e:real^N->bool) SUBSET t` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN EXPAND_TAC "e" THEN REWRITE_TAC[ENDS_IN_SEGMENT];
        UNDISCH_TAC `(rho:real^N->bool) SUBSET UNIONS l` THEN REWRITE_TAC[SUBSET] THEN
        DISCH_THEN MATCH_MP_TAC THEN MATCH_MP_TAC MOI_FN2_BARY_IN_C THEN
        EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN
        ASM_REWRITE_TAC[]];
      ASM_REWRITE_TAC[] THEN ARITH_TAC];
    ALL_TAC] THEN
  ASM_CASES_TAC `(rho:real^N->bool) INTER UNIONS l = {}` THENL
   [SUBGOAL_THEN `~moi_frn_vp m l (rho:real^N->bool)` (fun th -> REWRITE_TAC[th]) THENL
     [ASM_REWRITE_TAC[moi_frn_vp]; ALL_TAC] THEN
    SUBGOAL_THEN `{t | t IN moi_fn2_ptri m l /\ (e:real^N->bool) SUBSET t} = {}`
    SUBST1_TAC THENL
     [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN X_GEN_TAC `t:real^N->bool` THEN
      USE_THEN "PT" (fun th -> REWRITE_TAC[th]) THEN STRIP_TAC THEN
      UNDISCH_TAC `(t:real^N->bool) IN barycentric_subdivision (barycentric_subdivision m)` THEN
      REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `{rho:real^N->bool,rho'} SUBSET g` ASSUME_TAC THENL
       [MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                       `{rho:real^N->bool,rho'}`; `g:(real^N->bool)->bool`]
                      MOI_FRN_CHAIN_HULL_SUBSET) THEN
        ASM_REWRITE_TAC[MOI_FN2_HULL2] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `(e:real^N->bool) SUBSET t` THEN EXPAND_TAC "e" THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `?s:real^N->bool. s IN g /\ s IN barycentric_subdivision l`
      (X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THENL
       [MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `g:(real^N->bool)->bool`] MOI_FN2_CHAIN_MEETS_L) THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
        UNDISCH_TAC `~((t:real^N->bool) INTER UNIONS l = {})` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS l /\ ~(s = {}) /\
                    (s SUBSET rho \/ rho SUBSET s)`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THENL
       [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision m) (g:(real^N->bool)->bool)` THEN
        REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
         [UNDISCH_TAC `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN
          MATCH_MP_TAC(SET_RULE `(r:real^N->bool) IN k ==> r SUBSET UNIONS k`) THEN
          ASM_REWRITE_TAC[];
          ASM_MESON_TAC[];
          FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `(rho:real^N->bool) INTER UNIONS l = {}` THEN
      UNDISCH_TAC `~(rho:real^N->bool = {})` THEN
      UNDISCH_TAC `(s:real^N->bool) SUBSET rho \/ rho SUBSET s` THEN
      UNDISCH_TAC `~(s:real^N->bool = {})` THEN
      UNDISCH_TAC `(s:real^N->bool) SUBSET UNIONS l` THEN SET_TAC[];
      REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_frn_vp m l (rho:real^N->bool)` (fun th -> REWRITE_TAC[th] THEN
                                                    ASSUME_TAC th) THENL
   [ASM_REWRITE_TAC[moi_frn_vp] THEN DISCH_TAC THEN
    UNDISCH_TAC `~((rho:real^N->bool) IN barycentric_subdivision l)` THEN
    REWRITE_TAC[] THEN FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!r:real^N->bool. r IN barycentric_subdivision m /\
                                           r SUBSET UNIONS l
                                           ==> r IN barycentric_subdivision l`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (rho:real^N->bool) = &1 /\ aff_dim (rho':real^N->bool) = &2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `rho:real^N->bool`]
                  MOI_FN2_VP_NOT_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                   `{rho:real^N->bool,rho'}`; `rho:real^N->bool`; `rho':real^N->bool`]
                  MOI_FRN_CHAIN_DIM_LT) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    MP_TAC(ISPEC `rho:real^N->bool` AFF_DIM_GE) THEN
    MP_TAC(ISPEC `rho:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
    REWRITE_TAC[ASSUME `~(rho:real^N->bool = {})`] THEN
    SUBGOAL_THEN `aff_dim (rho':real^N->bool) <= &2` MP_TAC THENL
     [UNDISCH_TAC `!r:real^N->bool. r IN barycentric_subdivision m ==> aff_dim r <= &2` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~(aff_dim (rho:real^N->bool) = &0)` THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `rho:real^N->bool`]
                MOI_FN2_VP_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(x:real^N) IN rho /\ y IN rho` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  UNDISCH_THEN `rho = segment[x:real^N,y]` (K ALL_TAC) THEN
  SUBGOAL_THEN `{x:real^N} IN barycentric_subdivision l /\
                ~({y:real^N} IN barycentric_subdivision l)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FN2_VERT_L]; ALL_TAC] THEN
  SUBGOAL_THEN `~((rho':real^N->bool) IN barycentric_subdivision l)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~((rho:real^N->bool) IN barycentric_subdivision l)` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                   (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
    REWRITE_TAC[simplicial_subcomplex] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    EXISTS_TAC `rho':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FN2_NESTED_FACE THEN
    EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision m) {{x:real^N},rho,rho'} /\
                moi_bar_chain (barycentric_subdivision m) {{y:real^N},rho,rho'}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FN2_CHAIN3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~({x:real^N} = rho) /\ ~({x:real^N} = rho') /\
                ~({y:real^N} = rho) /\ ~({y:real^N} = rho') /\ ~({x:real^N} = {y})`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SET_RULE `{a:real^N} = {b} <=> a = b`] THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[AFF_DIM_SING] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC `tx = convex hull (IMAGE simplex_barycentre {{x:real^N},rho,rho'})` THEN
  ABBREV_TAC `ty = convex hull (IMAGE simplex_barycentre {{y:real^N},rho,rho'})` THEN
  SUBGOAL_THEN
   `!z:real^N. {z} IN barycentric_subdivision m /\ z IN rho /\ ~({z} = rho) /\ ~({z} = rho')
               ==> convex hull (IMAGE simplex_barycentre {{z},rho,rho'}) IN
                   barycentric_subdivision (barycentric_subdivision m) /\
                   aff_dim (convex hull (IMAGE simplex_barycentre {{z},rho,rho'})) = &2 /\
                   (e:real^N->bool) SUBSET convex hull (IMAGE simplex_barycentre {{z},rho,rho'})`
  (LABEL_TAC "TZ") THENL
   [X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision m) {{z:real^N},rho,rho'}`
    ASSUME_TAC THENL [MATCH_MP_TAC MOI_FN2_CHAIN3 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `{{z:real^N},rho,rho'}` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                     `{{z:real^N},rho,rho'}`] MOI_FRN_BARY_AFF_DIM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
      EXPAND_TAC "e" THEN REWRITE_TAC[GSYM MOI_FN2_HULL2] THEN
      MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(tx:real^N->bool = ty)` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["tx"; "ty"] THEN DISCH_TAC THEN
    SUBGOAL_THEN `{{x:real^N},rho,rho'} = {{y},rho,rho'}` MP_TAC THENL
     [MATCH_MP_TAC MOI_FRN_CHAIN_HULL_INJ THEN
      EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN
      REPEAT CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    DISCH_THEN(MP_TAC o AP_TERM `\s:(real^N->bool)->bool. {x:real^N} IN s`) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(tx:real^N->bool) IN barycentric_subdivision (barycentric_subdivision m) /\
                aff_dim tx = &2 /\ (e:real^N->bool) SUBSET tx`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "tx" THEN USE_THEN "TZ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(ty:real^N->bool) IN barycentric_subdivision (barycentric_subdivision m) /\
                aff_dim ty = &2 /\ (e:real^N->bool) SUBSET ty`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "ty" THEN USE_THEN "TZ" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((tx:real^N->bool) INTER UNIONS l = {})` ASSUME_TAC THENL
   [EXPAND_TAC "tx" THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `{{x:real^N},rho,rho'}`] MOI_FN2_CHAIN_MEETS_L) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    EXISTS_TAC `{x:real^N}` THEN ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `(ty:real^N->bool) INTER UNIONS l = {}` ASSUME_TAC THENL
   [EXPAND_TAC "ty" THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `{{y:real^N},rho,rho'}`] MOI_FN2_CHAIN_MEETS_L) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `~q ==> (~p <=> q) ==> p`) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(tx:real^N->bool) IN moi_fn2_ptri m l /\ ~(ty IN moi_fn2_ptri m l)`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "PT" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `{t | t IN barycentric_subdivision (barycentric_subdivision m) /\
         aff_dim t = &2 /\ (e:real^N->bool) SUBSET t} = {tx,ty}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FN2_CARD2_EQ THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN
      EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ASM_REWRITE_TAC[IN_ELIM_THM]];
    ALL_TAC] THEN
  USE_THEN "PT" (fun th -> REWRITE_TAC[th]) THEN
  SUBGOAL_THEN `{t | (t IN barycentric_subdivision (barycentric_subdivision m) /\
                      aff_dim t = &2 /\ ~(t INTER UNIONS l = {})) /\
                     (e:real^N->bool) SUBSET t} = {tx}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_SING] THEN
    X_GEN_TAC `t:real^N->bool` THEN
    EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(t:real^N->bool) IN {tx,ty}` MP_TAC THENL
       [UNDISCH_TAC
         `{t | t IN barycentric_subdivision (barycentric_subdivision m) /\
               aff_dim t = &2 /\ (e:real^N->bool) SUBSET t} = {tx,ty}` THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST_ALL_TAC) THENL
       [REWRITE_TAC[];
        UNDISCH_TAC `~((ty:real^N->bool) INTER UNIONS l = {})` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[CARD_SING]]);;

(* An edge of the second derived is the segment between the barycentres of  *)
(* a two-element chain.                                                      *)

let MOI_FN2_K_EDGE = prove
 (`!(c:(real^N->bool)->bool) e.
     moi_bar_complex c /\ e IN barycentric_subdivision c /\ aff_dim e = &1
     ==> ?rho rho'. rho IN c /\ rho' IN c /\ ~(rho = {}) /\ rho SUBSET rho' /\
                    ~(rho = rho') /\
                    e = segment[simplex_barycentre rho,simplex_barycentre rho']`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(e:real^N->bool) IN barycentric_subdivision c` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `CARD (g:(real^N->bool)->bool) = 2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
                  MOI_FRN_BARY_AFF_DIM) THEN
    ASM_REWRITE_TAC[] THEN UNDISCH_TAC `aff_dim (e:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INT_ARITH `&1:int = x - &1 <=> x = &2`; INT_OF_NUM_EQ] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `g:(real^N->bool)->bool` MOI_FC2_CARD_EQ_2) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `FINITE (g:(real^N->bool)->bool)` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  UNDISCH_TAC `moi_bar_chain c (g:(real^N->bool)->bool)` THEN
  ASM_REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY;
                  DE_MORGAN_THM] THEN
  STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N->bool`; `b:real^N->bool`]) THEN
  REWRITE_TAC[] THEN STRIP_TAC THENL
   [MAP_EVERY EXISTS_TAC [`a:real^N->bool`; `b:real^N->bool`] THEN
    ASM_REWRITE_TAC[MOI_FN2_HULL2] THEN ASM_MESON_TAC[];
    MAP_EVERY EXISTS_TAC [`b:real^N->bool`; `a:real^N->bool`] THEN
    ASM_REWRITE_TAC[MOI_FN2_HULL2] THEN ASM_MESON_TAC[SEGMENT_SYM]]);;

(* The frontier of N as the union of the graph edges.                        *)

let MOI_FN2_HASSE = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> derived_frontier m l =
         UNIONS {segment[simplex_barycentre f,simplex_barycentre tri] | f tri |
                 moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\
                 f SUBSET tri /\ ~(f = tri)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_BOUNDARY_NC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_NC_KP) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN
  MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))`;
                 `moi_fn2_ptri (m:(real^N->bool)->bool) l`] MOI_FN2_KP_SURFACE_BOUNDARY) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
  X_GEN_TAC `e:real^N->bool` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `e:real^N->bool`]
                  MOI_FN2_K_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `rho:real^N->bool` (X_CHOOSE_THEN `rho':real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`rho:real^N->bool`; `rho':real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `rho:real^N->bool`;
                   `rho':real^N->bool`] MOI_FN2_FR_EDGE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC `CARD {t | t IN moi_fn2_ptri m l /\ (e:real^N->bool) SUBSET t} = 1` THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (X_CHOOSE_THEN `tri:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(f:real^N->bool) IN barycentric_subdivision m /\ ~(f = {})`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `moi_frn_vp m l (f:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN
      SIMP_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision m) {f:real^N->bool,tri}` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FN2_CHAIN2 THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[GSYM MOI_FN2_HULL2; MOI_BAR_IN_SUBDIVISION] THEN
      EXISTS_TAC `{f:real^N->bool,tri}` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MOI_FN2_HULL2] THEN
      MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                     `{f:real^N->bool,tri}`] MOI_FRN_BARY_AFF_DIM) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN INT_ARITH_TAC;
      MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`;
                     `tri:real^N->bool`] MOI_FN2_FR_EDGE) THEN
      ASM_REWRITE_TAC[]]]);;

(* ========================================================================= *)
(* The components of the frontier of N and of N minus UNIONS l. Both         *)
(* correspond to the classes of the relation of pc_moi_fnd_rn on the         *)
(* first-derived simplices meeting UNIONS l without lying in it              *)
(* (moi_frn_vp): the class of f is the least moi_frn_rclosed set containing  *)
(* f.                                                                        *)
(* ========================================================================= *)

let moi_fn2_cls = new_definition
 `moi_fn2_cls (m:(real^N->bool)->bool) (l:(real^N->bool)->bool) (f:real^N->bool) =
    INTERS {X | moi_frn_rclosed m l X /\ f IN X}`;;

let moi_fn2_frx = new_definition
 `moi_fn2_frx (m:(real^N->bool)->bool) (X:(real^N->bool)->bool) =
    UNIONS {segment[simplex_barycentre f,simplex_barycentre tri] | f tri |
            f IN X /\ tri IN barycentric_subdivision m /\ f SUBSET tri /\ ~(f = tri)}`;;

let moi_fn2_ux = new_definition
 `moi_fn2_ux (m:(real^N->bool)->bool) (l:(real^N->bool)->bool) (X:(real^N->bool)->bool) =
    {x | x IN derived_nbhd m l DIFF UNIONS l /\ ?r. r IN X /\ x IN relative_interior r}`;;

(* Closure properties of the relation.                                       *)

let MOI_FN2_RCLOSED_ALL = prove
 (`!(m:(real^N->bool)->bool) l. moi_frn_rclosed m l {r | moi_frn_vp m l r}`,
  REWRITE_TAC[moi_frn_rclosed; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FN2_RCLOSED_COMPL = prove
 (`!(m:(real^N->bool)->bool) l X.
     moi_frn_rclosed m l X ==> moi_frn_rclosed m l ({r | moi_frn_vp m l r} DIFF X)`,
  REWRITE_TAC[moi_frn_rclosed; IN_ELIM_THM; IN_DIFF] THEN MESON_TAC[SUBSET_REFL]);;

let MOI_FN2_RCLOSED_INTER = prove
 (`!(m:(real^N->bool)->bool) l X Y.
     moi_frn_rclosed m l X /\ moi_frn_rclosed m l Y ==> moi_frn_rclosed m l (X INTER Y)`,
  REWRITE_TAC[moi_frn_rclosed; IN_INTER] THEN MESON_TAC[]);;

let MOI_FN2_CLS_BASIC = prove
 (`!(m:(real^N->bool)->bool) l f.
     moi_frn_vp m l f
     ==> moi_frn_rclosed m l (moi_fn2_cls m l f) /\ f IN moi_fn2_cls m l f /\
         (!Y. moi_frn_rclosed m l Y /\ f IN Y ==> moi_fn2_cls m l f SUBSET Y)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN REWRITE_TAC[moi_fn2_cls] THEN
  REPEAT CONJ_TAC THENL
   [GEN_REWRITE_TAC I [moi_frn_rclosed] THEN REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN
    CONJ_TAC THENL
     [X_GEN_TAC `r:real^N->bool` THEN
      DISCH_THEN(MP_TAC o SPEC `{r:real^N->bool | moi_frn_vp m l r}`) THEN
      REWRITE_TAC[MOI_FN2_RCLOSED_ALL; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`r:real^N->bool`; `r':real^N->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      X_GEN_TAC `Z:(real^N->bool)->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(r:real^N->bool) IN Z` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `moi_frn_rclosed m l (Z:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_frn_rclosed] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[];
    REWRITE_TAC[SUBSET; IN_INTERS; IN_ELIM_THM] THEN MESON_TAC[]]);;

let MOI_FN2_CLS_VP = prove
 (`!(m:(real^N->bool)->bool) l f r.
     moi_frn_vp m l f /\ r IN moi_fn2_cls m l f ==> moi_frn_vp m l r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
                MOI_FN2_CLS_BASIC) THEN
  ASM_REWRITE_TAC[moi_frn_rclosed] THEN ASM_MESON_TAC[]);;

(* Two classes are equal or disjoint; a member determines its class.         *)

let MOI_FN2_CLS_MEMBER = prove
 (`!(m:(real^N->bool)->bool) l f g.
     moi_frn_vp m l f /\ g IN moi_fn2_cls m l f ==> moi_fn2_cls m l g = moi_fn2_cls m l f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_frn_vp m l (g:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FN2_CLS_VP]; ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
                MOI_FN2_CLS_BASIC) THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->bool`]
                MOI_FN2_CLS_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RG") (CONJUNCTS_THEN2 (LABEL_TAC "GG")
    (LABEL_TAC "MG"))) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "RF") (CONJUNCTS_THEN2 (LABEL_TAC "FF")
    (LABEL_TAC "MF"))) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [USE_THEN "MG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_CASES_TAC `(f:real^N->bool) IN moi_fn2_cls m l g` THENL
   [USE_THEN "MF" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_fn2_cls m l (f:real^N->bool) SUBSET
    moi_fn2_cls m l f INTER ({r | moi_frn_vp m l r} DIFF moi_fn2_cls m l g)`
  MP_TAC THENL
   [USE_THEN "MF" MATCH_MP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FN2_RCLOSED_INTER THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FN2_RCLOSED_COMPL THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[IN_INTER; IN_DIFF; IN_ELIM_THM]];
    REWRITE_TAC[SUBSET; IN_INTER; IN_DIFF] THEN
    DISCH_THEN(MP_TAC o SPEC `g:real^N->bool`) THEN ASM_REWRITE_TAC[]]);;

let MOI_FN2_CLS_CASES = prove
 (`!(m:(real^N->bool)->bool) l f g.
     moi_frn_vp m l f /\ moi_frn_vp m l g
     ==> moi_fn2_cls m l f = moi_fn2_cls m l g \/
         moi_fn2_cls m l f INTER moi_fn2_cls m l g = {}`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `moi_fn2_cls m l (f:real^N->bool) INTER moi_fn2_cls m l g = {}` THEN
  ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `r:real^N->bool` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
  RULE_ASSUM_TAC(REWRITE_RULE[IN_INTER]) THEN
  ASM_MESON_TAC[MOI_FN2_CLS_MEMBER]);;

(* A point of a segment from the barycentre of f to that of a larger         *)
(* simplex lies in the relative interior of one of the two.                  *)

let MOI_FN2_SEG_RELINT = prove
 (`!(c:(real^N->bool)->bool) f tri x.
     moi_bar_complex c /\ f IN c /\ tri IN c /\ ~(f = {}) /\ f SUBSET tri /\
     x IN segment[simplex_barycentre f,simplex_barycentre tri]
     ==> x IN relative_interior f \/ x IN relative_interior tri`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(?n. n simplex (f:real^N->bool)) /\ (?n. n simplex (tri:real^N->bool))`
  (CONJUNCTS_THEN2 (X_CHOOSE_TAC `n1:int`) (X_CHOOSE_TAC `n2:int`)) THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `~(tri:real^N->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (f:real^N->bool) IN relative_interior f /\
                simplex_barycentre (tri:real^N->bool) IN relative_interior tri`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN segment[simplex_barycentre f,simplex_barycentre tri]` THEN
  ONCE_REWRITE_TAC[SEGMENT_SYM] THEN REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
  REWRITE_TAC[IN_UNION; IN_INSERT; NOT_IN_EMPTY] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN
  MP_TAC(ISPECL [`tri:real^N->bool`; `simplex_barycentre (tri:real^N->bool)`;
                 `simplex_barycentre (f:real^N->bool)`]
                IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      MATCH_MP_TAC(SET_RULE `!a b c:real^N->bool. x IN a /\ a SUBSET b /\ b SUBSET c
                                                 ==> x IN c`) THEN
      MAP_EVERY EXISTS_TAC [`f:real^N->bool`; `tri:real^N->bool`] THEN
      ASM_REWRITE_TAC[CLOSURE_SUBSET] THEN
      ASM_MESON_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_IN]];
    ASM SET_TAC[]]);;

(* Membership in the graph pieces.                                           *)

let MOI_FN2_IN_FRX = prove
 (`!(m:(real^N->bool)->bool) X x.
     x IN moi_fn2_frx m X <=>
     ?f tri. f IN X /\ tri IN barycentric_subdivision m /\ f SUBSET tri /\ ~(f = tri) /\
             x IN segment[simplex_barycentre f,simplex_barycentre tri]`,
  REWRITE_TAC[moi_fn2_frx; IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FN2_IN_FR = prove
 (`!(m:(real^N->bool)->bool) l x.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> (x IN derived_frontier m l <=>
          ?f tri. moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\
                  f SUBSET tri /\ ~(f = tri) /\
                  x IN segment[simplex_barycentre f,simplex_barycentre tri])`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_HASSE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FN2_VP_SUPER = prove
 (`!(m:(real^N->bool)->bool) l f tri.
     moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\ f SUBSET tri
     ==> moi_frn_vp m l tri`,
  REWRITE_TAC[moi_frn_vp] THEN SET_TAC[]);;

let MOI_FN2_FRX_SPLIT = prove
 (`!(m:(real^N->bool)->bool) l X.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ moi_frn_rclosed m l X
     ==> derived_frontier m l =
         moi_fn2_frx m X UNION moi_fn2_frx m ({r | moi_frn_vp m l r} DIFF X)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  X_GEN_TAC `x:real^N` THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
                MOI_FN2_IN_FR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[IN_UNION; MOI_FN2_IN_FRX; IN_DIFF; IN_ELIM_THM] THEN
  UNDISCH_TAC `moi_frn_rclosed m l (X:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_frn_rclosed] THEN MESON_TAC[]);;

let MOI_FN2_FRX_DISJ = prove
 (`!(m:(real^N->bool)->bool) l X.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ moi_frn_rclosed m l X
     ==> moi_fn2_frx m X INTER moi_fn2_frx m ({r | moi_frn_vp m l r} DIFF X) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; MOI_FN2_IN_FRX; IN_DIFF; IN_ELIM_THM] THEN
  X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f:real^N->bool` (X_CHOOSE_THEN `tri:real^N->bool` STRIP_ASSUME_TAC))
    (X_CHOOSE_THEN `f':real^N->bool` (X_CHOOSE_THEN `tri':real^N->bool` STRIP_ASSUME_TAC))) THEN
  UNDISCH_TAC `moi_frn_rclosed m l (X:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_frn_rclosed] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_frn_vp m l (f:real^N->bool) /\ moi_frn_vp m l (tri:real^N->bool) /\
                moi_frn_vp m l (tri':real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FN2_VP_SUPER]; ALL_TAC] THEN
  SUBGOAL_THEN `(tri:real^N->bool) IN X /\ ~((tri':real^N->bool) IN X)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(f:real^N->bool) IN barycentric_subdivision m /\ ~(f = {}) /\
                (f':real^N->bool) IN barycentric_subdivision m /\ ~(f' = {})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_frn_vp m l (f:real^N->bool)` THEN
    UNDISCH_TAC `moi_frn_vp m l (f':real^N->bool)` THEN
    REWRITE_TAC[moi_frn_vp] THEN SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `f:real^N->bool`;
                 `tri:real^N->bool`; `x:real^N`] MOI_FN2_SEG_RELINT) THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `f':real^N->bool`;
                 `tri':real^N->bool`; `x:real^N`] MOI_FN2_SEG_RELINT) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!r r':real^N->bool. r IN barycentric_subdivision m /\
                  r' IN barycentric_subdivision m /\
                  x IN relative_interior r /\ x IN relative_interior r' ==> r = r'`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_RELINT_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`barycentric_subdivision (m:(real^N->bool)->bool)`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* The vertices of a triangle of a complex are vertices of the complex.      *)

let MOI_FN2_TRI_VERTEX_IN = prove
 (`!(c:(real^N->bool)->bool) a b d.
     moi_bar_complex c /\ convex hull {a,b,d} IN c /\ ~affine_dependent {a,b,d}
     ==> {a} IN c /\ {b} IN c /\ {d} IN c`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `moi_bar_complex (c:(real^N->bool)->bool)` THEN
  REWRITE_TAC[moi_bar_complex] THEN
  DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
  EXISTS_TAC `convex hull {a:real^N,b,d}` THEN ASM_REWRITE_TAC[FACE_OF_SING] THEN
  ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; IN_INSERT]);;

(* Every first-derived simplex meeting the polygon without lying in it is an *)
(* end of an edge of the frontier graph.                                     *)

let MOI_FN2_VP_HASSE_END = prove
 (`!(m:(real^N->bool)->bool) l r.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ moi_frn_vp m l r
     ==> ?f tri. moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\
                 f SUBSET tri /\ ~(f = tri) /\ (r = f \/ r = tri)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision m /\ ~(r = {}) /\
                ~(r INTER UNIONS l = {}) /\ ~(r SUBSET UNIONS l)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_frn_vp m l (r:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN
    SIMP_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim (r:real^N->bool) = &1 \/ aff_dim r = &2` MP_TAC THENL
   [MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
                  MOI_FN2_VP_NOT_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `r:real^N->bool` AFF_DIM_GE) THEN
    MP_TAC(ISPEC `r:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
    REWRITE_TAC[ASSUME `~(r:real^N->bool = {})`] THEN
    SUBGOAL_THEN `aff_dim (r:real^N->bool) <= &2` MP_TAC THENL
     [UNDISCH_TAC `!r:real^N->bool. r IN barycentric_subdivision m ==> aff_dim r <= &2` THEN
      DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `r:real^N->bool`]
                  MOI_FRN_CM_PURE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `tri:real^N->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`r:real^N->bool`; `tri:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `aff_dim (tri:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
                MOI_FRN_FULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (l:(real^N->bool)->bool)`;
                 `r INTER UNIONS l:real^N->bool`] MOI_FN2_SIMPLEX_HAS_VERTEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `simplicial_complex (barycentric_subdivision (l:(real^N->bool)->bool))` THEN
    SIMP_TAC[MOI_BAR_SIMPLICIAL_COMPLEX];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{w:real^N} IN barycentric_subdivision m` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                   (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `r:real^N->bool`;
                 `w:real^N`] MOI_FRN_TRI_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `{x:real^N} IN barycentric_subdivision m /\ {y:real^N} IN barycentric_subdivision m`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `w:real^N`;
                   `x:real^N`; `y:real^N`] MOI_FN2_TRI_VERTEX_IN) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; SIMP_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((x:real^N) IN UNIONS l /\ y IN UNIONS l)` ASSUME_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`;
                   `w:real^N`; `x:real^N`; `y:real^N`] MOI_FN2_FULL_TRIPLE) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{x:real^N} IN barycentric_subdivision l /\
                  {y:real^N} IN barycentric_subdivision l` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FN2_VERT_L]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
    TRY(UNDISCH_TAC `r = convex hull {w:real^N,x,y}` THEN DISCH_THEN SUBST1_TAC THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT] THEN NO_TAC) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?z:real^N. ~(z = w) /\ ~(z IN UNIONS l) /\ {z} IN barycentric_subdivision m /\
                           convex hull {w,z} IN barycentric_subdivision m /\
                           aff_dim (convex hull {w,z}) = &1 /\
                           convex hull {w,z} SUBSET r`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `(x:real^N) IN UNIONS l` THENL
     [EXISTS_TAC `y:real^N` THEN
      SUBGOAL_THEN `~((y:real^N) IN UNIONS l)` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `w:real^N`;
                     `y:real^N`; `x:real^N`] MOI_FRN_TRI_EDGE_IN) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `{w:real^N,y,x} = {w,x,y}` SUBST1_TAC THENL
         [REWRITE_TAC[INSERT_AC]; ALL_TAC] THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `{w:real^N,y,x} = {w,x,y}` SUBST1_TAC THENL
       [REWRITE_TAC[INSERT_AC]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `w:real^N`;
                     `x:real^N`; `y:real^N`] MOI_FRN_TRI_EDGE_IN) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`convex hull {w:real^N,z}`; `r:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_frn_vp] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN EXISTS_TAC `w:real^N` THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
        UNDISCH_TAC `(w:real^N) IN r INTER UNIONS l` THEN SET_TAC[]];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `z:real^N`) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
    DISCH_TAC THEN UNDISCH_TAC `aff_dim (convex hull {w:real^N,z}) = &1` THEN
    UNDISCH_TAC `aff_dim (r:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC]);;

(* A connected subset of s meeting a component of s lies in it.               *)

let MOI_FN2_CC_ABSORB = prove
 (`!(s:real^N->bool) a x t.
     x IN connected_component s a /\ x IN t /\ t SUBSET s /\ connected t
     ==> t SUBSET connected_component s a`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CONNECTED_COMPONENT_EQ) THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]);;

(* The graph pieces are closed.                                              *)

let MOI_FN2_FRX_CLOSED = prove
 (`!(m:(real^N->bool)->bool) X.
     FINITE (barycentric_subdivision m) /\ X SUBSET barycentric_subdivision m
     ==> closed (moi_fn2_frx m X)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fn2_frx] THEN MATCH_MP_TAC CLOSED_UNIONS THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{segment[simplex_barycentre f,simplex_barycentre tri] |
                 f IN barycentric_subdivision (m:(real^N->bool)->bool) /\
                 tri IN barycentric_subdivision m}` THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`\(f:real^N->bool) (tri:real^N->bool).
                       segment[simplex_barycentre f,simplex_barycentre tri]`;
                     `barycentric_subdivision (m:(real^N->bool)->bool)`;
                     `\(f:real^N->bool). barycentric_subdivision (m:(real^N->bool)->bool)`]
                    FINITE_PRODUCT_DEPENDENT) THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[SUBSET]];
    REWRITE_TAC[FORALL_IN_GSPEC; CLOSED_SEGMENT]]);;

(* The piece of a class is the component of the frontier through the         *)
(* barycentre of any member.                                                 *)

let MOI_FN2_FRX_COMPONENT = prove
 (`!(m:(real^N->bool)->bool) l f0.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ moi_frn_vp m l f0
     ==> moi_fn2_frx m (moi_fn2_cls m l f0) =
         connected_component (derived_frontier m l) (simplex_barycentre f0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f0:real^N->bool`]
                MOI_FN2_CLS_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MIN"))) THEN
  ABBREV_TAC `X = moi_fn2_cls m l (f0:real^N->bool)` THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN X ==> moi_frn_vp m l r` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_frn_rclosed m l (X:(real^N->bool)->bool)` THEN
    SIMP_TAC[moi_frn_rclosed];
    ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN derived_frontier m l <=>
                  ?f tri. moi_frn_vp m l f /\ tri IN barycentric_subdivision m /\
                          f SUBSET tri /\ ~(f = tri) /\
                          x IN segment[simplex_barycentre f,simplex_barycentre tri]`
  (LABEL_TAC "FR") THENL
   [GEN_TAC THEN MATCH_MP_TAC MOI_FN2_IN_FR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_fn2_frx m (X:(real^N->bool)->bool) SUBSET derived_frontier m l`
  ASSUME_TAC THENL
   [GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[MOI_FN2_IN_FRX] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (X_CHOOSE_THEN `tri:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    USE_THEN "FR" (fun th -> REWRITE_TAC[th]) THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->bool`; `tri:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `!r:real^N->bool. r IN X ==> moi_frn_vp m l r` THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (f0:real^N->bool) IN moi_fn2_frx m X` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f0:real^N->bool`]
                  MOI_FN2_VP_HASSE_END) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (X_CHOOSE_THEN `tri:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    REWRITE_TAC[MOI_FN2_IN_FRX] THEN
    MAP_EVERY EXISTS_TAC [`f:real^N->bool`; `tri:real^N->bool`] THEN ASM_REWRITE_TAC[] THENL
     [UNDISCH_TAC `(f0:real^N->bool) = f` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
      UNDISCH_TAC `(f0:real^N->bool) = tri` THEN DISCH_THEN(SUBST_ALL_TAC o SYM) THEN
      REWRITE_TAC[ENDS_IN_SEGMENT] THEN
      UNDISCH_TAC `moi_frn_rclosed m l (X:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_frn_rclosed] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      EXISTS_TAC `f0:real^N->bool` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (f0:real^N->bool) IN derived_frontier m l` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ABBREV_TAC `Y = {r:real^N->bool | moi_frn_vp m l r /\
                     simplex_barycentre r IN
                     connected_component (derived_frontier m l) (simplex_barycentre f0)}` THEN
    SUBGOAL_THEN `!r r':real^N->bool.
                    moi_frn_vp m l r /\ moi_frn_vp m l r' /\ r SUBSET r' /\ ~(r = r')
                    ==> segment[simplex_barycentre r,simplex_barycentre r'] SUBSET
                        derived_frontier m l`
    (LABEL_TAC "SEG") THENL
     [REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN
      DISCH_TAC THEN USE_THEN "FR" (fun th -> REWRITE_TAC[th]) THEN
      MAP_EVERY EXISTS_TAC [`r:real^N->bool`; `r':real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_frn_vp m l (r':real^N->bool)` THEN SIMP_TAC[moi_frn_vp];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_frn_rclosed m l (Y:(real^N->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "Y" THEN REWRITE_TAC[moi_frn_rclosed; IN_ELIM_THM] THEN
      SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`r:real^N->bool`; `r':real^N->bool`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
       [ASM_CASES_TAC `r:real^N->bool = r'` THENL
         [UNDISCH_TAC `simplex_barycentre (r:real^N->bool) IN
                       connected_component (derived_frontier m l) (simplex_barycentre f0)` THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`derived_frontier m (l:(real^N->bool)->bool)`;
                       `simplex_barycentre (f0:real^N->bool)`;
                       `simplex_barycentre (r:real^N->bool)`;
                       `segment[simplex_barycentre r:real^N,simplex_barycentre r']`]
                      MOI_FN2_CC_ABSORB) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[ENDS_IN_SEGMENT; CONNECTED_SEGMENT] THEN
          USE_THEN "SEG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
          REWRITE_TAC[ENDS_IN_SEGMENT]];
        ASM_CASES_TAC `r:real^N->bool = r'` THENL
         [UNDISCH_TAC `simplex_barycentre (r:real^N->bool) IN
                       connected_component (derived_frontier m l) (simplex_barycentre f0)` THEN
          ASM_REWRITE_TAC[];
          ALL_TAC] THEN
        MP_TAC(ISPECL [`derived_frontier m (l:(real^N->bool)->bool)`;
                       `simplex_barycentre (f0:real^N->bool)`;
                       `simplex_barycentre (r:real^N->bool)`;
                       `segment[simplex_barycentre r':real^N,simplex_barycentre r]`]
                      MOI_FN2_CC_ABSORB) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[ENDS_IN_SEGMENT; CONNECTED_SEGMENT] THEN
          USE_THEN "SEG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
          REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
          REWRITE_TAC[ENDS_IN_SEGMENT]]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(X:(real^N->bool)->bool) SUBSET Y` ASSUME_TAC THENL
     [USE_THEN "MIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Y" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC I [IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    GEN_REWRITE_TAC I [SUBSET] THEN REWRITE_TAC[MOI_FN2_IN_FRX] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (X_CHOOSE_THEN `tri:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(f:real^N->bool) IN Y` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "Y" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`derived_frontier m (l:(real^N->bool)->bool)`;
                   `simplex_barycentre (f0:real^N->bool)`;
                   `simplex_barycentre (f:real^N->bool)`;
                   `segment[simplex_barycentre f:real^N,simplex_barycentre tri]`]
                  MOI_FN2_CC_ABSORB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[ENDS_IN_SEGMENT; CONNECTED_SEGMENT] THEN
      USE_THEN "SEG" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FN2_VP_SUPER THEN EXISTS_TAC `f:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN
    EXISTS_TAC `derived_frontier m (l:(real^N->bool)->bool)` THEN
    REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT; CONNECTED_COMPONENT_SUBSET] THEN
    SUBGOAL_THEN `(X:(real^N->bool)->bool) SUBSET barycentric_subdivision m /\
                  {r:real^N->bool | moi_frn_vp m l r} DIFF X SUBSET
                  barycentric_subdivision m` STRIP_ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN
      ASM_MESON_TAC[moi_frn_vp];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[MOI_FN2_FRX_CLOSED];
      MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `X:(real^N->bool)->bool`] MOI_FN2_FRX_SPLIT) THEN
      MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `X:(real^N->bool)->bool`] MOI_FN2_FRX_DISJ) THEN
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN DISCH_TAC THEN
      SUBGOAL_THEN `moi_fn2_frx m (X:(real^N->bool)->bool) =
                    derived_frontier m l DIFF
                    moi_fn2_frx m ({r | moi_frn_vp m l r} DIFF X)`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC OPEN_IN_DIFF_CLOSED THEN ASM_SIMP_TAC[MOI_FN2_FRX_CLOSED];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `simplex_barycentre (f0:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC I [IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM_REWRITE_TAC[]]]);;

(* Barycentres of such simplices lie on the frontier.                        *)

let MOI_FN2_BARY_IN_FR = prove
 (`!(m:(real^N->bool)->bool) l f.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ moi_frn_vp m l f
     ==> simplex_barycentre f IN derived_frontier m l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
                MOI_FN2_VP_HASSE_END) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:real^N->bool` (X_CHOOSE_THEN `tri:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[MOI_FN2_IN_FR] THEN
  MAP_EVERY EXISTS_TAC [`g:real^N->bool`; `tri:real^N->bool`] THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT]);;

(* The components of the frontier are the pieces of the classes.              *)

let MOI_FN2_COMPONENTS_FR = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> components (derived_frontier m l) =
         {moi_fn2_frx m (moi_fn2_cls m l f) | f | moi_frn_vp m l f}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_COMPONENTS; IN_ELIM_THM] THEN X_GEN_TAC `c:real^N->bool` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    UNDISCH_TAC `(x:real^N) IN derived_frontier m l` THEN
    ASM_SIMP_TAC[MOI_FN2_IN_FR] THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (X_CHOOSE_THEN `tri:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `f:real^N->bool` THEN ASM_SIMP_TAC[MOI_FN2_FRX_COMPONENT] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN
    MP_TAC(ISPECL [`derived_frontier m (l:(real^N->bool)->bool)`;
                   `simplex_barycentre (f:real^N->bool)`;
                   `simplex_barycentre (f:real^N->bool)`;
                   `segment[simplex_barycentre f:real^N,simplex_barycentre tri]`]
                  MOI_FN2_CC_ABSORB) THEN
    ANTS_TAC THENL
     [REWRITE_TAC[ENDS_IN_SEGMENT; CONNECTED_SEGMENT] THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC I [IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
        MATCH_MP_TAC MOI_FN2_BARY_IN_FR THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
        ASM_SIMP_TAC[MOI_FN2_IN_FR] THEN
        MAP_EVERY EXISTS_TAC [`f:real^N->bool`; `tri:real^N->bool`] THEN
        ASM_REWRITE_TAC[]];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `simplex_barycentre (f:real^N->bool)` THEN
    ASM_SIMP_TAC[MOI_FN2_FRX_COMPONENT; MOI_FN2_BARY_IN_FR]]);;

(* The open pieces of N minus the polygon: complementary classes split it.   *)

let MOI_FN2_UX_SPLIT = prove
 (`!(m:(real^N->bool)->bool) l X.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ moi_frn_rclosed m l X
     ==> moi_fn2_ux m l X UNION moi_fn2_ux m l ({r | moi_frn_vp m l r} DIFF X) =
         derived_nbhd m l DIFF UNIONS l /\
         moi_fn2_ux m l X INTER moi_fn2_ux m l ({r | moi_frn_vp m l r} DIFF X) = {}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    REWRITE_TAC[IN_UNION; moi_fn2_ux; IN_ELIM_THM; IN_DIFF] THEN
    EQ_TAC THENL [MESON_TAC[]; ALL_TAC] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
                  MOI_FRN_COVER) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(r:real^N->bool) IN X` THENL
     [DISJ1_TAC THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[EXTENSION; IN_INTER; moi_fn2_ux; IN_ELIM_THM; IN_DIFF; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r':real^N->bool` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(r:real^N->bool) = r'` (fun th -> ASM_MESON_TAC[th]) THEN
    MATCH_MP_TAC MOI_FRN_RELINT_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`barycentric_subdivision (m:(real^N->bool)->bool)`; `x:real^N`] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_frn_rclosed m l (X:(real^N->bool)->bool)` THEN
    UNDISCH_TAC `moi_frn_vp m l (r':real^N->bool)` THEN
    REWRITE_TAC[moi_frn_rclosed; moi_frn_vp] THEN ASM_MESON_TAC[]]);;

(* The open piece of a class is the component of N minus the polygon        *)
(* through the barycentre of any member.                                     *)

let MOI_FN2_UX_COMPONENT = prove
 (`!(m:(real^N->bool)->bool) l f0.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ moi_frn_vp m l f0
     ==> moi_fn2_ux m l (moi_fn2_cls m l f0) =
         connected_component (derived_nbhd m l DIFF UNIONS l) (simplex_barycentre f0)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f0:real^N->bool`]
                MOI_FN2_CLS_BASIC) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "MIN"))) THEN
  ABBREV_TAC `X = moi_fn2_cls m l (f0:real^N->bool)` THEN
  ABBREV_TAC `S = derived_nbhd m l DIFF UNIONS (l:(real^N->bool)->bool)` THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f0:real^N->bool`]
                MOI_FRN_VP_BARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplex_barycentre (f0:real^N->bool) IN S` ASSUME_TAC THENL
   [EXPAND_TAC "S" THEN ASM_REWRITE_TAC[IN_DIFF]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [ABBREV_TAC `Y = {r:real^N->bool | moi_frn_vp m l r /\
                     simplex_barycentre r IN connected_component S (simplex_barycentre f0)}` THEN
    SUBGOAL_THEN `moi_frn_rclosed m l (Y:(real^N->bool)->bool)` ASSUME_TAC THENL
     [EXPAND_TAC "Y" THEN REWRITE_TAC[moi_frn_rclosed; IN_ELIM_THM] THEN
      SIMP_TAC[] THEN MAP_EVERY X_GEN_TAC [`r:real^N->bool`; `r':real^N->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CONNECTED_COMPONENT_EQ o check (fun th ->
        can (term_match [] `simplex_barycentre (r:real^N->bool) IN
                            connected_component S (simplex_barycentre f0)`) (concl th))) THEN
      GEN_REWRITE_TAC I [IN] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (is_disj o concl)) THENL
       [EXPAND_TAC "S" THEN MATCH_MP_TAC MOI_FRN_ADJ_CC THEN ASM_REWRITE_TAC[];
        ONCE_REWRITE_TAC[CONNECTED_COMPONENT_SYM_EQ] THEN
        EXPAND_TAC "S" THEN MATCH_MP_TAC MOI_FRN_ADJ_CC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(X:(real^N->bool)->bool) SUBSET Y` ASSUME_TAC THENL
     [USE_THEN "MIN" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN EXPAND_TAC "Y" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      GEN_REWRITE_TAC I [IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; moi_fn2_ux; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(r:real^N->bool) IN Y` MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "Y" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o MATCH_MP CONNECTED_COMPONENT_EQ o check (fun th ->
      can (term_match [] `simplex_barycentre (r:real^N->bool) IN
                          connected_component S (simplex_barycentre f0)`) (concl th))) THEN
    GEN_REWRITE_TAC I [IN] THEN ONCE_REWRITE_TAC[CONNECTED_COMPONENT_SYM_EQ] THEN
    EXPAND_TAC "S" THEN MATCH_MP_TAC MOI_FRN_PIECE_CC THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(x:real^N) IN derived_nbhd m l DIFF UNIONS l` THEN SIMP_TAC[IN_DIFF];
    MATCH_MP_TAC CONNECTED_SUBSET_CLOPEN THEN EXISTS_TAC `S:real^N->bool` THEN
    REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT; CONNECTED_COMPONENT_SUBSET] THEN
    SUBGOAL_THEN `open_in (subtopology euclidean S) (moi_fn2_ux m l X) /\
                  open_in (subtopology euclidean S)
                    (moi_fn2_ux m l ({r:real^N->bool | moi_frn_vp m l r} DIFF X))`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[moi_fn2_ux] THEN CONJ_TAC THEN
      MATCH_MP_TAC MOI_FRN_UX_OPEN THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FN2_RCLOSED_COMPL THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `X:(real^N->bool)->bool`] MOI_FN2_UX_SPLIT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(STRIP_ASSUME_TAC o REWRITE_RULE
        [ASSUME `derived_nbhd m l DIFF UNIONS (l:(real^N->bool)->bool) = S`])] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `moi_fn2_ux m l X =
                    S DIFF moi_fn2_ux m l ({r:real^N->bool | moi_frn_vp m l r} DIFF X)`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC CLOSED_IN_DIFF THEN ASM_REWRITE_TAC[CLOSED_IN_REFL];
      ASM_REWRITE_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `simplex_barycentre (f0:real^N->bool)` THEN CONJ_TAC THENL
       [GEN_REWRITE_TAC I [IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[moi_fn2_ux; IN_ELIM_THM] THEN CONJ_TAC THENL
         [ASM_REWRITE_TAC[IN_DIFF];
          EXISTS_TAC `f0:real^N->bool` THEN ASM_REWRITE_TAC[]]]]]);;

(* The components of N minus the polygon are the open pieces of the classes. *)

let MOI_FN2_COMPONENTS_NL = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> components (derived_nbhd m l DIFF UNIONS l) =
         {moi_fn2_ux m l (moi_fn2_cls m l f) | f | moi_frn_vp m l f}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN
  REWRITE_TAC[IN_COMPONENTS; IN_ELIM_THM] THEN X_GEN_TAC `c:real^N->bool` THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `x:real^N` (CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC)) THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
                  MOI_FRN_COVER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_SIMP_TAC[MOI_FN2_UX_COMPONENT] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_EQ THEN GEN_REWRITE_TAC I [IN] THEN
    ONCE_REWRITE_TAC[CONNECTED_COMPONENT_SYM_EQ] THEN
    MATCH_MP_TAC MOI_FRN_PIECE_CC THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `simplex_barycentre (f:real^N->bool)` THEN
    ASM_SIMP_TAC[MOI_FN2_UX_COMPONENT] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
                  MOI_FRN_VP_BARY) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[IN_DIFF]]);;

(* Distinct classes have distinct pieces.                                    *)

let MOI_FN2_PIECES_INJ = prove
 (`!(m:(real^N->bool)->bool) l f g.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ moi_frn_vp m l f /\ moi_frn_vp m l g
     ==> (moi_fn2_frx m (moi_fn2_cls m l f) = moi_fn2_frx m (moi_fn2_cls m l g)
          ==> moi_fn2_cls m l f = moi_fn2_cls m l g) /\
         (moi_fn2_ux m l (moi_fn2_cls m l f) = moi_fn2_ux m l (moi_fn2_cls m l g)
          ==> moi_fn2_cls m l f = moi_fn2_cls m l g)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->bool`]
                MOI_FRN_VP_BARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
                MOI_FN2_CLS_BASIC) THEN
  ASM_REWRITE_TAC[moi_frn_rclosed] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(g:real^N->bool) IN moi_fn2_cls m l f ==>
                moi_fn2_cls m l f = moi_fn2_cls m l g`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FN2_CLS_MEMBER]; ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN barycentric_subdivision m /\
                   simplex_barycentre g IN relative_interior r ==> r = g`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_RELINT_UNIQUE THEN
    MAP_EVERY EXISTS_TAC [`barycentric_subdivision (m:(real^N->bool)->bool)`;
                          `simplex_barycentre (g:real^N->bool)`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_frn_vp];
    ALL_TAC] THEN
  CONJ_TAC THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THENL
   [SUBGOAL_THEN `simplex_barycentre (g:real^N->bool) IN
                  moi_fn2_frx m (moi_fn2_cls m l f)` MP_TAC THENL
     [ASM_SIMP_TAC[MOI_FN2_FRX_COMPONENT] THEN
      GEN_REWRITE_TAC I [IN] THEN MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN
      MATCH_MP_TAC MOI_FN2_BARY_IN_FR THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MOI_FN2_IN_FRX] THEN
    DISCH_THEN(X_CHOOSE_THEN `f':real^N->bool` (X_CHOOSE_THEN `tri':real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `f':real^N->bool`;
                   `tri':real^N->bool`; `simplex_barycentre (g:real^N->bool)`]
                  MOI_FN2_SEG_RELINT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `moi_frn_vp m l (f':real^N->bool)` MP_TAC THENL
       [ASM_MESON_TAC[]; SIMP_TAC[moi_frn_vp] THEN SET_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `(f':real^N->bool) = g` (fun th -> ASM_MESON_TAC[th]) THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_frn_vp];
      SUBGOAL_THEN `(tri':real^N->bool) = g` SUBST_ALL_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[]];
    SUBGOAL_THEN `simplex_barycentre (g:real^N->bool) IN
                  moi_fn2_ux m l (moi_fn2_cls m l f)` MP_TAC THENL
     [ASM_REWRITE_TAC[] THEN REWRITE_TAC[moi_fn2_ux; IN_ELIM_THM; IN_DIFF] THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `g:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `g:real^N->bool`]
                    MOI_FN2_CLS_BASIC) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[moi_fn2_ux; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(r:real^N->bool) = g` (fun th -> ASM_MESON_TAC[th]) THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[moi_frn_vp]]);;

(* Some first-derived simplex meets the polygon without lying in it.         *)

let MOI_FN2_VP_EXISTS = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> ?f. moi_frn_vp m l f`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `~(UNIONS l:real^N->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
  SUBGOAL_THEN `?q:real^N->bool. q IN barycentric_subdivision m /\ x IN q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN UNIONS l` THEN
    UNDISCH_TAC `UNIONS (barycentric_subdivision l) = UNIONS (l:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                   (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision (m:(real^N->bool)->bool)`; `q:real^N->bool`]
                MOI_FRN_CM_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tri:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `tri:real^N->bool` THEN REWRITE_TAC[moi_frn_vp] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN DISCH_TAC THEN
  SUBGOAL_THEN `(tri:real^N->bool) IN barycentric_subdivision l` MP_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th ->
      can (term_match [] `!r:real^N->bool. r IN barycentric_subdivision m /\
                                           r SUBSET UNIONS l
                                           ==> r IN barycentric_subdivision l`) (concl th))) THEN
    ASM_REWRITE_TAC[];
    DISCH_TAC THEN
    UNDISCH_TAC `!s:real^N->bool. s IN barycentric_subdivision l ==> aff_dim s <= &1` THEN
    DISCH_THEN(MP_TAC o SPEC `tri:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC]);;

(* Conclusion (9) and the finiteness and nonemptiness of the components of   *)
(* the frontier.                                                             *)

let MOI_FN2_COMPONENT_COUNT = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> FINITE (components (derived_frontier m l)) /\
         ~(components (derived_frontier m l) = {}) /\
         CARD (components (derived_nbhd m l DIFF UNIONS l)) =
         CARD (components (derived_frontier m l))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {f:real^N->bool | moi_frn_vp m l f}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `barycentric_subdivision (m:(real^N->bool)->bool)` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN SIMP_TAC[moi_frn_vp];
    ALL_TAC] THEN
  ABBREV_TAC `R = IMAGE (moi_fn2_cls m l) {f:real^N->bool | moi_frn_vp m l f}` THEN
  SUBGOAL_THEN `FINITE (R:((real^N->bool)->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "R" THEN MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `components (derived_frontier m l) = IMAGE (moi_fn2_frx m) R /\
                components (derived_nbhd m l DIFF UNIONS l) =
                IMAGE (moi_fn2_ux m (l:(real^N->bool)->bool)) R`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FN2_COMPONENTS_FR; MOI_FN2_COMPONENTS_NL] THEN
    EXPAND_TAC "R" THEN REWRITE_TAC[GSYM IMAGE_o] THEN
    CONJ_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN
    REWRITE_TAC[IN_IMAGE; IN_ELIM_THM; o_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN EXPAND_TAC "R" THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MATCH_MP_TAC MOI_FN2_VP_EXISTS THEN ASM_REWRITE_TAC[];
    SUBGOAL_THEN `CARD (IMAGE (moi_fn2_ux m (l:(real^N->bool)->bool)) R) = CARD R /\
                  CARD (IMAGE (moi_fn2_frx m) R) = CARD R`
    (fun th -> REWRITE_TAC[th]) THEN
    CONJ_TAC THEN MATCH_MP_TAC CARD_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN
    MAP_EVERY X_GEN_TAC [`X1:(real^N->bool)->bool`; `X2:(real^N->bool)->bool`] THEN
    EXPAND_TAC "R" THEN REWRITE_TAC[IN_IMAGE; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `x:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `y:real^N->bool` STRIP_ASSUME_TAC) MP_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N->bool`;
                   `y:real^N->bool`] MOI_FN2_PIECES_INJ) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[]]);;

(* ========================================================================= *)
(* The annulus case. pc_moi_fnd_surfb proves the statement term              *)
(* MOI_FND_SURFACE_PLANAR; with two boundary circles and chi = 0 it          *)
(* gives a PL homeomorphism from holed_disk_model 1 onto N carrying the     *)
(* model frontier onto the frontier of N, and pc_moi_fnd_euler's map        *)
(* moi_feu_hd1_map moves the model to the square annulus with its two ends. *)
(* ========================================================================= *)

(* The frontier of the disk with one hole and its image in the annulus model. *)

let MOI_FN2_HD1_FRONTIER_EQ = prove
 (`frontier (holed_disk_model 1) =
   (interval[vec 0:real^2,vector[&8; &4]] DIFF interval[vector[&2; &1],vector[&4; &3]])
   DIFF (interval(vec 0:real^2,vector[&8; &4]) DIFF interval[vector[&2; &1],vector[&4; &3]])
   UNION
   (interval[vec 0:real^2,vector[&8; &4]] DIFF interval(vector[&2; &1],vector[&4; &3]))
   INTER interval[vector[&2; &1],vector[&4; &3]]`,
  REWRITE_TAC[MOI_FEU_HOLED_DISK_MODEL_1; frontier] THEN
  SIMP_TAC[CLOSURE_CLOSED; CLOSED_DIFF; CLOSED_INTERVAL; OPEN_INTERVAL] THEN
  REWRITE_TAC[INTERIOR_DIFF; INTERIOR_CLOSED_INTERVAL] THEN
  SUBGOAL_THEN `closure (interval(vector[&2; &1]:real^2,vector[&4; &3])) =
                interval[vector[&2; &1],vector[&4; &3]]` SUBST1_TAC THENL
   [MATCH_MP_TAC CLOSURE_OPEN_INTERVAL THEN
    REWRITE_TAC[INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2; VECTOR_2] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `z:real^2` THEN
  REWRITE_TAC[IN_DIFF; IN_UNION; IN_INTER; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
              VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_FN2_RF_SQUARE = prove
 (`!r. &0 < r
       ==> relative_frontier (interval[--vector[r;r]:real^2,vector[r;r]]) =
           interval[--vector[r;r]:real^2,vector[r;r]] DIFF
           interval(--vector[r;r]:real^2,vector[r;r])`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `~(interior (interval[--vector[r;r]:real^2,vector[r;r]]) = {})`
  ASSUME_TAC THENL
   [REWRITE_TAC[INTERIOR_CLOSED_INTERVAL; INTERVAL_NE_EMPTY; DIMINDEX_2; FORALL_2;
                VECTOR_2; VECTOR_NEG_COMPONENT] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_NONEMPTY_INTERIOR; FRONTIER_CLOSED_INTERVAL]);;

let MOI_FN2_HD1_FRONTIER = prove
 (`IMAGE moi_feu_hd1_map (frontier (holed_disk_model 1)) =
   relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]) UNION
   relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]])`,
  SIMP_TAC[MOI_FN2_RF_SQUARE; REAL_ARITH `&0 < &1 /\ &0 < &2`] THEN
  REWRITE_TAC[MOI_FN2_HD1_FRONTIER_EQ] THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN X_GEN_TAC `z:real^2` THEN
    REWRITE_TAC[IN_DIFF; IN_UNION; IN_INTER; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
                VEC_COMPONENT; VECTOR_NEG_COMPONENT; MOI_FEU_HD1_MAP_COMPONENTS] THEN
    REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
    REWRITE_TAC[SUBSET; IN_IMAGE] THEN X_GEN_TAC `w:real^2` THEN DISCH_TAC THEN
    EXISTS_TAC `moi_feu_hd1_inv w` THEN CONJ_TAC THENL
     [REWRITE_TAC[CART_EQ; DIMINDEX_2; FORALL_2;
                  MOI_FEU_HD1_MAP_COMPONENTS; MOI_FEU_HD1_INV_COMPONENTS] THEN
      UNDISCH_TAC `(w:real^2) IN
        interval[--vector[&1;&1],vector[&1;&1]] DIFF interval(--vector[&1;&1],vector[&1;&1])
        UNION
        interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&2;&2],vector[&2;&2])` THEN
      REWRITE_TAC[IN_DIFF; IN_UNION; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
                  VECTOR_NEG_COMPONENT] THEN
      REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC;
      UNDISCH_TAC `(w:real^2) IN
        interval[--vector[&1;&1],vector[&1;&1]] DIFF interval(--vector[&1;&1],vector[&1;&1])
        UNION
        interval[--vector[&2;&2],vector[&2;&2]] DIFF interval(--vector[&2;&2],vector[&2;&2])` THEN
      REWRITE_TAC[IN_DIFF; IN_UNION; IN_INTER; IN_INTERVAL; DIMINDEX_2; FORALL_2; VECTOR_2;
                  VEC_COMPONENT; VECTOR_NEG_COMPONENT; MOI_FEU_HD1_INV_COMPONENTS] THEN
      REPEAT COND_CASES_TAC THEN ASM_REAL_ARITH_TAC]]);;

(* Conclusions (1)-(5) together, with the polyhedron of N's complex.          *)

let MOI_FN2_NC_FACTS = prove
 (`!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l)
     ==> FINITE (derived_nbhd_complex m l) /\
         combinatorial_manifold_with_boundary 2 (derived_nbhd_complex m l) /\
         surface_boundary (derived_nbhd_complex m l) = derived_frontier m l /\
         connected (derived_nbhd m l) /\
         complex_euler (derived_nbhd_complex m l) = &0 /\
         UNIONS (derived_nbhd_complex m l) = derived_nbhd m l /\
         ~(derived_nbhd m l = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_F7_CONTEXT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_NC_KP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FN2_BOUNDARY_NC; MOI_FN2_NBHD_CONNECTED; MOI_FN2_NBHD_EULER] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (m:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `s:real^N->bool` THEN
    DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
    UNDISCH_TAC `moi_bar_complex (barycentric_subdivision (barycentric_subdivision
                   (m:(real^N->bool)->bool)))` THEN
    REWRITE_TAC[moi_bar_complex] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    EXISTS_TAC `tr:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC MOI_FN2_NC_CMWB THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FN2_UNIONS_FACES THEN X_GEN_TAC `tr:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?n. n simplex (tr:real^N->bool)` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `moi_bar_complex (barycentric_subdivision (barycentric_subdivision
                     (m:(real^N->bool)->bool)))` THEN
      REWRITE_TAC[moi_bar_complex] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN
      ASM SET_TAC[];
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]];
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CONTEXT) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_N_FACTS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN
    UNDISCH_TAC `~(UNIONS l:real^N->bool = {})` THEN SET_TAC[]]);;

(* The statement of MOI_FSB_BD_CIRCLES (pc_moi_fnd_surfb0), used here as an  *)
(* explicit hypothesis; pc_moi_fnd_nb2f discharges it.                       *)

let moi_fn2_bdc_body =
 `!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold_with_boundary 2 c
     ==> FINITE (components (surface_boundary c)) /\
         (!j. j IN components (surface_boundary c) ==> pl_sphere 1 j)`;;

(* Conclusion (10) from the planar-surface theorem.                          *)

let MOI_FN2_ANNULUS = prove
 (mk_imp(MOI_FND_SURFACE_PLANAR,
  `!(m:(real^N->bool)->bool) l.
     FINITE m /\ combinatorial_manifold 2 m /\ simplicial_subcomplex l m /\
     pl_sphere 1 (UNIONS l) /\ CARD (components (derived_frontier m l)) = 2
     ==> ?j1 j2. pl_annulus_with_ends (derived_nbhd m l) j1 j2 /\
                 derived_frontier m l = j1 UNION j2`),
  DISCH_THEN(LABEL_TAC "PLANAR") THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_NC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  USE_THEN "PLANAR" (MP_TAC o SPEC `derived_nbhd_complex (m:(real^N->bool)->bool) l`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `1` o CONJUNCT2 o CONJUNCT2) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `g:real^N->real^2`
    STRIP_ASSUME_TAC)) THEN
  X_CHOOSE_TAC `h:real^2->real^2` MOI_FEU_HD1_PL_HOMEOMORPHISM THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE ((f:real^2->real^N) o (h:real^2->real^2))
           (relative_frontier (interval[--vector[&1;&1]:real^2,vector[&1;&1]]))`;
    `IMAGE ((f:real^2->real^N) o (h:real^2->real^2))
           (relative_frontier (interval[--vector[&2;&2]:real^2,vector[&2;&2]]))`] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[pl_annulus_with_ends] THEN
    MAP_EVERY EXISTS_TAC [`(f:real^2->real^N) o (h:real^2->real^2)`;
                          `moi_feu_hd1_map o (g:real^N->real^2)`] THEN
    REWRITE_TAC[] THEN MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `holed_disk_model 1` THEN ASM_REWRITE_TAC[] THEN
    ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM IMAGE_UNION; GSYM MOI_FN2_HD1_FRONTIER; IMAGE_o] THEN
  SUBGOAL_THEN `IMAGE (h:real^2->real^2) (IMAGE moi_feu_hd1_map
                  (frontier (holed_disk_model 1))) = frontier (holed_disk_model 1)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o] THEN
    MATCH_MP_TAC(SET_RULE `(!x. x IN s ==> (k:real^2->real^2) x = x) ==> IMAGE k s = s`) THEN
    X_GEN_TAC `x:real^2` THEN DISCH_TAC THEN REWRITE_TAC[o_THM] THEN
    UNDISCH_TAC `pl_homeomorphism
                   (holed_disk_model 1,
                    interval[--vector[&2;&2]:real^2,vector[&2;&2]] DIFF
                    interval(--vector[&1;&1]:real^2,vector[&1;&1]))
                   (moi_feu_hd1_map,h:real^2->real^2)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1 o CONJUNCT1) THEN
    MP_TAC(ISPEC `holed_disk_model 1` FRONTIER_SUBSET_CLOSED) THEN
    REWRITE_TAC[MOI_FEU_EULER_HOLED_DISK_MODEL; COMPACT_IMP_CLOSED] THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED; MOI_FEU_EULER_HOLED_DISK_MODEL] THEN ASM SET_TAC[];
    ASM_REWRITE_TAC[]]);;

(* The main theorem, with the two statements of pc_moi_fnd_surfb and         *)
(* pc_moi_fnd_surfb0 as hypotheses (discharged in pc_moi_fnd_nb2f).          *)

let MOI_FN2_POLYGON_2_COND = prove
 (mk_imp(mk_conj(MOI_FND_SURFACE_PLANAR, moi_fn2_bdc_body),
         MOI_FND_DERIVED_NBHD_POLYGON_2),
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "PLANAR") (LABEL_TAC "BDC")) THEN
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_NC_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
                MOI_FN2_COMPONENT_COUNT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FN2_CC_PROPS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k:real^N->bool. k IN components (derived_frontier m l) ==> pl_sphere 1 k`
  ASSUME_TAC THENL
   [USE_THEN "BDC" (MP_TAC o SPEC `derived_nbhd_complex (m:(real^N->bool)->bool) l`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (components (derived_frontier m (l:(real^N->bool)->bool))) = 1 \/
                CARD (components (derived_frontier m l)) = 2`
  ASSUME_TAC THENL
   [USE_THEN "PLANAR" (MP_TAC o SPEC `derived_nbhd_complex (m:(real^N->bool)->bool) l`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o CONJUNCT1 o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[REAL_ADD_LID; REAL_OF_NUM_LE] THEN
    SUBGOAL_THEN `~(CARD (components (derived_frontier m (l:(real^N->bool)->bool))) = 0)`
    MP_TAC THENL [ASM_SIMP_TAC[CARD_EQ_0]; ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD (components (derived_frontier m (l:(real^N->bool)->bool))) = 2
    ==> ?j1 j2. pl_annulus_with_ends (derived_nbhd m l) j1 j2 /\
                derived_frontier m l = j1 UNION j2`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(MATCH_MP MOI_FN2_ANNULUS (ASSUME MOI_FND_SURFACE_PLANAR)) THEN
    DISCH_THEN(MP_TAC o SPECL [`m:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REMOVE_THEN "PLANAR" (K ALL_TAC) THEN REMOVE_THEN "BDC" (K ALL_TAC) THEN
  ASM_REWRITE_TAC[]);;

