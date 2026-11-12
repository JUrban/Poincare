(* ========================================================================= *)
(* pc_moi_fnd_rn: foundations of the Moise PL core (Moise, Geometric         *)
(* Topology in Dimensions 2 and 3, GTM 47, pp.169-171 (23.11-23.12, 23.18),  *)
(* p.192 (26.3 proof), p.195 (26.6 proof)): second-derived neighbourhoods   *)
(* N = derived_nbhd t l of subcomplexes.  Main theorems (proving the         *)
(* statement terms of pc_moi_fnd_stmt.ml):                                   *)
(*   DERIVED_NBHD_COMBINATORIAL       = MOI_FND_DERIVED_NBHD_MANIFOLD        *)
(*   DERIVED_NBHD_DEFORMATION_RETRACT = MOI_FND_DERIVED_NBHD_RETRACT         *)
(*   SURFACE_NBHD_SIDES               = MOI_FND_SURFACE_NBHD_SIDES           *)
(* The ball case MOI_FND_DERIVED_NBHD_BALL is used only in dimension at most *)
(* 2 (pc_moi_fnd_stmt4), where pc_moi_fnd_rnb2 proves it.                   *)
(* Notation: c = barycentric_subdivision t (the first derived), k =         *)
(* barycentric_subdivision l, which is a full subcomplex of c; the simplices *)
(* of the second derived are the hulls of the barycentres of chains of c.   *)
(* The first section: generic facts on complexes, chains and simplexwise     *)
(* affine maps; fullness of the first derived of a subcomplex.               *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_stmt.ml";;
needs "src/pc_moi_fnd_dn.ml";;
needs "src/pc_moi_fnd_m3b.ml";;
needs "src/pc_moi_fnd_euler.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Locally finite complexes satisfy the complex axioms of pc_moi_bary.      *)
(* ------------------------------------------------------------------------- *)

let MOI_FRN_LF_BAR_COMPLEX = prove
 (`!c:(real^N->bool)->bool. lf_simplicial_complex c ==> moi_bar_complex c`,
  REWRITE_TAC[lf_simplicial_complex; moi_bar_complex] THEN MESON_TAC[]);;

(* A simplex of a complex whose relative interior meets the polyhedron of a *)
(* subcomplex belongs to the subcomplex.                                    *)

let MOI_FRN_RELINT_MEETS_SUBCOMPLEX = prove
 (`!(c:(real^N->bool)->bool) k s z.
     moi_bar_complex c /\ simplicial_subcomplex k c /\ s IN c /\
     z IN relative_interior s /\ z IN UNIONS k
     ==> s IN k`,
  REWRITE_TAC[moi_bar_complex; simplicial_subcomplex; IN_UNIONS] THEN
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(q:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET s INTER q` ASSUME_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_SIMP_TAC[SUBSET_REFL] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[IN_INTER] THEN
    ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `s INTER q:real^N->bool = s` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

(* The hull of the barycentres of a chain meets the polyhedron of a         *)
(* subcomplex exactly when some member of the chain is in the subcomplex.   *)

let MOI_FRN_CHAIN_HULL_MEETS = prove
 (`!(c:(real^N->bool)->bool) k f.
     moi_bar_complex c /\ simplicial_subcomplex k c /\ moi_bar_chain c f
     ==> (~(convex hull (IMAGE simplex_barycentre f) INTER UNIONS k = {}) <=>
          ?s. s IN f /\ s IN k)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `z:real^N`] MOI_BAR_CHAIN_HULL_RI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_bar_chain c (g:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET]; ALL_TAC] THEN
    ASM_CASES_TAC `g:(real^N->bool)->bool = {}` THENL
     [UNDISCH_TAC
       `z IN relative_interior
          (convex hull IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; RELATIVE_INTERIOR_EMPTY;
                      NOT_IN_EMPTY];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_MAX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    EXISTS_TAC `UNIONS g:real^N->bool` THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `z:real^N`] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_RI_MAX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `simplex_barycentre s:real^N` THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_BAR_CHAIN_BARYCENTRE_IN]]);;
let MOI_FRN_FULL_CHAIN = prove
 (`!(t:(real^N->bool)->bool) l f.
     moi_bar_complex t /\ simplicial_subcomplex l t /\ moi_bar_chain t f
     ==> convex hull (IMAGE simplex_barycentre f) INTER UNIONS l =
         convex hull (IMAGE simplex_barycentre (f INTER l))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `z:real^N` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `z:real^N`] MOI_BAR_CHAIN_HULL_RI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_bar_chain t (g:(real^N->bool)->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET]; ALL_TAC] THEN
    ASM_CASES_TAC `g:(real^N->bool)->bool = {}` THENL
     [UNDISCH_TAC
       `z IN relative_interior
          (convex hull IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; RELATIVE_INTERIOR_EMPTY;
                      NOT_IN_EMPTY];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
      MOI_BAR_CHAIN_MAX) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `UNIONS g IN (l:(real^N->bool)->bool)` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
      MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `z:real^N`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_BAR_CHAIN_RI_MAX THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:(real^N->bool)->bool) SUBSET f INTER l` ASSUME_TAC THENL
     [REWRITE_TAC[SUBSET; IN_INTER] THEN X_GEN_TAC `s:real^N->bool` THEN
      DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `simplicial_subcomplex (l:(real^N->bool)->bool) t` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      EXISTS_TAC `UNIONS g:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_BAR_CHAIN_FACE_OF_MAX THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `convex hull IMAGE simplex_barycentre (g:(real^N->bool)->bool) SUBSET
      convex hull IMAGE simplex_barycentre (f INTER l)` ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    REWRITE_TAC[SUBSET_INTER] THEN CONJ_TAC THENL
     [MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
    ASM_CASES_TAC `(f:(real^N->bool)->bool) INTER l = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; EMPTY_SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_bar_chain t ((f:(real^N->bool)->bool) INTER l)`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `f:(real^N->bool)->bool`
      THEN ASM_REWRITE_TAC[INTER_SUBSET];
      ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN
    EXISTS_TAC `UNIONS ((f:(real^N->bool)->bool) INTER l)` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_HULL_SUBSET_MAX THEN
      EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      SET_TAC[]]]);;
let MOI_FRN_FULL = prove
 (`!(t:(real^N->bool)->bool) l s.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     s IN barycentric_subdivision t
     ==> s INTER UNIONS l IN barycentric_subdivision l /\
         (s INTER UNIONS l) face_of s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o MATCH_MP MOI_FRN_LF_BAR_COMPLEX) THEN
  UNDISCH_TAC `(s:real^N->bool) IN barycentric_subdivision t` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `f:(real^N->bool)->bool`] MOI_FRN_FULL_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN CONJ_TAC THENL
   [EXISTS_TAC `(f:(real^N->bool)->bool) INTER l` THEN REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_bar_chain t (f:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_bar_chain; IN_INTER; INTER_SUBSET] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[FINITE_INTER] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[INTER_SUBSET]]);;
(* ------------------------------------------------------------------------- *)
(* Simplexwise affine extension of vertex values over a complex (no         *)
(* finiteness), and PL-ness and continuity for locally finite complexes.    *)
(* ------------------------------------------------------------------------- *)

let MOI_FRN_SIMPLEX_EXTREME_HULL = prove
 (`!s:real^N->bool.
     (?n. n simplex s)
     ==> ~affine_dependent {v | v extreme_point_of s} /\
         s = convex hull {v | v extreme_point_of s}`,
  GEN_TAC THEN REWRITE_TAC[SIMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:int` (X_CHOOSE_THEN `c:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  ASM_SIMP_TAC[EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT]);;

let MOI_FRN_SIMPLEXWISE_EXTENSION = prove
 (`!(K:(real^N->bool)->bool) (phi:real^N->real^M).
     moi_bar_complex K
     ==> ?h. (!s. s IN K ==> ?l y. linear l /\ !x. x IN s ==> h x = l x + y) /\
             (!v. {v} IN K ==> h v = phi v)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!s. s IN K
        ==> ?l y. linear l /\
                  !v. v extreme_point_of s
                      ==> (l:real^N->real^M) v + y = phi v`
  MP_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
    DISCH_THEN(MP_TAC o CONJUNCT1) THEN
    DISCH_THEN(MP_TAC o MATCH_MP (ISPECL
      [`{v:real^N | v extreme_point_of s}`; `phi:real^N->real^M`]
      MOI_REAL_AFFINE_EXTEND_POINTS)) THEN
    REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o REWRITE_RULE[RIGHT_IMP_EXISTS_THM; SKOLEM_THM]) THEN
  DISCH_THEN(X_CHOOSE_THEN `L:(real^N->bool)->real^N->real^M`
   (X_CHOOSE_THEN `Y:(real^N->bool)->real^M` (LABEL_TAC "LY"))) THEN
  ABBREV_TAC `S = \x:real^N. @s. s IN K /\ x IN s` THEN
  EXISTS_TAC `\x:real^N. (L:(real^N->bool)->real^N->real^M) (S x) x + Y (S x)`
  THEN
  SUBGOAL_THEN
   `!s x:real^N. s IN K /\ x IN s
        ==> (L:(real^N->bool)->real^N->real^M) (S x) x + Y (S x) =
            L s x + Y s`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `(S:real^N->real^N->bool) x IN K /\ x IN S x`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "S" THEN REWRITE_TAC[] THEN CONV_TAC SELECT_CONV THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    ABBREV_TAC `Fc = (s:real^N->bool) INTER S (x:real^N)` THEN
    SUBGOAL_THEN `(Fc:real^N->bool) face_of s /\ Fc face_of S (x:real^N)`
    STRIP_ASSUME_TAC THENL
     [EXPAND_TAC "Fc" THEN ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN Fc` ASSUME_TAC THENL
     [EXPAND_TAC "Fc" THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull {v:real^N | v extreme_point_of Fc}`
    ASSUME_TAC THENL
     [SUBGOAL_THEN `Fc = convex hull {v:real^N | v extreme_point_of Fc}`
      (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN CONJ_TAC THENL
       [ASM_MESON_TAC[FACE_OF_IMP_CONVEX]; ALL_TAC] THEN
      MATCH_MP_TAC FACE_OF_IMP_COMPACT THEN EXISTS_TAC `s:real^N->bool` THEN
      ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT];
      ALL_TAC] THEN
    MP_TAC(ISPECL
     [`(L:(real^N->bool)->real^N->real^M) (S(x:real^N))`;
      `(L:(real^N->bool)->real^N->real^M) s`;
      `(Y:(real^N->bool)->real^M) (S(x:real^N))`;
      `(Y:(real^N->bool)->real^M) s`;
      `{v:real^N | v extreme_point_of Fc}`] MOI_REAL_AFFINE_EQ_ON_CONVEX_HULL) THEN
    ANTS_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      X_GEN_TAC `w:real^N` THEN REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN
      SUBGOAL_THEN
       `(w:real^N) extreme_point_of s /\ w extreme_point_of S(x:real^N)`
      STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[EXTREME_POINT_OF_FACE]; ALL_TAC] THEN
      ASM_MESON_TAC[];
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    MAP_EVERY EXISTS_TAC
     [`(L:(real^N->bool)->real^N->real^M) s`; `(Y:(real^N->bool)->real^M) s`]
    THEN ASM_MESON_TAC[];
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`{v:real^N}`; `v:real^N`]) THEN
    ASM_REWRITE_TAC[IN_SING] THEN DISCH_THEN SUBST1_TAC THEN
    REMOVE_THEN "LY" (MP_TAC o SPEC `{v:real^N}`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    REWRITE_TAC[EXTREME_POINT_OF_SING]]);;
let MOI_FRN_SIMPLEXWISE_PL = prove
 (`!(K:(real^N->bool)->bool) (h:real^N->real^M).
     lf_simplicial_complex K /\
     (!s. s IN K ==> ?l y. linear l /\ !x. x IN s ==> h x = l x + y)
     ==> pl_map_on (UNIONS K) h /\ h continuous_on UNIONS K`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `p /\ (p ==> q) ==> p /\ q`) THEN
  REWRITE_TAC[PL_MAP_ON_IMP_CONTINUOUS_ON] THEN
  REWRITE_TAC[pl_map_on] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o SPEC `x:real^N` o last o CONJUNCTS o
    REWRITE_RULE[lf_simplicial_complex]) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->bool` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC
   [`{s:real^N->bool | s IN K /\ ~(s INTER u = {})}`; `u:real^N->bool`] THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `z:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `s:real^N->bool`) ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `k:real^N->bool` THEN STRIP_TAC THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; lf_simplicial_complex]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC(SET_RULE `(k:real^N->bool) IN K ==> k SUBSET UNIONS K`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `k:real^N->bool`) THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* Chains of the first derived c = barycentric_subdivision t: the           *)
(* minimum of a chain, injectivity of barycentres, and the second-derived  *)
(* neighbourhood and its complex in terms of chains of c meeting k =        *)
(* barycentric_subdivision l.                                                *)
(* ========================================================================= *)

let MOI_FRN_CHAIN_MIN = prove
 (`!c f:(real^N->bool)->bool.
     moi_bar_chain c f /\ ~(f = {})
     ==> INTERS f IN f /\ !s. s IN f ==> INTERS f SUBSET s`,
  REWRITE_TAC[moi_bar_chain] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC INTERS_IN_CHAIN THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_INTERS] THEN ASM_MESON_TAC[]]);;

(* Barycentres of distinct nonempty simplices of a complex are distinct.    *)

let MOI_FRN_BARYCENTRE_INJ = prove
 (`!(c:(real^N->bool)->bool) s t.
     moi_bar_complex c /\ s IN c /\ t IN c /\ ~(s = {}) /\ ~(t = {}) /\
     simplex_barycentre s = simplex_barycentre t
     ==> s = t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(?n. n simplex (s:real^N->bool)) /\ (?n. n simplex (t:real^N->bool))`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  SUBGOAL_THEN
   `simplex_barycentre s IN relative_interior (s:real^N->bool) /\
    simplex_barycentre t IN relative_interior (t:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR]; ALL_TAC] THEN
  SUBGOAL_THEN
   `(s INTER t) face_of (s:real^N->bool) /\ (s INTER t) face_of (t:real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET s INTER t /\ t SUBSET s INTER t`
  MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THENL
     [EXISTS_TAC `s:real^N->bool`; EXISTS_TAC `t:real^N->bool`] THEN
    ASM_REWRITE_TAC[SUBSET_REFL; DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER]
    THEN EXISTS_TAC `simplex_barycentre (t:real^N->bool)` THEN
    ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The second-derived neighbourhood in terms of chains of the first derived *)
(* c = barycentric_subdivision t, with k = barycentric_subdivision l.        *)
(* ------------------------------------------------------------------------- *)

let MOI_FRN_SETUP = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> lf_simplicial_complex (barycentric_subdivision t) /\
         moi_bar_complex (barycentric_subdivision t) /\
         UNIONS (barycentric_subdivision t) = UNIONS t /\
         simplicial_subcomplex (barycentric_subdivision l)
                               (barycentric_subdivision t) /\
         UNIONS (barycentric_subdivision l) = UNIONS l /\
         lf_simplicial_complex (barycentric_subdivision l) /\
         moi_bar_complex (barycentric_subdivision l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    BARYCENTRIC_SUBDIVISION_SUBCOMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF; UNIONS_BARYCENTRIC_SUBDIVISION;
               MOI_FRN_LF_BAR_COMPLEX] THEN
  SUBGOAL_THEN `lf_simplicial_complex (barycentric_subdivision l:(real^N->bool)->bool)`
   (fun th -> REWRITE_TAC[th; MATCH_MP MOI_FRN_LF_BAR_COMPLEX th]) THEN
  MATCH_MP_TAC MOI_FDN_LF_SUBCOMPLEX THEN
  EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF]);;

let MOI_FRN_IN_NBHD = prove
 (`!(t:(real^N->bool)->bool) l x.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> (x IN derived_nbhd t l <=>
          ?f. moi_bar_chain (barycentric_subdivision t) f /\
              (?s. s IN f /\ s IN barycentric_subdivision l) /\
              x IN convex hull (IMAGE simplex_barycentre f))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[derived_nbhd; IN_UNIONS; IN_ELIM_THM] THEN
  REWRITE_TAC[ISPEC `barycentric_subdivision t:(real^N->bool)->bool`
    MOI_BAR_IN_SUBDIVISION] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                   `barycentric_subdivision l:(real^N->bool)->bool`;
                   `f:(real^N->bool)->bool`] MOI_FRN_CHAIN_HULL_MEETS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre f):real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                   `barycentric_subdivision l:(real^N->bool)->bool`;
                   `f:(real^N->bool)->bool`] MOI_FRN_CHAIN_HULL_MEETS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_FRN_IN_NBHD_COMPLEX = prove
 (`!(t:(real^N->bool)->bool) l s.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> (s IN derived_nbhd_complex t l <=>
          ?f. moi_bar_chain (barycentric_subdivision t) f /\
              (?r. r IN f /\ r IN barycentric_subdivision l) /\
              s face_of convex hull (IMAGE simplex_barycentre f))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
  REWRITE_TAC[ISPEC `barycentric_subdivision t:(real^N->bool)->bool`
    MOI_BAR_IN_SUBDIVISION] THEN
  EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                   `barycentric_subdivision l:(real^N->bool)->bool`;
                   `f:(real^N->bool)->bool`] MOI_FRN_CHAIN_HULL_MEETS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    ASM_REWRITE_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre f):real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                   `barycentric_subdivision l:(real^N->bool)->bool`;
                   `f:(real^N->bool)->bool`] MOI_FRN_CHAIN_HULL_MEETS) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* The hull of a chain meeting k, and its vertices, are in the complex.     *)

let MOI_FRN_CHAIN_IN_NBHD_COMPLEX = prove
 (`!(t:(real^N->bool)->bool) l f.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     moi_bar_chain (barycentric_subdivision t) f /\
     (?r. r IN f /\ r IN barycentric_subdivision l)
     ==> convex hull (IMAGE simplex_barycentre f) IN derived_nbhd_complex t l /\
         (!s. s IN f ==> {simplex_barycentre s} IN derived_nbhd_complex t l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_SIMP_TAC[MOI_FRN_IN_NBHD_COMPLEX] THEN CONJ_TAC THENL
   [EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[FACE_OF_REFL_EQ;
      CONVEX_CONVEX_HULL] THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `{simplex_barycentre s:real^N} =
                  convex hull (IMAGE simplex_barycentre {s})`
    SUBST1_TAC THENL
     [REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
    EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FRN_LF_BAR_COMPLEX; BARYCENTRIC_SUBDIVISION_LF;
                 SING_SUBSET]]);;

(* ========================================================================= *)
(* The simplicial retraction of N onto UNIONS l (vertex b(s) goes           *)
(* to b(s INTER UNIONS l), s in c), and the convex hulls of the barycentres *)
(* of the faces of a simplex of c through a vertex of k, which lie in N.    *)
(* ========================================================================= *)

let MOI_FRN_RETRACTION_MAP = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> ?r. (!f. moi_bar_chain (barycentric_subdivision t) f /\
                  (?q. q IN f /\ q IN barycentric_subdivision l)
                  ==> (?L y. linear L /\
                             !x. x IN convex hull (IMAGE simplex_barycentre f)
                                 ==> r x = L x + y) /\
                      (!s. s IN f
                           ==> r (simplex_barycentre s) =
                               simplex_barycentre (s INTER UNIONS l))) /\
             pl_map_on (derived_nbhd t l) r /\
             r continuous_on derived_nbhd t l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (derived_nbhd_complex t l:(real^N->bool)->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FDN_DERIVED_NBHD_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL
   [`derived_nbhd_complex t l:(real^N->bool)->bool`;
    `\v:real^N. simplex_barycentre
        ((@s. s IN barycentric_subdivision t /\ ~(s = {}) /\
              simplex_barycentre s = v) INTER UNIONS l)`]
   MOI_FRN_SIMPLEXWISE_EXTENSION) THEN
  ASM_SIMP_TAC[MOI_FRN_LF_BAR_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real^N->real^N` THEN
  MP_TAC(ISPECL [`derived_nbhd_complex t l:(real^N->bool)->bool`;
                 `r:real^N->real^N`] MOI_FRN_SIMPLEXWISE_PL) THEN
  ASM_SIMP_TAC[MOI_FDN_UNIONS_DERIVED_NBHD_COMPLEX] THEN DISCH_TAC THEN
  X_GEN_TAC `f:(real^N->bool)->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `f:(real^N->bool)->bool`] MOI_FRN_CHAIN_IN_NBHD_COMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[];
    STRIP_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `simplex_barycentre s:real^N` o
    check (fun th -> can (find_term ((=) `phi:real^N->real^N`)) (concl th) ||
                     is_forall (concl th) &&
                     can (find_term (fun t -> is_select t)) (concl th))) THEN
  ASM_SIMP_TAC[] THEN DISCH_THEN SUBST1_TAC THEN AP_TERM_TAC THEN
  AP_THM_TAC THEN AP_TERM_TAC THEN
  MATCH_MP_TAC SELECT_UNIQUE THEN X_GEN_TAC `s':real^N->bool` THEN
  REWRITE_TAC[] THEN EQ_TAC THENL
   [STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_BARYCENTRE_INJ THEN
    EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT];
    DISCH_THEN SUBST1_TAC THEN ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]]);;
(* Affine maps commute with convex combinations and barycentres.            *)

let MOI_FRN_AFFINE_VSUM = prove
 (`!(L:real^N->real^M) y (p:A->bool) (mu:A->real) (q:A->real^N).
     linear L /\ FINITE p /\ sum p mu = &1
     ==> L (vsum p (\i. mu i % q i)) + y = vsum p (\i. mu i % (L (q i) + y))`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[LINEAR_VSUM; o_DEF] THEN
  ASM_SIMP_TAC[LINEAR_CMUL; VECTOR_ADD_LDISTRIB; VSUM_ADD] THEN
  ASM_SIMP_TAC[VSUM_RMUL; VECTOR_MUL_LID]);;

let MOI_FRN_AFFINE_BARYCENTRE = prove
 (`!(L:real^N->real^M) y s.
     linear L /\ FINITE {v | v extreme_point_of s} /\
     ~({v | v extreme_point_of s} = {})
     ==> L (simplex_barycentre s) + y =
         inv(&(CARD {v | v extreme_point_of s})) %
         vsum {v | v extreme_point_of s} (\v. L v + y)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplex_barycentre] THEN
  ABBREV_TAC `V = {v:real^N | v extreme_point_of s}` THEN
  SUBGOAL_THEN `~(&(CARD(V:real^N->bool)) = &0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_OF_NUM_EQ; CARD_EQ_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->real^M`; `y:real^M`; `V:real^N->bool`;
                 `\v:real^N. inv(&(CARD(V:real^N->bool)))`;
                 `\v:real^N. v`] MOI_FRN_AFFINE_VSUM) THEN
  ASM_SIMP_TAC[SUM_CONST; REAL_MUL_RINV] THEN
  REWRITE_TAC[GSYM VSUM_LMUL] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[]);;
(* An affine functional on a simplex tau taking the value 1 at the vertex a, *)
(* -1 at the vertex w and 0 at the other vertices, evaluated at barycentres *)
(* of faces.                                                                 *)

let MOI_FRN_FACE_FUNCTIONAL = prove
 (`!(tau:real^N->bool) a w.
     (?n. n simplex tau) /\ a extreme_point_of tau /\ w extreme_point_of tau
     ==> ?L y. linear (L:real^N->real^1) /\
               !r. r face_of tau /\ ~(r = {})
                   ==> drop(L (simplex_barycentre r) + y) =
                       ((if a IN r then &1 else &0) -
                        (if w IN r then &1 else &0)) /
                       &(CARD {v | v extreme_point_of r})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `tau:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  MP_TAC(ISPECL
   [`{v:real^N | v extreme_point_of tau}`;
    `\v:real^N. (if v = a then lift(&1) else vec 0) -
                (if v = w then lift(&1) else vec 0)`]
   MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^1`
   (X_CHOOSE_THEN `y:real^1` STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`L:real^N->real^1`; `y:real^1`] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `{v:real^N | v extreme_point_of r} SUBSET
                {v | v extreme_point_of tau}` ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[EXTREME_POINT_OF_FACE];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {v:real^N | v extreme_point_of r}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{v:real^N | v extreme_point_of tau}` THEN
    ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE];
    ALL_TAC] THEN
  SUBGOAL_THEN `~({v:real^N | v extreme_point_of r} = {})` ASSUME_TAC THENL
   [SUBGOAL_THEN `compact (r:real^N->bool) /\ convex r` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_COMPACT; FACE_OF_IMP_CONVEX;
                    SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MATCH_MP_TAC EXTREME_POINT_EXISTS_CONVEX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->real^1`; `y:real^1`; `r:real^N->bool`]
    MOI_FRN_AFFINE_BARYCENTRE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `vsum {v:real^N | v extreme_point_of r} (\v. L v + y) =
    vsum {v | v extreme_point_of r}
     (\v. (if v = a then lift(&1) else vec 0) -
          (if v = w then lift(&1) else vec 0))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC VSUM_EQ THEN ASM SET_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[VSUM_SUB; VSUM_DELTA] THEN
  SUBGOAL_THEN `((a:real^N) extreme_point_of r <=> a IN r) /\
                ((w:real^N) extreme_point_of r <=> w IN r)`
   (fun th -> REWRITE_TAC[th; IN_ELIM_THM]) THENL
   [ASM_MESON_TAC[EXTREME_POINT_OF_FACE]; ALL_TAC] THEN
  REWRITE_TAC[DROP_CMUL; DROP_SUB] THEN
  REWRITE_TAC[real_div] THEN
  ABBREV_TAC `z = inv(&(CARD {v:real^N | v extreme_point_of r}))` THEN
  ASM_CASES_TAC `(a:real^N) IN r` THEN ASM_CASES_TAC `(w:real^N) IN r` THEN
  ASM_REWRITE_TAC[DROP_VEC; LIFT_DROP] THEN REAL_ARITH_TAC);;
(* The hull of the barycentres of the faces of tau through a vertex a of k  *)
(* lies in N: a point of it lies in the open simplex of a chain of faces of *)
(* tau whose least member contains a (else the functional of               *)
(* MOI_FRN_FACE_FUNCTIONAL would be both >= 0 and < 0 there).                *)

let MOI_FRN_STAR_HULL_IN_NBHD = prove
 (`!(t:(real^N->bool)->bool) l tau a.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     tau IN barycentric_subdivision t /\ a extreme_point_of tau /\
     a IN UNIONS l
     ==> convex hull (IMAGE simplex_barycentre {r | r face_of tau /\ a IN r})
         SUBSET derived_nbhd t l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = barycentric_subdivision (t:(real^N->bool)->bool)` THEN
  ABBREV_TAC `k = barycentric_subdivision (l:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `?n. n simplex (tau:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex; FACE_OF_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN k` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `a:real^N`] THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex {r:real^N->bool | r face_of tau}` ASSUME_TAC
  THENL [ASM_MESON_TAC[MOI_FMB_FACE_COMPLEX; MOI_BAR_SIMPLICIAL_COMPLEX];
         ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN tau` ASSUME_TAC THENL
   [UNDISCH_TAC
     `(y:real^N) IN convex hull
        (IMAGE simplex_barycentre {r | r face_of tau /\ a IN r})` THEN
    SPEC_TAC(`y:real^N`,`y:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
    MATCH_MP_TAC HULL_MINIMAL THEN
    CONJ_TAC THENL [ALL_TAC; ASM_MESON_TAC[SIMPLEX_IMP_CONVEX]] THEN
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
    X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    SUBGOAL_THEN `simplex_barycentre r IN (r:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
      EXISTS_TAC `n':int` THEN ASM SET_TAC[];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:int`; `tau:real^N->bool`; `y:real^N`]
    MOI_BAR_SIMPLEX_COVERED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`{r:real^N->bool | r face_of tau}`;
                 `g0:(real^N->bool)->bool`; `y:real^N`]
    MOI_BAR_CHAIN_HULL_RI) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain {r:real^N->bool | r face_of tau} g`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `(y:real^N) IN relative_interior
        (convex hull IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; RELATIVE_INTERIOR_EMPTY;
                    NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{r:real^N->bool | r face_of tau}`;
                 `g:(real^N->bool)->bool`] MOI_FRN_CHAIN_MIN) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = INTERS (g:(real^N->bool)->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN g ==> r face_of tau /\ ~(r = {})`
  (LABEL_TAC "gface") THENL
   [UNDISCH_TAC `moi_bar_chain {r:real^N->bool | r face_of tau} g` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(a:real^N) IN m` THENL
   [ASM_SIMP_TAC[MOI_FRN_IN_NBHD] THEN
    EXISTS_TAC `({a:real^N}) INSERT (g:(real^N->bool)->bool)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_bar_chain {r:real^N->bool | r face_of tau} g` THEN
      REWRITE_TAC[moi_bar_chain; FINITE_INSERT; INSERT_SUBSET; IN_INSERT] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(r:real^N->bool) face_of tau` MP_TAC THENL
         [ASM SET_TAC[]; ASM_MESON_TAC[moi_bar_complex]];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`r1:real^N->bool`; `r2:real^N->bool`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `{a:real^N}` THEN ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s t. (y:real^N) IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `convex hull IMAGE simplex_barycentre (g:(real^N->bool)->bool)`
    THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "gface" (fun th ->
    MP_TAC(MATCH_MP th (ASSUME `(m:real^N->bool) IN g`))) THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (m:real^N->bool) /\ convex m` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_COMPACT; FACE_OF_IMP_CONVEX;
                  SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  MP_TAC(ISPEC `m:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N) extreme_point_of tau /\ w IN m` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[EXTREME_POINT_OF_FACE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tau:real^N->bool`; `a:real^N`; `w:real^N`]
    MOI_FRN_FACE_FUNCTIONAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^1`
   (X_CHOOSE_THEN `y0:real^1` (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "fval"))))
  THEN
  SUBGOAL_THEN
   `!r:real^N->bool. r face_of tau /\ ~(r = {})
        ==> &0 < &(CARD {v:real^N | v extreme_point_of r})`
  (LABEL_TAC "cardpos") THENL
   [X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN
    SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
    SUBGOAL_THEN `FINITE {v:real^N | v extreme_point_of r}` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN DISCH_TAC THEN
    ASM_MESON_TAC[CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull (IMAGE simplex_barycentre {r | r face_of tau /\ a IN r}) SUBSET
    {z:real^N | &0 <= drop((L:real^N->real^1) z + y0)}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN `~(r:real^N->bool = {})` ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_SIMP_TAC[] THEN MATCH_MP_TAC REAL_LE_DIV THEN
      REWRITE_TAC[REAL_POS] THEN COND_CASES_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[convex; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`; `u:real`; `v:real`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       `drop((L:real^N->real^1) (u % x1 + v % x2) + y0) =
        u * drop(L x1 + y0) + v * drop(L x2 + y0)`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; DROP_ADD; DROP_CMUL] THEN
        SUBGOAL_THEN `v = &1 - u` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= drop((L:real^N->real^1) y + y0)` MP_TAC THENL
   [UNDISCH_TAC
     `convex hull (IMAGE simplex_barycentre {r | r face_of tau /\ a IN r}) SUBSET
      {z:real^N | &0 <= drop((L:real^N->real^1) z + y0)}` THEN
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN REWRITE_TAC[REAL_NOT_LE] THEN
  SUBGOAL_THEN
   `~affine_dependent (IMAGE simplex_barycentre (g:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
    EXISTS_TAC `{r:real^N->bool | r face_of tau}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `(y:real^N) IN relative_interior
      (convex hull IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real^N->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "mupos") STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `FINITE (IMAGE simplex_barycentre (g:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain {r:real^N->bool | r face_of tau} g` THEN
    SIMP_TAC[moi_bar_chain; FINITE_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->real^1`; `y0:real^1`;
                 `IMAGE simplex_barycentre (g:(real^N->bool)->bool)`;
                 `mu:real^N->real`; `\p:real^N. p`] MOI_FRN_AFFINE_VSUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DROP_VSUM; o_DEF; DROP_CMUL] THEN
  SUBGOAL_THEN
   `&0 = sum (IMAGE simplex_barycentre (g:(real^N->bool)->bool)) (\p. &0)`
  SUBST1_TAC THENL [REWRITE_TAC[SUM_0]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_LT THEN REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "gface" (fun th ->
      MP_TAC(MATCH_MP th (ASSUME `(r:real^N->bool) IN g`))) THEN STRIP_TAC THEN
    USE_THEN "fval" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(r:real^N->bool) face_of tau`)
            (ASSUME `~(r:real^N->bool = {})`)))) THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(w:real^N) IN r` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x * --y ==> x * y <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "mupos" MATCH_MP_TAC THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fval" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(m:real^N->bool) face_of tau`)
            (ASSUME `~(m:real^N->bool = {})`)))) THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x * --y ==> x * y < &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [USE_THEN "mupos" MATCH_MP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LT_INV_EQ] THEN USE_THEN "cardpos" MATCH_MP_TAC THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;

(* ========================================================================= *)
(* The deformation retraction (the theorem                                   *)
(* DERIVED_NBHD_DEFORMATION_RETRACT): the straight-line homotopy from the    *)
(* identity to the simplicial retraction stays in N, since a point x of N    *)
(* and its image lie in the hull of the barycentres of the faces through a   *)
(* vertex of k of the carrier of x in c (MOI_FRN_STAR_HULL_IN_NBHD).         *)
(* ========================================================================= *)

let MOI_FRN_CHAIN_SEGMENT_IN_NBHD = prove
 (`!(t:(real^N->bool)->bool) l f s x z.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     moi_bar_chain (barycentric_subdivision t) f /\
     s IN f /\ s IN barycentric_subdivision l /\
     x IN convex hull (IMAGE simplex_barycentre f) /\
     z IN convex hull (IMAGE (\p. simplex_barycentre (p INTER UNIONS l)) f)
     ==> z IN UNIONS l /\
         !u. &0 <= u /\ u <= &1 ==> (&1 - u) % x + u % z IN derived_nbhd t l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(f:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                   `f:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `tau = UNIONS (f:(real^N->bool)->bool)` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                   `f:(real^N->bool)->bool`] MOI_FRN_CHAIN_MIN) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `m = INTERS (f:(real^N->bool)->bool)` THEN STRIP_TAC THEN
    SUBGOAL_THEN `!p:real^N->bool. p IN f ==> p IN barycentric_subdivision t /\
                                    ~(p = {}) /\ (?n. n simplex p)`
    (LABEL_TAC "fel") THENL
     [X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_BAR_CHAIN_ELEMENT THEN
      EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `!p:real^N->bool. p IN f ==> p face_of tau`
    (LABEL_TAC "fface") THENL
     [REPEAT STRIP_TAC THEN EXPAND_TAC "tau" THEN
      MATCH_MP_TAC MOI_BAR_CHAIN_FACE_OF_MAX THEN
      EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(m:real^N->bool) IN barycentric_subdivision l` ASSUME_TAC
    THENL
     [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                     (barycentric_subdivision t:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_subcomplex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
      EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
      ASM_SIMP_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    USE_THEN "fel" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(m:real^N->bool) IN f`))) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_TAC `nm:int`))) THEN
    MP_TAC(ISPEC `m:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
    SUBGOAL_THEN `(a:real^N) IN m` ASSUME_TAC THENL
     [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^N) IN UNIONS l` ASSUME_TAC THENL
     [UNDISCH_TAC `UNIONS (barycentric_subdivision l) =
                   UNIONS (l:(real^N->bool)->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^N) extreme_point_of tau` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`m:real^N->bool`; `tau:real^N->bool`; `a:real^N`]
        EXTREME_POINT_OF_FACE) THEN
      USE_THEN "fface" (fun th -> REWRITE_TAC[MATCH_MP th
        (ASSUME `(m:real^N->bool) IN f`)]) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `tau:real^N->bool`; `a:real^N`] MOI_FRN_STAR_HULL_IN_NBHD) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_TAC] THEN
    SUBGOAL_THEN
     `!p:real^N->bool. p IN f
        ==> (p INTER UNIONS l) face_of tau /\ a IN p INTER UNIONS l /\
            (p INTER UNIONS l) IN barycentric_subdivision l`
    (LABEL_TAC "pl") THENL
     [X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `p:real^N->bool`] MOI_FRN_FULL) THEN
      USE_THEN "fel" (fun th -> ASM_REWRITE_TAC[MATCH_MP th
        (ASSUME `(p:real^N->bool) IN f`)]) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
       [MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `p:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN USE_THEN "fface" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      ALL_TAC] THEN
    ABBREV_TAC
     `P = convex hull (IMAGE simplex_barycentre
                         {q:real^N->bool | q face_of tau /\ a IN q})` THEN
    SUBGOAL_THEN `(x:real^N) IN P /\ (z:real^N) IN P`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [UNDISCH_TAC
         `(x:real^N) IN convex hull IMAGE simplex_barycentre f` THEN
        SPEC_TAC(`x:real^N`,`q0:real^N`) THEN REWRITE_TAC[GSYM SUBSET] THEN
        EXPAND_TAC "P" THEN MATCH_MP_TAC HULL_MONO THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `p:real^N->bool` THEN
        REWRITE_TAC[IN_ELIM_THM] THEN CONJ_TAC THENL
         [USE_THEN "fface" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          ASM SET_TAC[]];
        UNDISCH_TAC
         `(z:real^N) IN
          convex hull IMAGE (\s. simplex_barycentre (s INTER UNIONS l)) f` THEN
        SPEC_TAC(`z:real^N`,`q0:real^N`) THEN
        REWRITE_TAC[GSYM SUBSET] THEN
        EXPAND_TAC "P" THEN MATCH_MP_TAC HULL_MONO THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN
        REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `p INTER UNIONS l:real^N->bool`
        THEN REWRITE_TAC[IN_ELIM_THM] THEN
        USE_THEN "pl" (fun th -> REWRITE_TAC[MATCH_MP th
          (ASSUME `(p:real^N->bool) IN f`)])];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `convex (tau INTER UNIONS l:real^N->bool)` ASSUME_TAC THENL
       [MATCH_MP_TAC FACE_OF_IMP_CONVEX THEN EXISTS_TAC `tau:real^N->bool` THEN
        MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `tau:real^N->bool`] MOI_FRN_FULL) THEN
        ASM_MESON_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `convex hull IMAGE (\s. simplex_barycentre (s INTER UNIONS l)) f SUBSET
        tau INTER UNIONS (l:(real^N->bool)->bool)`
      MP_TAC THENL
       [MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SUBSET; FORALL_IN_IMAGE] THEN
        X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN
        USE_THEN "pl" (MP_TAC o C MATCH_MP
          (ASSUME `(p:real^N->bool) IN f`)) THEN STRIP_TAC THEN
        SUBGOAL_THEN `simplex_barycentre (p INTER UNIONS l) IN
                      (p INTER UNIONS l:real^N->bool)` MP_TAC THENL
         [SUBGOAL_THEN `?n. n simplex (p INTER UNIONS l:real^N->bool)`
          STRIP_ASSUME_TAC THENL
           [ASM_MESON_TAC[lf_simplicial_complex]; ALL_TAC] THEN
          MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
          EXISTS_TAC `n:int` THEN ASM SET_TAC[];
          ALL_TAC] THEN
        SUBGOAL_THEN `(p:real^N->bool) SUBSET tau` MP_TAC THENL
         [ASM_SIMP_TAC[]; SET_TAC[]];
        ASM SET_TAC[]];
      X_GEN_TAC `u:real` THEN STRIP_TAC THEN
      UNDISCH_TAC `P SUBSET derived_nbhd t (l:(real^N->bool)->bool)` THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      SUBGOAL_THEN `convex (P:real^N->bool)` MP_TAC THENL
       [EXPAND_TAC "P" THEN REWRITE_TAC[CONVEX_CONVEX_HULL]; ALL_TAC] THEN
      REWRITE_TAC[convex] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]);;

let MOI_FRN_RETRACTION_FIXES = prove
 (`!(t:(real^N->bool)->bool) l r.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!f. moi_bar_chain (barycentric_subdivision t) f /\
          (?q. q IN f /\ q IN barycentric_subdivision l)
          ==> (?L y. linear L /\
                     !x. x IN convex hull (IMAGE simplex_barycentre f)
                         ==> r x = L x + y) /\
              (!s. s IN f
                   ==> r (simplex_barycentre s) =
                       simplex_barycentre (s INTER UNIONS l)))
     ==> !x. x IN UNIONS l ==> r x = x`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rf"))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `(x:real^N) IN UNIONS (barycentric_subdivision
                     (barycentric_subdivision l))`
  MP_TAC THENL
   [ASM_SIMP_TAC[MOI_BAR_UNIONS_SUBDIVISION]; ALL_TAC] THEN
  REWRITE_TAC[IN_UNIONS; MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
  SUBGOAL_THEN `~(f:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `(x:real^N) IN convex hull IMAGE simplex_barycentre f` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t) (f:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_MONO THEN
    EXISTS_TAC `barycentric_subdivision l:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex];
    ALL_TAC] THEN
  SUBGOAL_THEN `(f:(real^N->bool)->bool) SUBSET barycentric_subdivision l`
  ASSUME_TAC THENL [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  USE_THEN "rf" (MP_TAC o SPEC `f:(real^N->bool)->bool`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~(f:(real^N->bool)->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `q:real^N->bool`) THEN
    EXISTS_TAC `q:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `L:real^N->real^N` (X_CHOOSE_THEN `y:real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rl")))) (LABEL_TAC "rb")) THEN
  SUBGOAL_THEN
   `!p:real^N->bool. p IN f
      ==> (L:real^N->real^N) (simplex_barycentre p) + y = simplex_barycentre p`
  (LABEL_TAC "lb") THENL
   [X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN
    SUBGOAL_THEN `simplex_barycentre p IN
        convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))`
    ASSUME_TAC THENL
     [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `p:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    USE_THEN "rl" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `simplex_barycentre p IN
        convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))`))]) THEN
    USE_THEN "rb" (fun th -> REWRITE_TAC[MATCH_MP th
      (ASSUME `(p:real^N->bool) IN f`)]) THEN
    AP_TERM_TAC THEN
    SUBGOAL_THEN `(p:real^N->bool) SUBSET UNIONS l` MP_TAC THENL
     [UNDISCH_TAC `UNIONS (barycentric_subdivision l) =
                   UNIONS (l:(real^N->bool)->bool)` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      MATCH_MP_TAC(SET_RULE `(p:real^N->bool) IN k ==> p SUBSET UNIONS k`) THEN
      ASM SET_TAC[];
      SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->real^N`; `\x:real^N. x`; `y:real^N`;
                 `vec 0:real^N`; `IMAGE simplex_barycentre
                                    (f:(real^N->bool)->bool)`]
    MOI_REAL_AFFINE_EQ_ON_CONVEX_HULL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[LINEAR_ID; FORALL_IN_IMAGE; VECTOR_ADD_RID] THEN
    X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "lb" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
  ASM_REWRITE_TAC[VECTOR_ADD_RID] THEN DISCH_TAC THEN
  USE_THEN "rl" (fun th -> REWRITE_TAC[MATCH_MP th
    (ASSUME `(x:real^N) IN convex hull IMAGE simplex_barycentre f`)]) THEN
  ASM_REWRITE_TAC[]);;

let MOI_FRN_RETRACTION_MOVES = prove
 (`!(t:(real^N->bool)->bool) l r.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!f. moi_bar_chain (barycentric_subdivision t) f /\
          (?q. q IN f /\ q IN barycentric_subdivision l)
          ==> (?L y. linear L /\
                     !x. x IN convex hull (IMAGE simplex_barycentre f)
                         ==> r x = L x + y) /\
              (!s. s IN f
                   ==> r (simplex_barycentre s) =
                       simplex_barycentre (s INTER UNIONS l)))
     ==> !x. x IN derived_nbhd t l
             ==> r x IN UNIONS l /\
                 !u. &0 <= u /\ u <= &1
                     ==> (&1 - u) % x + u % r x IN derived_nbhd t l`,
  REPEAT GEN_TAC THEN DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rf"))) THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `x:real^N`] MOI_FRN_IN_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "rf" (MP_TAC o SPEC `f:(real^N->bool)->bool`) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `s:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2
   (X_CHOOSE_THEN `L:real^N->real^N` (X_CHOOSE_THEN `y:real^N`
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "rl")))) (LABEL_TAC "rb")) THEN
  MATCH_MP_TAC MOI_FRN_CHAIN_SEGMENT_IN_NBHD THEN
  MAP_EVERY EXISTS_TAC [`f:(real^N->bool)->bool`; `s:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `IMAGE (\s. simplex_barycentre (s INTER UNIONS l)) f =
    IMAGE (\x:real^N. (L:real^N->real^N) x + y)
          (IMAGE simplex_barycentre f)`
  SUBST1_TAC THENL
   [REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN MATCH_MP_TAC IMAGE_EQ THEN
    X_GEN_TAC `p:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "rb" (fun th -> REWRITE_TAC[GSYM(MATCH_MP th
      (ASSUME `(p:real^N->bool) IN f`))]) THEN
    USE_THEN "rl" MATCH_MP_TAC THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
    EXISTS_TAC `p:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[GSYM MOI_REAL_AFFINE_IMAGE_CONVEX_HULL] THEN
  REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `x:real^N` THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "rl" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]);;
(* The straight-line homotopy from the identity to a retraction r of a set *)
(* s onto j along which s is invariant.                                    *)

let MOI_FRN_STRAIGHT_HOMOTOPY = prove
 (`!(s:real^N->bool) j r.
     r continuous_on s /\
     (!x. x IN s
          ==> r x IN j /\
              !u. &0 <= u /\ u <= &1 ==> (&1 - u) % x + u % r x IN s) /\
     (!x. x IN j ==> r x = x)
     ==> homotopic_with (\h. !x. x IN j ==> h x = x)
           (subtopology euclidean s,subtopology euclidean s) (\x. x) r`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HOMOTOPIC_WITH_EUCLIDEAN] THEN
  EXISTS_TAC `\z:real^(1,N)finite_sum.
                (&1 - drop(fstcart z)) % sndcart z +
                drop(fstcart z) % (r:real^N->real^N)(sndcart z)` THEN
  REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; DROP_VEC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_ADD THEN CONJ_TAC THEN
    MATCH_MP_TAC CONTINUOUS_ON_MUL THEN
    SIMP_TAC[o_DEF; LIFT_SUB; LIFT_DROP; CONTINUOUS_ON_SUB; CONTINUOUS_ON_CONST;
             LINEAR_CONTINUOUS_ON; LINEAR_FSTCART; LINEAR_SNDCART; ETA_AX] THEN
    GEN_REWRITE_TAC LAND_CONV [GSYM o_DEF] THEN
    MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN
    SIMP_TAC[LINEAR_CONTINUOUS_ON; LINEAR_SNDCART; IMAGE_SNDCART_PCROSS] THEN
    COND_CASES_TAC THEN ASM_REWRITE_TAC[CONTINUOUS_ON_EMPTY];
    REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; FORALL_IN_PCROSS] THEN
    REWRITE_TAC[FSTCART_PASTECART; SNDCART_PASTECART; IN_INTERVAL_1] THEN
    REWRITE_TAC[DROP_VEC] THEN ASM_MESON_TAC[];
    VECTOR_ARITH_TAC;
    VECTOR_ARITH_TAC;
    REPEAT STRIP_TAC THEN ASM_SIMP_TAC[] THEN VECTOR_ARITH_TAC]);;

(* Loops in s are carried by j when the identity of s is homotopic to a     *)
(* map into j.                                                               *)

let MOI_FRN_HOMOTOPIC_IMP_LOOPS_CARRIED = prove
 (`!(s:real^N->bool) j r P.
     r continuous_on s /\ IMAGE r s SUBSET j /\
     homotopic_with P (subtopology euclidean s,subtopology euclidean s)
       (\x. x) r
     ==> loops_carried j s`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[loops_carried] THEN
  X_GEN_TAC `p:real^1->real^N` THEN STRIP_TAC THEN
  EXISTS_TAC `(r:real^N->real^N) o (p:real^1->real^N)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC PATH_CONTINUOUS_IMAGE THEN ASM_MESON_TAC[CONTINUOUS_ON_SUBSET];
    ASM_REWRITE_TAC[PATHFINISH_COMPOSE; PATHSTART_COMPOSE];
    REWRITE_TAC[PATH_IMAGE_COMPOSE] THEN ASM SET_TAC[];
    REWRITE_TAC[homotopic_loops] THEN
    SUBGOAL_THEN `p = (\x:real^N. x) o (p:real^1->real^N)` MP_TAC THENL
     [REWRITE_TAC[FUN_EQ_THM; o_THM]; ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC (RATOR_CONV o RAND_CONV) [th]) THEN
    MATCH_MP_TAC HOMOTOPIC_WITH_COMPOSE_CONTINUOUS_RIGHT THEN
    EXISTS_TAC `s:real^N->bool` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC HOMOTOPIC_WITH_MONO THEN
      EXISTS_TAC `P:(real^N->real^N)->bool` THEN ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[PATHFINISH_COMPOSE; PATHSTART_COMPOSE] THEN
      ASM_MESON_TAC[pathfinish; pathstart];
      ASM_MESON_TAC[path; path_image; SUBSET_REFL]]]);;
let DERIVED_NBHD_DEFORMATION_RETRACT = prove
 (`!(t:(real^N->bool)->bool) l.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> loops_carried (UNIONS l) (derived_nbhd t l) /\
         ?r. retraction (derived_nbhd t l,UNIONS l) r /\
             homotopic_with (\h. !x. x IN UNIONS l ==> h x = x)
               (subtopology euclidean (derived_nbhd t l),
                subtopology euclidean (derived_nbhd t l))
               (\x. x) r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_RETRACTION_MAP) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `r:real^N->real^N`] MOI_FRN_RETRACTION_MOVES) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `r:real^N->real^N`] MOI_FRN_RETRACTION_FIXES) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN `UNIONS l SUBSET derived_nbhd t (l:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
      MOI_FDN_DERIVED_NBHD_INTERIOR) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET_UNIONS]; ALL_TAC] THEN
    MESON_TAC[INTERIOR_OF_SUBSET; SUBSET_TRANS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `homotopic_with (\h. !x. x IN UNIONS l ==> h x = x)
      (subtopology euclidean (derived_nbhd t l),
       subtopology euclidean (derived_nbhd t l))
      (\x. x) (r:real^N->real^N)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_STRAIGHT_HOMOTOPY THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FRN_HOMOTOPIC_IMP_LOOPS_CARRIED THEN
    MAP_EVERY EXISTS_TAC
     [`r:real^N->real^N`;
      `\h:real^N->real^N. !x. x IN UNIONS l ==> h x = x`] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    EXISTS_TAC `r:real^N->real^N` THEN ASM_REWRITE_TAC[retraction] THEN
    ASM SET_TAC[]]);;

(* ========================================================================= *)
(* The maximal-coordinate description of N inside a simplex tau of          *)
(* c: a point of tau is in N iff its largest barycentric coordinate (with   *)
(* respect to tau) is attained at a vertex of tau lying in UNIONS l.        *)
(* ========================================================================= *)

(* Values of the functional of MOI_FRN_FACE_FUNCTIONAL at the vertices, and *)
(* at a convex combination of the vertices.                                  *)

let MOI_FRN_FUNCTIONAL_COMBINATION = prove
 (`!(tau:real^N->bool) a w (L:real^N->real^1) y0 (mu:real^N->real).
     (?n. n simplex tau) /\ a extreme_point_of tau /\
     w extreme_point_of tau /\ ~(a = w) /\ linear L /\
     (!r. r face_of tau /\ ~(r = {})
          ==> drop(L (simplex_barycentre r) + y0) =
              ((if a IN r then &1 else &0) - (if w IN r then &1 else &0)) /
              &(CARD {v | v extreme_point_of r})) /\
     sum {v | v extreme_point_of tau} mu = &1
     ==> drop(L (vsum {v | v extreme_point_of tau} (\v. mu v % v)) + y0) =
         mu a - mu w`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPEC `tau:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `FINITE {v:real^N | v extreme_point_of tau}` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->real^1`; `y0:real^1`;
                 `{v:real^N | v extreme_point_of tau}`;
                 `mu:real^N->real`; `\v:real^N. v`] MOI_FRN_AFFINE_VSUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DROP_VSUM; o_DEF; DROP_CMUL] THEN
  SUBGOAL_THEN
   `!v:real^N. v extreme_point_of tau
       ==> drop((L:real^N->real^1) v + y0) =
           (if v = a then &1 else &0) - (if v = w then &1 else &0)`
  ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `{v:real^N}`) THEN
    ASM_REWRITE_TAC[FACE_OF_SING; NOT_INSERT_EMPTY] THEN
    SUBGOAL_THEN `simplex_barycentre {v:real^N} = v` SUBST1_TAC THENL
     [REWRITE_TAC[simplex_barycentre; EXTREME_POINT_OF_SING] THEN
      REWRITE_TAC[SET_RULE `{x:real^N | x = v} = {v}`; VSUM_SING; CARD_SING]
      THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[EXTREME_POINT_OF_SING; IN_SING;
                SET_RULE `{x:real^N | x = v} = {v}`; CARD_SING] THEN
    DISCH_THEN SUBST1_TAC THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `sum {v:real^N | v extreme_point_of tau}
        (\v. mu v * drop((L:real^N->real^1) v + y0)) =
    sum {v | v extreme_point_of tau}
        (\v. (if v = a then mu v else &0) - (if v = w then mu v else &0))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real^N` THEN
    REWRITE_TAC[IN_ELIM_THM] THEN DISCH_TAC THEN ASM_SIMP_TAC[] THEN
    REPEAT(COND_CASES_TAC THEN ASM_REWRITE_TAC[]) THEN
    ASM_MESON_TAC[REAL_ARITH `x * (&1 - &0) = x - &0 /\ x * (&0 - &1) = &0 - x /\
                              x * (&0 - &0) = &0 - &0`];
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_SUB; SUM_DELTA; IN_ELIM_THM]);;
(* Sign of the functional on the open simplex of a chain of faces of tau.  *)

let MOI_FRN_CHAIN_FUNCTIONAL_NEG = prove
 (`!(tau:real^N->bool) a w (L:real^N->real^1) y0 g z.
     (?n. n simplex tau) /\ a extreme_point_of tau /\
     w extreme_point_of tau /\ linear L /\
     (!r. r face_of tau /\ ~(r = {})
          ==> drop(L (simplex_barycentre r) + y0) =
              ((if a IN r then &1 else &0) - (if w IN r then &1 else &0)) /
              &(CARD {v | v extreme_point_of r})) /\
     moi_bar_chain {r | r face_of tau} g /\ ~(g = {}) /\
     w IN INTERS g /\ ~(a IN INTERS g) /\
     z IN relative_interior (convex hull (IMAGE simplex_barycentre g))
     ==> drop(L z + y0) < &0`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:int`) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fval") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_complex {r:real^N->bool | r face_of tau}` ASSUME_TAC
  THENL [ASM_MESON_TAC[MOI_FMB_FACE_COMPLEX; MOI_BAR_SIMPLICIAL_COMPLEX];
         ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN g ==> r face_of tau /\ ~(r = {})`
  (LABEL_TAC "gface") THENL
   [UNDISCH_TAC `moi_bar_chain {r:real^N->bool | r face_of tau} g` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{r:real^N->bool | r face_of tau}`;
                 `g:(real^N->bool)->bool`] MOI_FRN_CHAIN_MIN) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = INTERS (g:(real^N->bool)->bool)` THEN STRIP_TAC THEN
  USE_THEN "gface" (fun th ->
    MP_TAC(MATCH_MP th (ASSUME `(m:real^N->bool) IN g`))) THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!r:real^N->bool. r face_of tau /\ ~(r = {})
        ==> &0 < &(CARD {v:real^N | v extreme_point_of r})`
  (LABEL_TAC "cardpos") THENL
   [X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    REWRITE_TAC[REAL_OF_NUM_LT; LT_NZ] THEN
    SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` MP_TAC THENL
     [MP_TAC(ISPECL [`n:int`; `tau:real^N->bool`; `r:real^N->bool`]
        SIMPLEX_FACE_OF_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(STRIP_ASSUME_TAC o MATCH_MP MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
    SUBGOAL_THEN `FINITE {v:real^N | v extreme_point_of r}` ASSUME_TAC THENL
     [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN DISCH_TAC THEN
    ASM_MESON_TAC[CONVEX_HULL_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `~affine_dependent (IMAGE simplex_barycentre (g:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
    EXISTS_TAC `{r:real^N->bool | r face_of tau}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC
   `(z:real^N) IN relative_interior
      (convex hull IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real^N->real`
    (CONJUNCTS_THEN2 (LABEL_TAC "mupos") STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `FINITE (IMAGE simplex_barycentre (g:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain {r:real^N->bool | r face_of tau} g` THEN
    SIMP_TAC[moi_bar_chain; FINITE_IMAGE];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:real^N->real^1`; `y0:real^1`;
                 `IMAGE simplex_barycentre (g:(real^N->bool)->bool)`;
                 `mu:real^N->real`; `\p:real^N. p`] MOI_FRN_AFFINE_VSUM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[DROP_VSUM; o_DEF; DROP_CMUL] THEN
  SUBGOAL_THEN
   `&0 = sum (IMAGE simplex_barycentre (g:(real^N->bool)->bool)) (\p. &0)`
  SUBST1_TAC THENL [REWRITE_TAC[SUM_0]; ALL_TAC] THEN
  MATCH_MP_TAC SUM_LT THEN REWRITE_TAC[FORALL_IN_IMAGE; EXISTS_IN_IMAGE] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN CONJ_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    USE_THEN "gface" (fun th ->
      MP_TAC(MATCH_MP th (ASSUME `(r:real^N->bool) IN g`))) THEN STRIP_TAC THEN
    USE_THEN "fval" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(r:real^N->bool) face_of tau`)
            (ASSUME `~(r:real^N->bool = {})`)))) THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(w:real^N) IN r` (fun th -> REWRITE_TAC[th]) THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC(REAL_ARITH `&0 <= x * --y ==> x * y <= &0`) THEN
    MATCH_MP_TAC REAL_LE_MUL THEN CONJ_TAC THENL
     [MATCH_MP_TAC REAL_LT_IMP_LE THEN USE_THEN "mupos" MATCH_MP_TAC THEN
      REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LE_MUL THEN REWRITE_TAC[REAL_LE_INV_EQ; REAL_POS] THEN
    COND_CASES_TAC THEN REAL_ARITH_TAC;
    EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "fval" (fun th -> MP_TAC(MATCH_MP th
      (CONJ (ASSUME `(m:real^N->bool) face_of tau`)
            (ASSUME `~(m:real^N->bool = {})`)))) THEN
    DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC(REAL_ARITH `&0 < x * --y ==> x * y < &0`) THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [USE_THEN "mupos" MATCH_MP_TAC THEN REWRITE_TAC[IN_IMAGE] THEN
      EXISTS_TAC `m:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[real_div; GSYM REAL_MUL_LNEG] THEN
    MATCH_MP_TAC REAL_LT_MUL THEN CONJ_TAC THENL
     [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
      REWRITE_TAC[REAL_LT_INV_EQ] THEN USE_THEN "cardpos" MATCH_MP_TAC THEN
      CONJ_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;
let MOI_FRN_CHAIN_FUNCTIONAL_POS = prove
 (`!(tau:real^N->bool) a w (L:real^N->real^1) y0 g z.
     (?n. n simplex tau) /\ linear L /\
     (!r. r face_of tau /\ ~(r = {})
          ==> drop(L (simplex_barycentre r) + y0) =
              ((if a IN r then &1 else &0) - (if w IN r then &1 else &0)) /
              &(CARD {v | v extreme_point_of r})) /\
     moi_bar_chain {r | r face_of tau} g /\ (!r. r IN g ==> a IN r) /\
     z IN convex hull (IMAGE simplex_barycentre g)
     ==> &0 <= drop(L z + y0)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_TAC `n:int`) MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "fval") STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool)) SUBSET
    {x:real^N | &0 <= drop((L:real^N->real^1) x + y0)}`
  MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; FORALL_IN_IMAGE; IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
      SUBGOAL_THEN `(r:real^N->bool) face_of tau /\ ~(r = {})`
      STRIP_ASSUME_TAC THENL
       [UNDISCH_TAC `moi_bar_chain {r:real^N->bool | r face_of tau} g` THEN
        REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      USE_THEN "fval" (fun th -> REWRITE_TAC[MATCH_MP th
        (CONJ (ASSUME `(r:real^N->bool) face_of tau`)
              (ASSUME `~(r:real^N->bool = {})`))]) THEN
      SUBGOAL_THEN `(a:real^N) IN r` (fun th -> REWRITE_TAC[th]) THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC REAL_LE_DIV THEN REWRITE_TAC[REAL_POS] THEN
      COND_CASES_TAC THEN REAL_ARITH_TAC;
      REWRITE_TAC[convex; IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`x1:real^N`; `x2:real^N`; `u:real`; `v:real`] THEN
      STRIP_TAC THEN
      SUBGOAL_THEN
       `drop((L:real^N->real^1) (u % x1 + v % x2) + y0) =
        u * drop(L x1 + y0) + v * drop(L x2 + y0)`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; DROP_ADD; DROP_CMUL] THEN
        SUBGOAL_THEN `v = &1 - u` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; REAL_ARITH_TAC];
        MATCH_MP_TAC REAL_LE_ADD THEN CONJ_TAC THEN
        MATCH_MP_TAC REAL_LE_MUL THEN ASM_REWRITE_TAC[]]];
    REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[]]);;
(* A point of tau whose largest coordinate is at a vertex of k is in N.    *)

let MOI_FRN_MAX_IMP_NBHD = prove
 (`!(t:(real^N->bool)->bool) l tau mu a.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     tau IN barycentric_subdivision t /\
     (!v. v extreme_point_of tau ==> &0 <= mu v) /\
     sum {v | v extreme_point_of tau} mu = &1 /\
     a extreme_point_of tau /\ a IN UNIONS l /\
     (!v. v extreme_point_of tau ==> mu v <= mu a)
     ==> vsum {v | v extreme_point_of tau} (\v. mu v % v) IN derived_nbhd t l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `c = barycentric_subdivision (t:(real^N->bool)->bool)` THEN
  ABBREV_TAC `k = barycentric_subdivision (l:(real^N->bool)->bool)` THEN
  ABBREV_TAC `y = vsum {v | v extreme_point_of tau} (\v. mu v % (v:real^N))`
  THEN
  SUBGOAL_THEN `?n. n simplex (tau:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  MP_TAC(ISPEC `tau:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex; FACE_OF_SING]; ALL_TAC] THEN
  SUBGOAL_THEN `{a:real^N} IN k` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `a:real^N`] THEN
    ASM_REWRITE_TAC[RELATIVE_INTERIOR_SING; IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex {r:real^N->bool | r face_of tau}` ASSUME_TAC
  THENL [ASM_MESON_TAC[MOI_FMB_FACE_COMPLEX; MOI_BAR_SIMPLICIAL_COMPLEX];
         ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN tau` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
    EXISTS_TAC `mu:real^N->real` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`n:int`; `tau:real^N->bool`; `y:real^N`]
    MOI_BAR_SIMPLEX_COVERED) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g0:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`{r:real^N->bool | r face_of tau}`;
                 `g0:(real^N->bool)->bool`; `y:real^N`]
    MOI_BAR_CHAIN_HULL_RI) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain {r:real^N->bool | r face_of tau} g`
  ASSUME_TAC THENL [ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `(y:real^N) IN relative_interior
        (convex hull IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; RELATIVE_INTERIOR_EMPTY;
                    NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{r:real^N->bool | r face_of tau}`;
                 `g:(real^N->bool)->bool`] MOI_FRN_CHAIN_MIN) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `m = INTERS (g:(real^N->bool)->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN g ==> r face_of tau /\ ~(r = {})`
  (LABEL_TAC "gface") THENL
   [UNDISCH_TAC `moi_bar_chain {r:real^N->bool | r face_of tau} g` THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `(a:real^N) IN m` THENL
   [ASM_SIMP_TAC[MOI_FRN_IN_NBHD] THEN
    EXISTS_TAC `({a:real^N}) INSERT (g:(real^N->bool)->bool)` THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_bar_chain {r:real^N->bool | r face_of tau} g` THEN
      REWRITE_TAC[moi_bar_chain; FINITE_INSERT; INSERT_SUBSET; IN_INSERT] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET] THEN X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
        SUBGOAL_THEN `(r:real^N->bool) face_of tau` MP_TAC THENL
         [ASM SET_TAC[]; ASM_MESON_TAC[moi_bar_complex]];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`r1:real^N->bool`; `r2:real^N->bool`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [EXISTS_TAC `{a:real^N}` THEN ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    MATCH_MP_TAC(SET_RULE `!s t. (y:real^N) IN s /\ s SUBSET t ==> y IN t`) THEN
    EXISTS_TAC `convex hull IMAGE simplex_barycentre (g:(real^N->bool)->bool)`
    THEN CONJ_TAC THENL
     [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
      MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  USE_THEN "gface" (fun th ->
    MP_TAC(MATCH_MP th (ASSUME `(m:real^N->bool) IN g`))) THEN STRIP_TAC THEN
  SUBGOAL_THEN `compact (m:real^N->bool) /\ convex m` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[FACE_OF_IMP_COMPACT; FACE_OF_IMP_CONVEX;
                  SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX];
    ALL_TAC] THEN
  MP_TAC(ISPEC `m:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` ASSUME_TAC) THEN
  SUBGOAL_THEN `(w:real^N) extreme_point_of tau /\ w IN m` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[EXTREME_POINT_OF_FACE]; ALL_TAC] THEN
  SUBGOAL_THEN `~(a:real^N = w)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tau:real^N->bool`; `a:real^N`; `w:real^N`]
    MOI_FRN_FACE_FUNCTIONAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^1`
   (X_CHOOSE_THEN `y0:real^1` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tau:real^N->bool`; `a:real^N`; `w:real^N`;
                 `L:real^N->real^1`; `y0:real^1`; `g:(real^N->bool)->bool`;
                 `y:real^N`] MOI_FRN_CHAIN_FUNCTIONAL_NEG) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tau:real^N->bool`; `a:real^N`; `w:real^N`;
                 `L:real^N->real^1`; `y0:real^1`; `mu:real^N->real`]
    MOI_FRN_FUNCTIONAL_COMBINATION) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(mu:real^N->real) w <= mu a` MP_TAC THENL
   [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ASM_REAL_ARITH_TAC]);;
(* Conversely, at a point of N in tau the largest coordinate is attained at *)
(* a vertex of k.                                                            *)

let MOI_FRN_NBHD_IMP_MAX = prove
 (`!(t:(real^N->bool)->bool) l tau mu.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     tau IN barycentric_subdivision t /\
     (!v. v extreme_point_of tau ==> &0 <= mu v) /\
     sum {v | v extreme_point_of tau} mu = &1 /\
     vsum {v | v extreme_point_of tau} (\v. mu v % v) IN derived_nbhd t l
     ==> ?a. a extreme_point_of tau /\ a IN UNIONS l /\
             !v. v extreme_point_of tau ==> mu v <= mu a`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `y = vsum {v | v extreme_point_of tau} (\v. mu v % (v:real^N))`
  THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `y:real^N`] MOI_FRN_IN_NBHD) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `c = barycentric_subdivision (t:(real^N->bool)->bool)` THEN
  ABBREV_TAC `k = barycentric_subdivision (l:(real^N->bool)->bool)` THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?n. n simplex (tau:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  MP_TAC(ISPEC `tau:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; STRIP_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN tau` ASSUME_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC RAND_CONV [th]) THEN
    REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
    EXISTS_TAC `mu:real^N->real` THEN ASM_REWRITE_TAC[IN_ELIM_THM] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                 `y:real^N`] MOI_BAR_CHAIN_HULL_RI) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain c (g:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC
     `(y:real^N) IN relative_interior
        (convex hull IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; RELATIVE_INTERIOR_EMPTY;
                    NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(f:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
    MOI_BAR_CHAIN_MAX) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `sg = UNIONS (g:(real^N->bool)->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN relative_interior sg` ASSUME_TAC THENL
   [EXPAND_TAC "sg" THEN MATCH_MP_TAC MOI_BAR_CHAIN_RI_MAX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(sg:real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(sg:real^N->bool) face_of tau` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC(SET_RULE `(s:real^N->bool) SUBSET t INTER s ==> s SUBSET t`)
    THEN MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
    EXISTS_TAC `sg:real^N->bool` THEN REWRITE_TAC[SUBSET_REFL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain {r:real^N->bool | r face_of tau} g`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `moi_bar_chain c (g:(real^N->bool)->bool)`) THEN
    REWRITE_TAC[moi_bar_chain; SUBSET; IN_ELIM_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN X_GEN_TAC `r:real^N->bool` THEN DISCH_TAC THEN
    MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `sg:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN EXPAND_TAC "sg" THEN
    MATCH_MP_TAC MOI_BAR_CHAIN_FACE_OF_MAX THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_FRN_CHAIN_MIN) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `mf = INTERS (f:(real^N->bool)->bool)` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(mf:real^N->bool) IN c /\ ~(mf = {}) /\ (?n. n simplex mf)`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_ELEMENT THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(mf:real^N->bool) SUBSET UNIONS l` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS k = UNIONS (l:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `s:real^N->bool` THEN
    CONJ_TAC THENL [ASM_SIMP_TAC[]; ASM SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPEC `mf:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  SUBGOAL_THEN `(a:real^N) IN mf` ASSUME_TAC THENL
   [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
  SUBGOAL_THEN `(mf:real^N->bool) face_of tau` ASSUME_TAC THENL
   [MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `sg:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(sg:real^N->bool) IN f` ASSUME_TAC THENL
     [ASM SET_TAC[]; ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  EXISTS_TAC `a:real^N` THEN
  SUBGOAL_THEN `(a:real^N) extreme_point_of tau` ASSUME_TAC THENL
   [ASM_MESON_TAC[EXTREME_POINT_OF_FACE]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  ASM_CASES_TAC `v:real^N = a` THENL
   [ASM_REWRITE_TAC[REAL_LE_REFL]; ALL_TAC] THEN
  MP_TAC(ISPECL [`tau:real^N->bool`; `a:real^N`; `v:real^N`]
    MOI_FRN_FACE_FUNCTIONAL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^1`
   (X_CHOOSE_THEN `y0:real^1` STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`tau:real^N->bool`; `a:real^N`; `v:real^N`;
                 `L:real^N->real^1`; `y0:real^1`; `g:(real^N->bool)->bool`;
                 `y:real^N`] MOI_FRN_CHAIN_FUNCTIONAL_POS) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`tau:real^N->bool`; `a:real^N`; `v:real^N`;
                 `L:real^N->real^1`; `y0:real^1`; `mu:real^N->real`]
    MOI_FRN_FUNCTIONAL_COMBINATION) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Vertex links of the derived neighbourhood complex N' at its              *)
(* vertices b(tau) (tau in c meeting UNIONS l): equal to the links in the   *)
(* second derived when tau is in k, and to the links in the closed star of  *)
(* the vertex a of c when UNIONS l meets tau in the single vertex a.        *)
(* ========================================================================= *)

(* A barycentre b(s) lying in the hull of the barycentres of a chain f is  *)
(* one of its vertices: s is in f.                                          *)

let MOI_FRN_BARYCENTRE_IN_CHAIN_HULL = prove
 (`!(c:(real^N->bool)->bool) f s.
     moi_bar_complex c /\ moi_bar_chain c f /\ s IN c /\ ~(s = {}) /\
     simplex_barycentre s IN convex hull (IMAGE simplex_barycentre f)
     ==> s IN f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_chain c {s:real^N->bool}` ASSUME_TAC THENL
   [REWRITE_TAC[moi_bar_chain; FINITE_SING; SING_SUBSET; IN_SING] THEN
    ASM_MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                 `{s:real^N->bool}`] MOI_BAR_CHAIN_HULL_INTER) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING] THEN
  ASM_CASES_TAC `(s:real^N->bool) IN f` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `f INTER {s:real^N->bool} = {}` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY] THEN ASM SET_TAC[]);;

let MOI_FRN_NBHD_COMPLEX_VERTEX_IMP = prove
 (`!(t:(real^N->bool)->bool) l w.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     {w} IN derived_nbhd_complex t l
     ==> ?s. s IN barycentric_subdivision t /\ ~(s = {}) /\
             ~(s INTER UNIONS l = {}) /\ w = simplex_barycentre s`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `{w:real^N} IN derived_nbhd_complex t l` THEN
  ASM_SIMP_TAC[MOI_FRN_IN_NBHD_COMPLEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `~affine_dependent (IMAGE simplex_barycentre (f:(real^N->bool)->bool))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
    EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `{w:real^N} face_of convex hull IMAGE simplex_barycentre f` THEN
  ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `cc:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `cc = {w:real^N}` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[GSYM CONVEX_HULL_EQ_SING] THEN
    FIRST_ASSUM(ACCEPT_TAC o SYM);
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN IMAGE simplex_barycentre f` MP_TAC THENL
   [UNDISCH_TAC `cc SUBSET IMAGE simplex_barycentre (f:(real^N->bool)->bool)`
    THEN REWRITE_TAC[ASSUME `cc = {w:real^N}`; SING_SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `p:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(p:real^N->bool) IN barycentric_subdivision t /\ ~(p = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(r:real^N->bool) SUBSET UNIONS l` ASSUME_TAC THENL
   [UNDISCH_TAC `UNIONS (barycentric_subdivision l) =
                 UNIONS (l:(real^N->bool)->bool)` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `(r:real^N->bool) IN k ==> r SUBSET UNIONS k`)
    THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(r:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N->bool) SUBSET r \/ r SUBSET p` MP_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  MAP_EVERY UNDISCH_TAC
   [`~(p:real^N->bool = {})`; `~(r:real^N->bool = {})`;
    `(r:real^N->bool) SUBSET UNIONS l`] THEN
  SET_TAC[]);;
let MOI_FRN_NBHD_COMPLEX_VERTEX_EXISTS = prove
 (`!(t:(real^N->bool)->bool) l s.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     s IN barycentric_subdivision t /\ ~(s = {}) /\ ~(s INTER UNIONS l = {})
     ==> {simplex_barycentre s} IN derived_nbhd_complex t l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `s:real^N->bool`] MOI_FRN_FULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `moi_bar_chain (barycentric_subdivision t)
      {s INTER UNIONS l, s:real^N->bool}`
  ASSUME_TAC THENL
   [REWRITE_TAC[moi_bar_chain; FINITE_INSERT; FINITE_SING; INSERT_SUBSET;
                SING_SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision l)
                     (barycentric_subdivision t:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
      REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL; INTER_SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `{s INTER UNIONS l, s:real^N->bool}`]
    MOI_FRN_CHAIN_IN_NBHD_COMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `s INTER UNIONS l:real^N->bool` THEN
    ASM_REWRITE_TAC[IN_INSERT];
    DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT2) THEN
    REWRITE_TAC[IN_INSERT]]);;
(* A simplex of t'' through a vertex b(tau) with tau in k meets UNIONS l, so *)
(* it and its faces are in N'.                                              *)

let MOI_FRN_THROUGH_K_IN_NBHD_COMPLEX = prove
 (`!(t:(real^N->bool)->bool) l tau r s.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     tau IN barycentric_subdivision l /\ ~(tau = {}) /\
     r IN barycentric_subdivision (barycentric_subdivision t) /\
     simplex_barycentre tau IN r /\ s face_of r
     ==> s IN derived_nbhd_complex t l`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(tau:real^N->bool) IN barycentric_subdivision t` ASSUME_TAC
  THENL [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC
   `(r:real^N->bool) IN barycentric_subdivision (barycentric_subdivision t)` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  SUBGOAL_THEN `(tau:real^N->bool) IN g` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_BARYCENTRE_IN_CHAIN_HULL THEN
    EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `barycentric_subdivision l:(real^N->bool)->bool`;
                 `g:(real^N->bool)->bool`] MOI_FRN_CHAIN_HULL_MEETS) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  EXISTS_TAC `tau:real^N->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_FRN_LINK_INNER = prove
 (`!(t:(real^N->bool)->bool) l tau.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     tau IN barycentric_subdivision l /\ ~(tau = {})
     ==> simplicial_link (derived_nbhd_complex t l) (simplex_barycentre tau) =
         simplicial_link (barycentric_subdivision (barycentric_subdivision t))
                         (simplex_barycentre tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[simplicial_link; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
      MOI_FDN_DERIVED_NBHD_COMPLEX_SUBCOMPLEX) THEN
    ASM_REWRITE_TAC[simplicial_subcomplex] THEN SET_TAC[];
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC))) THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FRN_THROUGH_K_IN_NBHD_COMPLEX THEN
      MAP_EVERY EXISTS_TAC [`tau:real^N->bool`; `r:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FRN_THROUGH_K_IN_NBHD_COMPLEX THEN
      MAP_EVERY EXISTS_TAC [`tau:real^N->bool`; `r:real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC
       `(r:real^N->bool) IN barycentric_subdivision (barycentric_subdivision t)`
      THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      MESON_TAC[FACE_OF_REFL; CONVEX_CONVEX_HULL]]]);;
let MOI_FRN_BARYCENTRE_SING = prove
 (`!a:real^N. simplex_barycentre {a} = a`,
  GEN_TAC THEN REWRITE_TAC[simplex_barycentre; EXTREME_POINT_OF_SING] THEN
  REWRITE_TAC[SET_RULE `{x:real^N | x = a} = {a}`; VSUM_SING; CARD_SING] THEN
  VECTOR_ARITH_TAC);;

(* At a vertex b(tau) where UNIONS l meets tau in the single vertex a, the  *)
(* link in N' is the link in the closed star of a in t''.                    *)

let MOI_FRN_LINK_SINGLE = prove
 (`!(t:(real^N->bool)->bool) l tau a.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     tau IN barycentric_subdivision t /\ tau INTER UNIONS l = {a} /\
     ~(tau SUBSET UNIONS l)
     ==> simplicial_link (derived_nbhd_complex t l) (simplex_barycentre tau) =
         simplicial_link
           (moi_fm3_cstar (barycentric_subdivision (barycentric_subdivision t)) a)
           (simplex_barycentre tau)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `tau:real^N->bool`] MOI_FRN_FULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{a:real^N} IN barycentric_subdivision t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(tau:real^N->bool = {})` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!x r. r IN barycentric_subdivision (barycentric_subdivision t) /\
          (a:real^N) IN r /\ x face_of r
          ==> x IN derived_nbhd_complex t l`
  (LABEL_TAC "thr") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_THROUGH_K_IN_NBHD_COMPLEX THEN
    MAP_EVERY EXISTS_TAC [`{a:real^N}`; `r:real^N->bool`] THEN
    ASM_REWRITE_TAC[MOI_FRN_BARYCENTRE_SING; NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  REWRITE_TAC[simplicial_link; moi_fm3_cstar; EXTENSION; IN_ELIM_THM] THEN
  X_GEN_TAC `s:real^N->bool` THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC))) THEN
    UNDISCH_TAC `(r:real^N->bool) IN derived_nbhd_complex t l` THEN
    REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `R:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(a:real^N) IN R` ASSUME_TAC THENL
     [UNDISCH_TAC
       `(R:real^N->bool) IN barycentric_subdivision (barycentric_subdivision t)`
      THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
      SUBGOAL_THEN `(tau:real^N->bool) IN f` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_FRN_BARYCENTRE_IN_CHAIN_HULL THEN
        EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `!r s. (x:real^N) IN r /\ r SUBSET s ==> x IN s`) THEN
        EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FACE_OF_IMP_SUBSET THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                     `barycentric_subdivision l:(real^N->bool)->bool`;
                     `f:(real^N->bool)->bool`] MOI_FRN_CHAIN_HULL_MEETS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(q:real^N->bool) SUBSET UNIONS l /\ ~(q = {})`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [UNDISCH_TAC `UNIONS (barycentric_subdivision l) =
                       UNIONS (l:(real^N->bool)->bool)` THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN
          MATCH_MP_TAC(SET_RULE `(q:real^N->bool) IN k ==> q SUBSET UNIONS k`)
          THEN ASM_REWRITE_TAC[];
          ASM_MESON_TAC[moi_bar_chain]];
        ALL_TAC] THEN
      SUBGOAL_THEN `(q:real^N->bool) SUBSET tau \/ tau SUBSET q` MP_TAC THENL
       [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
      STRIP_TAC THENL
       [SUBGOAL_THEN `q = {a:real^N}` SUBST_ALL_TAC THENL
         [MAP_EVERY UNDISCH_TAC
           [`(q:real^N->bool) SUBSET tau`; `(q:real^N->bool) SUBSET UNIONS l`;
            `~(q:real^N->bool = {})`;
            `tau INTER UNIONS l = {a:real^N}`] THEN SET_TAC[];
          ALL_TAC] THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE] THEN
        EXISTS_TAC `{a:real^N}` THEN
        ASM_REWRITE_TAC[MOI_FRN_BARYCENTRE_SING];
        MAP_EVERY UNDISCH_TAC
         [`(tau:real^N->bool) SUBSET q`; `(q:real^N->bool) SUBSET UNIONS l`;
          `~((tau:real^N->bool) SUBSET UNIONS l)`] THEN SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(R:real^N->bool) face_of R` ASSUME_TAC THENL
     [MATCH_MP_TAC FACE_OF_REFL THEN
      MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision t):
                       (real^N->bool)->bool`; `R:real^N->bool`]
        MOI_FDN_LF_SIMPLEX) THEN
      ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF];
      ALL_TAC] THEN
    SUBGOAL_THEN `(s:real^N->bool) face_of R` ASSUME_TAC THENL
     [MATCH_MP_TAC FACE_OF_TRANS THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `R:real^N->bool` THEN
      CONJ_TAC THENL
       [EXISTS_TAC `R:real^N->bool` THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `!r s. (x:real^N) IN r /\ r SUBSET s ==> x IN s`) THEN
        EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC FACE_OF_IMP_SUBSET THEN ASM_REWRITE_TAC[]]];
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `T0:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `r:real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `T1:real^N->bool` STRIP_ASSUME_TAC)
          STRIP_ASSUME_TAC)))) THEN
    CONJ_TAC THENL
     [USE_THEN "thr" MATCH_MP_TAC THEN EXISTS_TAC `T0:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN USE_THEN "thr" MATCH_MP_TAC THEN
    EXISTS_TAC `T1:real^N->bool` THEN ASM_REWRITE_TAC[]]);;
(* The closed star of a vertex of a combinatorial 3-manifold with boundary  *)
(* is one (its polyhedron is a cone over a PL 2-sphere or 2-ball).           *)

let MOI_FRN_UNIONS_CSTAR = prove
 (`!(c:(real^N->bool)->bool) a.
     lf_simplicial_complex c /\ {a} IN c /\
     ~(UNIONS (simplicial_link c a) = {})
     ==> UNIONS (moi_fm3_cstar c a) =
         UNIONS {segment [a,y] | y | y IN UNIONS (simplicial_link c a)}`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_UNIONS; moi_fm3_cstar; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `q:real^N->bool`;
                   `x:real^N`] MOI_FM3_IN_STAR) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(f:real^N->bool) face_of q` THEN
      DISCH_THEN(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
      UNDISCH_TAC `(x:real^N) IN f` THEN SET_TAC[];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM]];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM; moi_fm3_cstar] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `sg:real^N->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (is_var o lhs o concl)) THEN
    UNDISCH_TAC `(t:real^N->bool) IN simplicial_link c a` THEN
    REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC))) THEN
    EXISTS_TAC `q:real^N->bool` THEN CONJ_TAC THENL
     [EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC FACE_OF_REFL THEN ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX];
      ALL_TAC] THEN
    SUBGOAL_THEN `segment[a:real^N,y] SUBSET q` MP_TAC THENL
     [MATCH_MP_TAC SEGMENT_SUBSET_CONVEX THEN
      CONJ_TAC THENL [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(t:real^N->bool) face_of q` THEN
      DISCH_THEN(MP_TAC o MATCH_MP FACE_OF_IMP_SUBSET) THEN
      UNDISCH_TAC `(y:real^N) IN t` THEN SET_TAC[];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      ASM_REWRITE_TAC[]]]);;

(* The cone over a PL n-ball from a point seeing it injectively is a PL     *)
(* (n+1)-ball when there is room for an (n+1)-simplex.                      *)

let MOI_FRN_CONE_OVER_BALL = prove
 (`!(X:real^N->bool) v n.
     pl_ball n X /\ pl_polyhedron X /\ ~(v IN X) /\
     (!x y. x IN X /\ y IN X /\ y IN segment [v,x] ==> y = x) /\
     n + 1 <= dimindex(:N)
     ==> pl_ball (n + 1) (UNIONS {segment [v,x] | x IN X})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_ball n (X:real^N->bool)` THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `?v':real^N. ~(v' IN affine hull k)` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `~(s = (:real^N)) ==> ?x. ~(x IN s)`) THEN
    DISCH_TAC THEN
    MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_AFFINE_HULL) THEN
    ASM_REWRITE_TAC[AFF_DIM_UNIV] THEN
    UNDISCH_TAC `&n simplex (k:real^N->bool)` THEN
    REWRITE_TAC[simplex] THEN STRIP_TAC THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    UNDISCH_TAC `n + 1 <= dimindex(:N)` THEN
    REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_ADD] THEN
    UNDISCH_TAC `&(CARD (c:real^N->bool)):int = &n + &1` THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(k:real^N->bool = {}) /\ convex k /\ polytope k`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_EMPTY; SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYTOPE;
                  INT_ARITH `~(&n:int = -- &1)`];
    ALL_TAC] THEN
  REWRITE_TAC[pl_ball] THEN
  EXISTS_TAC `convex hull ((v':real^N) INSERT k)` THEN
  EXISTS_TAC `moi_con_conemap k (v':real^N) v (f:real^N->real^N)` THEN
  EXISTS_TAC `moi_con_conemap X (v:real^N) v' (g:real^N->real^N)` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[GSYM INT_OF_NUM_ADD] THEN
    MATCH_MP_TAC MOI_CON_CONE_SIMPLEX THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_SIMP_TAC[CONVEX_HULL_INSERT_SEGMENTS] THEN
  SUBGOAL_THEN `convex hull k = k:real^N->bool` (fun th -> REWRITE_TAC[th]) THENL
   [ASM_REWRITE_TAC[CONVEX_HULL_EQ]; ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `X:real^N->bool`; `v':real^N`; `v:real^N`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_CON_CONE_MAP) THEN
  ANTS_TAC THENL [ALL_TAC; SIMP_TAC[]] THEN
  ASM_SIMP_TAC[POLYTOPE_IMP_PL_POLYHEDRON] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[HULL_INC; SUBSET];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN STRIP_TAC THEN
  UNDISCH_TAC `(y:real^N) IN segment[v',x]` THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `u = &1` THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  UNDISCH_TAC `~((v':real^N) IN affine hull k)` THEN
  MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  SUBGOAL_THEN `~(&1 - u = &0)` ASSUME_TAC THENL
   [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(&1 - u) % v' = y - u % x:real^N` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN
   `v':real^N = inv(&1 - u) % y + (--(inv(&1 - u) * u)) % x`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `v':real^N = inv(&1 - u) % ((&1 - u) % v')` MP_TAC THENL
     [REWRITE_TAC[VECTOR_MUL_ASSOC] THEN ASM_SIMP_TAC[REAL_MUL_LINV] THEN
      REWRITE_TAC[VECTOR_MUL_LID];
      ALL_TAC] THEN
    DISCH_THEN(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    REWRITE_TAC[ASSUME `(&1 - u) % v' = y - u % x:real^N`] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC(REWRITE_RULE[affine] AFFINE_AFFINE_HULL) THEN
  ASM_SIMP_TAC[HULL_INC] THEN
  UNDISCH_TAC `~(&1 - u = &0)` THEN CONV_TAC REAL_FIELD);;
let MOI_FRN_LINK_SEGMENT = prove
 (`!(c:(real^N->bool)->bool) a.
     lf_simplicial_complex c /\ {a} IN c
     ==> ~(a IN UNIONS (simplicial_link c a)) /\
         !x y. x IN UNIONS (simplicial_link c a) /\
               y IN UNIONS (simplicial_link c a) /\ y IN segment[a,x]
               ==> y = x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~((a:real^N) IN UNIONS (simplicial_link c a))` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN ASM_MESON_TAC[MOI_FM3_LINK_IN]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MAP_EVERY X_GEN_TAC [`x:real^N`; `y:real^N`] THEN
  REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC))) THEN
  ASM_CASES_TAC `u = &1` THENL
   [ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
  ASM_CASES_TAC `u = &0` THENL
   [UNDISCH_TAC `(y:real^N) IN UNIONS (simplicial_link c a)` THEN
    ASM_REWRITE_TAC[VECTOR_ARITH `(&1 - &0) % a + &0 % x:real^N = a`];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `x:real^N`; `y:real^N`;
                 `u:real`] MOI_CMB_LINK_NOT_BETWEEN) THEN
  ASM_REWRITE_TAC[] THEN
  ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `p ==> ~p ==> q`) THEN
  VECTOR_ARITH_TAC);;

let MOI_FRN_BALL_LINK_DIM = prove
 (`!(c:(real^N->bool)->bool) a.
     lf_simplicial_complex c /\ {a} IN c /\
     pl_ball 2 (UNIONS (simplicial_link c a))
     ==> 3 <= dimindex(:N)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_ball 2 (UNIONS (simplicial_link c (a:real^N)))` THEN
  REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `~(k:real^N->bool = {})` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_EMPTY; INT_ARITH `~(&2:int = -- &1)`]; ALL_TAC] THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN simplicial_link c a /\ ~(s = {})`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `pl_homeomorphism (k,UNIONS (simplicial_link c (a:real^N)))
                   (f:real^N->real^N,g)` THEN
    REWRITE_TAC[pl_homeomorphism; homeomorphism] THEN STRIP_TAC THEN
    UNDISCH_TAC `IMAGE (f:real^N->real^N) k = UNIONS (simplicial_link c a)` THEN
    UNDISCH_TAC `~(k:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `z:real^N`) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_UNIONS] THEN
    DISCH_THEN(MP_TAC o SPEC `(f:real^N->real^N) z`) THEN
    MATCH_MP_TAC(TAUT `p /\ (q ==> r) ==> (p <=> q) ==> r`) THEN
    CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`simplicial_link c (a:real^N)`; `k:real^N->bool`;
                 `g:real^N->real^N`; `f:real^N->real^N`; `s:real^N->bool`]
    MOI_FM3_DISK_PURE) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_FM3_LINK_SC] THEN
    ASM_MESON_TAC[PL_HOMEOMORPHISM_SYM; pl_homeomorphism];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tr:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`; `tr:real^N->bool`]
    MOI_FM3_LINK_JOIN) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPEC `convex hull ((a:real^N) INSERT tr)` AFF_DIM_LE_UNIV) THEN
  ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;
let MOI_FRN_CSTAR_CMWB = prove
 (`!(c:(real^N->bool)->bool) a.
     combinatorial_manifold_with_boundary 3 c /\ {a} IN c
     ==> combinatorial_manifold_with_boundary 3 (moi_fm3_cstar c a)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    REWRITE_RULE[combinatorial_manifold_with_boundary]) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`] MOI_FM3_CSTAR) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N`] MOI_FRN_LINK_SEGMENT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (simplicial_link c (a:real^N))) \/
                pl_ball 2 (UNIONS (simplicial_link c a))` ASSUME_TAC THENL
   [UNDISCH_TAC `combinatorial_manifold_with_boundary 3 (c:(real^N->bool)->bool)`
    THEN REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
    DISCH_THEN(MP_TAC o SPEC `a:real^N` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_ball 3 (UNIONS {segment [a:real^N,y] | y | y IN UNIONS (simplicial_link c a)})`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM DISJ_CASES_TAC THENL
     [MP_TAC(ISPECL [`2`; `UNIONS (simplicial_link c (a:real^N))`; `a:real^N`]
        PL_BALL_CONE) THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`UNIONS (simplicial_link c (a:real^N))`; `a:real^N`; `2`]
      MOI_FRN_CONE_OVER_BALL) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_SIMP_TAC[MOI_FM3_LINK_POLYHEDRON] THEN
    TRY(CONJ_TAC THENL [FIRST_ASSUM ACCEPT_TAC; ALL_TAC]) THEN
    MATCH_MP_TAC MOI_FRN_BALL_LINK_DIM THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `a:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(UNIONS (simplicial_link c (a:real^N)) = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC
     `pl_ball 3 (UNIONS {segment [a:real^N,y] | y | y IN UNIONS (simplicial_link c a)})`
    THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `UNIONS {segment [a:real^N,y] | y | y IN {}} = {}` SUBST1_TAC
    THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[pl_ball; pl_homeomorphism; homeomorphism] THEN
    STRIP_TAC THEN UNDISCH_TAC `IMAGE (f:real^N->real^N) k = {}` THEN
    REWRITE_TAC[IMAGE_EQ_EMPTY] THEN
    ASM_MESON_TAC[SIMPLEX_EMPTY; INT_ARITH `~(&3:int = -- &1)`];
    ALL_TAC] THEN
  UNDISCH_TAC
   `pl_ball 3 (UNIONS {segment [a:real^N,y] | y | y IN UNIONS (simplicial_link c a)})`
  THEN REWRITE_TAC[pl_ball] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`moi_fm3_cstar c (a:real^N)`;
                 `IMAGE (f:real^N->real^N) (relative_frontier k)`]
    PL_BALL_TRIANGULATION_BOUNDARY) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_FRN_UNIONS_CSTAR] THEN REWRITE_TAC[pl_cell_with_boundary]
    THEN MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                               `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    SIMP_TAC[]]);;

(* ========================================================================= *)
(* Links of N' at frontier vertices b(tau) where UNIONS l meets             *)
(* tau in two or three vertices: explicit half-space charts built from the  *)
(* barycentric coordinates of tau, with explicit inverses.                  *)
(* ========================================================================= *)

(* The local link criterion of pc_moi_fnd_m3b in a form with an explicit   *)
(* inverse map G.                                                            *)

let MOI_FRN_LINK_BALL_BY_INVERSE = prove
 (`!(d:(real^N->bool)->bool) w W (g:real^N->real^3) (G:real^3->real^N) e d0.
     3 <= dimindex(:N) /\ lf_simplicial_complex d /\ {w} IN d /\
     W SUBSET UNIONS d /\ w IN W /\ &0 < e /\
     (!x. x IN UNIONS d /\ dist(w,x) < e ==> x IN W) /\
     pl_map_on W g /\ (!x. x IN W ==> G(g x) = x) /\ g w = vec 0 /\
     (!x. x IN W ==> &0 <= g x$3) /\
     G continuous at (vec 0) /\ G(vec 0) = w /\ &0 < d0 /\
     (!q. norm q < d0 /\ &0 <= q$3 ==> G q IN W /\ g(G q) = q)
     ==> pl_ball 2 (UNIONS (simplicial_link d w))`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FMB_LOCAL_LINK_BALL THEN
  MAP_EVERY EXISTS_TAC [`W:real^N->bool`; `g:real^N->real^3`] THEN
  ASM_REWRITE_TAC[VEC_COMPONENT] THEN REPEAT CONJ_TAC THENL
   [EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[];
    ASM_MESON_TAC[];
    X_GEN_TAC `e':real` THEN DISCH_TAC THEN
    UNDISCH_TAC `(G:real^3->real^N) continuous at (vec 0)` THEN
    REWRITE_TAC[continuous_at] THEN
    DISCH_THEN(MP_TAC o SPEC `e':real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `min d0 d1:real` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `q:real^3` THEN REWRITE_TAC[DIST_0; REAL_LT_MIN] THEN
    STRIP_TAC THEN EXISTS_TAC `(G:real^3->real^N) q` THEN
    ASM_SIMP_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:real^3`) THEN
    ASM_REWRITE_TAC[DIST_0] THEN ASM_MESON_TAC[DIST_SYM]]);;
(* PL maps into real^3 from three PL real-valued components.                *)

let MOI_FRN_PL_VECTOR3 = prove
 (`!(s:real^N->bool) f1 f2 f3.
     pl_map_on s (\x. lift(f1 x)) /\ pl_map_on s (\x. lift(f2 x)) /\
     pl_map_on s (\x. lift(f3 x))
     ==> pl_map_on s (\x. vector[f1 x; f2 x; f3 x]:real^3)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!i (h:real^N->real). pl_map_on s (\x. lift(h x))
        ==> pl_map_on s (\x. h x % basis i:real^3)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(\x:real^N. h x % basis i:real^3) =
                  (\z:real^1. drop z % basis i) o (\x. lift(h x))`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; o_THM; LIFT_DROP]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^1)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    MP_TAC(ISPECL [`(:real^1)`; `\z:real^1. drop z % basis i:real^3`;
                   `vec 0:real^3`] PL_MAP_ON_AFFINE) THEN
    SIMP_TAC[LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV; VECTOR_ADD_RID; ETA_AX] THEN
    DISCH_THEN MATCH_MP_TAC THEN REWRITE_TAC[linear; DROP_ADD; DROP_CMUL] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x:real^N. vector[f1 x; f2 x; f3 x]:real^3) =
    (\x. (\x. f1 x % basis 1 + f2 x % basis 2) x + f3 x % basis 3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_ADD THEN ASM_SIMP_TAC[] THEN
  MATCH_MP_TAC PL_MAP_ON_ADD THEN ASM_SIMP_TAC[]);;

(* Real-valued PL functions: sums, differences, scalar multiples, max, min. *)

let MOI_FRN_PL_REAL_RULES = prove
 (`!(s:real^N->bool) f g c.
     (pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
      ==> pl_map_on s (\x. lift(f x + g x)) /\
          pl_map_on s (\x. lift(f x - g x)) /\
          pl_map_on s (\x. lift(max (f x) (g x))) /\
          pl_map_on s (\x. lift(min (f x) (g x)))) /\
     (pl_map_on s (\x. lift(f x)) ==> pl_map_on s (\x. lift(c * f x)))`,
  REPEAT GEN_TAC THEN CONJ_TAC THENL
   [STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[LIFT_ADD] THEN MATCH_MP_TAC PL_MAP_ON_ADD THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[LIFT_SUB; VECTOR_SUB] THEN MATCH_MP_TAC PL_MAP_ON_ADD THEN
      ASM_REWRITE_TAC[] THEN
      ONCE_REWRITE_TAC[VECTOR_ARITH `--x:real^1 = --(&1) % x`] THEN
      MATCH_MP_TAC PL_MAP_ON_CMUL THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(f x)`;
                     `\x:real^N. lift(g x)`] PL_MAP_ON_LIFT_MAX) THEN
      ASM_REWRITE_TAC[LIFT_DROP];
      MP_TAC(ISPECL [`s:real^N->bool`; `\x:real^N. lift(f x)`;
                     `\x:real^N. lift(g x)`] PL_MAP_ON_LIFT_MIN) THEN
      ASM_REWRITE_TAC[LIFT_DROP]];
    DISCH_TAC THEN REWRITE_TAC[LIFT_CMUL] THEN
    MATCH_MP_TAC PL_MAP_ON_CMUL THEN ASM_REWRITE_TAC[]]);;

(* Sums over four distinct points.                                           *)

let MOI_FRN_SUM_VSUM_4 = prove
 (`!(v0:real^N) v1 v2 v3 (u:real^N->real).
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v0 = v3) /\ ~(v1 = v2) /\ ~(v1 = v3) /\
     ~(v2 = v3)
     ==> sum {v0,v1,v2,v3} u = u v0 + u v1 + u v2 + u v3 /\
         vsum {v0,v1,v2,v3} (\v. u v % v) =
         u v0 % v0 + u v1 % v1 + u v2 % v2 + u v3 % v3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; REAL_ADD_RID; VECTOR_ADD_RID]);;
(* Affine coordinates of a tetrahedron v0 v1 v2 v3: A sends v0 to 0 and vi *)
(* to basis i; B is its inverse on the affine hull.                         *)

let MOI_FRN_TET_COORDS = prove
 (`!(v0:real^N) v1 v2 v3.
     ~affine_dependent {v0,v1,v2,v3} /\
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v0 = v3) /\ ~(v1 = v2) /\ ~(v1 = v3) /\
     ~(v2 = v3)
     ==> ?A:real^N->real^3.
           (?L y. linear L /\ !x. A x = L x + y) /\
           (!y. A (v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (v3 - v0)) =
                y) /\
           (!x. x IN affine hull {v0,v1,v2,v3}
                ==> v0 + (A x)$1 % (v1 - v0) + (A x)$2 % (v2 - v0) +
                    (A x)$3 % (v3 - v0) = x)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`{v0:real^N,v1,v2,v3}`;
    `\v:real^N. if v = v0 then vec 0 else if v = v1 then basis 1
                else if v = v2 then basis 2 else basis 3:real^3`]
   MOI_REAL_AFFINE_EXTEND_POINTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `L:real^N->real^3` (X_CHOOSE_THEN `y0:real^3`
    STRIP_ASSUME_TAC)) THEN
  EXISTS_TAC `\x:real^N. (L:real^N->real^3) x + y0` THEN
  REWRITE_TAC[] THEN CONJ_TAC THENL
   [MAP_EVERY EXISTS_TAC [`L:real^N->real^3`; `y0:real^3`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(fun th ->
    MP_TAC(SPEC `v0:real^N` th) THEN MP_TAC(SPEC `v1:real^N` th) THEN
    MP_TAC(SPEC `v2:real^N` th) THEN MP_TAC(SPEC `v3:real^N` th)) THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `!y:real^3. (L:real^N->real^3)
       (v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (v3 - v0)) + y0 = y`
  ASSUME_TAC THENL
   [GEN_TAC THEN ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL; LINEAR_SUB] THEN
    SUBGOAL_THEN `(L:real^N->real^3) v1 - L v0 = basis 1 /\
                  L v2 - L v0 = basis 2 /\ L v3 - L v0 = basis 3`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN
      FIRST_X_ASSUM(fun th -> MP_TAC th THEN NO_TAC) ORELSE ALL_TAC THEN
      MAP_EVERY UNDISCH_TAC
       [`(L:real^N->real^3) v0 + y0 = vec 0`;
        `(L:real^N->real^3) v1 + y0 = basis 1`;
        `(L:real^N->real^3) v2 + y0 = basis 2`;
        `(L:real^N->real^3) v3 + y0 = basis 3`] THEN
      VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `(L:real^N->real^3) v0 + y0 = vec 0` THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_ADD_COMPONENT;
                VECTOR_MUL_COMPONENT; VEC_COMPONENT] THEN
    SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[AFFINE_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` MP_TAC) THEN
  ASM_SIMP_TAC[MOI_FRN_SUM_VSUM_4] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `x:real^N = v0 + (vector[u v1; u v2; u v3]:real^3)$1 % (v1 - v0) +
               (vector[u v1; u v2; u v3]:real^3)$2 % (v2 - v0) +
               (vector[u v1; u v2; u v3]:real^3)$3 % (v3 - v0)`
  SUBST1_TAC THENL
   [REWRITE_TAC[VECTOR_3] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM) THEN
    SUBGOAL_THEN `(u:real^N->real) v0 = &1 - u v1 - u v2 - u v3` SUBST1_TAC
    THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ASM_REWRITE_TAC[]]);;

(* Coordinate functions of real^3 are PL, and so are constants.             *)

let MOI_FRN_PL_COMPONENT = prove
 (`!(s:real^N->bool) i c.
     locally_polyhedral s
     ==> pl_map_on s (\y. lift(y$i)) /\ pl_map_on s (\y:real^N. lift c)`,
  REPEAT STRIP_TAC THENL
   [MP_TAC(ISPECL [`s:real^N->bool`; `\y:real^N. lift(y$i)`; `vec 0:real^1`]
      PL_MAP_ON_AFFINE) THEN
    ASM_REWRITE_TAC[VECTOR_ADD_RID; ETA_AX] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT;
                LIFT_ADD; LIFT_CMUL];
    ASM_SIMP_TAC[PL_MAP_ON_CONST]]);;

(* The chart for two vertices v0, v1 of a tetrahedron in UNIONS l.          *)

let moi_frn_psi2 = new_definition
 `moi_frn_psi2 (y:real^3) =
    vector[(&1 - y$1 - y$2 - y$3) - y$1; y$2 - y$3;
           max (&1 - y$1 - y$2 - y$3) (y$1) - max (y$2) (y$3)]:real^3`;;

let moi_frn_phi2 = new_definition
 `moi_frn_phi2 (q:real^3) =
    vector[((&1 + (&2 * q$3 - abs(q$1) + abs(q$2))) / &2 - q$1) / &2;
           ((&1 - (&2 * q$3 - abs(q$1) + abs(q$2))) / &2 + q$2) / &2;
           ((&1 - (&2 * q$3 - abs(q$1) + abs(q$2))) / &2 - q$2) / &2]:real^3`;;

let MOI_FRN_PSI2_PHI2 = prove
 (`(!q. moi_frn_psi2 (moi_frn_phi2 q) = q) /\
   (!y. moi_frn_phi2 (moi_frn_psi2 y) = y)`,
  REWRITE_TAC[moi_frn_psi2; moi_frn_phi2; CART_EQ; DIMINDEX_3; FORALL_3;
              VECTOR_3] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;


let MOI_FRN_PL_LIFT_ADD = prove
 (`!(s:real^N->bool) f g.
     pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
     ==> pl_map_on s (\x. lift(f x + g x))`,
  SIMP_TAC[MOI_FRN_PL_REAL_RULES]);;

let MOI_FRN_PL_LIFT_SUB = prove
 (`!(s:real^N->bool) f g.
     pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
     ==> pl_map_on s (\x. lift(f x - g x))`,
  SIMP_TAC[MOI_FRN_PL_REAL_RULES]);;

let MOI_FRN_PL_LIFT_MAX = prove
 (`!(s:real^N->bool) f g.
     pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
     ==> pl_map_on s (\x. lift(max (f x) (g x)))`,
  SIMP_TAC[MOI_FRN_PL_REAL_RULES]);;

let MOI_FRN_PL_LIFT_MIN = prove
 (`!(s:real^N->bool) f g.
     pl_map_on s (\x. lift(f x)) /\ pl_map_on s (\x. lift(g x))
     ==> pl_map_on s (\x. lift(min (f x) (g x)))`,
  SIMP_TAC[MOI_FRN_PL_REAL_RULES]);;

let MOI_FRN_PL_LIFT_CMUL = prove
 (`!(s:real^N->bool) f c.
     pl_map_on s (\x. lift(f x)) ==> pl_map_on s (\x. lift(c * f x))`,
  SIMP_TAC[MOI_FRN_PL_REAL_RULES]);;

let MOI_FRN_PL_LIFT_ABS = prove
 (`!(s:real^N->bool) f.
     pl_map_on s (\x. lift(f x)) ==> pl_map_on s (\x. lift(abs(f x)))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(\x:real^N. lift(abs(f x))) =
                (\x. lift(max (f x) (--(&1) * f x)))` SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM] THEN GEN_TAC THEN AP_TERM_TAC THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_PL_LIFT_MAX THEN ASM_SIMP_TAC[MOI_FRN_PL_LIFT_CMUL]);;

let MOI_FRN_PL_LIFT_DIV = prove
 (`!(s:real^N->bool) f c.
     pl_map_on s (\x. lift(f x)) ==> pl_map_on s (\x. lift(f x / c))`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[real_div] THEN
  ONCE_REWRITE_TAC[REAL_MUL_SYM] THEN ASM_SIMP_TAC[MOI_FRN_PL_LIFT_CMUL]);;

let MOI_FRN_PL_TAC =
  REPEAT(CONJ_TAC ORELSE
         MATCH_MP_TAC MOI_FRN_PL_LIFT_ADD ORELSE
         MATCH_MP_TAC MOI_FRN_PL_LIFT_SUB ORELSE
         MATCH_MP_TAC MOI_FRN_PL_LIFT_MAX ORELSE
         MATCH_MP_TAC MOI_FRN_PL_LIFT_MIN ORELSE
         MATCH_MP_TAC MOI_FRN_PL_LIFT_ABS ORELSE
         MATCH_MP_TAC MOI_FRN_PL_LIFT_DIV ORELSE
         MATCH_MP_TAC MOI_FRN_PL_LIFT_CMUL) THEN
  ASM_SIMP_TAC[MOI_FRN_PL_COMPONENT; LOCALLY_POLYHEDRAL_OPEN; OPEN_UNIV];;

let MOI_FRN_PSI2_PL = prove
 (`pl_map_on (:real^3) moi_frn_psi2`,
  SUBGOAL_THEN `moi_frn_psi2 =
     (\y. vector[(&1 - y$1 - y$2 - y$3) - y$1; y$2 - y$3;
                 max (&1 - y$1 - y$2 - y$3) (y$1) - max (y$2) (y$3)]:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_frn_psi2]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_PL_VECTOR3 THEN MOI_FRN_PL_TAC);;

let MOI_FRN_PHI2_CONTINUOUS = prove
 (`!x. moi_frn_phi2 continuous at x`,
  GEN_TAC THEN
  SUBGOAL_THEN `pl_map_on (:real^3) moi_frn_phi2` MP_TAC THENL
   [SUBGOAL_THEN `moi_frn_phi2 =
      (\q. vector[((&1 + (&2 * q$3 - abs(q$1) + abs(q$2))) / &2 - q$1) / &2;
             ((&1 - (&2 * q$3 - abs(q$1) + abs(q$2))) / &2 + q$2) / &2;
             ((&1 - (&2 * q$3 - abs(q$1) + abs(q$2))) / &2 - q$2) / &2]:real^3)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_frn_phi2]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FRN_PL_VECTOR3 THEN MOI_FRN_PL_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP PL_MAP_ON_IMP_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]]);;
(* The barycentre and convex combinations in tetrahedron coordinates.       *)

let MOI_FRN_TET_BARYCENTRE = prove
 (`!(v0:real^N) v1 v2 v3.
     ~affine_dependent {v0,v1,v2,v3} /\
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v0 = v3) /\ ~(v1 = v2) /\ ~(v1 = v3) /\
     ~(v2 = v3)
     ==> simplex_barycentre (convex hull {v0,v1,v2,v3}) =
         v0 + (&1 / &4) % (v1 - v0) + (&1 / &4) % (v2 - v0) +
         (&1 / &4) % (v3 - v0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_HULL] THEN
  REWRITE_TAC[barycentre; FINITE_INSERT; FINITE_EMPTY] THEN
  SUBGOAL_THEN `CARD {v0:real^N,v1,v2,v3} = 4` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `\v:real^N. inv(&4)`] MOI_FRN_SUM_VSUM_4) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  VECTOR_ARITH_TAC);;

let moi_frn_tcoef = new_definition
 `moi_frn_tcoef (v0:real^N) (v1:real^N) (v2:real^N) (v3:real^N) (y:real^3) (v:real^N) =
    if v = v0 then &1 - y$1 - y$2 - y$3 else if v = v1 then y$1
    else if v = v2 then y$2 else y$3`;;

let MOI_FRN_TCOEF_VSUM = prove
 (`!(v0:real^N) v1 v2 v3 y.
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v0 = v3) /\ ~(v1 = v2) /\ ~(v1 = v3) /\
     ~(v2 = v3)
     ==> sum {v0,v1,v2,v3} (moi_frn_tcoef v0 v1 v2 v3 y) = &1 /\
         vsum {v0,v1,v2,v3} (\v. moi_frn_tcoef v0 v1 v2 v3 y v % v) =
         v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (v3 - v0) /\
         moi_frn_tcoef v0 v1 v2 v3 y v0 = &1 - y$1 - y$2 - y$3 /\
         moi_frn_tcoef v0 v1 v2 v3 y v1 = y$1 /\
         moi_frn_tcoef v0 v1 v2 v3 y v2 = y$2 /\
         moi_frn_tcoef v0 v1 v2 v3 y v3 = y$3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v1:real^N = v0) /\ ~(v2:real^N = v0) /\ ~(v3:real^N = v0) /\
                ~(v2:real^N = v1) /\ ~(v3:real^N = v1) /\ ~(v3:real^N = v2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `moi_frn_tcoef (v0:real^N) v1 v2 v3 y`] MOI_FRN_SUM_VSUM_4) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN
  ASM_REWRITE_TAC[moi_frn_tcoef] THEN
  CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;
(* The relative interior of a maximal simplex of a locally finite complex  *)
(* is open in the polyhedron.                                                *)

let MOI_FRN_MAXIMAL_RELINT_OPEN = prove
 (`!(c:(real^N->bool)->bool) s.
     lf_simplicial_complex c /\ s IN c /\ (!r. r IN c /\ s SUBSET r ==> r = s)
     ==> open_in (subtopology euclidean (UNIONS c)) (relative_interior s)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `relative_interior s =
    UNIONS c DIFF UNIONS {r:real^N->bool | r IN c /\ ~(r = s)}`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
       [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(s:real^N->bool) SUBSET s INTER r` ASSUME_TAC THENL
       [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `s:real^N->bool` THEN
        REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
         [ASM_MESON_TAC[MOI_FM3_LF_INTER]; ALL_TAC] THEN
        REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
        ALL_TAC] THEN
      UNDISCH_TAC `~(r:real^N->bool = s)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
      REWRITE_TAC[SUBSET; IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `q:real^N->bool`
        STRIP_ASSUME_TAC) ASSUME_TAC) THEN
      SUBGOAL_THEN `q:real^N->bool = s` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
       [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
      ONCE_REWRITE_TAC[TAUT `p <=> ~ ~p`] THEN DISCH_TAC THEN
      SUBGOAL_THEN `?f:real^N->bool. f IN c /\ ~(f = s) /\ x IN f` MP_TAC
      THENL [ALL_TAC; ASM_MESON_TAC[]] THEN
      SUBGOAL_THEN `(x:real^N) IN relative_frontier s` MP_TAC THENL
       [REWRITE_TAC[relative_frontier; IN_DIFF] THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET];
        ALL_TAC] THEN
      SUBGOAL_THEN `polyhedron (s:real^N->bool)` ASSUME_TAC THENL
       [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_POLYHEDRON];
        ALL_TAC] THEN
      ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_POLYHEDRON; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `f:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `f:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(f:real^N->bool) facet_of s` THEN
      REWRITE_TAC[facet_of] THEN STRIP_TAC THEN CONJ_TAC THENL
       [ASM_MESON_TAC[MOI_FM3_LF_FACE]; ALL_TAC] THEN
      DISCH_TAC THEN UNDISCH_TAC `aff_dim(f:real^N->bool) = aff_dim(s:real^N->bool) - &1`
      THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    MATCH_MP_TAC OPEN_IN_DIFF THEN REWRITE_TAC[OPEN_IN_REFL] THEN
    MATCH_MP_TAC MOI_FDN_LF_CLOSED_IN_UNIONS THEN ASM_REWRITE_TAC[] THEN
    SET_TAC[]]);;
(* Coefficients of points of the tetrahedron in the coordinates A.          *)

let MOI_FRN_TET_HULL_COEF = prove
 (`!(v0:real^N) v1 v2 v3 (A:real^N->real^3) x.
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v0 = v3) /\ ~(v1 = v2) /\ ~(v1 = v3) /\
     ~(v2 = v3) /\
     (!y. A (v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (v3 - v0)) = y) /\
     x IN convex hull {v0,v1,v2,v3}
     ==> !v. v IN {v0,v1,v2,v3} ==> &0 <= moi_frn_tcoef v0 v1 v2 v3 (A x) v`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN convex hull {v0,v1,v2,v3}` THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N->real` MP_TAC) THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `u:real^N->real`] MOI_FRN_SUM_VSUM_4) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (ASSUME_TAC o SYM))) THEN
  SUBGOAL_THEN
   `x = v0 + (vector[(u:real^N->real) v1; u v2; u v3]:real^3)$1 % (v1 - v0) +
        (vector[u v1; u v2; u v3]:real^3)$2 % (v2 - v0) +
        (vector[u v1; u v2; u v3]:real^3)$3 % (v3 - v0)`
  ASSUME_TAC THENL
   [REWRITE_TAC[VECTOR_3] THEN
    FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC LAND_CONV [th]) THEN
    SUBGOAL_THEN `(u:real^N->real) v0 = &1 - u v1 - u v2 - u v3` SUBST1_TAC
    THENL [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^N->real^3) x = vector[(u:real^N->real) v1; u v2; u v3]`
  SUBST1_TAC THENL
   [FIRST_X_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v1:real^N = v0) /\ ~(v2:real^N = v0) /\ ~(v3:real^N = v0) /\
                ~(v2:real^N = v1) /\ ~(v3:real^N = v1) /\ ~(v3:real^N = v2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[moi_frn_tcoef; VECTOR_3] THEN
  ASM_MESON_TAC[REAL_ARITH `a + b + c + d = &1 ==> &1 - b - c - d = a`]);;
(* A frontier vertex b(tau) of N' with tau a tetrahedron of c: given an     *)
(* explicit PL homeomorphism psi of real^3 (inverse phi) turning the        *)
(* condition "the largest coordinate is at a vertex in UNIONS l" into       *)
(* psi(y)$3 >= 0, the link of b(tau) in N' is a PL 2-ball.                   *)

let MOI_FRN_TET_FRONTIER_CHART = prove
 (`!(t:(real^N->bool)->bool) l v0 v1 v2 v3 (psi:real^3->real^3) phi.
     combinatorial_manifold_with_boundary 3 t /\ simplicial_subcomplex l t /\
     convex hull {v0,v1,v2,v3} IN barycentric_subdivision t /\
     ~affine_dependent {v0,v1,v2,v3} /\
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v0 = v3) /\ ~(v1 = v2) /\ ~(v1 = v3) /\
     ~(v2 = v3) /\ v0 IN UNIONS l /\
     pl_map_on (:real^3) psi /\ (!q. psi(phi q) = q) /\ (!y. phi(psi y) = y) /\
     (!x. phi continuous at x) /\
     phi(vec 0) = vector[&1 / &4; &1 / &4; &1 / &4] /\
     (!y. (!v. v IN {v0,v1,v2,v3} ==> &0 <= moi_frn_tcoef v0 v1 v2 v3 y v)
          ==> ((?a. a IN {v0,v1,v2,v3} /\ a IN UNIONS l /\
                    !v. v IN {v0,v1,v2,v3}
                        ==> moi_frn_tcoef v0 v1 v2 v3 y v <=
                            moi_frn_tcoef v0 v1 v2 v3 y a) <=>
               &0 <= (psi y)$3))
     ==> pl_ball 2 (UNIONS (simplicial_link (derived_nbhd_complex t l)
                     (simplex_barycentre (convex hull {v0,v1,v2,v3}))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_X_ASSUM(LABEL_TAC "iff" o check (fun th ->
    try let (v,b) = dest_forall (concl th) in
        type_of v = `:real^3` && is_imp b && is_iff (snd(dest_imp b))
    with Failure _ -> false)) THEN
  SUBGOAL_THEN `CARD {v0:real^N,v1,v2,v3} = 4` ASSUME_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ABBREV_TAC `tau = convex hull {v0:real^N,v1,v2,v3}` THEN
  ABBREV_TAC `V = {v0:real^N,v1,v2,v3}` THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    REWRITE_RULE[combinatorial_manifold_with_boundary]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3
                  (barycentric_subdivision t:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_SIMP_TAC[COMBINATORIAL_WB_BARYCENTRIC]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. v extreme_point_of tau <=> v IN V` ASSUME_TAC THENL
   [MP_TAC(ISPEC `V:real^N->bool`
      EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(tau:real^N->bool) = &3` ASSUME_TAC THENL
   [EXPAND_TAC "tau" THEN ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL;
      AFF_DIM_AFFINE_INDEPENDENT] THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `3 <= dimindex(:N)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `tau:real^N->bool` AFF_DIM_LE_UNIV) THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[INT_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!r:real^N->bool. r IN barycentric_subdivision t /\ tau SUBSET r ==> r = tau`
  ASSUME_TAC THENL
   [X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(tau:real^N->bool) face_of r` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
      EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_CASES_TAC `tau:real^N->bool = r` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`tau:real^N->bool`; `r:real^N->bool`] FACE_OF_AFF_DIM_LT) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
    MP_TAC(ISPEC `barycentric_subdivision t:(real^N->bool)->bool` CM_WB_DIM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `r:real^N->bool`) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `tau:real^N->bool`] MOI_FRN_MAXIMAL_RELINT_OPEN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  ABBREV_TAC `w = simplex_barycentre (tau:real^N->bool)` THEN
  SUBGOAL_THEN `(w:real^N) IN relative_interior tau` ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (tau:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
    EXPAND_TAC "w" THEN MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "tau" THEN EXPAND_TAC "V" THEN
    REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e. &0 < e /\
                    !x:real^N. x IN UNIONS t /\ dist(w,x) < e
                               ==> x IN relative_interior tau`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean
       (UNIONS (t:(real^N->bool)->bool))) (relative_interior (tau:real^N->bool))`
    THEN REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `ball(w:real^N,e) INTER UNIONS t SUBSET relative_interior tau` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `v3:real^N`]
    MOI_FRN_TET_COORDS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A:real^N->real^3` (CONJUNCTS_THEN2
    (LABEL_TAC "Aaff") (CONJUNCTS_THEN2 (LABEL_TAC "AB") (LABEL_TAC "BA"))))
  THEN
  ABBREV_TAC `B = \y:real^3. v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) +
                             y$3 % (v3 - (v0:real^N))` THEN
  SUBGOAL_THEN `!y:real^3. (A:real^N->real^3) (B y) = y` (LABEL_TAC "AB'") THENL
   [EXPAND_TAC "B" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!x:real^N. x IN tau ==> (B:real^3->real^N) (A x) = x`
  (LABEL_TAC "BA'") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "B" THEN REWRITE_TAC[] THEN
    USE_THEN "BA" MATCH_MP_TAC THEN
    MP_TAC(ISPEC `V:real^N->bool` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `w = (B:real^3->real^N) (vector[&1 / &4; &1 / &4; &1 / &4])`
  ASSUME_TAC THENL
   [EXPAND_TAC "B" THEN EXPAND_TAC "w" THEN EXPAND_TAC "tau" THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[VECTOR_3] THEN
    MATCH_MP_TAC MOI_FRN_TET_BARYCENTRE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d0. &0 < d0 /\
         !q. norm q < d0
             ==> !v. v IN V
                     ==> &0 < moi_frn_tcoef v0 v1 v2 v3 ((phi:real^3->real^3) q)
                                                 (v:real^N)`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^3` o check (fun th ->
      can (find_term (fun t -> t = `at:real^3->(real^3)net`)) (concl th))) THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `&1 / &20`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `d0:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `d0:real` THEN ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `q:real^3` THEN DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `q:real^3`) THEN
    ASM_REWRITE_TAC[DIST_0] THEN REWRITE_TAC[dist] THEN DISCH_TAC THEN
    SUBGOAL_THEN
     `!i. 1 <= i /\ i <= 3
          ==> abs(((phi:real^3->real^3) q)$i - &1 / &4) < &1 / &20`
    ASSUME_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
      EXISTS_TAC `norm((phi:real^3->real^3) q - phi(vec 0))` THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`(phi:real^3->real^3) q - phi(vec 0)`; `i:num`]
        COMPONENT_LE_NORM) THEN
      ASM_REWRITE_TAC[DIMINDEX_3; VECTOR_SUB_COMPONENT] THEN
      SUBGOAL_THEN `(vector[&1 / &4; &1 / &4; &1 / &4]:real^3)$i = &1 / &4`
      SUBST1_TAC THENL
       [SUBGOAL_THEN `i = 1 \/ i = 2 \/ i = 3` MP_TAC THENL
         [ASM_ARITH_TAC; STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_3]];
        REWRITE_TAC[]];
      ALL_TAC] THEN
    FIRST_X_ASSUM(fun th -> MP_TAC(SPEC `1` th) THEN MP_TAC(SPEC `2` th) THEN
      MP_TAC(SPEC `3` th)) THEN
    CONV_TAC NUM_REDUCE_CONV THEN
    SUBGOAL_THEN `~(v1:real^N = v0) /\ ~(v2:real^N = v0) /\ ~(v3:real^N = v0) /\
                  ~(v2:real^N = v1) /\ ~(v3:real^N = v1) /\ ~(v3:real^N = v2)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    REPEAT DISCH_TAC THEN X_GEN_TAC `v:real^N` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[moi_frn_tcoef] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `UNIONS (derived_nbhd_complex t l) = derived_nbhd t (l:(real^N->bool)->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FDN_UNIONS_DERIVED_NBHD_COMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `derived_nbhd t l SUBSET UNIONS (t:(real^N->bool)->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FDN_DERIVED_NBHD_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `{w:real^N} IN derived_nbhd_complex t l` ASSUME_TAC THENL
   [EXPAND_TAC "w" THEN MATCH_MP_TAC MOI_FRN_NBHD_COMPLEX_VERTEX_EXISTS THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "tau" THEN EXPAND_TAC "V" THEN
      REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
      EXISTS_TAC `v0:real^N` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "tau" THEN MATCH_MP_TAC HULL_INC THEN EXPAND_TAC "V" THEN
      REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN derived_nbhd t l` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && is_comb(lhs(concl th)) &&
      can (find_term ((=) `derived_nbhd_complex:((real^N->bool)->bool)->
                ((real^N->bool)->bool)->(real^N->bool)->bool`)) (lhs(concl th)))) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{w:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  ABBREV_TAC `W = derived_nbhd t l INTER relative_interior (tau:real^N->bool)` THEN
  SUBGOAL_THEN `locally_polyhedral (W:real^N->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean (UNIONS t))
                   (relative_interior (tau:real^N->bool))` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `O:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `W = derived_nbhd t l INTER (O:real^N->bool)` SUBST1_TAC THENL
     [EXPAND_TAC "W" THEN ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && is_comb(lhs(concl th)) &&
      can (find_term ((=) `derived_nbhd_complex:((real^N->bool)->bool)->
                ((real^N->bool)->bool)->(real^N->bool)->bool`)) (lhs(concl th)))) THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_LF_COMPLEX THEN
    ASM_SIMP_TAC[MOI_FDN_DERIVED_NBHD_COMPLEX_LF];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_LINK_BALL_BY_INVERSE THEN
  MAP_EVERY EXISTS_TAC
   [`W:real^N->bool`; `(psi:real^3->real^3) o (A:real^N->real^3)`;
    `(B:real^3->real^N) o (phi:real^3->real^3)`; `e:real`; `d0:real`] THEN
  FIRST_ASSUM(fun th0 -> REWRITE_TAC[check (fun th ->
      is_eq(concl th) && is_comb(lhs(concl th)) &&
      can (find_term ((=) `derived_nbhd_complex:((real^N->bool)->bool)->
                ((real^N->bool)->bool)->(real^N->bool)->bool`)) (lhs(concl th)))
      th0]) THEN
  REWRITE_TAC[o_THM] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[MOI_FDN_DERIVED_NBHD_COMPLEX_LF]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [EXPAND_TAC "W" THEN SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [EXPAND_TAC "W" THEN REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN EXPAND_TAC "W" THEN
    REWRITE_TAC[IN_INTER] THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [USE_THEN "Aaff" (X_CHOOSE_THEN `LA:real^N->real^3` (X_CHOOSE_THEN
      `yA:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(A:real^N->real^3) = (\x. LA x + yA)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[ASSUME `!y:real^3. (phi:real^3->real^3) (psi y) = y`] THEN
    USE_THEN "BA'" MATCH_MP_TAC THEN
    MP_TAC(ISPEC `tau:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(x:real^N) IN W` THEN EXPAND_TAC "W" THEN SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ASSUME `w = (B:real^3->real^N) (vector[&1 / &4; &1 / &4; &1 / &4])`]
    THEN USE_THEN "AB'" (fun th -> REWRITE_TAC[th]) THEN
    UNDISCH_TAC `!q:real^3. (psi:real^3->real^3) ((phi:real^3->real^3) q) = q`
    THEN DISCH_THEN(MP_TAC o SPEC `vec 0:real^3`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N | v extreme_point_of tau} = V` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN tau /\ x IN derived_nbhd t l` STRIP_ASSUME_TAC
    THENL
     [MP_TAC(ISPEC `tau:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(x:real^N) IN W` THEN EXPAND_TAC "W" THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                   `A:real^N->real^3`; `x:real^N`] MOI_FRN_TET_HULL_COEF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[];
      DISCH_THEN(ASSUME_TAC o REWRITE_RULE[ASSUME `{v0:real^N,v1,v2,v3} = V`])]
    THEN
    USE_THEN "iff" (MP_TAC o SPEC `(A:real^N->real^3) x`) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                   `(A:real^N->real^3) x`] MOI_FRN_TCOEF_VSUM) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT1)) THEN
    DISCH_THEN(fun th -> SUBGOAL_THEN
     `vsum V (\v. moi_frn_tcoef v0 v1 v2 v3 ((A:real^N->real^3) x) v % v) =
      (x:real^N)` ASSUME_TAC THENL
     [REWRITE_TAC[th] THEN USE_THEN "BA" MATCH_MP_TAC THEN
      MP_TAC(ISPEC `V:real^N->bool` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      ASM SET_TAC[];
      ALL_TAC]) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `tau:real^N->bool`;
                   `moi_frn_tcoef (v0:real^N) v1 v2 v3 ((A:real^N->real^3) x)`]
      MOI_FRN_NBHD_IMP_MAX)
    THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "B" THEN
    SUBGOAL_THEN
     `(\y:real^3. v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (v3 - v0)) =
      (\y. v0 + (\y. y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (v3 - v0)) y)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
    MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
    REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `q:real^3` THEN STRIP_TAC THEN
  USE_THEN "AB'" (fun th -> REWRITE_TAC[th]) THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `!v:real^N. v IN V
                  ==> &0 < moi_frn_tcoef v0 v1 v2 v3 ((phi:real^3->real^3) q) v`
  ASSUME_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `(phi:real^3->real^3) q`] MOI_FRN_TCOEF_VSUM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o CONJUNCT1)) THEN
  DISCH_THEN(fun th -> SUBGOAL_THEN
   `vsum V (\v. moi_frn_tcoef v0 v1 v2 v3 ((phi:real^3->real^3) q) v % v) =
    (B:real^3->real^N) (phi q)` ASSUME_TAC THENL
   [REWRITE_TAC[th] THEN EXPAND_TAC "B" THEN REWRITE_TAC[]; ALL_TAC]) THEN
  EXPAND_TAC "W" THEN REWRITE_TAC[IN_INTER] THEN CONJ_TAC THENL
   [USE_THEN "iff" (MP_TAC o SPEC `(phi:real^3->real^3) q`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[REAL_LT_IMP_LE]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `tau:real^N->bool`;
                   `moi_frn_tcoef (v0:real^N) v1 v2 v3 ((phi:real^3->real^3) q)`;
                   `a:real^N`] MOI_FRN_MAX_IMP_NBHD) THEN
    ASM_SIMP_TAC[REAL_LT_IMP_LE];
    EXPAND_TAC "tau" THEN
    ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
    EXISTS_TAC `moi_frn_tcoef (v0:real^N) v1 v2 v3 ((phi:real^3->real^3) q)` THEN
    ASM_REWRITE_TAC[]]);;
(* The chart for three vertices v0, v1, v2 of a tetrahedron in UNIONS l.     *)

let moi_frn_psi3 = new_definition
 `moi_frn_psi3 (y:real^3) =
    vector[(&1 - y$1 - y$2 - y$3) - y$1; y$1 - y$2;
           max (&1 - y$1 - y$2 - y$3) (max (y$1) (y$2)) - y$3]:real^3`;;

let moi_frn_phi3 = new_definition
 `moi_frn_phi3 (q:real^3) =
    vector[(q$3 + &1 - max (q$1 + q$2) (max (q$2) (&0)) - &2 * q$2 - q$1) / &4
           + q$2;
           (q$3 + &1 - max (q$1 + q$2) (max (q$2) (&0)) - &2 * q$2 - q$1) / &4;
           &1 - &3 * ((q$3 + &1 - max (q$1 + q$2) (max (q$2) (&0)) -
                       &2 * q$2 - q$1) / &4) - &2 * q$2 - q$1]:real^3`;;

let MOI_FRN_PSI3_PHI3 = prove
 (`(!q. moi_frn_psi3 (moi_frn_phi3 q) = q) /\
   (!y. moi_frn_phi3 (moi_frn_psi3 y) = y)`,
  REWRITE_TAC[moi_frn_psi3; moi_frn_phi3; CART_EQ; DIMINDEX_3; FORALL_3;
              VECTOR_3] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let MOI_FRN_PSI3_PL = prove
 (`pl_map_on (:real^3) moi_frn_psi3`,
  SUBGOAL_THEN `moi_frn_psi3 =
     (\y. vector[(&1 - y$1 - y$2 - y$3) - y$1; y$1 - y$2;
           max (&1 - y$1 - y$2 - y$3) (max (y$1) (y$2)) - y$3]:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_frn_psi3]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_PL_VECTOR3 THEN MOI_FRN_PL_TAC);;

let MOI_FRN_PHI3_CONTINUOUS = prove
 (`!x. moi_frn_phi3 continuous at x`,
  GEN_TAC THEN
  SUBGOAL_THEN `pl_map_on (:real^3) moi_frn_phi3` MP_TAC THENL
   [SUBGOAL_THEN `moi_frn_phi3 =
      (\q. vector[(q$3 + &1 - max (q$1 + q$2) (max (q$2) (&0)) - &2 * q$2 - q$1)
                  / &4 + q$2;
           (q$3 + &1 - max (q$1 + q$2) (max (q$2) (&0)) - &2 * q$2 - q$1) / &4;
           &1 - &3 * ((q$3 + &1 - max (q$1 + q$2) (max (q$2) (&0)) -
                       &2 * q$2 - q$1) / &4) - &2 * q$2 - q$1]:real^3)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_frn_phi3]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FRN_PL_VECTOR3 THEN MOI_FRN_PL_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP PL_MAP_ON_IMP_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]]);;

let MOI_FRN_PHI23_ZERO = prove
 (`moi_frn_phi2 (vec 0) = vector[&1 / &4; &1 / &4; &1 / &4] /\
   moi_frn_phi3 (vec 0) = vector[&1 / &4; &1 / &4; &1 / &4]`,
  REWRITE_TAC[moi_frn_phi2; moi_frn_phi3; VEC_COMPONENT] THEN
  REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
  REAL_ARITH_TAC);;
(* A vertex of an affinely independent set is not in the convex hull of     *)
(* other vertices.                                                           *)

let MOI_FRN_VERTEX_NOT_IN_HULL = prove
 (`!(s:real^N->bool) t v.
     ~affine_dependent s /\ v IN s /\ t SUBSET s /\ ~(v IN t)
     ==> ~(v IN convex hull t)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `~affine_dependent (s:real^N->bool)` THEN
  REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `v:real^N` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex hull t SUBSET affine hull (s DELETE (v:real^N))` MP_TAC
  THENL
   [MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `affine hull t:real^N->bool` THEN
    REWRITE_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL] THEN
    MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_FRN_FRONTIER_LINK_TET2 = prove
 (`!(t:(real^N->bool)->bool) l v0 v1 v2 v3.
     combinatorial_manifold_with_boundary 3 t /\ simplicial_subcomplex l t /\
     convex hull {v0,v1,v2,v3} IN barycentric_subdivision t /\
     ~affine_dependent {v0,v1,v2,v3} /\
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v0 = v3) /\ ~(v1 = v2) /\ ~(v1 = v3) /\
     ~(v2 = v3) /\
     convex hull {v0,v1,v2,v3} INTER UNIONS l = convex hull {v0,v1}
     ==> pl_ball 2 (UNIONS (simplicial_link (derived_nbhd_complex t l)
                     (simplex_barycentre (convex hull {v0,v1,v2,v3}))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a:real^N. a IN {v0,v1,v2,v3} /\ a IN UNIONS l <=> a = v0 \/ a = v1`
  ASSUME_TAC THENL
   [GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(a:real^N) IN convex hull {v0,v1}` ASSUME_TAC THENL
       [UNDISCH_TAC `convex hull {v0,v1,v2,v3} INTER UNIONS l =
                     convex hull {v0:real^N,v1}` THEN
        DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN
        ASM_SIMP_TAC[IN_INTER; HULL_INC];
        ALL_TAC] THEN
      ASM_CASES_TAC `a:real^N = v0` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `a:real^N = v1` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`{v0:real^N,v1,v2,v3}`; `{v0:real^N,v1}`; `a:real^N`]
        MOI_FRN_VERTEX_NOT_IN_HULL) THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(a:real^N) IN convex hull {v0,v1}` MP_TAC THENL
       [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
        ALL_TAC] THEN
      SUBGOAL_THEN `(a:real^N) IN {v0,v1,v2,v3}` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_TET_FRONTIER_CHART THEN
  MAP_EVERY EXISTS_TAC [`moi_frn_psi2`; `moi_frn_phi2`] THEN
  ASM_REWRITE_TAC[MOI_FRN_PSI2_PHI2; MOI_FRN_PSI2_PL; MOI_FRN_PHI2_CONTINUOUS;
                  MOI_FRN_PHI23_ZERO] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[CONJ_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `y:real^3`] MOI_FRN_TCOEF_VSUM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_frn_psi2; VECTOR_3] THEN REAL_ARITH_TAC);;
let MOI_FRN_FRONTIER_LINK_TET3 = prove
 (`!(t:(real^N->bool)->bool) l v0 v1 v2 v3.
     combinatorial_manifold_with_boundary 3 t /\ simplicial_subcomplex l t /\
     convex hull {v0,v1,v2,v3} IN barycentric_subdivision t /\
     ~affine_dependent {v0,v1,v2,v3} /\
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v0 = v3) /\ ~(v1 = v2) /\ ~(v1 = v3) /\
     ~(v2 = v3) /\
     convex hull {v0,v1,v2,v3} INTER UNIONS l = convex hull {v0,v1,v2}
     ==> pl_ball 2 (UNIONS (simplicial_link (derived_nbhd_complex t l)
                     (simplex_barycentre (convex hull {v0,v1,v2,v3}))))`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!a:real^N. a IN {v0,v1,v2,v3} /\ a IN UNIONS l <=> a = v0 \/ a = v1 \/ a = v2`
  ASSUME_TAC THENL
   [GEN_TAC THEN EQ_TAC THENL
     [STRIP_TAC THEN
      SUBGOAL_THEN `(a:real^N) IN convex hull {v0,v1,v2}` ASSUME_TAC THENL
       [UNDISCH_TAC `convex hull {v0,v1,v2,v3} INTER UNIONS l =
                     convex hull {v0:real^N,v1,v2}` THEN
        DISCH_THEN(fun th -> REWRITE_TAC[SYM th]) THEN
        ASM_SIMP_TAC[IN_INTER; HULL_INC];
        ALL_TAC] THEN
      ASM_CASES_TAC `a:real^N = v0` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `a:real^N = v1` THEN ASM_REWRITE_TAC[] THEN
      ASM_CASES_TAC `a:real^N = v2` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`{v0:real^N,v1,v2,v3}`; `{v0:real^N,v1,v2}`; `a:real^N`]
        MOI_FRN_VERTEX_NOT_IN_HULL) THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `(a:real^N) IN convex hull {v0,v1,v2}` MP_TAC THENL
       [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
        ALL_TAC] THEN
      SUBGOAL_THEN `(a:real^N) IN {v0,v1,v2,v3}` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
        ALL_TAC] THEN
      ASM SET_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_TET_FRONTIER_CHART THEN
  MAP_EVERY EXISTS_TAC [`moi_frn_psi3`; `moi_frn_phi3`] THEN
  ASM_REWRITE_TAC[MOI_FRN_PSI3_PHI3; MOI_FRN_PSI3_PL; MOI_FRN_PHI3_CONTINUOUS;
                  MOI_FRN_PHI23_ZERO] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
  X_GEN_TAC `y:real^3` THEN REWRITE_TAC[CONJ_ASSOC] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[RIGHT_OR_DISTRIB; EXISTS_OR_THM; UNWIND_THM2] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY] THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `v3:real^N`;
                 `y:real^3`] MOI_FRN_TCOEF_VSUM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[moi_frn_psi3; VECTOR_3] THEN REAL_ARITH_TAC);;

(* ========================================================================= *)
(* Lemmas for the vertex links of N': enumerations of the vertex           *)
(* set of a simplex tau of the first derived and of its face tau INTER      *)
(* UNIONS l, closed stars, vertex counts.                                    *)
(* ========================================================================= *)

(* Enumerations of the vertex set V of tau and of the vertex set W of the  *)
(* face tau INTER UNIONS l.                                                  *)

let MOI_FRN_SETID_22 = prove
 (`!V W (a:real^N) b c d.
     W SUBSET V /\ W = {a,b} /\ V DIFF W = {c,d} ==> V = {a,b,c,d}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `V = W UNION (V DIFF W:real^N->bool)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_FRN_SETID_31 = prove
 (`!V W (a:real^N) b c d.
     W SUBSET V /\ W = {a,b,c} /\ V DIFF W = {d} ==> V = {a,b,c,d}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `V = W UNION (V DIFF W:real^N->bool)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_FRN_SETID_21 = prove
 (`!V W (a:real^N) b c.
     W SUBSET V /\ W = {a,b} /\ V DIFF W = {c} ==> V = {a,b,c}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `V = W UNION (V DIFF W:real^N->bool)` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

(* Enumerations of small vertex sets.                                        *)

let MOI_FRN_SPLIT_VERTS = prove
 (`!(V:real^N->bool) W.
     FINITE V /\ W SUBSET V
     ==> (CARD V = 4 /\ CARD W = 2
          ==> ?v0 v1 v2 v3. V = {v0,v1,v2,v3} /\ W = {v0,v1} /\
                            ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v0 = v3) /\
                            ~(v1 = v2) /\ ~(v1 = v3) /\ ~(v2 = v3)) /\
         (CARD V = 4 /\ CARD W = 3
          ==> ?v0 v1 v2 v3. V = {v0,v1,v2,v3} /\ W = {v0,v1,v2} /\
                            ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v0 = v3) /\
                            ~(v1 = v2) /\ ~(v1 = v3) /\ ~(v2 = v3)) /\
         (CARD V = 3 /\ CARD W = 2
          ==> ?v0 v1 v2. V = {v0,v1,v2} /\ W = {v0,v1} /\
                         ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2)) /\
         (CARD W = 1 ==> ?a. W = {a})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (W:real^N->bool) /\ FINITE (V DIFF W)` STRIP_ASSUME_TAC
  THENL [ASM_MESON_TAC[FINITE_SUBSET; FINITE_DIFF]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD (V DIFF W:real^N->bool) = CARD V - CARD W` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_DIFF]; ALL_TAC] THEN
  REPEAT CONJ_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `(W:real^N->bool) HAS_SIZE 2 /\ (V DIFF W) HAS_SIZE 2` MP_TAC
    THENL [ASM_REWRITE_TAC[HAS_SIZE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(BINOP_CONV HAS_SIZE_CONV)) THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `v0:real^N` (X_CHOOSE_THEN `v1:real^N` STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `v2:real^N` (X_CHOOSE_THEN `v3:real^N` STRIP_ASSUME_TAC)))
    THEN MAP_EVERY EXISTS_TAC [`v0:real^N`; `v1:real^N`; `v2:real^N`; `v3:real^N`]
    THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((v2:real^N) IN W) /\ ~((v3:real^N) IN W) /\
                  (v0:real^N) IN W /\ (v1:real^N) IN W` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(v2:real^N) IN V DIFF W /\ (v3:real^N) IN V DIFF W`
      MP_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FRN_SETID_22 THEN EXISTS_TAC `W:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`~((v2:real^N) IN W)`; `~((v3:real^N) IN W)`;
        `(v0:real^N) IN W`; `(v1:real^N) IN W`] THEN MESON_TAC[]];
    SUBGOAL_THEN `(W:real^N->bool) HAS_SIZE 3 /\ (V DIFF W) HAS_SIZE 1` MP_TAC
    THENL [ASM_REWRITE_TAC[HAS_SIZE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(BINOP_CONV HAS_SIZE_CONV)) THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `v0:real^N` (X_CHOOSE_THEN `v1:real^N`
        (X_CHOOSE_THEN `v2:real^N` STRIP_ASSUME_TAC)))
     (X_CHOOSE_THEN `v3:real^N` STRIP_ASSUME_TAC))
    THEN MAP_EVERY EXISTS_TAC [`v0:real^N`; `v1:real^N`; `v2:real^N`; `v3:real^N`]
    THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((v3:real^N) IN W) /\ (v0:real^N) IN W /\ (v1:real^N) IN W /\
                  (v2:real^N) IN W` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(v3:real^N) IN V DIFF W` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FRN_SETID_31 THEN EXISTS_TAC `W:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`~((v3:real^N) IN W)`; `(v0:real^N) IN W`; `(v1:real^N) IN W`;
        `(v2:real^N) IN W`] THEN MESON_TAC[]];
    SUBGOAL_THEN `(W:real^N->bool) HAS_SIZE 2 /\ (V DIFF W) HAS_SIZE 1` MP_TAC
    THENL [ASM_REWRITE_TAC[HAS_SIZE] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    CONV_TAC(LAND_CONV(BINOP_CONV HAS_SIZE_CONV)) THEN
    DISCH_THEN(CONJUNCTS_THEN2
     (X_CHOOSE_THEN `v0:real^N` (X_CHOOSE_THEN `v1:real^N` STRIP_ASSUME_TAC))
     (X_CHOOSE_THEN `v2:real^N` STRIP_ASSUME_TAC))
    THEN MAP_EVERY EXISTS_TAC [`v0:real^N`; `v1:real^N`; `v2:real^N`]
    THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `~((v2:real^N) IN W) /\ (v0:real^N) IN W /\ (v1:real^N) IN W`
    STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `(v2:real^N) IN V DIFF W` MP_TAC THENL
       [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
      REWRITE_TAC[IN_DIFF] THEN STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FRN_SETID_21 THEN EXISTS_TAC `W:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY UNDISCH_TAC
       [`~((v2:real^N) IN W)`; `(v0:real^N) IN W`; `(v1:real^N) IN W`] THEN
      MESON_TAC[]];
    SUBGOAL_THEN `(W:real^N->bool) HAS_SIZE 1` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN REWRITE_TAC[]]);;

(* Vertices of a complex are vertices of its barycentric subdivision; the  *)
(* edge from a vertex a of k to the barycentre of tau lies in the closed    *)
(* star of a; vertex counts of simplices of a combinatorial 3-manifold.     *)

let MOI_FRN_SING_IN_BARY = prove
 (`!(c:(real^N->bool)->bool) a.
     moi_bar_complex c /\ {a} IN c ==> {a} IN barycentric_subdivision c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` MOI_BAR_SUBDIVISION_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N` o GEN_REWRITE_RULE I [EXTENSION]) THEN
  REWRITE_TAC[IN_ELIM_THM] THEN DISCH_THEN SUBST1_TAC THEN
  EXISTS_TAC `{a:real^N}` THEN
  ASM_REWRITE_TAC[MOI_FRN_BARYCENTRE_SING; NOT_INSERT_EMPTY]);;

let MOI_FRN_EDGE_IN_CSTAR = prove
 (`!(c:(real^N->bool)->bool) a tau.
     {a} IN c /\ tau IN c /\ a IN tau
     ==> {simplex_barycentre tau} IN
         moi_fm3_cstar (barycentric_subdivision c) a`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_fm3_cstar; IN_ELIM_THM] THEN
  EXISTS_TAC `convex hull {a:real^N, simplex_barycentre tau}` THEN
  REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_CONVEX_HULL_2] THEN
  SIMP_TAC[HULL_INC; IN_INSERT] THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  EXISTS_TAC `{{a:real^N}, tau:real^N->bool}` THEN
  REWRITE_TAC[IMAGE_CLAUSES; MOI_FRN_BARYCENTRE_SING] THEN
  REWRITE_TAC[moi_bar_chain; FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET;
              EMPTY_SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{a:real^N} SUBSET tau /\ ~({} = tau:real^N->bool)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY; GSYM NOT_INSERT_EMPTY] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL]);;

let MOI_FRN_SIMPLEX_CARD_LE = prove
 (`!(c:(real^N->bool)->bool) s.
     combinatorial_manifold_with_boundary 3 c /\ s IN c
     ==> ~affine_dependent {v | v extreme_point_of s} /\
         s = convex hull {v | v extreme_point_of s} /\
         FINITE {v | v extreme_point_of s} /\
         CARD {v | v extreme_point_of s} <= 4`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` MP_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold_with_boundary; MOI_FDN_LF_SIMPLEX];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ABBREV_TAC `V = {v:real^N | v extreme_point_of s}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "hull")) THEN
  ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  MP_TAC(ISPEC `c:(real^N->bool)->bool` CM_WB_DIM) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN
  ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
  ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
  REWRITE_TAC[INT_ARITH `x - &1:int <= &3 <=> x <= &4`; INT_OF_NUM_LE]);;


(* ========================================================================= *)
(* Frontier links at barycentres of triangles tau of the first              *)
(* derived meeting UNIONS l in an edge.  The cofaces of tau are one or two  *)
(* tetrahedra (vertex links of a 3-manifold are 2-spheres or 2-disks, whose *)
(* edges lie in one or two triangles); explicit PL charts of their union    *)
(* near b(tau) carry N to a half-space (MOI_FRN_CHART_LINK_BALL).           *)
(* ========================================================================= *)

(* A generic local chart criterion for a vertex w of N'.                     *)

let MOI_FRN_CHART_LINK_BALL = prove
 (`!(t:(real^N->bool)->bool) l w S O (Y:real^N->real^3) (X:real^3->real^N)
    (psi:real^3->real^3) phi.
     3 <= dimindex(:N) /\ lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     {w} IN derived_nbhd_complex t l /\
     open_in (subtopology euclidean (UNIONS t)) O /\ w IN O /\ O SUBSET S /\
     pl_map_on S Y /\ (!x. x IN S ==> X(Y x) = x) /\
     pl_map_on (:real^3) psi /\ (!q. psi(phi q) = q) /\ (!y. phi(psi y) = y) /\
     phi continuous at (vec 0) /\ X continuous at (phi(vec 0)) /\
     X(phi(vec 0)) = w /\
     (!x. x IN O ==> (x IN derived_nbhd t l <=> &0 <= (psi(Y x))$3)) /\
     (?d. &0 < d /\
          !q. norm q < d /\ &0 <= q$3 ==> X(phi q) IN O /\ Y(X(phi q)) = phi q)
     ==> pl_ball 2 (UNIONS (simplicial_link (derived_nbhd_complex t l) w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS (derived_nbhd_complex t l) =
                derived_nbhd t (l:(real^N->bool)->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FDN_UNIONS_DERIVED_NBHD_COMPLEX];
                    ALL_TAC] THEN
  SUBGOAL_THEN `derived_nbhd t l SUBSET UNIONS (t:(real^N->bool)->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[MOI_FDN_DERIVED_NBHD_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN derived_nbhd t l` ASSUME_TAC THENL
   [MP_TAC(ASSUME `UNIONS (derived_nbhd_complex t l) =
                   derived_nbhd t (l:(real^N->bool)->bool)`) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `{w:real^N}` THEN ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN `?e. &0 < e /\
                    !x:real^N. x IN UNIONS t /\ dist(w,x) < e ==> x IN O`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean
                   (UNIONS (t:(real^N->bool)->bool))) (O:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
    DISCH_THEN(MP_TAC o SPEC `w:real^N` o CONJUNCT2) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `e:real` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN
    UNDISCH_TAC `ball(w:real^N,e) INTER UNIONS t SUBSET O` THEN
    REWRITE_TAC[SUBSET; IN_INTER; IN_BALL] THEN
    DISCH_THEN MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `locally_polyhedral (derived_nbhd t l INTER O:real^N->bool)`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `open_in (subtopology euclidean
                   (UNIONS (t:(real^N->bool)->bool))) (O:real^N->bool)`) THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `G:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `derived_nbhd t l INTER O =
                  derived_nbhd t l INTER (G:real^N->bool)` SUBST1_TAC THENL
     [MAP_EVERY UNDISCH_TAC
       [`O = UNIONS t INTER (G:real^N->bool)`;
        `derived_nbhd t l SUBSET UNIONS (t:(real^N->bool)->bool)`] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_INTER_OPEN THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `UNIONS (derived_nbhd_complex t l) =
                   derived_nbhd t (l:(real^N->bool)->bool)`) THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_LF_COMPLEX THEN
    ASM_SIMP_TAC[MOI_FDN_DERIVED_NBHD_COMPLEX_LF];
    ALL_TAC] THEN
  SUBGOAL_THEN `(psi:real^3->real^3) ((Y:real^N->real^3) w) = vec 0`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `vec 0:real^3` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `norm:real^3->real`))
      (concl th))) THEN
    ASM_REWRITE_TAC[NORM_0; VEC_COMPONENT; REAL_LE_REFL] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_LINK_BALL_BY_INVERSE THEN
  MAP_EVERY EXISTS_TAC
   [`derived_nbhd t l INTER O:real^N->bool`;
    `(psi:real^3->real^3) o (Y:real^N->real^3)`;
    `(X:real^3->real^N) o (phi:real^3->real^3)`; `e:real`; `d:real`] THEN
  ASM_REWRITE_TAC[o_THM] THEN
  CONJ_TAC THENL [ASM_SIMP_TAC[MOI_FDN_DERIVED_NBHD_COMPLEX_LF]; ALL_TAC] THEN
  CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN REWRITE_TAC[IN_INTER] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
    ASM_REWRITE_TAC[SUBSET_UNIV] THEN MATCH_MP_TAC PL_MAP_ON_SUBSET THEN
    EXISTS_TAC `S:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_INTER] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `derived_nbhd:((real^N->bool)->bool)->((real^N->bool)->bool)->real^N->bool`)) (concl th) &&
      can (find_term ((=) `psi:real^3->real^3`)) (concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  X_GEN_TAC `q:real^3` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `q:real^3` o check (fun th ->
    is_forall(concl th) && can (find_term ((=) `norm:real^3->real`))
    (concl th))) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IN_INTER] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(X:real^3->real^N) ((phi:real^3->real^3) q)` o
    check (fun th ->
      is_forall(concl th) && can (find_term ((=) `derived_nbhd:((real^N->bool)->bool)->((real^N->bool)->bool)->real^N->bool`)) (concl th) &&
      can (find_term ((=) `psi:real^3->real^3`)) (concl th))) THEN
  ASM_REWRITE_TAC[]);;

(* Chart maps of the plane-fold type and the quadrant map.                  *)

let moi_frn_psit = new_definition
 `moi_frn_psit (y:real^3) =
    vector[(&1 - y$1 - y$2 - abs(y$3)) - y$1; y$3;
           max (&1 - y$1 - y$2 - abs(y$3)) (y$1) - y$2]:real^3`;;

let moi_frn_phit = new_definition
 `moi_frn_phit (q:real^3) =
    vector[(&1 - abs(q$2) - (&1 - abs(q$2) + abs(q$1) - &2 * q$3) / &3 - q$1)
           / &2;
           (&1 - abs(q$2) + abs(q$1) - &2 * q$3) / &3;
           q$2]:real^3`;;

let moi_frn_qmap = new_definition
 `moi_frn_qmap (q:real^3) = vector[q$1; q$2 - q$3; min (q$2) (q$3)]:real^3`;;

let moi_frn_qinv = new_definition
 `moi_frn_qinv (q:real^3) =
    vector[q$1; q$3 + max (q$2) (&0); q$3 - min (q$2) (&0)]:real^3`;;

let MOI_FRN_PSIT_PHIT = prove
 (`(!q. moi_frn_psit (moi_frn_phit q) = q) /\
   (!y. moi_frn_phit (moi_frn_psit y) = y)`,
  REWRITE_TAC[moi_frn_psit; moi_frn_phit; CART_EQ; DIMINDEX_3; FORALL_3;
              VECTOR_3] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let MOI_FRN_QMAP_QINV = prove
 (`(!q. moi_frn_qmap (moi_frn_qinv q) = q) /\
   (!q. moi_frn_qinv (moi_frn_qmap q) = q)`,
  REWRITE_TAC[moi_frn_qmap; moi_frn_qinv; CART_EQ; DIMINDEX_3; FORALL_3;
              VECTOR_3] THEN
  REPEAT STRIP_TAC THEN REAL_ARITH_TAC);;

let MOI_FRN_PSIT_PL = prove
 (`pl_map_on (:real^3) moi_frn_psit`,
  SUBGOAL_THEN `moi_frn_psit =
     (\y. vector[(&1 - y$1 - y$2 - abs(y$3)) - y$1; y$3;
           max (&1 - y$1 - y$2 - abs(y$3)) (y$1) - y$2]:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_frn_psit]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_PL_VECTOR3 THEN MOI_FRN_PL_TAC);;

let MOI_FRN_QMAP_PL = prove
 (`pl_map_on (:real^3) moi_frn_qmap`,
  SUBGOAL_THEN `moi_frn_qmap =
     (\q. vector[q$1; q$2 - q$3; min (q$2) (q$3)]:real^3)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_frn_qmap]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_PL_VECTOR3 THEN MOI_FRN_PL_TAC);;

let MOI_FRN_PHIT_CONTINUOUS = prove
 (`!x. moi_frn_phit continuous at x`,
  GEN_TAC THEN
  SUBGOAL_THEN `pl_map_on (:real^3) moi_frn_phit` MP_TAC THENL
   [SUBGOAL_THEN `moi_frn_phit =
      (\q. vector[(&1 - abs(q$2) - (&1 - abs(q$2) + abs(q$1) - &2 * q$3) / &3 -
                   q$1) / &2;
                  (&1 - abs(q$2) + abs(q$1) - &2 * q$3) / &3;
                  q$2]:real^3)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_frn_phit]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FRN_PL_VECTOR3 THEN MOI_FRN_PL_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP PL_MAP_ON_IMP_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]]);;

let MOI_FRN_QINV_CONTINUOUS = prove
 (`!x. moi_frn_qinv continuous at x`,
  GEN_TAC THEN
  SUBGOAL_THEN `pl_map_on (:real^3) moi_frn_qinv` MP_TAC THENL
   [SUBGOAL_THEN `moi_frn_qinv =
      (\q. vector[q$1; q$3 + max (q$2) (&0); q$3 - min (q$2) (&0)]:real^3)`
    SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_frn_qinv]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FRN_PL_VECTOR3 THEN MOI_FRN_PL_TAC;
    DISCH_THEN(MP_TAC o MATCH_MP PL_MAP_ON_IMP_CONTINUOUS_ON) THEN
    SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]]);;

let MOI_FRN_PHIT_QINV_VALUES = prove
 (`moi_frn_phit (vec 0) = vector[&1 / &3; &1 / &3; &0] /\
   moi_frn_qinv (vec 0) = vec 0 /\
   (!q. (moi_frn_phit q)$3 = q$2) /\
   (!q. (moi_frn_qinv q)$2 = q$3 + max (q$2) (&0)) /\
   (!y. (moi_frn_psit y)$3 = max (&1 - y$1 - y$2 - abs(y$3)) (y$1) - y$2) /\
   (!q. (moi_frn_qmap q)$3 = min (q$2) (q$3))`,
  REWRITE_TAC[moi_frn_psit; moi_frn_phit; moi_frn_qmap; moi_frn_qinv;
              CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3; VEC_COMPONENT] THEN
  REAL_ARITH_TAC);;

let MOI_FRN_SUM_VSUM_3 = prove
 (`!(v0:real^N) v1 v2 (u:real^N->real).
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2)
     ==> sum {v0,v1,v2} u = u v0 + u v1 + u v2 /\
         vsum {v0,v1,v2} (\v. u v % v) = u v0 % v0 + u v1 % v1 + u v2 % v2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SIMP_TAC[SUM_CLAUSES; VSUM_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; REAL_ADD_RID; VECTOR_ADD_RID]);;

let MOI_FRN_TRI_BARYCENTRE = prove
 (`!(v0:real^N) v1 v2.
     ~affine_dependent {v0,v1,v2} /\ ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2)
     ==> simplex_barycentre (convex hull {v0,v1,v2}) =
         v0 + (&1 / &3) % (v1 - v0) + (&1 / &3) % (v2 - v0)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_BAR_SIMPLEX_BARYCENTRE_HULL] THEN
  REWRITE_TAC[barycentre; FINITE_INSERT; FINITE_EMPTY] THEN
  SUBGOAL_THEN `CARD {v0:real^N,v1,v2} = 3` SUBST1_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`;
                 `\v:real^N. inv(&3)`] MOI_FRN_SUM_VSUM_3) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o CONJUNCT2) THEN
  VECTOR_ARITH_TAC);;

let MOI_FRN_RELINT_IN_OPEN_STAR = prove
 (`!(c:(real^N->bool)->bool) r w x.
     moi_bar_complex c /\ r IN c /\ w IN r /\ x IN relative_interior r
     ==> x IN moi_sta_open_star c w`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^N->bool` THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) SUBSET r INTER s` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `r:real^N->bool` THEN
    REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `moi_bar_complex (c:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_complex] THEN ASM_MESON_TAC[];
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `x:real^N` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    ASM SET_TAC[]]);;

(* The neighbourhood near the barycentre of a face triangle of a tetrahedron *)
(* (maximum barycentric coordinate at v0 or v1).                             *)

let MOI_FRN_TET_NBHD_NEAR = prove
 (`!(t:(real^N->bool)->bool) l v0 v1 v2 u (y:real^3).
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     convex hull {v0,v1,v2,u} IN barycentric_subdivision t /\
     ~affine_dependent {v0,v1,v2,u} /\
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v0 = u) /\ ~(v1 = v2) /\ ~(v1 = u) /\
     ~(v2 = u) /\
     v0 IN UNIONS l /\ v1 IN UNIONS l /\ ~(v2 IN UNIONS l) /\
     &0 <= y$1 /\ &0 <= y$2 /\ &0 <= y$3 /\ y$3 < y$1 /\ y$3 < y$2 /\
     y$3 < &1 - y$1 - y$2 - y$3
     ==> (v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (u - v0) IN
          derived_nbhd t l <=>
          y$2 <= max (&1 - y$1 - y$2 - y$3) (y$1))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v:real^N. v extreme_point_of convex hull {v0,v1,v2,u} <=>
                           v IN {v0,v1,v2,u}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `{v0:real^N,v1,v2,u}`
      EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N | v extreme_point_of convex hull {v0,v1,v2,u}} =
                {v0,v1,v2,u}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u:real^N`;
                 `y:real^3`] MOI_FRN_TCOEF_VSUM) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `mu = moi_frn_tcoef (v0:real^N) v1 v2 u y` THEN STRIP_TAC THEN
  SUBGOAL_THEN `!v:real^N. v IN {v0,v1,v2,u} ==> &0 <= mu v` ASSUME_TAC THENL
   [X_GEN_TAC `v:real^N` THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `v0 + (y:real^3)$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (u - v0) =
    vsum {v:real^N | v extreme_point_of convex hull {v0,v1,v2,u}}
         (\v. mu v % v)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `convex hull {v0:real^N,v1,v2,u}`; `mu:real^N->real`]
      MOI_FRN_NBHD_IMP_MAX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (CONJUNCTS_THEN2 MP_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "mx")))) THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    STRIP_TAC THEN FIRST_X_ASSUM SUBST_ALL_TAC THENL
     [REMOVE_THEN "mx" (MP_TAC o SPEC `v2:real^N`) THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN REAL_ARITH_TAC;
      REMOVE_THEN "mx" (MP_TAC o SPEC `v2:real^N`) THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN REAL_ARITH_TAC;
      ASM_MESON_TAC[];
      REMOVE_THEN "mx" (MP_TAC o SPEC `v1:real^N`) THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN ASM_REAL_ARITH_TAC];
    DISCH_TAC THEN
    ASM_CASES_TAC `(y:real^3)$1 <= &1 - y$1 - y$2 - y$3` THENL
     [MATCH_MP_TAC MOI_FRN_MAX_IMP_NBHD THEN EXISTS_TAC `v0:real^N` THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN
      REWRITE_TAC[NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
      MATCH_MP_TAC MOI_FRN_MAX_IMP_NBHD THEN EXISTS_TAC `v1:real^N` THEN
      ASM_REWRITE_TAC[IN_INSERT] THEN
      REWRITE_TAC[NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC]]);;

(* Edges of 2-disk and 2-sphere links lie in one or two triangles; the      *)
(* cofaces of a triangle of a combinatorial 3-manifold with boundary.       *)

(* Adapted from MOI_SCF_SURF_EDGE_NOT3 (pc_moi_smo_cf.ml), with           *)
(* MOI_FM3_DISK_OPEN_IMAGE for disks in place of MOI_SCF_OPEN_IMAGE_R2.     *)

let MOI_FRN_DISK_EDGE_NOT3 = prove
 (`!L k (h:real^N->real^N) g e t1 t2 t3.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (UNIONS L,k) (h,g) /\
        e IN L /\ aff_dim e = &1 /\
        t1 IN L /\ aff_dim t1 = &2 /\ e SUBSET t1 /\
        t2 IN L /\ aff_dim t2 = &2 /\ e SUBSET t2 /\
        t3 IN L /\ aff_dim t3 = &2 /\ e SUBSET t3 /\
        ~(t1 = t2) /\ ~(t1 = t3) /\ ~(t2 = t3)
        ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`] MOI_SCF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                 `t1:real^N->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c1:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `a:real^N`; `b:real^N`;
                 `t2:real^N->bool`] MOI_SCF_TRIANGLE_ON_EDGE) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `c2:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(c1:real^N = c2)` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `~(t1:real^N->bool = t2)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {a,b,c1} INTER convex hull {a,b,c2} = convex hull {a:real^N,b}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `{a:real^N,b,c1}`;
                   `{a:real^N,b,c2}`] MOI_REAL_SIMPLICIAL_COMPLEX_INTER_HULL) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    AP_TERM_TAC THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`a:real^N`; `b:real^N`; `c1:real^N`; `c2:real^N`]
    MOI_SCF_UNFOLD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:real^2->real^N` (X_CHOOSE_THEN `W:real^2->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `z:real^2` STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `h:real^N->real^N`; `g:real^N->real^N`;
                 `f:real^2->real^N`; `W:real^2->bool`]
    MOI_FM3_DISK_OPEN_IMAGE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `IMAGE (f:real^2->real^N) W SUBSET
                 convex hull {a,b,c1} UNION convex hull {a,b,c2}` THEN
    UNDISCH_TAC `(t1:real^N->bool) IN L` THEN
    UNDISCH_TAC `(t2:real^N->bool) IN L` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    DISCH_THEN(MP_TAC o CONJUNCT1)] THEN
  REWRITE_TAC[OPEN_IN_CONTAINS_BALL] THEN
  DISCH_THEN(MP_TAC o SPEC `(f:real^2->real^N) z` o CONJUNCT2) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:real^2->real^N) z IN closure(relative_interior t3)`
  MP_TAC THENL
   [ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; MOI_CON_SC_CONVEX;
                 CLOSURE_CLOSED; MOI_SCF_SC_CLOSED] THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t3:real^N->bool`]
      MOI_CON_SC_CONVEX) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t3:real^N->bool`]
      MOI_SCF_SC_CLOSED) THEN
    ASM_SIMP_TAC[CONVEX_CLOSURE_RELATIVE_INTERIOR; CLOSURE_CLOSED] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[CLOSURE_APPROACHABLE] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(y:real^N) IN IMAGE (f:real^2->real^N) W` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
    REWRITE_TAC[IN_INTER; IN_BALL] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `t3:real^N->bool` THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t3:real^N->bool`;
                 `t1:real^N->bool`] MOI_SCF_DISTINCT_RELINT) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t3:real^N->bool`;
                 `t2:real^N->bool`] MOI_SCF_DISTINCT_RELINT) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `IMAGE (f:real^2->real^N) W SUBSET
               convex hull {a,b,c1} UNION convex hull {a,b,c2}` THEN
  UNDISCH_TAC `(y:real^N) IN IMAGE (f:real^2->real^N) W` THEN
  UNDISCH_TAC `(y:real^N) IN relative_interior t3` THEN
  SUBGOAL_THEN `~(t3:real^N->bool = t1) /\ ~(t3 = t2)` MP_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_FRN_LINK_EDGE_COFACES = prove
 (`!(c:(real^N->bool)->bool) v e.
     lf_simplicial_complex c /\ {v} IN c /\
     (pl_sphere 2 (UNIONS (simplicial_link c v)) \/
      pl_ball 2 (UNIONS (simplicial_link c v))) /\
     e IN simplicial_link c v /\ aff_dim e = &1
     ==> FINITE {t | t IN simplicial_link c v /\ aff_dim t = &2 /\ e SUBSET t} /\
         1 <= CARD {t | t IN simplicial_link c v /\ aff_dim t = &2 /\
                        e SUBSET t} /\
         CARD {t | t IN simplicial_link c v /\ aff_dim t = &2 /\
                   e SUBSET t} <= 2`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `simplicial_complex (simplicial_link c (v:real^N)) /\
                FINITE (simplicial_link c (v:real^N))` STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FM3_LINK_SC; MOI_FM3_LINK_FINITE]; ALL_TAC] THEN
  ABBREV_TAC `L = simplicial_link c (v:real^N)` THEN
  ABBREV_TAC `ts = {t:real^N->bool | t IN L /\ aff_dim t = &2 /\ e SUBSET t}` THEN
  SUBGOAL_THEN `FINITE (ts:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "ts" THEN MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [SUBGOAL_THEN `UNIONS (L:(real^N->bool)->bool) homeomorphic
                  sphere(vec 0:real^3,&1)` ASSUME_TAC THENL
     [EXPAND_TAC "L" THEN MATCH_MP_TAC MOI_SCF_LINK_SPHERE THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`]
      MOI_SCF_SURF_EDGE) THEN
    ASM_REWRITE_TAC[] THEN ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `pl_ball 2 (UNIONS (L:(real^N->bool)->bool))` THEN
  REWRITE_TAC[pl_ball; pl_homeomorphism] THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `homeomorphism (UNIONS (L:(real^N->bool)->bool),k)
                              (g:real^N->real^N,f)` ASSUME_TAC THENL
   [ONCE_REWRITE_TAC[HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
    ASM_SIMP_TAC[CARD_EQ_0] THEN EXPAND_TAC "ts" THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    MATCH_MP_TAC MOI_FM3_DISK_PURE THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `g:real^N->real^N`;
                          `f:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[ARITH_RULE `n <= 2 <=> ~(3 <= n)`] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `ts:(real^N->bool)->bool` CHOOSE_SUBSET) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `3`) THEN
  ASM_REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:(real^N->bool)->bool` MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
   (X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
     (X_CHOOSE_THEN `t3:real^N->bool` STRIP_ASSUME_TAC)))) THEN
  MATCH_MP_TAC MOI_FRN_DISK_EDGE_NOT3 THEN
  MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `k:real^N->bool`;
    `g:real^N->real^N`; `f:real^N->real^N`; `e:real^N->bool`;
    `t1:real^N->bool`; `t2:real^N->bool`; `t3:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(u:(real^N->bool)->bool) SUBSET ts` THEN
  ASM_REWRITE_TAC[] THEN EXPAND_TAC "ts" THEN
  REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_FRN_TET_OVER_TRIANGLE = prove
 (`!(c:(real^N->bool)->bool) v0 v1 v2 r.
     lf_simplicial_complex c /\ convex hull {v0,v1,v2} IN c /\
     ~affine_dependent {v0,v1,v2} /\ ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2) /\
     r IN c /\ aff_dim r = &3 /\ convex hull {v0,v1,v2} SUBSET r
     ==> ?u. r = convex hull {v0,v1,v2,u} /\ ~affine_dependent {v0,v1,v2,u} /\
             ~(u = v0) /\ ~(u = v1) /\ ~(u = v2)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `r:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_FM3_LF_SIMPLEX]; ALL_TAC] THEN
  ABBREV_TAC `V = {v:real^N | v extreme_point_of r}` THEN STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool) /\ CARD V = 4` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
    MP_TAC(ISPEC `V:real^N->bool` AFF_DIM_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `aff_dim (V:real^N->bool) = &3` SUBST1_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_CONVEX_HULL]; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `&3:int = x - &1 <=> x = &4`; INT_OF_NUM_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v0:real^N,v1,v2} SUBSET V` ASSUME_TAC THENL
   [SUBGOAL_THEN `(convex hull {v0:real^N,v1,v2}) face_of r` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_SUBSET_FACE THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPEC `{v0:real^N,v1,v2}`
      EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN
    EXPAND_TAC "V" THEN REWRITE_TAC[SUBSET; EXTENSION; IN_ELIM_THM] THEN
    DISCH_TAC THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`convex hull {v0:real^N,v1,v2}`; `r:real^N->bool`;
                   `x:real^N`] EXTREME_POINT_OF_FACE) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD {v0:real^N,v1,v2} = 3` ASSUME_TAC THENL
   [SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `?u:real^N. u IN V /\ ~(u IN {v0,v1,v2})` STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE `!a b:real^N->bool. a SUBSET b /\ ~(b = a)
                            ==> ?u. u IN b /\ ~(u IN a)`) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `CARD {v0:real^N,v1,v2} = 4` THEN ASM_REWRITE_TAC[] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `~((u:real^N) IN {v0,v1,v2})` THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `V = {v0:real^N,v1,v2,u}` SUBST_ALL_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [UNDISCH_TAC `{v0:real^N,v1,v2} SUBSET V` THEN
      UNDISCH_TAC `(u:real^N) IN V` THEN SET_TAC[];
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]);;

let MOI_FRN_TRIANGLE_COFACES = prove
 (`!(c:(real^N->bool)->bool) v0 v1 v2.
     combinatorial_manifold_with_boundary 3 c /\
     convex hull {v0,v1,v2} IN c /\ ~affine_dependent {v0,v1,v2} /\
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2)
     ==> ?u1 u2.
           convex hull {v0,v1,v2,u1} IN c /\ convex hull {v0,v1,v2,u2} IN c /\
           ~affine_dependent {v0,v1,v2,u1} /\ ~affine_dependent {v0,v1,v2,u2} /\
           ~(u1 = v0) /\ ~(u1 = v1) /\ ~(u1 = v2) /\
           ~(u2 = v0) /\ ~(u2 = v1) /\ ~(u2 = v2) /\
           (!r. r IN c /\ aff_dim r = &3 /\ convex hull {v0,v1,v2} SUBSET r
                ==> r = convex hull {v0,v1,v2,u1} \/
                    r = convex hull {v0,v1,v2,u2})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC(CONJUNCT1(REWRITE_RULE[combinatorial_manifold_with_boundary]
   (ASSUME `combinatorial_manifold_with_boundary 3
              (c:(real^N->bool)->bool)`))) THEN
  SUBGOAL_THEN `!v:real^N. v extreme_point_of convex hull {v0,v1,v2} <=>
                           v IN {v0,v1,v2}` ASSUME_TAC THENL
   [MP_TAC(ISPEC `{v0:real^N,v1,v2}`
      EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v2:real^N} IN c` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FM3_LF_FACE THEN
    EXISTS_TAC `convex hull {v0:real^N,v1,v2}` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {v0:real^N,v1} face_of convex hull {v0,v1,v2}`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{v0:real^N,v1}` THEN REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((v2:real^N) IN convex hull {v0,v1})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~affine_dependent {v0:real^N,v1,v2}` THEN
    REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `v2:real^N` THEN
    REWRITE_TAC[IN_INSERT] THEN
    SUBGOAL_THEN `{v0:real^N,v1,v2} DELETE v2 = {v0,v1}` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {v0:real^N,v1} IN simplicial_link c v2`
  ASSUME_TAC THENL
   [REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LF_FACE THEN
      EXISTS_TAC `convex hull {v0:real^N,v1,v2}` THEN ASM_REWRITE_TAC[];
      EXISTS_TAC `convex hull {v0:real^N,v1,v2}` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(convex hull {v0:real^N,v1}) = &1` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_2]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v2:real^N`;
                 `convex hull {v0:real^N,v1}`] MOI_FRN_LINK_EDGE_COFACES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 3
                   (c:(real^N->bool)->bool)` THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
    DISCH_THEN(MP_TAC o SPEC `v2:real^N` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v2:real^N`;
                 `convex hull {v0:real^N,v1}`; `&2:int`; `&3:int`]
    MOI_FM3_LINK_CARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HULL_INSERT_HULL] THEN
  SUBGOAL_THEN `{v2:real^N,v0,v1} = {v0,v1,v2}` SUBST1_TAC THENL
   [SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  ABBREV_TAC `R = {r:real^N->bool | r IN c /\ aff_dim r = &3 /\
                                    convex hull {v0,v1,v2} SUBSET r}` THEN
  SUBGOAL_THEN `FINITE (R:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{t:real^N->bool | t IN c /\ v0 IN t}` THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_STAR_FINITE THEN ASM_REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `convex hull {v0:real^N,v1,v2}` THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      EXPAND_TAC "R" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN
      X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  STRIP_TAC THEN
  SUBGOAL_THEN `?r1 r2:real^N->bool. R = {r1,r2}` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `CARD(R:(real^N->bool)->bool) = 1 \/ CARD R = 2` MP_TAC THENL
     [ASM_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `(R:(real^N->bool)->bool) HAS_SIZE 1` MP_TAC THENL
       [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
      CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
      DISCH_THEN(X_CHOOSE_TAC `a:real^N->bool`) THEN
      MAP_EVERY EXISTS_TAC [`a:real^N->bool`; `a:real^N->bool`] THEN
      ASM_REWRITE_TAC[INSERT_AC];
      SUBGOAL_THEN `(R:(real^N->bool)->bool) HAS_SIZE 2` MP_TAC THENL
       [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
      CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
      DISCH_THEN(X_CHOOSE_THEN `a:real^N->bool` (X_CHOOSE_THEN
        `b:real^N->bool` STRIP_ASSUME_TAC)) THEN
      MAP_EVERY EXISTS_TAC [`a:real^N->bool`; `b:real^N->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r1:real^N->bool) IN R /\ (r2:real^N->bool) IN R`
  MP_TAC THENL [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  EXPAND_TAC "R" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v0:real^N`; `v1:real^N`;
                 `v2:real^N`; `r1:real^N->bool`] MOI_FRN_TET_OVER_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v0:real^N`; `v1:real^N`;
                 `v2:real^N`; `r2:real^N->bool`] MOI_FRN_TET_OVER_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u2:real^N` STRIP_ASSUME_TAC) THEN
  MAP_EVERY EXISTS_TAC [`u1:real^N`; `u2:real^N`] THEN
  REPEAT CONJ_TAC THEN TRY(ASM_MESON_TAC[]) THEN
  X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) IN R` MP_TAC THENL
   [EXPAND_TAC "R" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[]);;

(* Continuity, relative interiors and coordinates on triangles.             *)

let MOI_FRN_PARAM_CONTINUOUS = prove
 (`!(v0:real^N) a b c x.
     (\y:real^3. v0 + y$1 % a + y$2 % b + y$3 % c) continuous at x`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN
   `(\y:real^3. (v0:real^N) + y$1 % a + y$2 % b + y$3 % c) =
    (\y. v0 + (\y. y$1 % a + y$2 % b + y$3 % c) y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
  MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
  REWRITE_TAC[linear; VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REPEAT STRIP_TAC THEN VECTOR_ARITH_TAC);;

let MOI_FRN_FOLD_CONTINUOUS = prove
 (`!(f:real^3->real^N) g x.
     (!x. f continuous at x) /\ (!x. g continuous at x) /\
     (!y. y$3 = &0 ==> f y = g y)
     ==> (\y. if &0 <= y$3 then f y else g y) continuous at x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`\y:real^3. &0 <= y$3`; `f:real^3->real^N`;
                 `g:real^3->real^N`; `{y:real^3 | y$3 >= &0}`;
                 `{y:real^3 | y$3 <= &0}`] CONTINUOUS_ON_CASES) THEN
  REWRITE_TAC[CLOSED_HALFSPACE_COMPONENT_GE; CLOSED_HALFSPACE_COMPONENT_LE] THEN
  ANTS_TAC THENL
   [REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC CONTINUOUS_AT_IMP_CONTINUOUS_ON THEN ASM_REWRITE_TAC[];
      X_GEN_TAC `y:real^3` THEN REWRITE_TAC[IN_ELIM_THM; real_ge] THEN
      STRIP_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `{y:real^3 | y$3 >= &0} UNION {y | y$3 <= &0} = (:real^3)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_UNION; IN_ELIM_THM; IN_UNIV] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SIMP_TAC[CONTINUOUS_ON_EQ_CONTINUOUS_AT; OPEN_UNIV; IN_UNIV]);;

let MOI_FRN_AFFINE_NEAR = prove
 (`!(A:real^N->real^3) w e.
     (?L y. linear L /\ !x. A x = L x + y) /\ &0 < e
     ==> ?r. &0 < r /\
             !x. dist(w,x) < r
                 ==> abs((A x)$1 - (A w)$1) < e /\
                     abs((A x)$2 - (A w)$2) < e /\
                     abs((A x)$3 - (A w)$3) < e`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "aff") ASSUME_TAC) THEN
  SUBGOAL_THEN `(A:real^N->real^3) continuous at w` MP_TAC THENL
   [USE_THEN "aff" (X_CHOOSE_THEN `L:real^N->real^3`
      (X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(A:real^N->real^3) = (\x. L x + y0)` SUBST1_TAC THENL
     [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
    MATCH_MP_TAC CONTINUOUS_ADD THEN REWRITE_TAC[CONTINUOUS_CONST] THEN
    REWRITE_TAC[ETA_AX] THEN MATCH_MP_TAC LINEAR_CONTINUOUS_AT THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `e:real`) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[DIST_SYM]; ALL_TAC] THEN
  REWRITE_TAC[dist] THEN DISCH_TAC THEN
  REPEAT CONJ_TAC THEN MATCH_MP_TAC REAL_LET_TRANS THEN
  EXISTS_TAC `norm((A:real^N->real^3) x - A w)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[GSYM VECTOR_SUB_COMPONENT] THEN
  REWRITE_TAC[COMPONENT_LE_NORM]);;

let MOI_FRN_TET_RELINT = prove
 (`!(v0:real^N) v1 v2 u (y:real^3).
     ~affine_dependent {v0,v1,v2,u} /\
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v0 = u) /\ ~(v1 = v2) /\ ~(v1 = u) /\
     ~(v2 = u) /\
     &0 < y$1 /\ &0 < y$2 /\ &0 < y$3 /\ &0 < &1 - y$1 - y$2 - y$3
     ==> v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (u - v0) IN
         relative_interior(convex hull {v0,v1,v2,u})`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
  EXISTS_TAC `moi_frn_tcoef (v0:real^N) v1 v2 u y` THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u:real^N`;
                 `y:real^3`] MOI_FRN_TCOEF_VSUM) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN REPEAT STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_FRN_TRI_RELINT = prove
 (`!(v0:real^N) v1 v2 a b.
     ~affine_dependent {v0,v1,v2} /\ ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2) /\
     &0 < a /\ &0 < b /\ &0 < &1 - a - b
     ==> v0 + a % (v1 - v0) + b % (v2 - v0) IN
         relative_interior(convex hull {v0,v1,v2})`,
  REPEAT STRIP_TAC THEN
  ASM_SIMP_TAC[RELATIVE_INTERIOR_CONVEX_HULL_EXPLICIT; IN_ELIM_THM] THEN
  EXISTS_TAC `\v:real^N. if v = v0 then &1 - a - b else if v = v1 then a
                         else b` THEN
  ASM_SIMP_TAC[MOI_FRN_SUM_VSUM_3] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(v1:real^N = v0) /\ ~(v2:real^N = v0) /\ ~(v2:real^N = v1)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let MOI_FRN_TRI_FACE_COORDS = prove
 (`!(v0:real^N) v1 v2 u (A:real^N->real^3) x.
     (!y. A (v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (u - v0)) = y) /\
     x IN convex hull {v0,v1,v2}
     ==> x = v0 + (A x)$1 % (v1 - v0) + (A x)$2 % (v2 - v0) /\
         (A x)$3 = &0 /\ &0 <= (A x)$1 /\ &0 <= (A x)$2 /\
         (A x)$1 + (A x)$2 <= &1`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (LABEL_TAC "AB") (X_CHOOSE_THEN `p:real`
    (X_CHOOSE_THEN `q:real` (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `(x:real^N) = v0 + (vector[q;s;&0]:real^3)$1 % (v1 - v0) +
                (vector[q;s;&0]:real^3)$2 % (v2 - v0) +
                (vector[q;s;&0]:real^3)$3 % (u - v0)` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[VECTOR_3] THEN
    SUBGOAL_THEN `p = &1 - q - s` SUBST1_TAC THENL
     [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A:real^N->real^3) x = vector[q;s;&0]` SUBST1_TAC THENL
   [FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
    USE_THEN "AB" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  REWRITE_TAC[VECTOR_3] THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN TRY ASM_REAL_ARITH_TAC THEN
  SUBGOAL_THEN `p = &1 - q - s` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let moi_frn_xfold = new_definition
 `moi_frn_xfold (v0:real^N) v1 v2 u1 u2 (y:real^3) =
    if &0 <= y$3 then v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (u1 - v0)
    else v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (v0 - u2)`;;

let moi_frn_yfold = new_definition
 `moi_frn_yfold (A1:real^N->real^3) (A2:real^N->real^3) s1 (x:real^N) =
    if x IN s1 then A1 x
    else vector[(A2 x)$1; (A2 x)$2; --((A2 x)$3)]:real^3`;;

let MOI_FRN_XFOLD_CONTINUOUS = prove
 (`!(v0:real^N) v1 v2 u1 u2 x. moi_frn_xfold v0 v1 v2 u1 u2 continuous at x`,
  REPEAT GEN_TAC THEN
  SUBGOAL_THEN `moi_frn_xfold (v0:real^N) v1 v2 u1 u2 =
    (\y. if &0 <= y$3
         then (\y:real^3. v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) +
                          y$3 % (u1 - v0)) y
         else (\y:real^3. v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) +
                          y$3 % (v0 - u2)) y)`
  SUBST1_TAC THENL [REWRITE_TAC[FUN_EQ_THM; moi_frn_xfold]; ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_FOLD_CONTINUOUS THEN
  REWRITE_TAC[MOI_FRN_PARAM_CONTINUOUS] THEN
  REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[VECTOR_MUL_LZERO]);;

let MOI_FRN_TRI_HULL_EXPLICIT = prove
 (`!(v0:real^N) v1 v2 x.
     x IN convex hull {v0,v1,v2}
     ==> ?a b. &0 <= a /\ &0 <= b /\ a + b <= &1 /\
               x = v0 + a % (v1 - v0) + b % (v2 - v0)`,
  REPEAT GEN_TAC THEN REWRITE_TAC[CONVEX_HULL_3; IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real` (X_CHOOSE_THEN `q:real`
    (X_CHOOSE_THEN `s:real` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`q:real`; `s:real`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `p = &1 - q - s` SUBST1_TAC THENL
   [ASM_REAL_ARITH_TAC; VECTOR_ARITH_TAC]);;

let MOI_FRN_TRI_FACE_A = prove
 (`!(v0:real^N) v1 v2 u (A:real^N->real^3) a b.
     (!y. A (v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (u - v0)) = y)
     ==> A (v0 + a % (v1 - v0) + b % (v2 - v0)) = vector[a;b;&0]`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `vector[a;b;&0]:real^3`) THEN
  REWRITE_TAC[VECTOR_3; VECTOR_MUL_LZERO; VECTOR_ADD_RID]);;

let MOI_FRN_PL_FLIP_AFFINE = prove
 (`!(s:real^N->bool) (A:real^N->real^3).
     locally_polyhedral s /\ (?L y. linear L /\ !x. A x = L x + y)
     ==> pl_map_on s A /\
         pl_map_on s (\x. vector[(A x)$1; (A x)$2; --((A x)$3)]:real^3)`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `L:real^N->real^3`
    (X_CHOOSE_THEN `y0:real^3` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(A:real^N->real^3) = (\x. L x + y0)` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[FUN_EQ_THM]; ALL_TAC] THEN
  CONJ_TAC THENL [MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[];
                  ALL_TAC] THEN
  SUBGOAL_THEN
   `(\x. vector[((\x. (L:real^N->real^3) x + y0) x)$1;
                ((\x. L x + y0) x)$2;
                --(((\x. L x + y0) x)$3)]:real^3) =
    (\x. ((\v:real^3. vector[v$1; v$2; --(v$3)]:real^3) o L) x +
         vector[y0$1; y0$2; --(y0$3)])`
  SUBST1_TAC THENL
   [REWRITE_TAC[FUN_EQ_THM; o_THM; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
                VECTOR_ADD_COMPONENT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[ETA_AX] THEN
  MATCH_MP_TAC LINEAR_COMPOSE THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[linear; CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3;
              VECTOR_ADD_COMPONENT; VECTOR_MUL_COMPONENT] THEN
  REAL_ARITH_TAC);;

(* ========================================================================= *)
(* The two triangle charts (two cofaces: interior triangle; one             *)
(* coface: boundary triangle) and MOI_FRN_FRONTIER_LINK_TRI2.               *)
(* ========================================================================= *)

let MOI_FRN_TRI_CHART_INT = prove
 (`!(t:(real^N->bool)->bool) l v0 v1 v2 u1 u2.
     combinatorial_manifold_with_boundary 3 t /\ simplicial_subcomplex l t /\
     convex hull {v0,v1,v2} IN barycentric_subdivision t /\
     convex hull {v0,v1,v2,u1} IN barycentric_subdivision t /\
     convex hull {v0,v1,v2,u2} IN barycentric_subdivision t /\
     ~affine_dependent {v0,v1,v2} /\
     ~affine_dependent {v0,v1,v2,u1} /\ ~affine_dependent {v0,v1,v2,u2} /\
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2) /\
     ~(u1 = v0) /\ ~(u1 = v1) /\ ~(u1 = v2) /\
     ~(u2 = v0) /\ ~(u2 = v1) /\ ~(u2 = v2) /\
     convex hull {v0,v1,v2,u1} INTER convex hull {v0,v1,v2,u2} =
     convex hull {v0,v1,v2} /\
     v0 IN UNIONS l /\ v1 IN UNIONS l /\ ~(v2 IN UNIONS l) /\
     moi_sta_open_star (barycentric_subdivision t)
        (simplex_barycentre (convex hull {v0,v1,v2})) SUBSET
     convex hull {v0,v1,v2,u1} UNION convex hull {v0,v1,v2,u2}
     ==> pl_ball 2 (UNIONS (simplicial_link (derived_nbhd_complex t l)
                     (simplex_barycentre (convex hull {v0,v1,v2}))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC(CONJUNCT1(REWRITE_RULE[combinatorial_manifold_with_boundary]
   (ASSUME `combinatorial_manifold_with_boundary 3
              (t:(real^N->bool)->bool)`))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v0:real^N = u1) /\ ~(v1 = u1) /\ ~(v2 = u1) /\
                ~(v0:real^N = u2) /\ ~(v1 = u2) /\ ~(v2 = u2)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`]
    MOI_FRN_TRI_BARYCENTRE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `3 <= dimindex(:N)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `convex hull {v0:real^N,v1,v2,u1}` AFF_DIM_LE_UNIV) THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[INT_ARITH `&4 - &1:int <= x <=> &3 <= x`; INT_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `{simplex_barycentre (convex hull {v0:real^N,v1,v2})} IN
                derived_nbhd_complex t l` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_NBHD_COMPLEX_VERTEX_EXISTS THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `v0:real^N` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (convex hull {v0:real^N,v1,v2}) IN
                relative_interior (convex hull {v0,v1,v2})` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `simplex_barycentre (convex hull {v0:real^N,v1,v2})`)) THEN
    MATCH_MP_TAC MOI_FRN_TRI_RELINT THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `w = simplex_barycentre (convex hull {v0:real^N,v1,v2})` THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u1:real^N`]
    MOI_FRN_TET_COORDS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real^N->real^3` (CONJUNCTS_THEN2
    (LABEL_TAC "Aaff1") (CONJUNCTS_THEN2 (LABEL_TAC "AB1") (LABEL_TAC "BA1"))))
  THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u2:real^N`]
    MOI_FRN_TET_COORDS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A2:real^N->real^3` (CONJUNCTS_THEN2
    (LABEL_TAC "Aaff2") (CONJUNCTS_THEN2 (LABEL_TAC "AB2") (LABEL_TAC "BA2"))))
  THEN
  SUBGOAL_THEN
   `!x:real^N. x IN convex hull {v0,v1,v2,u1}
      ==> v0 + ((A1:real^N->real^3) x)$1 % (v1 - v0) + (A1 x)$2 % (v2 - v0) +
          (A1 x)$3 % (u1 - v0) = x /\
          &0 <= (A1 x)$1 /\ &0 <= (A1 x)$2 /\ &0 <= (A1 x)$3 /\
          &0 <= &1 - (A1 x)$1 - (A1 x)$2 - (A1 x)$3`
  (LABEL_TAC "S1") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "BA1" MATCH_MP_TAC THEN
      MP_TAC(ISPEC `{v0:real^N,v1,v2,u1}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u1:real^N`;
                   `(A1:real^N->real^3) x`] MOI_FRN_TCOEF_VSUM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u1:real^N`;
                   `A1:real^N->real^3`; `x:real^N`] MOI_FRN_TET_HULL_COEF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `v0:real^N` th) THEN
      MP_TAC(SPEC `v1:real^N` th) THEN MP_TAC(SPEC `v2:real^N` th) THEN
      MP_TAC(SPEC `u1:real^N` th)) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN convex hull {v0,v1,v2,u2}
      ==> v0 + ((A2:real^N->real^3) x)$1 % (v1 - v0) + (A2 x)$2 % (v2 - v0) +
          (A2 x)$3 % (u2 - v0) = x /\
          &0 <= (A2 x)$1 /\ &0 <= (A2 x)$2 /\ &0 <= (A2 x)$3 /\
          &0 <= &1 - (A2 x)$1 - (A2 x)$2 - (A2 x)$3`
  (LABEL_TAC "S2") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "BA2" MATCH_MP_TAC THEN
      MP_TAC(ISPEC `{v0:real^N,v1,v2,u2}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u2:real^N`;
                   `(A2:real^N->real^3) x`] MOI_FRN_TCOEF_VSUM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u2:real^N`;
                   `A2:real^N->real^3`; `x:real^N`] MOI_FRN_TET_HULL_COEF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `v0:real^N` th) THEN
      MP_TAC(SPEC `v1:real^N` th) THEN MP_TAC(SPEC `v2:real^N` th) THEN
      MP_TAC(SPEC `u2:real^N` th)) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN convex hull {v0,v1,v2}
      ==> (A1:real^N->real^3) x = A2 x /\ (A1 x)$3 = &0`
  (LABEL_TAC "TAU") THENL
   [X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FRN_TRI_HULL_EXPLICIT) THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real` (X_CHOOSE_THEN `b:real`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u1:real^N`;
                   `A1:real^N->real^3`; `a:real`; `b:real`]
      MOI_FRN_TRI_FACE_A) THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u2:real^N`;
                   `A2:real^N->real^3`; `a:real`; `b:real`]
      MOI_FRN_TRI_FACE_A) THEN
    ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN ASM_REWRITE_TAC[VECTOR_3];
    ALL_TAC] THEN
  SUBGOAL_THEN `(A1:real^N->real^3) w = vector[&1 / &3; &1 / &3; &0] /\
                (A2:real^N->real^3) w = vector[&1 / &3; &1 / &3; &0]`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `w:real^N` &&
      not(lhs(concl th) = `simplex_barycentre (convex hull {v0:real^N,v1,v2})`)))
    THEN CONJ_TAC THEN MATCH_MP_TAC MOI_FRN_TRI_FACE_A THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A1:real^N->real^3`; `w:real^N`; `&1 / &20`]
    MOI_FRN_AFFINE_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "N1"))) THEN
  MP_TAC(ISPECL [`A2:real^N->real^3`; `w:real^N`; `&1 / &20`]
    MOI_FRN_AFFINE_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r2:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "N2"))) THEN
  ABBREV_TAC `r = min r1 r2` THEN
  SUBGOAL_THEN `&0 < r` ASSUME_TAC THENL
   [EXPAND_TAC "r" THEN ASM_REWRITE_TAC[REAL_LT_MIN]; ALL_TAC] THEN
  ABBREV_TAC `O = moi_sta_open_star (barycentric_subdivision t) (w:real^N)
                  INTER ball(w,r)` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS t)) (O:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN
    REWRITE_TAC[OPEN_BALL] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS (barycentric_subdivision t):real^N->bool`)) THEN
    MATCH_MP_TAC MOI_STA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FRN_RELINT_IN_OPEN_STAR THEN
    EXISTS_TAC `convex hull {v0:real^N,v1,v2}` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(O:real^N->bool) SUBSET
                convex hull {v0,v1,v2,u1} UNION convex hull {v0,v1,v2,u2}`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC(SET_RULE
     `!a b c:real^N->bool. a SUBSET c ==> a INTER b SUBSET c`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `pl_map_on (convex hull {v0,v1,v2,u1} UNION convex hull {v0:real^N,v1,v2,u2})
      (moi_frn_yfold (A1:real^N->real^3) A2 (convex hull {v0,v1,v2,u1}))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_MAP_ON_UNION THEN
    SUBGOAL_THEN `compact(convex hull {v0:real^N,v1,v2,u1}) /\
                  compact(convex hull {v0:real^N,v1,v2,u2}) /\
                  locally_polyhedral(convex hull {v0:real^N,v1,v2,u1}) /\
                  locally_polyhedral(convex hull {v0:real^N,v1,v2,u2})`
    STRIP_ASSUME_TAC THENL
     [SIMP_TAC[COMPACT_CONVEX_HULL; FINITE_IMP_COMPACT; FINITE_INSERT;
               FINITE_EMPTY; LOCALLY_POLYHEDRAL_POLYTOPE;
               POLYTOPE_CONVEX_HULL];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC PL_MAP_ON_EQ THEN EXISTS_TAC `A1:real^N->real^3` THEN
      CONJ_TAC THENL [SIMP_TAC[moi_frn_yfold]; ALL_TAC] THEN
      MP_TAC(ISPECL [`convex hull {v0:real^N,v1,v2,u1}`; `A1:real^N->real^3`]
        MOI_FRN_PL_FLIP_AFFINE) THEN
      ASM_SIMP_TAC[];
      MATCH_MP_TAC PL_MAP_ON_EQ THEN
      EXISTS_TAC `\x. vector[((A2:real^N->real^3) x)$1; (A2 x)$2;
                             --((A2 x)$3)]:real^3` THEN
      CONJ_TAC THENL
       [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[moi_frn_yfold] THEN
        COND_CASES_TAC THEN REWRITE_TAC[] THEN
        SUBGOAL_THEN `(x:real^N) IN convex hull {v0,v1,v2}` MP_TAC THENL
         [MP_TAC(ASSUME `convex hull {v0,v1,v2,u1} INTER
                         convex hull {v0,v1,v2,u2} =
                         convex hull {v0:real^N,v1,v2}`) THEN
          DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[IN_INTER];
          ALL_TAC] THEN
        DISCH_THEN(fun th -> USE_THEN "TAU" (MP_TAC o C MATCH_MP th)) THEN
        STRIP_TAC THEN
        ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN
        UNDISCH_TAC `((A1:real^N->real^3) x)$3 = &0` THEN
        ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
        MP_TAC(ISPECL [`convex hull {v0:real^N,v1,v2,u2}`; `A2:real^N->real^3`]
          MOI_FRN_PL_FLIP_AFFINE) THEN
        ASM_SIMP_TAC[]];
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      SET_TAC[];
      MATCH_MP_TAC CLOSED_SUBSET THEN ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN
      SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN convex hull {v0,v1,v2,u1} UNION convex hull {v0,v1,v2,u2}
      ==> moi_frn_xfold v0 v1 v2 u1 u2
            (moi_frn_yfold (A1:real^N->real^3) A2 (convex hull {v0,v1,v2,u1})
               x) = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN REWRITE_TAC[IN_UNION] THEN
    ASM_CASES_TAC `(x:real^N) IN convex hull {v0,v1,v2,u1}` THENL
     [DISCH_TAC THEN
      USE_THEN "S1" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(x:real^N) IN convex hull {v0,v1,v2,u1}`))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[moi_frn_yfold; moi_frn_xfold];
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      USE_THEN "S2" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(x:real^N) IN convex hull {v0,v1,v2,u2}`))) THEN
      STRIP_TAC THEN
      ASM_REWRITE_TAC[moi_frn_yfold; moi_frn_xfold; VECTOR_3] THEN
      FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
        check (fun th -> is_eq(concl th) && rhs(concl th) = `x:real^N`)) THEN
      COND_CASES_TAC THENL
       [SUBGOAL_THEN `((A2:real^N->real^3) x)$3 = &0` SUBST1_TAC THENL
         [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        REWRITE_TAC[REAL_NEG_0; VECTOR_MUL_LZERO];
        VECTOR_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN O
      ==> x IN convex hull {v0,v1,v2,u1} UNION convex hull {v0,v1,v2,u2} /\
          abs(((A1:real^N->real^3) x)$1 - &1 / &3) < &1 / &20 /\
          abs((A1 x)$2 - &1 / &3) < &1 / &20 /\ abs((A1 x)$3 - &0) < &1 / &20 /\
          abs(((A2:real^N->real^3) x)$1 - &1 / &3) < &1 / &20 /\
          abs((A2 x)$2 - &1 / &3) < &1 / &20 /\ abs((A2 x)$3 - &0) < &1 / &20`
  (LABEL_TAC "OX") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `(O:real^N->bool) SUBSET
                convex hull {v0,v1,v2,u1} UNION convex hull {v0,v1,v2,u2}`) THEN
      REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `dist(w:real^N,x) < r1 /\ dist(w,x) < r2` STRIP_ASSUME_TAC
    THENL
     [UNDISCH_TAC `(x:real^N) IN O` THEN EXPAND_TAC "O" THEN EXPAND_TAC "r" THEN
      REWRITE_TAC[IN_INTER; IN_BALL; REAL_LT_MIN] THEN SIMP_TAC[];
      ALL_TAC] THEN
    USE_THEN "N1" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `dist(w:real^N,x) < r1`))) THEN
    USE_THEN "N2" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `dist(w:real^N,x) < r2`))) THEN
    ASM_REWRITE_TAC[VECTOR_3] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN O
      ==> (x IN derived_nbhd t l <=>
           &0 <= (moi_frn_psit (moi_frn_yfold (A1:real^N->real^3) A2
                    (convex hull {v0,v1,v2,u1}) x))$3)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    USE_THEN "OX" (fun th -> MP_TAC(MATCH_MP th (ASSUME `(x:real^N) IN O`))) THEN
    REWRITE_TAC[IN_UNION] THEN STRIP_TAC THEN
    REWRITE_TAC[MOI_FRN_PHIT_QINV_VALUES; moi_frn_yfold] THENL
     [ASM_REWRITE_TAC[] THEN
      USE_THEN "S1" (fun th -> MP_TAC(MATCH_MP th
        (ASSUME `(x:real^N) IN convex hull {v0,v1,v2,u1}`))) THEN
      STRIP_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `v0:real^N`; `v1:real^N`; `v2:real^N`; `u1:real^N`;
                     `(A1:real^N->real^3) x`] MOI_FRN_TET_NBHD_NEAR) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
      ASM_CASES_TAC `(x:real^N) IN convex hull {v0,v1,v2,u1}` THENL
       [ASM_REWRITE_TAC[] THEN
        USE_THEN "S1" (fun th -> MP_TAC(MATCH_MP th
          (ASSUME `(x:real^N) IN convex hull {v0,v1,v2,u1}`))) THEN
        STRIP_TAC THEN
        MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `v0:real^N`; `v1:real^N`; `v2:real^N`; `u1:real^N`;
                       `(A1:real^N->real^3) x`] MOI_FRN_TET_NBHD_NEAR) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN ASM_REAL_ARITH_TAC;
        ASM_REWRITE_TAC[VECTOR_3] THEN
        USE_THEN "S2" (fun th -> MP_TAC(MATCH_MP th
          (ASSUME `(x:real^N) IN convex hull {v0,v1,v2,u2}`))) THEN
        STRIP_TAC THEN
        MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                       `v0:real^N`; `v1:real^N`; `v2:real^N`; `u2:real^N`;
                       `(A2:real^N->real^3) x`] MOI_FRN_TET_NBHD_NEAR) THEN
        ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
        ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
        ASM_REAL_ARITH_TAC]];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_frn_xfold (v0:real^N) v1 v2 u1 u2 (moi_frn_phit (vec 0)) = w`
  ASSUME_TAC THENL
   [REWRITE_TAC[MOI_FRN_PHIT_QINV_VALUES; moi_frn_xfold; VECTOR_3;
                VEC_COMPONENT; REAL_LE_REFL; VECTOR_MUL_LZERO;
                VECTOR_ADD_RID] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `w:real^N` &&
      not(lhs(concl th) = `simplex_barycentre (convex hull {v0:real^N,v1,v2})`)))
    THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN convex hull {v0,v1,v2}` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {v0:real^N,v1,v2} SUBSET convex hull {v0,v1,v2,u1} /\
                convex hull {v0:real^N,v1,v2} SUBSET convex hull {v0,v1,v2,u2}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !q. norm q < d /\ &0 <= q$3
            ==> moi_frn_xfold (v0:real^N) v1 v2 u1 u2 (moi_frn_phit q) IN O /\
                moi_frn_yfold (A1:real^N->real^3) A2 (convex hull {v0,v1,v2,u1})
                  (moi_frn_xfold v0 v1 v2 u1 u2 (moi_frn_phit q)) =
                moi_frn_phit q`
  ASSUME_TAC THENL
   [MP_TAC(SPEC `vec 0:real^3` MOI_FRN_PHIT_CONTINUOUS) THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `&1 / &20`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "C1"))) THEN
    MP_TAC(ISPECL [`moi_frn_phit`; `moi_frn_xfold (v0:real^N) v1 v2 u1 u2`;
                   `vec 0:real^3`] CONTINUOUS_AT_COMPOSE) THEN
    REWRITE_TAC[MOI_FRN_PHIT_CONTINUOUS; MOI_FRN_XFOLD_CONTINUOUS] THEN
    REWRITE_TAC[continuous_at; o_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "C2"))) THEN
    EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `q:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN `dist(w:real^N,moi_frn_xfold v0 v1 v2 u1 u2 (moi_frn_phit q))
                  < r` ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN
      REMOVE_THEN "C2" (MP_TAC o SPEC `q:real^3`) THEN
      ASM_REWRITE_TAC[DIST_0];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `abs((moi_frn_phit q)$1 - &1 / &3) < &1 / &20 /\
      abs((moi_frn_phit q)$2 - &1 / &3) < &1 / &20 /\
      abs((moi_frn_phit q)$3) < &1 / &20`
    STRIP_ASSUME_TAC THENL
     [REMOVE_THEN "C1" (MP_TAC o SPEC `q:real^3`) THEN
      ASM_REWRITE_TAC[DIST_0; CONJUNCT1 MOI_FRN_PHIT_QINV_VALUES; dist] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`moi_frn_phit q - vector[&1 / &3; &1 / &3; &0]`; `1`]
        COMPONENT_LE_NORM) THEN
      MP_TAC(ISPECL [`moi_frn_phit q - vector[&1 / &3; &1 / &3; &0]`; `2`]
        COMPONENT_LE_NORM) THEN
      MP_TAC(ISPECL [`moi_frn_phit q - vector[&1 / &3; &1 / &3; &0]`; `3`]
        COMPONENT_LE_NORM) THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_3; REAL_SUB_RZERO] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `y = moi_frn_phit q` THEN
    UNDISCH_TAC `dist(w:real^N,moi_frn_xfold v0 v1 v2 u1 u2 y) < r` THEN
    EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `&0 < (y:real^3)$3` THENL
     [SUBGOAL_THEN `moi_frn_xfold (v0:real^N) v1 v2 u1 u2 y =
                    v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (u1 - v0)`
      SUBST1_TAC THENL
       [ASM_SIMP_TAC[moi_frn_xfold; REAL_LT_IMP_LE]; ALL_TAC] THEN
      SUBGOAL_THEN `v0 + (y:real^3)$1 % (v1 - v0) + y$2 % (v2 - v0) +
                    y$3 % (u1 - v0) IN
                    relative_interior(convex hull {v0:real^N,v1,v2,u1})`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_FRN_TET_RELINT THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FRN_RELINT_IN_OPEN_STAR THEN
        EXISTS_TAC `convex hull {v0:real^N,v1,v2,u1}` THEN ASM_REWRITE_TAC[] THEN
        ASM_MESON_TAC[SUBSET];
        REWRITE_TAC[moi_frn_yfold] THEN COND_CASES_TAC THENL
         [USE_THEN "AB1" (fun th -> REWRITE_TAC[th]);
          ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]]];
      ALL_TAC] THEN
    ASM_CASES_TAC `(y:real^3)$3 = &0` THENL
     [SUBGOAL_THEN `moi_frn_xfold (v0:real^N) v1 v2 u1 u2 y =
                    v0 + y$1 % (v1 - v0) + y$2 % (v2 - v0)`
      SUBST1_TAC THENL
       [ASM_REWRITE_TAC[moi_frn_xfold; REAL_LE_REFL; VECTOR_MUL_LZERO;
                        VECTOR_ADD_RID];
        ALL_TAC] THEN
      SUBGOAL_THEN `v0 + (y:real^3)$1 % (v1 - v0) + y$2 % (v2 - v0) IN
                    relative_interior(convex hull {v0:real^N,v1,v2})`
      ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_FRN_TRI_RELINT THEN ASM_REWRITE_TAC[] THEN
        ASM_REAL_ARITH_TAC;
        ALL_TAC] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FRN_RELINT_IN_OPEN_STAR THEN
        EXISTS_TAC `convex hull {v0:real^N,v1,v2}` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `v0 + (y:real^3)$1 % (v1 - v0) + y$2 % (v2 - v0) IN
                    convex hull {v0:real^N,v1,v2,u1}` ASSUME_TAC THENL
       [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
      ASM_REWRITE_TAC[moi_frn_yfold] THEN
      MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u1:real^N`;
                     `A1:real^N->real^3`; `(y:real^3)$1`; `(y:real^3)$2`]
        MOI_FRN_TRI_FACE_A) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
      ASM_REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3];
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3)$3 < &0` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN
     `moi_frn_xfold (v0:real^N) v1 v2 u1 u2 y =
      v0 + (vector[(y:real^3)$1; y$2; --(y$3)]:real^3)$1 % (v1 - v0) +
      (vector[(y:real^3)$1; y$2; --(y$3)]:real^3)$2 % (v2 - v0) +
      (vector[(y:real^3)$1; y$2; --(y$3)]:real^3)$3 % (u2 - v0)`
    SUBST1_TAC THENL
     [ASM_SIMP_TAC[moi_frn_xfold; REAL_ARITH `y < &0 ==> ~(&0 <= y)`;
                   VECTOR_3] THEN VECTOR_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN
     `v0 + (vector[(y:real^3)$1; y$2; --(y$3)]:real^3)$1 % (v1 - v0) +
      (vector[(y:real^3)$1; y$2; --(y$3)]:real^3)$2 % (v2 - v0) +
      (vector[(y:real^3)$1; y$2; --(y$3)]:real^3)$3 % (u2 - v0) IN
      relative_interior(convex hull {v0:real^N,v1,v2,u2})`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FRN_TET_RELINT THEN ASM_REWRITE_TAC[VECTOR_3] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FRN_RELINT_IN_OPEN_STAR THEN
      EXISTS_TAC `convex hull {v0:real^N,v1,v2,u2}` THEN ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `~(v0 + (vector[(y:real^3)$1; y$2; --(y$3)]:real^3)$1 % (v1 - v0) +
        (vector[(y:real^3)$1; y$2; --(y$3)]:real^3)$2 % (v2 - v0) +
        (vector[(y:real^3)$1; y$2; --(y$3)]:real^3)$3 % (u2 - v0) IN
        convex hull {v0:real^N,v1,v2,u1})`
    ASSUME_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN
       `v0 + (vector[(y:real^3)$1; y$2; --(y$3)]:real^3)$1 % (v1 - v0) +
        (vector[(y:real^3)$1; y$2; --(y$3)]:real^3)$2 % (v2 - v0) +
        (vector[(y:real^3)$1; y$2; --(y$3)]:real^3)$3 % (u2 - v0) IN
        convex hull {v0:real^N,v1,v2}`
      MP_TAC THENL
       [MP_TAC(ASSUME `convex hull {v0,v1,v2,u1} INTER
                       convex hull {v0,v1,v2,u2} =
                       convex hull {v0:real^N,v1,v2}`) THEN
        DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[IN_INTER] THEN
        ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
        ALL_TAC] THEN
      DISCH_THEN(fun th -> USE_THEN "TAU" (MP_TAC o C MATCH_MP th)) THEN
      USE_THEN "AB2" (fun th -> REWRITE_TAC[th]) THEN
      DISCH_THEN(fun th -> MP_TAC(CONJUNCT2 th) THEN REWRITE_TAC[CONJUNCT1 th])
      THEN REWRITE_TAC[VECTOR_3] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ASM_REWRITE_TAC[moi_frn_yfold] THEN
    USE_THEN "AB2" (fun th -> REWRITE_TAC[th]) THEN
    REWRITE_TAC[CART_EQ; DIMINDEX_3; FORALL_3; VECTOR_3] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_CHART_LINK_BALL THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull {v0,v1,v2,u1} UNION convex hull {v0:real^N,v1,v2,u2}`;
    `O:real^N->bool`;
    `moi_frn_yfold (A1:real^N->real^3) A2 (convex hull {v0,v1,v2,u1})`;
    `moi_frn_xfold (v0:real^N) v1 v2 u1 u2`; `moi_frn_psit`; `moi_frn_phit`]
  THEN ASM_REWRITE_TAC[MOI_FRN_PSIT_PL; MOI_FRN_PSIT_PHIT;
                       MOI_FRN_PHIT_CONTINUOUS; MOI_FRN_XFOLD_CONTINUOUS]);;

let MOI_FRN_TRI_CHART_BD = prove
 (`!(t:(real^N->bool)->bool) l v0 v1 v2 u1.
     combinatorial_manifold_with_boundary 3 t /\ simplicial_subcomplex l t /\
     convex hull {v0,v1,v2} IN barycentric_subdivision t /\
     convex hull {v0,v1,v2,u1} IN barycentric_subdivision t /\
     ~affine_dependent {v0,v1,v2} /\
     ~affine_dependent {v0,v1,v2,u1} /\
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2) /\
     ~(u1 = v0) /\ ~(u1 = v1) /\ ~(u1 = v2) /\
     v0 IN UNIONS l /\ v1 IN UNIONS l /\ ~(v2 IN UNIONS l) /\
     moi_sta_open_star (barycentric_subdivision t)
        (simplex_barycentre (convex hull {v0,v1,v2})) SUBSET
     convex hull {v0,v1,v2,u1}
     ==> pl_ball 2 (UNIONS (simplicial_link (derived_nbhd_complex t l)
                     (simplex_barycentre (convex hull {v0,v1,v2}))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC(CONJUNCT1(REWRITE_RULE[combinatorial_manifold_with_boundary]
   (ASSUME `combinatorial_manifold_with_boundary 3
              (t:(real^N->bool)->bool)`))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(v0:real^N = u1) /\ ~(v1 = u1) /\ ~(v2 = u1)`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`]
    MOI_FRN_TRI_BARYCENTRE) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(ASSUME_TAC o SYM) THEN
  SUBGOAL_THEN `3 <= dimindex(:N)` ASSUME_TAC THENL
   [MP_TAC(ISPEC `convex hull {v0:real^N,v1,v2,u1}` AFF_DIM_LE_UNIV) THEN
    ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
    REWRITE_TAC[INT_ARITH `&4 - &1:int <= x <=> &3 <= x`; INT_OF_NUM_LE];
    ALL_TAC] THEN
  SUBGOAL_THEN `{simplex_barycentre (convex hull {v0:real^N,v1,v2})} IN
                derived_nbhd_complex t l` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_NBHD_COMPLEX_VERTEX_EXISTS THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `v0:real^N` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (convex hull {v0:real^N,v1,v2}) IN
                relative_interior (convex hull {v0,v1,v2})` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `simplex_barycentre (convex hull {v0:real^N,v1,v2})`)) THEN
    MATCH_MP_TAC MOI_FRN_TRI_RELINT THEN
    ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `w = simplex_barycentre (convex hull {v0:real^N,v1,v2})` THEN
  MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u1:real^N`]
    MOI_FRN_TET_COORDS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `A1:real^N->real^3` (CONJUNCTS_THEN2
    (LABEL_TAC "Aaff1") (CONJUNCTS_THEN2 (LABEL_TAC "AB1") (LABEL_TAC "BA1"))))
  THEN
  SUBGOAL_THEN
   `!x:real^N. x IN convex hull {v0,v1,v2,u1}
      ==> v0 + ((A1:real^N->real^3) x)$1 % (v1 - v0) + (A1 x)$2 % (v2 - v0) +
          (A1 x)$3 % (u1 - v0) = x /\
          &0 <= (A1 x)$1 /\ &0 <= (A1 x)$2 /\ &0 <= (A1 x)$3 /\
          &0 <= &1 - (A1 x)$1 - (A1 x)$2 - (A1 x)$3`
  (LABEL_TAC "S1") THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN CONJ_TAC THENL
     [USE_THEN "BA1" MATCH_MP_TAC THEN
      MP_TAC(ISPEC `{v0:real^N,v1,v2,u1}` CONVEX_HULL_SUBSET_AFFINE_HULL) THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u1:real^N`;
                   `(A1:real^N->real^3) x`] MOI_FRN_TCOEF_VSUM) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`v0:real^N`; `v1:real^N`; `v2:real^N`; `u1:real^N`;
                   `A1:real^N->real^3`; `x:real^N`] MOI_FRN_TET_HULL_COEF) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `v0:real^N` th) THEN
      MP_TAC(SPEC `v1:real^N` th) THEN MP_TAC(SPEC `v2:real^N` th) THEN
      MP_TAC(SPEC `u1:real^N` th)) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(A1:real^N->real^3) w = vector[&1 / &3; &1 / &3; &0]`
  ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `w:real^N` &&
      not(lhs(concl th) = `simplex_barycentre (convex hull {v0:real^N,v1,v2})`)))
    THEN MATCH_MP_TAC MOI_FRN_TRI_FACE_A THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`A1:real^N->real^3`; `w:real^N`; `&1 / &20`]
    MOI_FRN_AFFINE_NEAR) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` (CONJUNCTS_THEN2 ASSUME_TAC
    (LABEL_TAC "N1"))) THEN
  ABBREV_TAC `O = moi_sta_open_star (barycentric_subdivision t) (w:real^N)
                  INTER ball(w,r)` THEN
  SUBGOAL_THEN `open_in (subtopology euclidean (UNIONS t)) (O:real^N->bool)`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC OPEN_IN_INTER_OPEN THEN
    REWRITE_TAC[OPEN_BALL] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS (barycentric_subdivision t):real^N->bool`)) THEN
    MATCH_MP_TAC MOI_STA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN O` ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER; CENTRE_IN_BALL] THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FRN_RELINT_IN_OPEN_STAR THEN
    EXISTS_TAC `convex hull {v0:real^N,v1,v2}` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `(O:real^N->bool) SUBSET convex hull {v0,v1,v2,u1}`
  ASSUME_TAC THENL
   [EXPAND_TAC "O" THEN MATCH_MP_TAC(SET_RULE
     `!a b c:real^N->bool. a SUBSET c ==> a INTER b SUBSET c`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `pl_map_on (convex hull {v0:real^N,v1,v2,u1})
                          (A1:real^N->real^3)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`convex hull {v0:real^N,v1,v2,u1}`; `A1:real^N->real^3`]
      MOI_FRN_PL_FLIP_AFFINE) THEN
    ASM_SIMP_TAC[LOCALLY_POLYHEDRAL_POLYTOPE; POLYTOPE_CONVEX_HULL;
                 FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN convex hull {v0,v1,v2,u1}
      ==> (\y:real^3. (v0:real^N) + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (u1 - v0))
            ((A1:real^N->real^3) x) = x`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN REWRITE_TAC[] THEN
    USE_THEN "S1" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(x:real^N) IN convex hull {v0,v1,v2,u1}`))) THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N. x IN O
      ==> (x IN derived_nbhd t l <=>
           &0 <= ((moi_frn_qmap o moi_frn_psit) ((A1:real^N->real^3) x))$3)`
  ASSUME_TAC THENL
   [X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN convex hull {v0,v1,v2,u1} /\ dist(w,x) < r`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ASSUME `(O:real^N->bool) SUBSET convex hull {v0,v1,v2,u1}`) THEN
        REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
        ASM_REWRITE_TAC[];
        UNDISCH_TAC `(x:real^N) IN O` THEN EXPAND_TAC "O" THEN
        REWRITE_TAC[IN_INTER; IN_BALL] THEN SIMP_TAC[]];
      ALL_TAC] THEN
    USE_THEN "N1" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `dist(w:real^N,x) < r`))) THEN
    ASM_REWRITE_TAC[VECTOR_3] THEN STRIP_TAC THEN
    USE_THEN "S1" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(x:real^N) IN convex hull {v0,v1,v2,u1}`))) THEN
    STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `v0:real^N`; `v1:real^N`; `v2:real^N`; `u1:real^N`;
                   `(A1:real^N->real^3) x`] MOI_FRN_TET_NBHD_NEAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[o_THM; MOI_FRN_PHIT_QINV_VALUES] THEN
    REWRITE_TAC[moi_frn_psit; VECTOR_3] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(\y:real^3. (v0:real^N) + y$1 % (v1 - v0) + y$2 % (v2 - v0) + y$3 % (u1 - v0))
      ((moi_frn_phit o moi_frn_qinv) (vec 0)) = w`
  ASSUME_TAC THENL
   [REWRITE_TAC[o_THM; CONJUNCT1 MOI_FRN_PHIT_QINV_VALUES;
                CONJUNCT1(CONJUNCT2 MOI_FRN_PHIT_QINV_VALUES)] THEN
    REWRITE_TAC[VECTOR_3; VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rhs(concl th) = `w:real^N` &&
      not(lhs(concl th) = `simplex_barycentre (convex hull {v0:real^N,v1,v2})`)))
    THEN REFL_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(w:real^N) IN convex hull {v0,v1,v2}` ASSUME_TAC THENL
   [ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {v0:real^N,v1,v2} SUBSET convex hull {v0,v1,v2,u1}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(moi_frn_phit o moi_frn_qinv) continuous at (vec 0)`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_AT_COMPOSE THEN
    REWRITE_TAC[MOI_FRN_PHIT_CONTINUOUS; MOI_FRN_QINV_CONTINUOUS];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?d. &0 < d /\
        !q. norm q < d /\ &0 <= q$3
            ==> (\y:real^3. (v0:real^N) + y$1 % (v1 - v0) + y$2 % (v2 - v0) +
                            y$3 % (u1 - v0))
                  ((moi_frn_phit o moi_frn_qinv) q) IN O /\
                (A1:real^N->real^3)
                  ((\y:real^3. (v0:real^N) + y$1 % (v1 - v0) + y$2 % (v2 - v0) +
                               y$3 % (u1 - v0))
                     ((moi_frn_phit o moi_frn_qinv) q)) =
                (moi_frn_phit o moi_frn_qinv) q`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `(moi_frn_phit o moi_frn_qinv) continuous at (vec 0)`) THEN
    REWRITE_TAC[continuous_at] THEN DISCH_THEN(MP_TAC o SPEC `&1 / &20`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    DISCH_THEN(X_CHOOSE_THEN `d1:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "C1"))) THEN
    MP_TAC(ISPECL [`moi_frn_phit o moi_frn_qinv`;
                   `\y:real^3. (v0:real^N) + y$1 % (v1 - v0) + y$2 % (v2 - v0) +
                               y$3 % (u1 - v0)`;
                   `vec 0:real^3`] CONTINUOUS_AT_COMPOSE) THEN
    ASM_REWRITE_TAC[MOI_FRN_PARAM_CONTINUOUS] THEN
    REWRITE_TAC[continuous_at] THEN
    DISCH_THEN(MP_TAC o SPEC `r:real`) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `d2:real` (CONJUNCTS_THEN2 ASSUME_TAC
      (LABEL_TAC "C2"))) THEN
    EXISTS_TAC `min d1 d2` THEN ASM_REWRITE_TAC[REAL_LT_MIN] THEN
    X_GEN_TAC `q:real^3` THEN STRIP_TAC THEN
    SUBGOAL_THEN
     `dist(w:real^N,(\y:real^3. (v0:real^N) + y$1 % (v1 - v0) + y$2 % (v2 - v0) +
                                y$3 % (u1 - v0))
                    ((moi_frn_phit o moi_frn_qinv) q)) < r`
    ASSUME_TAC THENL
     [ONCE_REWRITE_TAC[DIST_SYM] THEN
      REMOVE_THEN "C2" (MP_TAC o SPEC `q:real^3`) THEN
      ASM_REWRITE_TAC[DIST_0; o_THM];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `abs(((moi_frn_phit o moi_frn_qinv) q)$1 - &1 / &3) < &1 / &20 /\
      abs(((moi_frn_phit o moi_frn_qinv) q)$2 - &1 / &3) < &1 / &20 /\
      abs(((moi_frn_phit o moi_frn_qinv) q)$3) < &1 / &20`
    STRIP_ASSUME_TAC THENL
     [REMOVE_THEN "C1" (MP_TAC o SPEC `q:real^3`) THEN
      ASM_REWRITE_TAC[DIST_0; dist] THEN
      REWRITE_TAC[o_THM; CONJUNCT1 MOI_FRN_PHIT_QINV_VALUES;
                  CONJUNCT1(CONJUNCT2 MOI_FRN_PHIT_QINV_VALUES)] THEN
      DISCH_TAC THEN
      MP_TAC(ISPECL [`moi_frn_phit (moi_frn_qinv q) -
                      vector[&1 / &3; &1 / &3; &0]`; `1`] COMPONENT_LE_NORM) THEN
      MP_TAC(ISPECL [`moi_frn_phit (moi_frn_qinv q) -
                      vector[&1 / &3; &1 / &3; &0]`; `2`] COMPONENT_LE_NORM) THEN
      MP_TAC(ISPECL [`moi_frn_phit (moi_frn_qinv q) -
                      vector[&1 / &3; &1 / &3; &0]`; `3`] COMPONENT_LE_NORM) THEN
      REWRITE_TAC[VECTOR_SUB_COMPONENT; VECTOR_3; REAL_SUB_RZERO] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `&0 <= ((moi_frn_phit o moi_frn_qinv) q)$3` ASSUME_TAC THENL
     [REWRITE_TAC[o_THM; MOI_FRN_PHIT_QINV_VALUES] THEN ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    ABBREV_TAC `y = (moi_frn_phit o moi_frn_qinv) q` THEN
    UNDISCH_TAC
     `dist(w:real^N,(\y:real^3. (v0:real^N) + y$1 % (v1 - v0) + y$2 % (v2 - v0) +
                                y$3 % (u1 - v0)) y) < r` THEN
    EXPAND_TAC "O" THEN REWRITE_TAC[IN_INTER; IN_BALL] THEN
    DISCH_THEN(fun th -> REWRITE_TAC[th]) THEN
    USE_THEN "AB1" (fun th -> REWRITE_TAC[th]) THEN
    ASM_CASES_TAC `&0 < (y:real^3)$3` THENL
     [MATCH_MP_TAC MOI_FRN_RELINT_IN_OPEN_STAR THEN
      EXISTS_TAC `convex hull {v0:real^N,v1,v2,u1}` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_MESON_TAC[SUBSET]; ALL_TAC] THEN
      MATCH_MP_TAC MOI_FRN_TET_RELINT THEN ASM_REWRITE_TAC[] THEN
      ASM_REAL_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(y:real^3)$3 = &0` ASSUME_TAC THENL
     [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    ASM_REWRITE_TAC[VECTOR_MUL_LZERO; VECTOR_ADD_RID] THEN
    MATCH_MP_TAC MOI_FRN_RELINT_IN_OPEN_STAR THEN
    EXISTS_TAC `convex hull {v0:real^N,v1,v2}` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FRN_TRI_RELINT THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_CHART_LINK_BALL THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull {v0:real^N,v1,v2,u1}`; `O:real^N->bool`;
    `A1:real^N->real^3`;
    `\y:real^3. (v0:real^N) + y$1 % (v1 - v0) + y$2 % (v2 - v0) +
                y$3 % (u1 - v0)`;
    `moi_frn_qmap o moi_frn_psit`; `moi_frn_phit o moi_frn_qinv`] THEN
  ASM_REWRITE_TAC[MOI_FRN_PARAM_CONTINUOUS] THEN
  REWRITE_TAC[o_THM; MOI_FRN_PSIT_PHIT; MOI_FRN_QMAP_QINV] THEN
  MATCH_MP_TAC PL_MAP_ON_COMPOSE THEN EXISTS_TAC `(:real^3)` THEN
  REWRITE_TAC[MOI_FRN_PSIT_PL; MOI_FRN_QMAP_PL; SUBSET_UNIV]);;

let MOI_FRN_FRONTIER_LINK_TRI2 = prove
 (`!(t:(real^N->bool)->bool) l v0 v1 v2.
     combinatorial_manifold_with_boundary 3 t /\ simplicial_subcomplex l t /\
     convex hull {v0,v1,v2} IN barycentric_subdivision t /\
     ~affine_dependent {v0,v1,v2} /\
     ~(v0 = v1) /\ ~(v0 = v2) /\ ~(v1 = v2) /\
     convex hull {v0,v1,v2} INTER UNIONS l = convex hull {v0,v1}
     ==> pl_ball 2 (UNIONS (simplicial_link (derived_nbhd_complex t l)
                     (simplex_barycentre (convex hull {v0,v1,v2}))))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC(CONJUNCT1(REWRITE_RULE[combinatorial_manifold_with_boundary]
   (ASSUME `combinatorial_manifold_with_boundary 3
              (t:(real^N->bool)->bool)`))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3
                  (barycentric_subdivision t:(real^N->bool)->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[COMBINATORIAL_WB_BARYCENTRIC]; ALL_TAC] THEN
  SUBGOAL_THEN `(v0:real^N) IN UNIONS l /\ v1 IN UNIONS l /\
                ~(v2 IN UNIONS l)` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `~((v2:real^N) IN convex hull {v0,v1})` ASSUME_TAC THENL
     [DISCH_TAC THEN
      UNDISCH_TAC `~affine_dependent {v0:real^N,v1,v2}` THEN
      REWRITE_TAC[affine_dependent] THEN EXISTS_TAC `v2:real^N` THEN
      REWRITE_TAC[IN_INSERT] THEN
      SUBGOAL_THEN `{v0:real^N,v1,v2} DELETE v2 = {v0,v1}` SUBST1_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      ASM_MESON_TAC[CONVEX_HULL_SUBSET_AFFINE_HULL; SUBSET];
      ALL_TAC] THEN
    MP_TAC(ASSUME `convex hull {v0,v1,v2} INTER UNIONS l =
                   convex hull {v0:real^N,v1}`) THEN
    REWRITE_TAC[EXTENSION; IN_INTER] THEN DISCH_TAC THEN
    REPEAT CONJ_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `v0:real^N`);
      FIRST_X_ASSUM(MP_TAC o SPEC `v1:real^N`);
      FIRST_X_ASSUM(MP_TAC o SPEC `v2:real^N`)] THEN
    ASM_SIMP_TAC[HULL_INC; IN_INSERT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `v0:real^N`; `v1:real^N`; `v2:real^N`]
    MOI_FRN_TRIANGLE_COFACES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u1:real^N` (X_CHOOSE_THEN `u2:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `aff_dim(convex hull {v0:real^N,v1,v2}) = &2 /\
    aff_dim(convex hull {v0:real^N,v1,v2,u1}) = &3 /\
    aff_dim(convex hull {v0:real^N,v1,v2,u2}) = &3`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_AFFINE_INDEPENDENT] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `convex hull {v0:real^N,v1,v2} SUBSET convex hull {v0,v1,v2,u1} /\
                convex hull {v0:real^N,v1,v2} SUBSET convex hull {v0,v1,v2,u2}`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (convex hull {v0:real^N,v1,v2}) IN
                relative_interior (convex hull {v0,v1,v2})` ASSUME_TAC THENL
   [ASM_SIMP_TAC[MOI_FRN_TRI_BARYCENTRE] THEN
    MATCH_MP_TAC MOI_FRN_TRI_RELINT THEN ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `moi_sta_open_star (barycentric_subdivision t)
      (simplex_barycentre (convex hull {v0:real^N,v1,v2})) SUBSET
    convex hull {v0,v1,v2,u1} UNION convex hull {v0,v1,v2,u2}`
  ASSUME_TAC THENL
   [REWRITE_TAC[SUBSET; moi_sta_open_star; IN_ELIM_THM; IN_UNIONS] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool`
      STRIP_ASSUME_TAC) (MP_TAC o SPEC `s:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `convex hull {v0:real^N,v1,v2} SUBSET s` ASSUME_TAC THENL
     [SUBGOAL_THEN `convex hull {v0:real^N,v1,v2} SUBSET
                    convex hull {v0,v1,v2} INTER s` MP_TAC THENL
       [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN
        EXISTS_TAC `convex hull {v0:real^N,v1,v2}` THEN
        REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
         [UNDISCH_TAC `moi_bar_complex
                        (barycentric_subdivision t:(real^N->bool)->bool)` THEN
          REWRITE_TAC[moi_bar_complex] THEN ASM_MESON_TAC[];
          REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
          EXISTS_TAC `simplex_barycentre (convex hull {v0:real^N,v1,v2})` THEN
          ASM_REWRITE_TAC[IN_INTER] THEN
          ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
        SET_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &3 /\ &2 <= aff_dim s`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MP_TAC(ISPEC `barycentric_subdivision t:(real^N->bool)->bool`
          CM_WB_DIM) THEN ASM_REWRITE_TAC[] THEN
        DISCH_THEN(MP_TAC o SPEC `s:real^N->bool`) THEN ASM_REWRITE_TAC[];
        FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) o
          check (fun th -> is_eq(concl th) &&
            rhs(concl th) = `&2:int`)) THEN
        MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    ASM_CASES_TAC `aff_dim(s:real^N->bool) = &3` THENL
     [FIRST_X_ASSUM(MP_TAC o SPEC `s:real^N->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `u2:real^N`)) (concl th)))
      THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `s = convex hull {v0:real^N,v1,v2}` SUBST_ALL_TAC THENL
     [CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC;
      ASM SET_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `u1:real^N = u2` THENL
   [FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MATCH_MP_TAC MOI_FRN_TRI_CHART_BD THEN EXISTS_TAC `u2:real^N` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_TRI_CHART_INT THEN
  MAP_EVERY EXISTS_TAC [`u1:real^N`; `u2:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(convex hull {v0:real^N,v1,v2,u1} = convex hull {v0,v1,v2,u2})`
  ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `{v0:real^N,v1,v2,u1} = {v0,v1,v2,u2}` MP_TAC THENL
     [MP_TAC(ISPEC `{v0:real^N,v1,v2,u1}`
        EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      MP_TAC(ISPEC `{v0:real^N,v1,v2,u2}`
        EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(MP_TAC o SPEC `u1:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {v0,v1,v2,u1} INTER convex hull {v0,v1,v2,u2} IN
    barycentric_subdivision t /\
    (convex hull {v0,v1,v2,u1} INTER convex hull {v0,v1,v2,u2}) face_of
    convex hull {v0:real^N,v1,v2,u1}`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `moi_bar_complex
                  (barycentric_subdivision t:(real^N->bool)->bool)`) THEN
    REWRITE_TAC[moi_bar_complex] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (K ALL_TAC) (CONJUNCTS_THEN2 ASSUME_TAC
      (MP_TAC o SPECL [`convex hull {v0:real^N,v1,v2,u1}`;
                       `convex hull {v0:real^N,v1,v2,u2}`]))) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `convex hull {v0:real^N,v1,v2,u1}` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `X = convex hull {v0,v1,v2,u1} INTER
                  convex hull {v0:real^N,v1,v2,u2}` THEN
  SUBGOAL_THEN `convex hull {v0:real^N,v1,v2} SUBSET X /\
                X SUBSET convex hull {v0,v1,v2,u1} /\
                X SUBSET convex hull {v0,v1,v2,u2}` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "X" THEN REWRITE_TAC[INTER_SUBSET; SUBSET_INTER] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 <= aff_dim(X:real^N->bool) /\ aff_dim X <= &3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [FIRST_ASSUM((fun th -> GEN_REWRITE_TAC LAND_CONV [SYM th]) o
        check (fun th -> is_eq(concl th) && rhs(concl th) = `&2:int`)) THEN
      MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM_REWRITE_TAC[];
      FIRST_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
        check (fun th -> is_eq(concl th) && rhs(concl th) = `&3:int`)) THEN
      MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC `aff_dim(X:real^N->bool) = &3` THENL
   [SUBGOAL_THEN `X = convex hull {v0:real^N,v1,v2,u1} /\
                  X = convex hull {v0:real^N,v1,v2,u2}` MP_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
      EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      DISCH_THEN(fun th -> UNDISCH_TAC
        `~(convex hull {v0:real^N,v1,v2,u1} = convex hull {v0,v1,v2,u2})` THEN
        REWRITE_TAC[GSYM(CONJUNCT1 th); GSYM(CONJUNCT2 th)])];
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC MOI_FM3_LF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC]);;

(* ========================================================================= *)
(* The vertex links of N', the boundary of N' and the theorem                *)
(* DERIVED_NBHD_COMBINATORIAL.                                               *)
(* A point of N lies in complex_boundary N' iff it has no euclidean         *)
(* neighbourhood in N; by invariance of domain this happens iff it is on    *)
(* the frontier of N in UNIONS t or on complex_boundary t.                  *)
(* ========================================================================= *)

(* The vertex links of N'.                                                   *)

let MOI_FRN_NBHD_VERTEX_LINK = prove
 (`!(t:(real^N->bool)->bool) l w.
     combinatorial_manifold_with_boundary 3 t /\ simplicial_subcomplex l t /\
     {w} IN derived_nbhd_complex t l
     ==> pl_sphere 2 (UNIONS (simplicial_link (derived_nbhd_complex t l) w)) \/
         pl_ball 2 (UNIONS (simplicial_link (derived_nbhd_complex t l) w))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(ASSUME_TAC o CONJUNCT1 o
    REWRITE_RULE[combinatorial_manifold_with_boundary]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3
     (barycentric_subdivision t:(real^N->bool)->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[COMBINATORIAL_WB_BARYCENTRIC]; ALL_TAC] THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3
     (barycentric_subdivision (barycentric_subdivision t):(real^N->bool)->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[COMBINATORIAL_WB_BARYCENTRIC]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `w:real^N`] MOI_FRN_NBHD_COMPLEX_VERTEX_IMP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `{simplex_barycentre tau:real^N} IN
                barycentric_subdivision (barycentric_subdivision t)`
  ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_DERIVED_NBHD_COMPLEX_SUBCOMPLEX; simplicial_subcomplex;
                  SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `tau:real^N->bool`] MOI_FRN_FULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(tau:real^N->bool) SUBSET UNIONS l` THENL
   [SUBGOAL_THEN `tau INTER UNIONS l = tau:real^N->bool` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `tau:real^N->bool`] MOI_FRN_LINK_INNER) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    UNDISCH_TAC `combinatorial_manifold_with_boundary 3
     (barycentric_subdivision (barycentric_subdivision t):(real^N->bool)->bool)`
    THEN REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
    DISCH_THEN(MP_TAC o SPEC `simplex_barycentre tau:real^N` o CONJUNCT2) THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV THEN SIMP_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `tau:real^N->bool`] MOI_FRN_SIMPLEX_CARD_LE) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `V = {v:real^N | v extreme_point_of tau}` THEN STRIP_TAC THEN
  SUBGOAL_THEN `?W. W SUBSET V /\ tau INTER UNIONS l = convex hull (W:real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPECL [`V:real^N->bool`; `tau INTER UNIONS l:real^N->bool`]
      FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM(fun th0 -> REWRITE_TAC[SYM(check (fun th ->
      is_eq(concl th) && lhs(concl th) = `tau:real^N->bool`) th0)]) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(W:real^N->bool = {}) /\ ~(W = V)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN DISCH_TAC THENL
     [UNDISCH_TAC `~(tau INTER UNIONS l:real^N->bool = {})` THEN
      REWRITE_TAC[ASSUME `tau INTER UNIONS l = convex hull (W:real^N->bool)`;
                  ASSUME `W:real^N->bool = {}`; CONVEX_HULL_EMPTY];
      UNDISCH_TAC `~((tau:real^N->bool) SUBSET UNIONS l)` THEN
      SUBGOAL_THEN `tau INTER UNIONS l = tau:real^N->bool` MP_TAC THENL
       [REWRITE_TAC[ASSUME `tau INTER UNIONS l = convex hull (W:real^N->bool)`;
                    ASSUME `W:real^N->bool = V`] THEN
        CONV_TAC SYM_CONV THEN FIRST_ASSUM ACCEPT_TAC;
        SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD(W:real^N->bool) < CARD(V:real^N->bool) /\ 1 <= CARD W`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CARD_PSUBSET THEN
      ASM_REWRITE_TAC[PSUBSET];
      REWRITE_TAC[ARITH_RULE `1 <= n <=> ~(n = 0)`] THEN
      MP_TAC(ISPEC `W:real^N->bool` CARD_EQ_0) THEN ANTS_TAC THENL
       [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `V:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC THEN FIRST_ASSUM ACCEPT_TAC]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`V:real^N->bool`; `W:real^N->bool`] MOI_FRN_SPLIT_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN(LABEL_TAC "split")] THEN
  ASM_CASES_TAC `CARD(W:real^N->bool) = 1` THENL
   [USE_THEN "split" (MP_TAC o el 3 o CONJUNCTS) THEN
    REWRITE_TAC[ASSUME `CARD(W:real^N->bool) = 1`] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    UNDISCH_TAC `tau INTER UNIONS l = convex hull {a:real^N}` THEN
    REWRITE_TAC[CONVEX_HULL_SING] THEN DISCH_TAC THEN
    SUBGOAL_THEN `{a:real^N} IN barycentric_subdivision l` ASSUME_TAC THENL
     [MP_TAC(ASSUME `tau INTER UNIONS l IN
                     barycentric_subdivision (l:(real^N->bool)->bool)`) THEN
      REWRITE_TAC[ASSUME `tau INTER UNIONS l = {a:real^N}`];
      ALL_TAC] THEN
    SUBGOAL_THEN `{a:real^N} IN barycentric_subdivision t` ASSUME_TAC THENL
     [MP_TAC(ASSUME `simplicial_subcomplex (barycentric_subdivision l)
                       (barycentric_subdivision t:(real^N->bool)->bool)`) THEN
      REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN FIRST_ASSUM ACCEPT_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(a:real^N) IN tau` ASSUME_TAC THENL
     [MP_TAC(ASSUME `tau INTER UNIONS l = {a:real^N}`) THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `tau:real^N->bool`; `a:real^N`] MOI_FRN_LINK_SINGLE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[]; DISCH_THEN SUBST1_TAC] THEN
    MP_TAC(ISPECL
     [`barycentric_subdivision (barycentric_subdivision t):(real^N->bool)->bool`;
      `a:real^N`] MOI_FRN_CSTAR_CMWB) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FRN_SING_IN_BARY THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
    DISCH_THEN(MP_TAC o SPEC `simplex_barycentre tau:real^N` o CONJUNCT2) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
    MATCH_MP_TAC MOI_FRN_EDGE_IN_CSTAR THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISJ2_TAC THEN
  SUBGOAL_THEN `(CARD(V:real^N->bool) = 4 /\ CARD(W:real^N->bool) = 2) \/
                (CARD V = 4 /\ CARD W = 3) \/ (CARD V = 3 /\ CARD W = 2)`
  MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`CARD(W:real^N->bool) < CARD(V:real^N->bool)`;
      `CARD(V:real^N->bool) <= 4`; `1 <= CARD(W:real^N->bool)`;
      `~(CARD(W:real^N->bool) = 1)`] THEN ARITH_TAC;
    ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
    is_eq(concl th) && lhs(concl th) = `tau:real^N->bool`)) THEN
  STRIP_TAC THENL
   [USE_THEN "split" (MP_TAC o el 0 o CONJUNCTS) THEN
    REWRITE_TAC[ASSUME `CARD(V:real^N->bool) = 4`;
                ASSUME `CARD(W:real^N->bool) = 2`] THEN
    DISCH_THEN(X_CHOOSE_THEN `v0:real^N` (X_CHOOSE_THEN `v1:real^N`
      (X_CHOOSE_THEN `v2:real^N` (X_CHOOSE_THEN `v3:real^N`
         STRIP_ASSUME_TAC)))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `V:real^N->bool`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `W:real^N->bool`)) THEN
    MATCH_MP_TAC MOI_FRN_FRONTIER_LINK_TET2 THEN ASM_REWRITE_TAC[];
    USE_THEN "split" (MP_TAC o el 1 o CONJUNCTS) THEN
    REWRITE_TAC[ASSUME `CARD(V:real^N->bool) = 4`;
                ASSUME `CARD(W:real^N->bool) = 3`] THEN
    DISCH_THEN(X_CHOOSE_THEN `v0:real^N` (X_CHOOSE_THEN `v1:real^N`
      (X_CHOOSE_THEN `v2:real^N` (X_CHOOSE_THEN `v3:real^N`
         STRIP_ASSUME_TAC)))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `V:real^N->bool`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `W:real^N->bool`)) THEN
    MATCH_MP_TAC MOI_FRN_FRONTIER_LINK_TET3 THEN ASM_REWRITE_TAC[];
    USE_THEN "split" (MP_TAC o el 2 o CONJUNCTS) THEN
    REWRITE_TAC[ASSUME `CARD(V:real^N->bool) = 3`;
                ASSUME `CARD(W:real^N->bool) = 2`] THEN
    DISCH_THEN(X_CHOOSE_THEN `v0:real^N` (X_CHOOSE_THEN `v1:real^N`
      (X_CHOOSE_THEN `v2:real^N` STRIP_ASSUME_TAC))) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `V:real^N->bool`)) THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `W:real^N->bool`)) THEN
    MATCH_MP_TAC MOI_FRN_FRONTIER_LINK_TRI2 THEN ASM_REWRITE_TAC[]]);;

(* Euclidean neighbourhoods pass to subsets containing an open set, and two *)
(* euclidean neighbourhoods of a point in X SUBSET Y give a neighbourhood of *)
(* the point in Y inside X (invariance of domain).                          *)

let MOI_FRN_MINT_MONO = prove
 (`!(X:real^N->bool) Y A x.
     X SUBSET Y /\ open_in (subtopology euclidean Y) A /\ A SUBSET X /\
     x IN A /\ moi_fmb_mint Y x
     ==> moi_fmb_mint X x`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fmb_mint; homeomorphic] THEN
  STRIP_TAC THEN
  MAP_EVERY EXISTS_TAC [`U INTER A:real^N->bool`;
                        `IMAGE (f:real^N->real^3) (U INTER A)`] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean Y) (U INTER A:real^N->bool)`
  ASSUME_TAC THENL [ASM_SIMP_TAC[OPEN_IN_INTER]; ALL_TAC] THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET Y` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `Y:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`g:real^3->real^N`; `U:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC OPEN_IN_SUBSET_TRANS THEN EXISTS_TAC `Y:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    MAP_EVERY EXISTS_TAC [`f:real^N->real^3`; `g:real^3->real^N`] THEN
    MATCH_MP_TAC HOMEOMORPHISM_OF_SUBSETS THEN
    MAP_EVERY EXISTS_TAC [`U:real^N->bool`; `V:real^3->bool`] THEN
    ASM_REWRITE_TAC[INTER_SUBSET] THEN
    UNDISCH_TAC `homeomorphism (U,V) (f:real^N->real^3,g)` THEN
    REWRITE_TAC[homeomorphism] THEN SET_TAC[]]);;

let MOI_FRN_MINT_INTERIOR = prove
 (`!(X:real^N->bool) Y x.
     X SUBSET Y /\ moi_fmb_mint X x /\ moi_fmb_mint Y x
     ==> ?A. open_in (subtopology euclidean Y) A /\ x IN A /\ A SUBSET X`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_fmb_mint; homeomorphic] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC MP_TAC) THEN
  DISCH_THEN(CONJUNCTS_THEN2
    (X_CHOOSE_THEN `U1:real^N->bool` (X_CHOOSE_THEN `V1:real^3->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h1:real^N->real^3`
          (X_CHOOSE_TAC `k1:real^3->real^N`)))))))
    (X_CHOOSE_THEN `U2:real^N->bool` (X_CHOOSE_THEN `V2:real^3->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h2:real^N->real^3`
          (X_CHOOSE_TAC `k2:real^3->real^N`)))))))) THEN
  EXISTS_TAC `U1 INTER U2:real^N->bool` THEN
  SUBGOAL_THEN `(U1:real^N->bool) SUBSET X /\ (U2:real^N->bool) SUBSET Y`
  STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL [ALL_TAC; ASM SET_TAC[]; ASM SET_TAC[]] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean U1) (U1 INTER U2:real^N->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean Y) (U2:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `G:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `G:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (h1:real^N->real^3) (U1 INTER U2))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `V1:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
    MAP_EVERY EXISTS_TAC [`k1:real^3->real^N`; `U1:real^N->bool`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ASSUME `homeomorphism (U1,V1) (h1:real^N->real^3,k1)`) THEN
  MP_TAC(ASSUME `homeomorphism (U2,V2) (h2:real^N->real^3,k2)`) THEN
  REWRITE_TAC[homeomorphism] THEN STRIP_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `IMAGE (k1:real^3->real^N) (IMAGE h1 (U1 INTER U2)) = U1 INTER U2`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(h2:real^N->real^3) o (k1:real^3->real^N)`;
                 `IMAGE (h1:real^N->real^3) (U1 INTER U2)`]
    INVARIANCE_OF_DOMAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `V1:real^3->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `U2:real^N->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
      REWRITE_TAC[o_THM] THEN
      MAP_EVERY X_GEN_TAC [`y1:real^3`; `y2:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(k1:real^3->real^N) y1 IN U1 INTER U2 /\
                    (k1:real^3->real^N) y2 IN U1 INTER U2`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(k1:real^3->real^N) y1 = k1 y2` MP_TAC THENL
       [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `h1:real^N->real^3`) THEN
      SUBGOAL_THEN `(y1:real^3) IN V1 /\ (y2:real^3) IN V1` STRIP_ASSUME_TAC
      THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MATCH_MP_TAC OPEN_IN_TRANS THEN EXISTS_TAC `U2:real^N->bool` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `U1 INTER U2 = IMAGE (k2:real^3->real^N) (IMAGE h2 (U1 INTER U2))`
  SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_OPEN_MAP THEN
  MAP_EVERY EXISTS_TAC [`h2:real^N->real^3`; `V2:real^3->bool`] THEN
  ASM_REWRITE_TAC[homeomorphism] THEN
  MATCH_MP_TAC OPEN_SUBSET THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

(* Points of complex_boundary c have no euclidean neighbourhoods in any     *)
(* subset S of UNIONS c containing them (adapted from the proof of          *)
(* MOI_FMB_MINT_CB in pc_moi_fnd_m3b.ml).                                    *)

let MOI_FRN_CB_NOT_MINT = prove
 (`!(c:(real^N->bool)->bool) S x.
        combinatorial_manifold_with_boundary 3 c /\ S SUBSET UNIONS c /\
        x IN S /\ x IN complex_boundary c
        ==> ~moi_fmb_mint S x`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS c` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `x:real^N`] MOI_FMB_CHART) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `W:real^N->bool` (X_CHOOSE_THEN `p:real^N->real^3`
    (X_CHOOSE_THEN `p':real^3->real^N` (X_CHOOSE_THEN `O:real^3->bool`
      STRIP_ASSUME_TAC)))) THEN
  SUBGOAL_THEN `((p:real^N->real^3) x)$3 = &0` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[moi_fmb_mint; homeomorphic; NOT_EXISTS_THM] THEN
  MAP_EVERY X_GEN_TAC [`U:real^N->bool`; `V:real^3->bool`] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `h:real^N->real^3`
      (X_CHOOSE_TAC `h':real^3->real^N`))))) THEN
  SUBGOAL_THEN `(U:real^N->bool) SUBSET UNIONS c` ASSUME_TAC THENL
   [ASM_MESON_TAC[OPEN_IN_IMP_SUBSET; SUBSET_TRANS]; ALL_TAC] THEN
  SUBGOAL_THEN `open_in (subtopology euclidean U) (U INTER W:real^N->bool)`
  ASSUME_TAC THENL
   [UNDISCH_TAC `open_in (subtopology euclidean (UNIONS c)) (W:real^N->bool)` THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `Tt:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `Tt:real^N->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `open (IMAGE (h:real^N->real^3) (U INTER W))` ASSUME_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_TRANS THEN EXISTS_TAC `V:real^3->bool` THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`h:real^N->real^3`; `h':real^3->real^N`; `U:real^N->bool`;
                   `V:real^3->bool`; `U INTER W:real^N->bool`]
      HOMEOMORPHISM_IMP_OPEN_MAP) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    check (fun th -> can (term_match []
      `homeomorphism (U:real^N->bool,V:real^3->bool) (f,g)`) (concl th))) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism] o
    check (fun th -> can (term_match []
      `homeomorphism (W:real^N->bool,IMAGE (p:real^N->real^3) W) (f,g)`)
      (concl th))) THEN
  SUBGOAL_THEN
   `IMAGE (h':real^3->real^N) (IMAGE h (U INTER W)) = U INTER W`
  ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`(p:real^N->real^3) o (h':real^3->real^N)`;
                 `IMAGE (h:real^N->real^3) (U INTER W)`]
    INVARIANCE_OF_DOMAIN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC CONTINUOUS_ON_COMPOSE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `V:real^3->bool` THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
        EXISTS_TAC `W:real^N->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]];
      REWRITE_TAC[o_THM] THEN
      MAP_EVERY X_GEN_TAC [`y1:real^3`; `y2:real^3`] THEN STRIP_TAC THEN
      SUBGOAL_THEN `(h':real^3->real^N) y1 IN U INTER W /\
                    (h':real^3->real^N) y2 IN U INTER W`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(h':real^3->real^N) y1 = h' y2` MP_TAC THENL
       [ASM_MESON_TAC[IN_INTER]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o AP_TERM `h:real^N->real^3`) THEN
      SUBGOAL_THEN `(y1:real^3) IN V /\ (y2:real^3) IN V` STRIP_ASSUME_TAC
      THENL [ASM SET_TAC[]; ASM_SIMP_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[IMAGE_o] THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^N->real^3) x` o
    GEN_REWRITE_RULE I [open_def]) THEN
  ANTS_TAC THENL
   [MATCH_MP_TAC FUN_IN_IMAGE THEN ASM_REWRITE_TAC[IN_INTER]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `(p:real^N->real^3) x - (e / &2) % basis 3`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[dist; VECTOR_ARITH `(a - b) - a:real^N = --b`; NORM_NEG;
                NORM_MUL] THEN
    SIMP_TAC[NORM_BASIS; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `(p:real^N->real^3) x - (e / &2) % basis 3 IN IMAGE p W`
  MP_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[IN_INTER; IN_ELIM_THM; VECTOR_SUB_COMPONENT;
                  VECTOR_MUL_COMPONENT] THEN
  SIMP_TAC[BASIS_COMPONENT; DIMINDEX_3; ARITH] THEN ASM_REAL_ARITH_TAC);;

(* The boundary of N'.                                                       *)

let MOI_FRN_NBHD_BOUNDARY = prove
 (`!(t:(real^N->bool)->bool) l.
     combinatorial_manifold_with_boundary 3 t /\ simplicial_subcomplex l t /\
     combinatorial_manifold_with_boundary 3 (derived_nbhd_complex t l)
     ==> complex_boundary (derived_nbhd_complex t l) =
         derived_frontier t l UNION (derived_nbhd t l INTER complex_boundary t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASSUME_TAC(CONJUNCT1(REWRITE_RULE[combinatorial_manifold_with_boundary]
   (ASSUME `combinatorial_manifold_with_boundary 3
              (t:(real^N->bool)->bool)`))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`]
    DERIVED_NBHD_BASIC) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[EXTENSION; IN_UNION; IN_INTER] THEN X_GEN_TAC `x:real^N` THEN
  ASM_CASES_TAC `(x:real^N) IN derived_nbhd t l` THEN ASM_REWRITE_TAC[] THENL
   [ALL_TAC;
    MATCH_MP_TAC(TAUT `~p /\ ~q ==> (p <=> q)`) THEN CONJ_TAC THENL
     [MP_TAC(ISPEC `derived_nbhd_complex t l:(real^N->bool)->bool`
        MOI_FMB_CB_SUBSET) THEN ASM_REWRITE_TAC[SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`subtopology euclidean (UNIONS t):(real^N)topology`;
                     `derived_nbhd t l:real^N->bool`]
        FRONTIER_OF_SUBSET_CLOSED_IN) THEN
      ASM_REWRITE_TAC[derived_frontier; SUBSET] THEN
      DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[]]] THEN
  SUBGOAL_THEN `(x:real^N) IN UNIONS t` ASSUME_TAC THENL
   [MP_TAC(ASSUME `derived_nbhd t l SUBSET UNIONS (t:(real^N->bool)->bool)`)
    THEN REWRITE_TAC[SUBSET] THEN DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`derived_nbhd_complex t l:(real^N->bool)->bool`; `x:real^N`]
    MOI_FMB_MINT_CB) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  SUBGOAL_THEN
   `(x:real^N) IN derived_frontier t l <=>
    ~(?u. open_in (subtopology euclidean (UNIONS t)) u /\ x IN u /\
          u SUBSET derived_nbhd t l)`
  SUBST1_TAC THENL
   [REWRITE_TAC[derived_frontier; frontier_of; IN_DIFF; interior_of;
                IN_ELIM_THM] THEN
    MATCH_MP_TAC(TAUT `p ==> (p /\ q <=> q)`) THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS t):(real^N)topology`;
                   `derived_nbhd t l:real^N->bool`] CLOSURE_OF_SUBSET) THEN
    ASM_REWRITE_TAC[TOPSPACE_EUCLIDEAN_SUBTOPOLOGY] THEN
    REWRITE_TAC[SUBSET] THEN
    DISCH_THEN(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC(TAUT `(p ==> ~r /\ q) /\ (q /\ ~r ==> p)
                     ==> (~p <=> ~q \/ r)`) THEN
  CONJ_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `~((x:real^N) IN complex_boundary t)` ASSUME_TAC THENL
     [DISCH_TAC THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `derived_nbhd t l:real^N->bool`;
                     `x:real^N`] MOI_FRN_CB_NOT_MINT) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_fmb_mint (UNIONS t) (x:real^N)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `x:real^N`] MOI_FMB_MINT_CB) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FRN_MINT_INTERIOR THEN ASM_REWRITE_TAC[];
    STRIP_TAC THEN
    SUBGOAL_THEN `moi_fmb_mint (UNIONS t) (x:real^N)` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `x:real^N`] MOI_FMB_MINT_CB) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FRN_MINT_MONO THEN
    MAP_EVERY EXISTS_TAC [`UNIONS t:real^N->bool`; `u:real^N->bool`] THEN
    ASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* DERIVED_NBHD_COMBINATORIAL (Moise 23.11-23.12).                           *)
(* ------------------------------------------------------------------------- *)

let DERIVED_NBHD_COMBINATORIAL = prove
 (`!(t:(real^N->bool)->bool) l.
     combinatorial_manifold_with_boundary 3 t /\ simplicial_subcomplex l t
     ==> combinatorial_manifold_with_boundary 3 (derived_nbhd_complex t l) /\
         complex_boundary (derived_nbhd_complex t l) =
         derived_frontier t l UNION (derived_nbhd t l INTER complex_boundary t)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `combinatorial_manifold_with_boundary 3
                  (derived_nbhd_complex t l:(real^N->bool)->bool)`
  ASSUME_TAC THENL
   [REWRITE_TAC[combinatorial_manifold_with_boundary] THEN
    CONV_TAC NUM_REDUCE_CONV THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FDN_DERIVED_NBHD_COMPLEX_LF THEN
      ASM_MESON_TAC[combinatorial_manifold_with_boundary];
      X_GEN_TAC `w:real^N` THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_FRN_NBHD_VERTEX_LINK THEN ASM_REWRITE_TAC[]];
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FRN_NBHD_BOUNDARY THEN
    ASM_REWRITE_TAC[]]);;

(* ========================================================================= *)
(* Combinatorial 2-manifolds (finite): dimension at most 2, each edge in     *)
(* exactly two triangles, each vertex in a triangle, local dual connectivity *)
(* at vertices. These are the lemmas MOI_FSA_CARD_EQ_1 ... MOI_FSA_CM_LCONN  *)
(* of pc_moi_fnd_surfa, here named MOI_FRN_SA_CARD_EQ_1 ...                  *)
(* MOI_FRN_SA_CM_LCONN, since pc_moi_fnd_surfa is not loaded by this file.   *)
(* ========================================================================= *)

let MOI_FRN_SA_CARD_EQ_1 = prove
 (`!s:A->bool. FINITE s /\ CARD s = 1 <=> ?a. s = {a}`,
  GEN_TAC THEN EQ_TAC THENL
   [REWRITE_TAC[GSYM HAS_SIZE; HAS_SIZE_1_EXISTS; EXISTS_UNIQUE_THM] THEN
    STRIP_TAC THEN EXISTS_TAC `x:A` THEN ASM SET_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[FINITE_SING; CARD_SING]]);;

let MOI_FRN_SA_PAIR_SIZE = prove
 (`!x y:A. ~(x = y) ==> {x,y} HAS_SIZE 2`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[HAS_SIZE] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN ARITH_TAC);;

let MOI_FRN_SA_DOUBLE_COUNT = prove
 (`!(R:A->B->bool) s t.
        FINITE s /\ FINITE t
        ==> nsum s (\x. CARD {y | y IN t /\ R x y}) =
            nsum t (\y. CARD {x | x IN s /\ R x y})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`R:A->B->bool`; `(\x:A y:B. 1)`; `s:A->bool`; `t:B->bool`]
    NSUM_NSUM_RESTRICT) THEN
  ASM_REWRITE_TAC[] THEN
  ASM_SIMP_TAC[CARD_EQ_NSUM; FINITE_RESTRICT]);;

let MOI_FRN_SA_CARD_PAIR = prove
 (`!x y:A. ~(x = y) ==> CARD {x,y} = 2`,
  MESON_TAC[MOI_FRN_SA_PAIR_SIZE; HAS_SIZE]);;

let MOI_FRN_SA_LK_DIM = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g s.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\ s IN L
        ==> aff_dim s <= &1`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM INT_NOT_LT] THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex (s:real^N->bool) /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_CONVEX];
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `&1 < aff_dim({}:real^N->bool)` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET UNIONS L` ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `compact (k:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`g:real^N->real^N`; `affine hull (s:real^N->bool)`;
                 `affine hull (k:real^N->bool)`;
                 `relative_interior (s:real^N->bool)`]
    INVARIANCE_OF_DOMAIN_AFFINE_SETS) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[AFFINE_AFFINE_HULL; AFF_DIM_AFFINE_HULL;
                OPEN_IN_RELATIVE_INTERIOR] THEN
    REPEAT CONJ_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
      UNDISCH_TAC `&1 < aff_dim(s:real^N->bool)` THEN INT_ARITH_TAC;
      MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
      EXISTS_TAC `UNIONS L:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[];
      MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      MP_TAC(ISPECL [`affine:(real^N->bool)->bool`; `k:real^N->bool`] HULL_SUBSET) THEN
      MP_TAC(ISPEC `k:real^N->bool` RELATIVE_FRONTIER_SUBSET) THEN
      ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
      MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[]];
    DISCH_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`;
                 `IMAGE (g:real^N->real^N) (relative_interior s)`]
    RELATIVE_INTERIOR_MAXIMAL) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `k:real^N->bool` RELATIVE_FRONTIER_SUBSET) THEN
    ASM_SIMP_TAC[COMPACT_IMP_CLOSED] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(relative_interior (s:real^N->bool) = {})` MP_TAC THENL
   [ASM_SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY]; ALL_TAC] THEN
  REWRITE_TAC[relative_frontier] THEN
  MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
  UNDISCH_TAC `IMAGE (g:real^N->real^N) (UNIONS L) = relative_frontier k` THEN
  REWRITE_TAC[relative_frontier] THEN ASM SET_TAC[]);;

let MOI_FRN_SA_LOCAL_STAR = prove
 (`!(L:(real^N->bool)->bool) u.
        FINITE L /\ (!s. s IN L ==> compact s)
        ==> ?r. &0 < r /\
                !y. y IN UNIONS L /\ dist(u,y) < r
                    ==> ?s. s IN L /\ u IN s /\ y IN s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`UNIONS {s | s IN L /\ ~((u:real^N) IN s)}`; `u:real^N`]
    SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN
      ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; COMPACT_IMP_CLOSED];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `r:real` THEN ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `s:real^N->bool`
    STRIP_ASSUME_TAC) ASSUME_TAC) THEN
  EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `(u:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
  ANTS_TAC THENL
   [REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `dist(u:real^N,y) < r` THEN REAL_ARITH_TAC]);;

let MOI_FRN_SA_RF_TWO_POINTS = prove
 (`!k:real^N->bool.
        &2 simplex k
        ==> ?a b. ~(a = b) /\ a IN relative_frontier k /\
                  b IN relative_frontier k`,
  GEN_TAC THEN REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(C:real^N->bool) HAS_SIZE 3` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(C:real^N->bool)):int = &2 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_3] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    (X_CHOOSE_THEN `c:real^N` STRIP_ASSUME_TAC))) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `~collinear{a:real^N,b,c}` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[COLLINEAR_3_EQ_AFFINE_DEPENDENT]; ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`] THEN
  ASM_SIMP_TAC[RELATIVE_FRONTIER_OF_TRIANGLE; IN_UNION; ENDS_IN_SEGMENT]);;

let MOI_FRN_SA_EDGE_SEG = prove
 (`!(L:(real^N->bool)->bool) u e.
        simplicial_complex L /\ {u} IN L /\ e IN L /\ aff_dim e = &1 /\
        u IN e
        ==> ?x. ~(x = u) /\ e = segment[u,x] /\ {x} IN L`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `&1 simplex (e:real^N->bool)` MP_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `n:int` o C MATCH_MP
      (ASSUME `(e:real^N->bool) IN L`)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(C:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(C:real^N->bool)):int = &1 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `(u:real^N) extreme_point_of segment[p,q]` MP_TAC THENL
   [REWRITE_TAC[GSYM FACE_OF_SING] THEN
    SUBGOAL_THEN `{u:real^N} = {u} INTER e` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `e:real^N->bool`)) THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{p:real^N} IN L /\ {q:real^N} IN L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; GSYM SEGMENT_CONVEX_HULL;
                    EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  REWRITE_TAC[EXTREME_POINT_OF_SEGMENT] THEN STRIP_TAC THENL
   [EXISTS_TAC `q:real^N`; EXISTS_TAC `p:real^N`] THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `u:real^N`)) THEN
  ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN REWRITE_TAC[INSERT_AC] THEN
  ASM_MESON_TAC[]);;

let MOI_FRN_SA_LK_STAR_U = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u s.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\ {u} IN L /\
        s IN L /\ u IN s
        ==> s = {u} \/ aff_dim s = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                 `g:real^N->real^N`; `s:real^N->bool`] MOI_FRN_SA_LK_DIM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `&0 <= aff_dim(s:real^N->bool)` MP_TAC THENL
   [REWRITE_TAC[AFF_DIM_POS_LE] THEN ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMP_IMP; INT_ARITH `&0 <= x:int /\ x <= &1 <=> x = &0 \/ x = &1`] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(s:real^N->bool) = &0` THEN REWRITE_TAC[AFF_DIM_EQ_0] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
  UNDISCH_TAC `(u:real^N) IN {a}` THEN REWRITE_TAC[IN_SING] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[]);;

let MOI_FRN_SA_LK_CONNECTED = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g.
        &2 simplex k /\ homeomorphism (relative_frontier k,UNIONS L) (f,g)
        ==> connected (UNIONS L) /\
            !p. p IN UNIONS L ==> connected (UNIONS L DELETE p)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `convex (k:real^N->bool) /\ bounded k /\ aff_dim k = &2`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_POLYTOPE;
                  POLYTOPE_IMP_BOUNDED; AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      rand(concl th) = `UNIONS L:real^N->bool`)) THEN
    MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC CONNECTED_SPHERE_GEN THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  X_GEN_TAC `p:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `UNIONS L DELETE (p:real^N) =
                IMAGE (f:real^N->real^N) (relative_frontier k DELETE g p)`
  SUBST1_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_DELETE; IN_IMAGE] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC CONNECTED_CONTINUOUS_IMAGE THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `relative_frontier k:real^N->bool` THEN
    ASM_REWRITE_TAC[DELETE_SUBSET];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`k:real^N->bool`; `(:real^1)`; `(g:real^N->real^N) p`]
    HOMEOMORPHIC_PUNCTURED_SPHERE_AFFINE_GEN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[AFFINE_UNIV; AFF_DIM_UNIV; DIMINDEX_1] THEN
    CONJ_TAC THENL [ASM SET_TAC[]; INT_ARITH_TAC];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP HOMEOMORPHIC_CONNECTEDNESS) THEN
  REWRITE_TAC[CONNECTED_UNIV]);;

let MOI_FRN_SA_LK_EDGE = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\ {u} IN L
        ==> ?e. e IN L /\ aff_dim e = &1 /\ u IN e`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
  DISCH_THEN(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM]) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN L /\ u IN s ==> s = {u}` ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `f:real^N->real^N`; `g:real^N->real^N`; `u:real^N`;
                   `s:real^N->bool`] MOI_FRN_SA_LK_STAR_U) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `u:real^N`] MOI_FRN_SA_LOCAL_STAR) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_FRN_SA_LK_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[CONNECTED_CLOPEN] THEN
  DISCH_THEN(MP_TAC o SPEC `{u:real^N}`) THEN
  SUBGOAL_THEN `(u:real^N) IN UNIONS L` ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[OPEN_IN_OPEN] THEN EXISTS_TAC `ball(u:real^N,r)` THEN
      REWRITE_TAC[OPEN_BALL] THEN
      REWRITE_TAC[EXTENSION; IN_INTER; IN_SING; IN_BALL] THEN
      X_GEN_TAC `y:real^N` THEN EQ_TAC THENL
       [DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[DIST_REFL]; ALL_TAC] THEN
      STRIP_TAC THEN FIRST_X_ASSUM(MP_TAC o SPEC `y:real^N`) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `s = {u:real^N}` SUBST_ALL_TAC THENL
       [ASM_MESON_TAC[]; ASM SET_TAC[]];
      REWRITE_TAC[CLOSED_IN_CLOSED] THEN EXISTS_TAC `{u:real^N}` THEN
      REWRITE_TAC[CLOSED_SING] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_INSERT_EMPTY] THEN DISCH_TAC THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_FRN_SA_RF_TWO_POINTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
  SUBGOAL_THEN `(f:real^N->real^N) a = u /\ f b = u` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  UNDISCH_TAC `~(a:real^N = b)` THEN REWRITE_TAC[] THEN
  ASM_MESON_TAC[]);;

let MOI_FRN_SA_SEG_DIST = prove
 (`!u x:real^N t. &0 <= t ==> dist(u,(&1 - t) % u + t % x) = t * dist(u,x)`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[dist] THEN
  REWRITE_TAC[VECTOR_ARITH `u - ((&1 - t) % u + t % x):real^N = t % (u - x)`] THEN
  ASM_SIMP_TAC[NORM_MUL; real_abs]);;

let MOI_FRN_SA_LK_NOT1 = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u e0.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\ {u} IN L /\
        e0 IN L /\ aff_dim e0 = &1 /\ u IN e0 /\
        (!e. e IN L /\ aff_dim e = &1 /\ u IN e ==> e = e0)
        ==> F`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `u:real^N`; `e0:real^N->bool`]
    MOI_FRN_SA_EDGE_SEG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!s:real^N->bool. s IN L /\ u IN s ==> s SUBSET segment[u,x]`
  ASSUME_TAC THENL
   [X_GEN_TAC `s:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `f:real^N->real^N`; `g:real^N->real^N`; `u:real^N`;
                   `s:real^N->bool`] MOI_FRN_SA_LK_STAR_U) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [ASM_REWRITE_TAC[SING_SUBSET; ENDS_IN_SEGMENT];
      SUBGOAL_THEN `s:real^N->bool = e0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[SUBSET_REFL]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `u:real^N`] MOI_FRN_SA_LOCAL_STAR) THEN
  ANTS_TAC THENL
   [ASM_MESON_TAC[simplicial_complex; SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `&0 < dist(u:real^N,x)` ASSUME_TAC THENL
   [ASM_MESON_TAC[DIST_POS_LT]; ALL_TAC] THEN
  ABBREV_TAC `rho = min r (dist(u:real^N,x)) / &2` THEN
  SUBGOAL_THEN `&0 < rho /\ rho < r /\ rho < dist(u:real^N,x)`
  STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "rho" THEN UNDISCH_TAC `&0 < r` THEN
    UNDISCH_TAC `&0 < dist(u:real^N,x)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  ABBREV_TAC `m = (&1 - rho / dist(u,x)) % u + (rho / dist(u:real^N,x)) % x` THEN
  SUBGOAL_THEN `&0 <= rho / dist(u:real^N,x) /\ rho / dist(u,x) <= &1`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[REAL_LE_DIV; REAL_LT_IMP_LE; REAL_LE_LDIV_EQ] THEN
    UNDISCH_TAC `rho < dist(u:real^N,x)` THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N) IN segment[u,x] /\ dist(u,m) = rho` STRIP_ASSUME_TAC THENL
   [EXPAND_TAC "m" THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `rho / dist(u:real^N,x)` THEN
      ASM_REWRITE_TAC[];
      ASM_SIMP_TAC[MOI_FRN_SA_SEG_DIST] THEN
      ASM_SIMP_TAC[REAL_DIV_RMUL; REAL_LT_IMP_NZ]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!y:real^N. y IN segment[u,x] /\ dist(u,y) = rho ==> y = m`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN REWRITE_TAC[IN_SEGMENT] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real` STRIP_ASSUME_TAC)
      ASSUME_TAC) THEN
    UNDISCH_TAC `dist(u:real^N,y) = rho` THEN ASM_SIMP_TAC[MOI_FRN_SA_SEG_DIST] THEN
    DISCH_TAC THEN EXPAND_TAC "m" THEN
    SUBGOAL_THEN `t = rho / dist(u:real^N,x)` (fun th -> REWRITE_TAC[th]) THEN
    ASM_SIMP_TAC[REAL_EQ_RDIV_EQ];
    ALL_TAC] THEN
  SUBGOAL_THEN `(m:real^N) IN UNIONS L /\ (x:real^N) IN UNIONS L`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[IN_UNIONS] THEN CONJ_TAC THEN
    EXISTS_TAC `e0:real^N->bool` THEN ASM_REWRITE_TAC[ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_FRN_SA_LK_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `m:real^N` o CONJUNCT2) THEN
  ASM_REWRITE_TAC[CONNECTED_OPEN_IN] THEN
  MAP_EVERY EXISTS_TAC
   [`(UNIONS L DELETE (m:real^N)) INTER ball(u,rho)`;
    `(UNIONS L DELETE (m:real^N)) INTER ((:real^N) DIFF cball(u,rho))`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN REWRITE_TAC[OPEN_BALL];
    MATCH_MP_TAC OPEN_IN_OPEN_INTER THEN
    REWRITE_TAC[GSYM closed; CLOSED_CBALL];
    REWRITE_TAC[SUBSET; IN_UNION; IN_INTER; IN_DELETE; IN_BALL; IN_CBALL;
                IN_DIFF; IN_UNIV] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `dist(u:real^N,y) = rho` THENL
     [MATCH_MP_TAC(TAUT `F ==> p`) THEN
      UNDISCH_TAC `~(y:real^N = m)` THEN REWRITE_TAC[] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `(y:real^N) IN UNIONS L` THEN REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(SPEC `y:real^N` (ASSUME `!y:real^N. y IN UNIONS L /\ dist(u,y) < r
                                  ==> ?s. s IN L /\ u IN s /\ y IN s`)) THEN
      ANTS_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN
        CONJ_TAC THENL [EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
                        ASM_REAL_ARITH_TAC];
        ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_MESON_TAC[SUBSET];
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_DELETE; IN_BALL; IN_CBALL; IN_DIFF;
                IN_UNIV; NOT_IN_EMPTY] THEN MESON_TAC[REAL_LT_IMP_LE];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `u:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_DELETE; IN_BALL; DIST_REFL] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{u:real^N}` THEN
      ASM_REWRITE_TAC[IN_SING];
      DISCH_THEN(ASSUME_TAC o SYM) THEN
      UNDISCH_TAC `dist(u:real^N,m) = rho` THEN ASM_REWRITE_TAC[DIST_REFL] THEN
      ASM_REAL_ARITH_TAC];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_DELETE; IN_CBALL; IN_DIFF; IN_UNIV] THEN
    ASM_REWRITE_TAC[REAL_NOT_LE] THEN
    DISCH_THEN(ASSUME_TAC o SYM) THEN
    UNDISCH_TAC `dist(u:real^N,m) = rho` THEN ASM_REWRITE_TAC[] THEN
    ASM_REAL_ARITH_TAC]);;

let MOI_FRN_SA_EDGE_VERTS = prove
 (`!(L:(real^N->bool)->bool) e.
        simplicial_complex L /\ e IN L /\ aff_dim e = &1
        ==> ?p q. ~(p = q) /\ e = segment[p,q] /\ {p} IN L /\ {q} IN L /\
                  {u | {u} IN L /\ u IN e} = {p,q}`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [simplicial_complex]) THEN
  SUBGOAL_THEN `&1 simplex (e:real^N->bool)` MP_TAC THENL
   [FIRST_X_ASSUM(X_CHOOSE_TAC `n:int` o C MATCH_MP
      (ASSUME `(e:real^N->bool) IN L`)) THEN
    FIRST_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(SUBST_ALL_TAC o SYM) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[simplex] THEN
  DISCH_THEN(X_CHOOSE_THEN `C:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(C:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [ASM_SIMP_TAC[HAS_SIZE; AFFINE_INDEPENDENT_IMP_FINITE] THEN
    UNDISCH_TAC `&(CARD(C:real^N->bool)):int = &1 + &1` THEN
    REWRITE_TAC[INT_OF_NUM_ADD; INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  SUBGOAL_THEN `e = segment[p:real^N,q]` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[SEGMENT_CONVEX_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `{p:real^N} IN L /\ {q:real^N} IN L` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; GSYM SEGMENT_CONVEX_HULL;
                    EXTREME_POINT_OF_SEGMENT];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`p:real^N`; `q:real^N`] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL [REWRITE_TAC[SEGMENT_CONVEX_HULL]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `u:real^N` THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `{u:real^N} face_of e` MP_TAC THENL
     [SUBGOAL_THEN `{u:real^N} = {u} INTER e` SUBST1_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[]];
      ASM_REWRITE_TAC[FACE_OF_SING; GSYM SEGMENT_CONVEX_HULL;
                      EXTREME_POINT_OF_SEGMENT]];
    STRIP_TAC THEN ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; ENDS_IN_SEGMENT]]);;

let MOI_FRN_SA_LK_DEG_GE2 = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\ {u} IN L
        ==> 2 <= CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE {e:real^N->bool | e IN L /\ aff_dim e = &1 /\ u IN e}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                 `g:real^N->real^N`; `u:real^N`] MOI_FRN_SA_LK_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e0:real^N->bool` STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[ARITH_RULE `2 <= n <=> ~(n = 0) /\ ~(n = 1)`] THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    EXISTS_TAC `e0:real^N->bool` THEN ASM_REWRITE_TAC[IN_ELIM_THM];
    DISCH_TAC THEN
    MP_TAC(ISPEC `{e:real^N->bool | e IN L /\ aff_dim e = &1 /\ u IN e}`
      MOI_FRN_SA_CARD_EQ_1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_TAC `e1:real^N->bool`) THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `f:real^N->real^N`; `g:real^N->real^N`; `u:real^N`;
                   `e0:real^N->bool`] MOI_FRN_SA_LK_NOT1) THEN
    ASM_REWRITE_TAC[] THEN
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e:real^N->bool) IN {e | e IN L /\ aff_dim e = &1 /\ u IN e} /\
                  (e0:real^N->bool) IN {e | e IN L /\ aff_dim e = &1 /\ u IN e}`
    MP_TAC THENL [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
    ASM_REWRITE_TAC[IN_SING] THEN MESON_TAC[]]);;

let MOI_FRN_SA_LK_CHI = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g)
        ==> complex_euler L =
            &(CARD {u | {u} IN L}) - &(CARD {e | e IN L /\ aff_dim e = &1})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FEU_COMPLEX_EULER_SUM] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN L /\ ~(s = {})} =
    {s | s IN L /\ aff_dim s = &0} UNION {e | e IN L /\ aff_dim e = &1}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_UNION] THEN
    ASM_CASES_TAC `(s:real^N->bool) IN L` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                   `f:real^N->real^N`; `g:real^N->real^N`; `s:real^N->bool`]
      MOI_FRN_SA_LK_DIM) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `s:real^N->bool = {}` THEN ASM_REWRITE_TAC[AFF_DIM_EMPTY] THENL
     [CONV_TAC INT_REDUCE_CONV;
      MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `DISJOINT {s:real^N->bool | s IN L /\ aff_dim s = &0}
             {e | e IN L /\ aff_dim e = &1}`
  ASSUME_TAC THENL
   [REWRITE_TAC[DISJOINT; EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `s:real^N->bool` THEN
    ASM_CASES_TAC `aff_dim(s:real^N->bool) = &0` THEN ASM_REWRITE_TAC[] THEN
    CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_UNION; FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `sum {s:real^N->bool | s IN L /\ aff_dim s = &0}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {s:real^N->bool | s IN L /\ aff_dim s = &0} (\s. &1) /\
    sum {e:real^N->bool | e IN L /\ aff_dim e = &1}
        (\s. (-- &1) pow num_of_int(aff_dim s)) =
    sum {e:real^N->bool | e IN L /\ aff_dim e = &1} (\s. -- &1)`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC SUM_EQ THEN
    SIMP_TAC[IN_ELIM_THM; NUM_OF_INT_OF_NUM] THEN
    CONV_TAC REAL_RAT_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_SIMP_TAC[SUM_CONST; FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `{s:real^N->bool | s IN L /\ aff_dim s = &0} =
    IMAGE (\u:real^N. {u}) {u | {u} IN L}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `s:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE; AFF_DIM_EQ_0] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN L}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\u:real^N. {u}`; `{u:real^N | {u} IN L}`] CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[NUM_OF_INT_OF_NUM] THEN
  CONV_TAC REAL_RAT_REDUCE_CONV THEN
  REWRITE_TAC[REAL_MUL_RID; REAL_MUL_RNEG; GSYM real_sub]);;

let MOI_FRN_SA_LK_HANDSHAKE = prove
 (`!L:(real^N->bool)->bool.
        simplicial_complex L
        ==> nsum {u | {u} IN L}
                 (\u. CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e}) =
            2 * CARD {e | e IN L /\ aff_dim e = &1}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN L}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\(u:real^N) (e:real^N->bool). u IN e`; `{u:real^N | {u} IN L}`;
                 `{e:real^N->bool | e IN L /\ aff_dim e = &1}`]
    MOI_FRN_SA_DOUBLE_COUNT) THEN
  ASM_SIMP_TAC[FINITE_RESTRICT] THEN
  SUBGOAL_THEN
   `!u:real^N. {e | e IN {e:real^N->bool | e IN L /\ aff_dim e = &1} /\ u IN e} =
              {e | e IN L /\ aff_dim e = &1 /\ u IN e}`
  (fun th -> REWRITE_TAC[th]) THENL
   [GEN_TAC THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; CONJ_ASSOC]; ALL_TAC] THEN
  DISCH_THEN SUBST1_TAC THEN
  MATCH_MP_TAC EQ_TRANS THEN
  EXISTS_TAC `nsum {e:real^N->bool | e IN L /\ aff_dim e = &1} (\e. 2)` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC NSUM_EQ THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `e:real^N->bool`]
      MOI_FRN_SA_EDGE_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
      STRIP_ASSUME_TAC)) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FRN_SA_CARD_PAIR THEN
    ASM_REWRITE_TAC[];
    ASM_SIMP_TAC[NSUM_CONST; FINITE_RESTRICT] THEN ARITH_TAC]);;

let MOI_FRN_SA_LK_DEG2 = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g u.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\
        complex_euler L = &0 /\ {u} IN L
        ==> CARD {e | e IN L /\ aff_dim e = &1 /\ u IN e} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE {u:real^N | {u} IN L}` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_IMAGE_INJ THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_FRN_SA_LK_CHI) THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[REAL_ARITH `&0 = a - b <=> b = a`; REAL_OF_NUM_EQ] THEN
  DISCH_TAC THEN
  MP_TAC(ISPEC `L:(real^N->bool)->bool` MOI_FRN_SA_LK_HANDSHAKE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `!v:real^N. v IN {u | {u} IN L}
                ==> 2 <= CARD {e | e IN L /\ aff_dim e = &1 /\ v IN e}`
  ASSUME_TAC THENL
   [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FRN_SA_LK_DEG_GE2 THEN
    MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                          `g:real^N->real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM LE_ANTISYM] THEN CONJ_TAC THENL
   [ALL_TAC;
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_ELIM_THM]] THEN
  REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`\v:real^N. 2`;
                 `\v:real^N. CARD {e | e IN L /\ aff_dim e = &1 /\ v IN e}`;
                 `{u:real^N | {u} IN L}`] NSUM_LT) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN EXISTS_TAC `u:real^N` THEN
    ASM_REWRITE_TAC[IN_ELIM_THM];
    ALL_TAC] THEN
  ASM_SIMP_TAC[NSUM_CONST] THEN ARITH_TAC);;

let MOI_FRN_SA_SC_FACTS = prove
 (`!L:(real^N->bool)->bool.
        simplicial_complex L
        ==> FINITE L /\ (!s. s IN L ==> compact s /\ convex s)`,
  GEN_TAC THEN REWRITE_TAC[simplicial_complex] THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `s:real^N->bool` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(X_CHOOSE_TAC `n:int` o C MATCH_MP
    (ASSUME `(s:real^N->bool) IN L`)) THEN
  ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_COMPACT; SIMPLEX_IMP_CONVEX]);;

let MOI_FRN_SA_LK_EDGES_CONN = prove
 (`!(L:(real^N->bool)->bool) (k:real^N->bool) (f:real^N->real^N) g U.
        simplicial_complex L /\ &2 simplex k /\
        homeomorphism (relative_frontier k,UNIONS L) (f,g) /\
        U SUBSET {e | e IN L /\ aff_dim e = &1} /\ ~(U = {}) /\
        (!e e'. e IN U /\ e' IN L /\ aff_dim e' = &1 /\ ~(e INTER e' = {})
                ==> e' IN U)
        ==> U = {e | e IN L /\ aff_dim e = &1}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (L:(real^N->bool)->bool) /\
                (!s:real^N->bool. s IN L ==> compact s)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_SA_SC_FACTS]; ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `e1:real^N->bool` THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`] MOI_FRN_SA_LK_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  MAP_EVERY EXISTS_TAC
   [`UNIONS U:real^N->bool`;
    `UNIONS {e:real^N->bool | e IN L /\ aff_dim e = &1 /\ ~(e IN U)}`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `L:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `U SUBSET {e:real^N->bool | e IN L /\ aff_dim e = &1}` THEN
      SET_TAC[];
      X_GEN_TAC `t:real^N->bool` THEN DISCH_TAC THEN
      MATCH_MP_TAC COMPACT_IMP_CLOSED THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      UNDISCH_TAC `U SUBSET {e:real^N->bool | e IN L /\ aff_dim e = &1}` THEN
      UNDISCH_TAC `(t:real^N->bool) IN U` THEN SET_TAC[]];
    MATCH_MP_TAC CLOSED_UNIONS THEN
    ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM; COMPACT_IMP_CLOSED];
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `?e:real^N->bool. e IN L /\ aff_dim e = &1 /\ y IN e`
    MP_TAC THENL
     [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`;
                     `f:real^N->real^N`; `g:real^N->real^N`; `s:real^N->bool`]
        MOI_FRN_SA_LK_DIM) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_POS_LE) THEN
      SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
       [REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `y:real^N` THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      REWRITE_TAC[INT_ARITH `&0 <= x:int /\ x <= &1 <=> x = &0 \/ x = &1`;
                  IMP_IMP] THEN
      STRIP_TAC THENL
       [UNDISCH_TAC `aff_dim(s:real^N->bool) = &0` THEN
        REWRITE_TAC[AFF_DIM_EQ_0] THEN
        DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
        UNDISCH_TAC `(y:real^N) IN {a}` THEN REWRITE_TAC[IN_SING] THEN
        DISCH_THEN SUBST_ALL_TAC THEN
        MATCH_MP_TAC MOI_FRN_SA_LK_EDGE THEN
        MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                              `g:real^N->real^N`] THEN
        ASM_REWRITE_TAC[];
        EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[]];
      DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
      ASM_CASES_TAC `(e:real^N->bool) IN U` THENL
       [DISJ1_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[];
        DISJ2_TAC THEN EXISTS_TAC `e:real^N->bool` THEN ASM_REWRITE_TAC[]]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_UNIONS; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `y:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 (X_CHOOSE_THEN `e':real^N->bool` STRIP_ASSUME_TAC)
         ASSUME_TAC)) THEN
    UNDISCH_TAC `~((e':real^N->bool) IN U)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `e:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    UNDISCH_TAC `~(U:(real^N->bool)->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `e0:real^N->bool`) THEN
    SUBGOAL_THEN `(e0:real^N->bool) IN L /\ aff_dim e0 = &1` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `U SUBSET {e:real^N->bool | e IN L /\ aff_dim e = &1}` THEN
      UNDISCH_TAC `(e0:real^N->bool) IN U` THEN
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(e0:real^N->bool = {})` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN EXISTS_TAC `y:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS] THEN
    CONJ_TAC THEN EXISTS_TAC `e0:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    SUBGOAL_THEN `~(e1:real^N->bool = {})` MP_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim({}:real^N->bool) = &1` THEN
      REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN EXISTS_TAC `y:real^N` THEN
    REWRITE_TAC[IN_INTER; IN_UNIONS; IN_ELIM_THM] THEN
    CONJ_TAC THEN EXISTS_TAC `e1:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

let MOI_FRN_SA_CM_LINK = prove
 (`!c (v:real^N).
        FINITE c /\ combinatorial_manifold 2 c /\ {v} IN c
        ==> simplicial_complex c /\ simplicial_complex (simplicial_link c v) /\
            ?k:real^N->bool f:real^N->real^N g. &2 simplex k /\
                    homeomorphism (relative_frontier k,
                                   UNIONS (simplicial_link c v)) (f,g) /\
                    complex_euler (simplicial_link c v) = &0`,
  REPEAT GEN_TAC THEN REWRITE_TAC[combinatorial_manifold] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_SCF_LINK_SC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `v:real^N`) THEN ASM_REWRITE_TAC[] THEN
  CONV_TAC NUM_REDUCE_CONV THEN REWRITE_TAC[pl_sphere] THEN
  CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
    (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                        `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[pl_homeomorphism]; ALL_TAC] THEN
  MP_TAC(ISPECL [`relative_frontier (k:real^N->bool)`;
                 `&1 - (-- &1) pow 2`;
                 `simplicial_link c (v:real^N)`; `f:real^N->real^N`;
                 `g:real^N->real^N`] MOI_FEU_PL_HOMEOMORPHIC_EULER) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[MOI_SCF_LINK_SC] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FEU_EULER_SIMPLEX_FRONTIER THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC COMPACT_RELATIVE_FRONTIER_BOUNDED THEN
      ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE; POLYTOPE_IMP_BOUNDED]];
    DISCH_THEN SUBST1_TAC THEN CONV_TAC REAL_RAT_REDUCE_CONV]);;

let MOI_FRN_SA_CM_DIM = prove
 (`!c s:real^N->bool.
        FINITE c /\ combinatorial_manifold 2 c /\ s IN c ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN
  ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_MESON_TAC[combinatorial_manifold];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_SC_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_SCF_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s':real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s':real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FRN_SA_CM_LINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))))) THEN
  MP_TAC(ISPECL [`simplicial_link c (v:real^N)`; `k:real^N->bool`;
                 `f:real^N->real^N`; `g:real^N->real^N`; `s':real^N->bool`]
    MOI_FRN_SA_LK_DIM) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(convex hull ((v:real^N) INSERT s')) = aff_dim s' + &1` THEN
  ASM_REWRITE_TAC[] THEN INT_ARITH_TAC);;

let MOI_FRN_SA_CM_EDGE2 = prove
 (`!c e:real^N->bool.
        FINITE c /\ combinatorial_manifold 2 c /\ e IN c /\ aff_dim e = &1
        ==> CARD {t | t IN c /\ aff_dim t = &2 /\ e SUBSET t} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_LF_SC THEN ASM_MESON_TAC[combinatorial_manifold];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FRN_SA_EDGE_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `u:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FRN_SA_CM_LINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC `L = simplicial_link c (v:real^N)` THEN
  FIRST_X_ASSUM(SUBST_ALL_TAC o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `e:real^N->bool`)) THEN
  SUBGOAL_THEN `segment[v:real^N,u] = convex hull (v INSERT {u})` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL]; ALL_TAC] THEN
  SUBGOAL_THEN `{u:real^N} IN L` ASSUME_TAC THENL
   [EXPAND_TAC "L" THEN REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN
    ASM_REWRITE_TAC[IN_SING] THEN
    EXISTS_TAC `segment[v:real^N,u]` THEN
    ASM_REWRITE_TAC[FACE_OF_SING; EXTREME_POINT_OF_SEGMENT; ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{t:real^N->bool | t IN c /\ aff_dim t = &2 /\ segment[v,u] SUBSET t} =
    IMAGE (\s. convex hull (v INSERT s)) {s | s IN L /\ aff_dim s = &1 /\ u IN s}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `t:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN EQ_TAC THENL
     [STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
        MOI_SCF_LINK_OPP) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `segment[v:real^N,u] SUBSET t` THEN
        MESON_TAC[SUBSET; ENDS_IN_SEGMENT];
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN CONJ_TAC THENL
       [UNDISCH_TAC `aff_dim(convex hull ((v:real^N) INSERT s)) = aff_dim s + &1` THEN
        UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
        INT_ARITH_TAC;
        MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `{u:real^N}`;
                       `s:real^N->bool`] MOI_SCF_LINK_JOIN_SUBSET) THEN
        ASM_REWRITE_TAC[] THEN
        UNDISCH_TAC `segment[v:real^N,u] SUBSET t` THEN ASM_REWRITE_TAC[] THEN
        SIMP_TAC[SING_SUBSET]];
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `{u:real^N}`;
                     `s:real^N->bool`] MOI_SCF_LINK_JOIN_SUBSET) THEN
      ASM_REWRITE_TAC[SING_SUBSET] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\s:real^N->bool. convex hull (v INSERT s)`;
                 `{s:real^N->bool | s IN L /\ aff_dim s = &1 /\ u IN s}`]
    CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`]
        MOI_SCF_LINK_JOIN_INJ) THEN
      ASM_MESON_TAC[];
      MATCH_MP_TAC FINITE_RESTRICT THEN EXPAND_TAC "L" THEN
      ASM_MESON_TAC[simplicial_complex]];
    DISCH_THEN SUBST1_TAC] THEN
  MATCH_MP_TAC MOI_FRN_SA_LK_DEG2 THEN
  MAP_EVERY EXISTS_TAC [`k:real^N->bool`; `f:real^N->real^N`;
                        `g:real^N->real^N`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_FRN_SA_CM_VTRI = prove
 (`!c v:real^N.
        FINITE c /\ combinatorial_manifold 2 c /\ {v} IN c
        ==> ?t. t IN c /\ aff_dim t = &2 /\ v IN t`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FRN_SA_CM_LINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC `L = simplicial_link c (v:real^N)` THEN
  SUBGOAL_THEN `?s:real^N->bool. s IN L /\ ~(s = {})` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `k:real^N->bool` MOI_FRN_SA_RF_TWO_POINTS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N`
      STRIP_ASSUME_TAC)) THEN
    FIRST_ASSUM(STRIP_ASSUME_TAC o GEN_REWRITE_RULE I [homeomorphism]) THEN
    SUBGOAL_THEN `(f:real^N->real^N) a IN UNIONS L` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`] MOI_SCF_SC_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                 `g:real^N->real^N`; `w:real^N`] MOI_FRN_SA_LK_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `convex hull ((v:real^N) INSERT e)` THEN ASM_REWRITE_TAC[] THEN
  INT_ARITH_TAC);;

let MOI_FRN_SA_CM_LCONN = prove
 (`!c (v:real^N) Y.
        FINITE c /\ combinatorial_manifold 2 c /\ {v} IN c /\
        Y SUBSET {t | t IN c /\ aff_dim t = &2 /\ v IN t} /\ ~(Y = {}) /\
        (!t t' u. t IN Y /\ t' IN c /\ aff_dim t' = &2 /\ v IN t' /\
                  ~(u = v) /\ {u} IN c /\ u IN t /\ u IN t'
                  ==> t' IN Y)
        ==> Y = {t | t IN c /\ aff_dim t = &2 /\ v IN t}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_FRN_SA_CM_LINK) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f:real^N->real^N`
      (X_CHOOSE_THEN `g:real^N->real^N` STRIP_ASSUME_TAC))))) THEN
  ABBREV_TAC `L = simplicial_link c (v:real^N)` THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `k:real^N->bool`; `f:real^N->real^N`;
                 `g:real^N->real^N`;
                 `{s:real^N->bool | s IN L /\ aff_dim s = &1 /\
                                    convex hull (v INSERT s) IN Y}`]
    MOI_FRN_SA_LK_EDGES_CONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [SET_TAC[];
      UNDISCH_TAC `~(Y:(real^N->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `t:real^N->bool`) THEN
      SUBGOAL_THEN `(t:real^N->bool) IN c /\ aff_dim t = &2 /\ v IN t`
      STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
        MOI_SCF_LINK_OPP) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `s:real^N->bool` THEN REWRITE_TAC[IN_ELIM_THM] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
        INT_ARITH_TAC;
        UNDISCH_TAC `(t:real^N->bool) IN Y` THEN ASM_REWRITE_TAC[]];
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `?u:real^N. {u} IN L /\ u IN s1 /\ u IN s2` STRIP_ASSUME_TAC THENL
       [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s1 INTER s2:real^N->bool`]
          MOI_SCF_SC_VERTEX) THEN
        ANTS_TAC THENL
         [ASM_REWRITE_TAC[] THEN
          SUBGOAL_THEN `(s1 INTER s2:real^N->bool) face_of s1` MP_TAC THENL
           [ASM_MESON_TAC[simplicial_complex]; ALL_TAC] THEN
          ASM_MESON_TAC[simplicial_complex];
          REWRITE_TAC[IN_INTER] THEN MESON_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s1:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s2:real^N->bool`]
        MOI_SCF_LINK_JOIN) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `~(u:real^N = v) /\ {u} IN c /\ u IN convex hull (v INSERT s1) /\
        u IN convex hull (v INSERT s2) /\
        aff_dim(convex hull ((v:real^N) INSERT s2)) = &2`
      STRIP_ASSUME_TAC THENL
       [REPEAT CONJ_TAC THENL
         [DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[];
          UNDISCH_TAC `{u:real^N} IN L` THEN EXPAND_TAC "L" THEN
          SIMP_TAC[simplicial_link; IN_ELIM_THM];
          MATCH_MP_TAC(SET_RULE `!s t (x:real^N). s SUBSET t /\ x IN s ==> x IN t`) THEN
          EXISTS_TAC `s1:real^N->bool` THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC(SET_RULE `!s t (x:real^N). s SUBSET t /\ x IN s ==> x IN t`) THEN
          EXISTS_TAC `s2:real^N->bool` THEN ASM_REWRITE_TAC[];
          ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
        ALL_TAC] THEN
      FIRST_X_ASSUM MATCH_MP_TAC THEN
      MAP_EVERY EXISTS_TAC [`convex hull ((v:real^N) INSERT s1)`; `u:real^N`] THEN
      ASM_REWRITE_TAC[] THEN CONV_TAC INT_REDUCE_CONV];
    ALL_TAC] THEN
  DISCH_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `t:real^N->bool` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `t:real^N->bool`]
    MOI_SCF_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `s:real^N->bool`]
    MOI_SCF_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) IN
                {s | s IN L /\ aff_dim s = &1 /\ convex hull (v INSERT s) IN Y}`
  MP_TAC THENL
   [ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

(* ========================================================================= *)
(* Towards SURFACE_NBHD_SIDES.  Local structure of the first                 *)
(* derived c near the surface: 2-sphere links at vertices of k = bary s,    *)
(* two tetrahedra over each triangle of k, purity; the simplices of c that  *)
(* meet UNIONS s without lying in it (moi_frn_vp) and the sets of them      *)
(* closed under inclusion either way (moi_frn_rclosed); rotation about a    *)
(* vertex of k; dual connectivity and vertex cycles of 2-sphere complexes. *)
(* ========================================================================= *)

let MOI_FRN_TOUCH_CLOSED = prove
 (`!(TR:(real^N->bool)->bool) Z.
     FINITE TR /\ (!t. t IN TR ==> closed t /\ ~(t = {})) /\
     connected (UNIONS TR) /\ Z SUBSET TR /\ ~(Z = {}) /\
     (!t t'. t IN Z /\ t' IN TR /\ ~(t INTER t' = {}) ==> t' IN Z)
     ==> Z = TR`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC(SET_RULE `!z t:(real^N->bool)->bool. z SUBSET t /\ t DIFF z = {}
                          ==> z = t`) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `connected (UNIONS (TR:(real^N->bool)->bool))` THEN
  REWRITE_TAC[CONNECTED_CLOSED] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN
  MAP_EVERY EXISTS_TAC [`UNIONS (Z:(real^N->bool)->bool)`;
                        `UNIONS (TR DIFF Z:(real^N->bool)->bool)`] THEN
  SUBGOAL_THEN `FINITE (Z:(real^N->bool)->bool) /\
                FINITE (TR DIFF Z:(real^N->bool)->bool)` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `TR:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    MATCH_MP_TAC CLOSED_UNIONS THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ASM SET_TAC[];
    REWRITE_TAC[EXTENSION; IN_INTER; NOT_IN_EMPTY; IN_UNIONS; IN_DIFF] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `t:real^N->bool`
      STRIP_ASSUME_TAC) (CONJUNCTS_THEN2 (X_CHOOSE_THEN `t':real^N->bool`
      STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
    UNDISCH_TAC `~((t':real^N->bool) IN Z)` THEN REWRITE_TAC[] THEN
    FIRST_X_ASSUM MATCH_MP_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    SUBGOAL_THEN `?t:real^N->bool. t IN Z` STRIP_ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(t:real^N->bool = {})` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS] THEN
    EXISTS_TAC `x:real^N` THEN CONJ_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    UNDISCH_TAC `~(TR DIFF Z:(real^N->bool)->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_DIFF] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~(t:real^N->bool = {})` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `x:real^N`) THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER; IN_UNIONS; IN_DIFF] THEN
    EXISTS_TAC `x:real^N` THEN CONJ_TAC THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[]]);;

let MOI_FRN_SPHERE_DCONN = prove
 (`!(L:(real^N->bool)->bool) Z.
     simplicial_complex L /\ UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\
     Z SUBSET {t | t IN L /\ aff_dim t = &2} /\ ~(Z = {}) /\
     (!t t'. t IN Z /\ t' IN L /\ aff_dim t' = &2 /\ aff_dim(t INTER t') = &1
             ==> t' IN Z)
     ==> Z = {t | t IN L /\ aff_dim t = &2}`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC MOI_FRN_TOUCH_CLOSED THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_SIMP_TAC[MOI_SCF_SC_FINITE];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[MOI_SCF_SC_CLOSED];
      UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    SUBGOAL_THEN `UNIONS {t:real^N->bool | t IN L /\ aff_dim t = &2} =
                  UNIONS L` SUBST1_TAC THENL
     [MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
       [SET_TAC[]; ALL_TAC] THEN
      REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
      X_GEN_TAC `x:real^N` THEN
      DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `s:real^N->bool`]
        MOI_SCF_SURF_PURE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o MATCH_MP HOMEOMORPHIC_CONNECTEDNESS o
      check (fun th -> can (term_match [] `(a:real^N->bool) homeomorphic
        (b:real^3->bool)`) (concl th))) THEN
    DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC CONNECTED_SPHERE THEN
    REWRITE_TAC[DIMINDEX_3] THEN ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `t':real^N->bool`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^N->bool) IN L /\ aff_dim t = &2` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t INTER t':real^N->bool) IN L` ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (L:(real^N->bool)->bool)` THEN
    REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `t INTER t':real^N->bool`]
    MOI_SCF_SC_VERTEX) THEN ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `w:real^N`;
                 `{u:real^N->bool | u IN Z /\ w IN u}`]
    MOI_SCF_SURF_VERTEX_CONNECTED) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `t'':real^N->bool` THEN ASM_REWRITE_TAC[]];
    REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `t':real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
    SIMP_TAC[]]);;
let MOI_FRN_KVERTEX_SPHERE = prove
 (`!(t:(real^N->bool)->bool) s a.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     {a} IN barycentric_subdivision s
     ==> {a} IN barycentric_subdivision t /\
         simplicial_complex (simplicial_link (barycentric_subdivision t) a) /\
         UNIONS (simplicial_link (barycentric_subdivision t) a) homeomorphic
         sphere(vec 0:real^3,&1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `{a:real^N} IN barycentric_subdivision t` ASSUME_TAC THENL
   [MP_TAC(ASSUME `simplicial_subcomplex (barycentric_subdivision s)
                     (barycentric_subdivision t:(real^N->bool)->bool)`) THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `pl_sphere 2 (UNIONS (simplicial_link
                  (barycentric_subdivision t) (a:real^N)))` ASSUME_TAC THENL
   [ALL_TAC;
    ASM_SIMP_TAC[MOI_FM3_LINK_SC; MOI_SCF_LINK_SPHERE]] THEN
  SUBGOAL_THEN `moi_bar_complex (s:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FDN_SUBCOMPLEX_BAR_COMPLEX THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_FRN_LF_BAR_COMPLEX];
    ALL_TAC] THEN
  MP_TAC(ISPEC `s:(real^N->bool)->bool` MOI_BAR_SUBDIVISION_VERTICES) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `a:real^N` o GEN_REWRITE_RULE I [EXTENSION]) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(r:real^N->bool) IN t` ASSUME_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FDN_LF_SIMPLEX]; ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN relative_interior r` ASSUME_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `a:real^N`)) THEN
    MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v:real^N. {v} IN s /\ v IN r` STRIP_ASSUME_TAC THENL
   [MP_TAC(ISPEC `r:real^N->bool` EXTREME_POINT_EXISTS_CONVEX) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_COMPACT; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `v:real^N` THEN CONJ_TAC THENL
     [MP_TAC(ASSUME `simplicial_subcomplex (s:(real^N->bool)->bool) t`) THEN
      REWRITE_TAC[simplicial_subcomplex] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING];
      ASM_MESON_TAC[extreme_point_of]];
    ALL_TAC] THEN
  MATCH_MP_TAC INTERIOR_LINK_RETRIANGULATION THEN
  MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `v:real^N`] THEN
  ASM_SIMP_TAC[] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[IN_DIFF; IN_UNIONS; IN_ELIM_THM] THEN CONJ_TAC THENL
   [EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET];
    ALL_TAC] THEN
  REWRITE_TAC[NOT_EXISTS_THM; simplicial_link; IN_ELIM_THM] THEN
  X_GEN_TAC `q:real^N->bool` THEN STRIP_TAC THEN
  UNDISCH_TAC `~((v:real^N) IN q)` THEN REWRITE_TAC[] THEN
  SUBGOAL_THEN `(r:real^N->bool) SUBSET r INTER q` MP_TAC THENL
   [MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `r:real^N->bool` THEN
    REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
     [UNDISCH_TAC `lf_simplicial_complex (t:(real^N->bool)->bool)` THEN
      REWRITE_TAC[lf_simplicial_complex] THEN ASM_MESON_TAC[];
      REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[IN_INTER] THEN
      ASM_MESON_TAC[RELATIVE_INTERIOR_SUBSET; SUBSET]];
    ASM SET_TAC[]]);;
let moi_frn_vp = new_definition
 `moi_frn_vp (t:(real^N->bool)->bool) (s:(real^N->bool)->bool)
             (r:real^N->bool) <=>
    r IN barycentric_subdivision t /\ ~(r INTER UNIONS s = {}) /\
    ~(r SUBSET UNIONS s)`;;

let moi_frn_rclosed = new_definition
 `moi_frn_rclosed (t:(real^N->bool)->bool) (s:(real^N->bool)->bool)
                  (X:(real^N->bool)->bool) <=>
    (!r. r IN X ==> moi_frn_vp t s r) /\
    (!r r'. r IN X /\ moi_frn_vp t s r' /\ (r SUBSET r' \/ r' SUBSET r)
            ==> r' IN X)`;;

let MOI_FRN_KTRI_TETS = prove
 (`!(t:(real^N->bool)->bool) s D.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     D IN barycentric_subdivision s /\ aff_dim D = &2
     ==> D IN barycentric_subdivision t /\
         CARD {r | r IN barycentric_subdivision t /\ aff_dim r = &3 /\
                   D SUBSET r} = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(D:real^N->bool) IN barycentric_subdivision t` ASSUME_TAC THENL
   [MP_TAC(ASSUME `simplicial_subcomplex (barycentric_subdivision s)
                     (barycentric_subdivision t:(real^N->bool)->bool)`) THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(D:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(D:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision s:(real^N->bool)->bool`;
                 `D:real^N->bool`] MOI_FM3_LF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `a:real^N`] MOI_FRN_KVERTEX_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `a:real^N`;
                 `D:real^N->bool`] MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `a:real^N`;
                 `e:real^N->bool`] MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(e:real^N->bool) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `aff_dim(D:real^N->bool) = &2` THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `D:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `a:real^N`;
                 `e:real^N->bool`; `&2:int`; `&3:int`] MOI_FM3_LINK_CARD) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; ALL_TAC] THEN
  FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `D:real^N->bool`)) THEN
  DISCH_THEN SUBST1_TAC THEN MATCH_MP_TAC MOI_SCF_SURF_EDGE THEN
  ASM_REWRITE_TAC[]);;

let MOI_FRN_NEAR_PURE = prove
 (`!(t:(real^N->bool)->bool) s a r.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     {a} IN barycentric_subdivision s /\
     r IN barycentric_subdivision t /\ a IN r
     ==> ?r3. r3 IN barycentric_subdivision t /\ aff_dim r3 = &3 /\
              a IN r3 /\ r SUBSET r3`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `a:real^N`] MOI_FRN_KVERTEX_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `a:real^N`;
                 `r:real^N->bool`] MOI_FM3_LINK_OPP) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?tau:real^N->bool.
                  tau IN simplicial_link (barycentric_subdivision t) a /\
                  aff_dim tau = &2 /\ q SUBSET tau`
  STRIP_ASSUME_TAC THENL
   [ASM_CASES_TAC `q:real^N->bool = {}` THENL
     [SUBGOAL_THEN `?x:real^N. x IN UNIONS (simplicial_link
                      (barycentric_subdivision t) a)` STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_TAC THEN
        UNDISCH_TAC `UNIONS (simplicial_link (barycentric_subdivision t)
          (a:real^N)) homeomorphic sphere(vec 0:real^3,&1)` THEN
        ASM_REWRITE_TAC[] THEN ONCE_REWRITE_TAC[HOMEOMORPHIC_SYM] THEN
        REWRITE_TAC[HOMEOMORPHIC_EMPTY; SPHERE_EQ_EMPTY] THEN REAL_ARITH_TAC;
        ALL_TAC] THEN
      UNDISCH_TAC `(x:real^N) IN UNIONS (simplicial_link
                      (barycentric_subdivision t) a)` THEN
      REWRITE_TAC[IN_UNIONS] THEN
      DISCH_THEN(X_CHOOSE_THEN `p:real^N->bool` STRIP_ASSUME_TAC) THEN
      MP_TAC(ISPECL [`simplicial_link (barycentric_subdivision t) (a:real^N)`;
                     `p:real^N->bool`] MOI_SCF_SURF_PURE) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
      MATCH_MP_TAC MONO_EXISTS THEN ASM SET_TAC[];
      MATCH_MP_TAC MOI_SCF_SURF_PURE THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `a:real^N`;
                 `tau:real^N->bool`] MOI_FM3_LINK_JOIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  EXISTS_TAC `convex hull ((a:real^N) INSERT tau)` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]);;
let MOI_FRN_FULL_SUBSET = prove
 (`!(t:(real^N->bool)->bool) s r.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     r IN barycentric_subdivision t /\ r SUBSET UNIONS s
     ==> r IN barycentric_subdivision s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FRN_FULL) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `r INTER UNIONS s = r:real^N->bool` SUBST1_TAC THENL
   [ASM SET_TAC[]; SIMP_TAC[]]);;

let MOI_FRN_VERTEX_ROTATION = prove
 (`!(t:(real^N->bool)->bool) s X a r.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     (!D. D IN barycentric_subdivision s ==> aff_dim D <= &2) /\
     moi_frn_rclosed t s X /\ {a} IN barycentric_subdivision s /\
     (?D. D IN barycentric_subdivision s /\ aff_dim D = &2 /\ a IN D) /\
     r IN X /\ aff_dim r = &3 /\ a IN r
     ==> ?r' D. r' IN X /\ aff_dim r' = &3 /\
                D IN barycentric_subdivision s /\ aff_dim D = &2 /\
                D SUBSET r'`,
  REPEAT GEN_TAC THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
   (CONJUNCTS_THEN2 (X_CHOOSE_THEN `D0:real^N->bool` STRIP_ASSUME_TAC)
    STRIP_ASSUME_TAC))))))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `a:real^N`] MOI_FRN_KVERTEX_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `L = simplicial_link (barycentric_subdivision t) (a:real^N)` THEN
  SUBGOAL_THEN `(a:real^N) IN UNIONS s` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS (barycentric_subdivision s):real^N->bool`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{a:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q:real^N->bool. q IN L
      ==> convex hull (a INSERT q) IN barycentric_subdivision t /\
          aff_dim (convex hull (a INSERT q)) = aff_dim q + &1 /\
          a IN convex hull (a INSERT q) /\ q SUBSET convex hull (a INSERT q)`
  (LABEL_TAC "J") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `a:real^N`;
                   `q:real^N->bool`] MOI_FM3_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `Z = {q:real^N->bool | q IN L /\ aff_dim q = &2 /\
                                    convex hull (a INSERT q) IN X}` THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `a:real^N`;
                 `r:real^N->bool`] MOI_FM3_LINK_OPP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    ASM_MESON_TAC[moi_frn_rclosed; moi_frn_vp; simplicial_subcomplex; SUBSET];
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `q0:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(q0:real^N->bool) IN Z` ASSUME_TAC THENL
   [EXPAND_TAC "Z" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(q0:real^N->bool) IN L`))) THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `aff_dim(r:real^N->bool) = &3` THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `r:real^N->bool`)) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      UNDISCH_TAC `(r:real^N->bool) IN X` THEN
      FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `r:real^N->bool`)) THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  ASM_CASES_TAC
   `?q E:real^N->bool. q IN Z /\ E IN L /\ aff_dim E = &1 /\ E SUBSET q /\
                       convex hull (a INSERT E) IN barycentric_subdivision s`
  THENL
   [FIRST_X_ASSUM(X_CHOOSE_THEN `q:real^N->bool` (X_CHOOSE_THEN
      `E:real^N->bool` STRIP_ASSUME_TAC)) THEN
    MAP_EVERY EXISTS_TAC [`convex hull ((a:real^N) INSERT q)`;
                          `convex hull ((a:real^N) INSERT E)`] THEN
    UNDISCH_TAC `(q:real^N->bool) IN Z` THEN EXPAND_TAC "Z" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(q:real^N->bool) IN L`))) THEN
    USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(E:real^N->bool) IN L`))) THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THENL
     [INT_ARITH_TAC; INT_ARITH_TAC;
      MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM(ASSUME_TAC o REWRITE_RULE[NOT_EXISTS_THM] o check (fun th ->
    is_neg(concl th) && is_exists(rand(concl th)))) THEN
  SUBGOAL_THEN `Z = {q:real^N->bool | q IN L /\ aff_dim q = &2}` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_SPHERE_DCONN THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Z" THEN SET_TAC[];
      ASM SET_TAC[];
      ALL_TAC] THEN
    MAP_EVERY X_GEN_TAC [`q:real^N->bool`; `q':real^N->bool`] THEN
    STRIP_TAC THEN
    UNDISCH_TAC `(q:real^N->bool) IN Z` THEN EXPAND_TAC "Z" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(q INTER q':real^N->bool) IN L` ASSUME_TAC THENL
     [UNDISCH_TAC `simplicial_complex (L:(real^N->bool)->bool)` THEN
      REWRITE_TAC[simplicial_complex] THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(convex hull ((a:real^N) INSERT (q INTER q')) IN
                    barycentric_subdivision s)` ASSUME_TAC THENL
     [FIRST_X_ASSUM(MP_TAC o SPECL [`q:real^N->bool`;
        `q INTER q':real^N->bool`] o check (fun th -> is_forall(concl th) &&
        can (find_term ((=) `Z:(real^N->bool)->bool`)) (concl th))) THEN
      EXPAND_TAC "Z" THEN ASM_REWRITE_TAC[IN_ELIM_THM; INTER_SUBSET];
      ALL_TAC] THEN
    USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(q INTER q':real^N->bool) IN L`))) THEN
    USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(q':real^N->bool) IN L`))) THEN
    USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(q:real^N->bool) IN L`))) THEN
    REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `moi_frn_vp t s (convex hull ((a:real^N) INSERT (q INTER q')))`
    ASSUME_TAC THENL
     [REWRITE_TAC[moi_frn_vp] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `~(convex hull ((a:real^N) INSERT
          (q INTER q')) IN barycentric_subdivision s)` THEN
        REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FRN_FULL_SUBSET THEN
        EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_frn_vp t s (convex hull ((a:real^N) INSERT q'))`
    ASSUME_TAC THENL
     [REWRITE_TAC[moi_frn_vp] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        DISCH_TAC THEN
        SUBGOAL_THEN `convex hull ((a:real^N) INSERT q') IN
                      barycentric_subdivision s` MP_TAC THENL
         [MATCH_MP_TAC MOI_FRN_FULL_SUBSET THEN
        EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
          DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o
            check (fun th -> is_forall(concl th) &&
              can (find_term ((=) `&2:int`)) (concl th) &&
              not (can (find_term ((=) `Z:(real^N->bool)->bool`)) (concl th)))))
          THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]];
      ALL_TAC] THEN
    UNDISCH_TAC `moi_frn_rclosed t s (X:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_frn_rclosed] THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN DISCH_TAC THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `convex hull ((a:real^N) INSERT (q INTER q'))` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN
      EXISTS_TAC `convex hull ((a:real^N) INSERT q)` THEN
      ASM_REWRITE_TAC[] THEN DISJ2_TAC THEN MATCH_MP_TAC HULL_MONO THEN
      SET_TAC[];
      DISJ1_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `a:real^N`;
                 `D0:real^N->bool`] MOI_FM3_LINK_OPP) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ASSUME `simplicial_subcomplex (barycentric_subdivision s)
                     (barycentric_subdivision t:(real^N->bool)->bool)`) THEN
    REWRITE_TAC[simplicial_subcomplex; SUBSET] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[]] THEN
  DISCH_THEN(X_CHOOSE_THEN `E0:real^N->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(E0:real^N->bool) IN L`))) THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(E0:real^N->bool) = &1` ASSUME_TAC THENL
   [UNDISCH_TAC `aff_dim(D0:real^N->bool) = &2` THEN
    FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `D0:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `E0:real^N->bool`]
    MOI_SCF_SURF_PURE) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    UNDISCH_TAC `aff_dim(E0:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q1:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPECL [`q1:real^N->bool`; `E0:real^N->bool`] o
    check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `Z:(real^N->bool)->bool`)) (concl th) &&
      not(is_eq(snd(strip_forall(concl th)))))) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN
  FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `D0:real^N->bool`)) THEN
  ASM_REWRITE_TAC[]);;
let MOI_FRN_EDGE_TWO_TRIANGLES = prove
 (`!(L:(real^N->bool)->bool) E t1 t2 t.
     simplicial_complex L /\ UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\
     E IN L /\ aff_dim E = &1 /\
     t1 IN L /\ aff_dim t1 = &2 /\ E SUBSET t1 /\
     t2 IN L /\ aff_dim t2 = &2 /\ E SUBSET t2 /\ ~(t1 = t2) /\
     t IN L /\ aff_dim t = &2 /\ E SUBSET t
     ==> t = t1 \/ t = t2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `E:real^N->bool`]
    MOI_SCF_SURF_EDGE) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `{u:real^N->bool | u IN L /\ aff_dim u = &2 /\ E SUBSET u}
                HAS_SIZE 2` MP_TAC THENL
   [ASM_REWRITE_TAC[HAS_SIZE] THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_SIMP_TAC[MOI_SCF_SC_FINITE];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N->bool` (X_CHOOSE_THEN `y:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o GEN_REWRITE_RULE I [EXTENSION])))) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  DISCH_THEN(fun th -> MP_TAC(SPEC `t:real^N->bool` th) THEN
    MP_TAC(SPEC `t1:real^N->bool` th) THEN MP_TAC(SPEC `t2:real^N->bool` th)) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~(t1:real^N->bool = t2)` THEN MESON_TAC[]);;
let MOI_FRN_MOD_CONG_ADD = prove
 (`!i j k n. i MOD n = j MOD n ==> (i + k) MOD n = (j + k) MOD n`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
  ASM_REWRITE_TAC[]);;

let MOI_FRN_MOD_SUC_NE = prove
 (`!i n. 3 <= n ==> ~((i + 1) MOD n = i MOD n) /\ ~((i + 2) MOD n = i MOD n)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(SPECL [`i:num`; `n:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `r = i MOD n` THEN ABBREV_TAC `q = i DIV n` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(i + 1) MOD n = (r + 1) MOD n /\ (i + 2) MOD n = (r + 2) MOD n`
  (fun th -> REWRITE_TAC[th]) THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOD_EQ THEN EXISTS_TAC `q:num` THEN
    ASM_ARITH_TAC;
    ALL_TAC] THEN
  CONJ_TAC THENL
   [ASM_CASES_TAC `r + 1 < n` THENL
     [ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
      SUBGOAL_THEN `r + 1 = n` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[MOD_REFL] THEN ASM_ARITH_TAC]];
    ASM_CASES_TAC `r + 2 < n` THENL
     [ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
      ALL_TAC] THEN
    ASM_CASES_TAC `r + 2 = n` THENL
     [ASM_REWRITE_TAC[MOD_REFL] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    SUBGOAL_THEN `(r + 2) MOD n = 1` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC;
      ASM_ARITH_TAC]]);;
let MOI_FRN_PERIODIC_MOD = prove
 (`!(S:num->A) n. ~(n = 0) /\ (!i. S(i + n) = S i) ==> !i. S i = S(i MOD n)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!k i. (S:num->A)(i + k * n) = S i` ASSUME_TAC THENL
   [INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
    GEN_TAC THEN REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `i:num` THEN
  MP_TAC(SPECL [`i:num`; `n:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
    [CONJUNCT1 th]) THEN
  ONCE_REWRITE_TAC[ADD_SYM] THEN ASM_REWRITE_TAC[]);;

let MOI_FRN_PERIODIC_MULT = prove
 (`!(S:num->A) n. (!i. S(i + n) = S i) ==> !k i. S(i + k * n) = S i`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  INDUCT_TAC THEN REWRITE_TAC[MULT_CLAUSES; ADD_CLAUSES] THEN
  GEN_TAC THEN REWRITE_TAC[ADD_ASSOC] THEN ASM_REWRITE_TAC[]);;

let MOI_FRN_PERIODIC_INJ = prove
 (`!(S:num->A) n.
     ~(n = 0) /\ (!i. S(i + n) = S i) /\
     (!i j. i < n /\ j < n /\ S i = S j ==> i = j)
     ==> !i j. S i = S j ==> i MOD n = j MOD n`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN
  MP_TAC(ISPECL [`S:num->A`; `n:num`] MOI_FRN_PERIODIC_MOD) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN DISCH_TAC THEN
  FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_SIMP_TAC[DIVISION]);;

let MOI_FRN_SPHERE_CYCLE = prove
 (`!(L:(real^N->bool)->bool) w.
     simplicial_complex L /\ UNIONS L homeomorphic sphere(vec 0:real^3,&1) /\
     {w} IN L
     ==> ?n S. 3 <= n /\ (!i. S(i + n) = (S:num->real^N->bool) i) /\
               (!i j. S i = S j ==> i MOD n = j MOD n) /\
               (!i. S i IN L /\ aff_dim(S i) = &2 /\ w IN S i /\
                    S i INTER S(SUC i) IN L /\
                    aff_dim(S i INTER S(SUC i)) = &1 /\
                    w IN S i INTER S(SUC i)) /\
               (!t. t IN L /\ aff_dim t = &2 /\ w IN t
                    ==> ?i. i < n /\ t = S i) /\
               (!i t. t IN L /\ aff_dim t = &2 /\
                      S i INTER S(SUC i) SUBSET t
                      ==> t = S i \/ t = S(SUC i)) /\
               (!i j. S i INTER S(SUC i) = S j INTER S(SUC j)
                      ==> i MOD n = j MOD n) /\
               (!E. E IN L /\ aff_dim E = &1 /\ w IN E
                    ==> ?i. i < n /\ E = S i INTER S(SUC i))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `w:real^N`] MOI_SCF_SURF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `S:num->real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
        ASSUME_TAC)))))) THEN
  MAP_EVERY EXISTS_TAC [`n:num`; `S:num->real^N->bool`] THEN
  SUBGOAL_THEN `~(n = 0)` ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `!i j. (S:num->real^N->bool) i = S j ==> i MOD n = j MOD n`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_PERIODIC_INJ THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!i. (S:num->real^N->bool) i INTER S(SUC i) IN L /\
                    w IN S i INTER S(SUC i)` ASSUME_TAC THENL
   [GEN_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_CON_SC_FACE THEN
      EXISTS_TAC `(S:num->real^N->bool) i` THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `(S:num->real^N->bool) i`;
                     `(S:num->real^N->bool) (SUC i)`] MOI_CON_SC_INTER) THEN
      ASM_SIMP_TAC[];
      ASM_REWRITE_TAC[IN_INTER]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!i. ~((S:num->real^N->bool) i = S(SUC i))` ASSUME_TAC THENL
   [GEN_TAC THEN DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
      `!i j. (S:num->real^N->bool) i = S j ==> i MOD n = j MOD n`)) THEN
    REWRITE_TAC[ADD1] THEN
    ONCE_REWRITE_TAC[GSYM MOD_ADD_MOD] THEN
    SUBGOAL_THEN `1 MOD n = 1` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ALL_TAC] THEN
    MP_TAC(SPECL [`i:num`; `n:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN
    ASM_CASES_TAC `i MOD n + 1 < n` THENL
     [ASM_SIMP_TAC[MOD_LT] THEN ARITH_TAC;
      SUBGOAL_THEN `i MOD n + 1 = n` SUBST1_TAC THENL
       [ASM_ARITH_TAC; REWRITE_TAC[MOD_REFL]] THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!i t. t IN L /\ aff_dim t = &2 /\
          (S:num->real^N->bool) i INTER S(SUC i) SUBSET t
          ==> t = S i \/ t = S(SUC i)`
  (LABEL_TAC "TWO") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_EDGE_TWO_TRIANGLES THEN
    EXISTS_TAC `L:(real^N->bool)->bool` THEN
    EXISTS_TAC `(S:num->real^N->bool) i INTER S(SUC i)` THEN
    ASM_REWRITE_TAC[INTER_SUBSET];
    ALL_TAC] THEN

  SUBGOAL_THEN
   `!i j. (S:num->real^N->bool) i INTER S(SUC i) = S j INTER S(SUC j)
          ==> i MOD n = j MOD n`
  (LABEL_TAC "EINJ") THENL
   [MAP_EVERY X_GEN_TAC [`i:num`; `j:num`] THEN DISCH_TAC THEN
    SUBGOAL_THEN `((S:num->real^N->bool) j = S i \/ S j = S(SUC i)) /\
                  (S(SUC j) = S i \/ S(SUC j) = S(SUC i))` MP_TAC THENL
     [CONJ_TAC THEN USE_THEN "TWO" MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      SET_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC(TAUT `(a ==> r) /\ (b /\ c ==> r) /\ (b /\ d ==> r)
                       ==> (a \/ b) /\ (c \/ d) ==> r`) THEN
    REPEAT CONJ_TAC THENL
     [DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
        `!i j. (S:num->real^N->bool) i = S j ==> i MOD n = j MOD n`)) THEN
      SIMP_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `j MOD n = (i + 1) MOD n /\ (j + 1) MOD n = i MOD n`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[GSYM ADD1] THEN CONJ_TAC THEN
        FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
          can (term_match [] `!i j. (S:num->real^N->bool) i = S j ==>
                                    i MOD n = j MOD n`) (concl th))) THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(SPECL [`j:num`; `i + 1`; `1`; `n:num`] MOI_FRN_MOD_CONG_ADD) THEN
      ASM_REWRITE_TAC[ARITH_RULE `(i + 1) + 1 = i + 2`] THEN
      MP_TAC(SPECL [`i:num`; `n:num`] MOI_FRN_MOD_SUC_NE) THEN
      ASM_REWRITE_TAC[] THEN MESON_TAC[];
      STRIP_TAC THEN
      SUBGOAL_THEN `(S:num->real^N->bool) j = S(SUC j)` MP_TAC THENL
       [REWRITE_TAC[ASSUME `(S:num->real^N->bool) j = S(SUC i)`;
                    ASSUME `(S:num->real^N->bool) (SUC j) = S(SUC i)`];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN
  X_GEN_TAC `E:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `E:real^N->bool`]
    MOI_SCF_SURF_PURE) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?x. x < n /\ tau = (S:num->real^N->bool) x`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `?i. i < n /\ t = (S:num->real^N->bool) i`))
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `E:real^N->bool`;
                 `tau:real^N->bool`] MOI_SCF_SURF_OTHER_TRIANGLE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `tau':real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `?y. y < n /\ tau' = (S:num->real^N->bool) y`
  STRIP_ASSUME_TAC THENL
   [FIRST_X_ASSUM(MATCH_MP_TAC o check (fun th -> is_forall(concl th) &&
      can (find_term ((=) `?i. i < n /\ t = (S:num->real^N->bool) i`))
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~((S:num->real^N->bool) x = S y)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim((S:num->real^N->bool) x INTER S y) = &1`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_SCF_INTER_DIM THEN
    MAP_EVERY EXISTS_TAC [`L:(real^N->bool)->bool`; `E:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THEN TRY(CONV_TAC INT_REDUCE_CONV) THEN
    TRY(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `tau:real^N->bool`))) THEN
    TRY(FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `tau':real^N->bool`))) THEN
    ASM_REWRITE_TAC[SUBSET_INTER] THEN CONV_TAC INT_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `SUC(x + n - 1) = x + n` ASSUME_TAC THENL
   [ASM_ARITH_TAC; ALL_TAC] THEN
  SUBGOAL_THEN `(S:num->real^N->bool) (x + n) = S x` ASSUME_TAC THENL
   [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim((S:num->real^N->bool) x INTER S(x + n - 1)) = &1`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(S:num->real^N->bool) x INTER S(x + n - 1) =
                  S(x + n - 1) INTER S(SUC(x + n - 1))` SUBST1_TAC THENL
     [REWRITE_TAC[ASSUME `SUC(x + n - 1) = x + n`;
                  ASSUME `(S:num->real^N->bool) (x + n) = S x`; INTER_COMM];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim((S:num->real^N->bool) x INTER S(SUC x)) = &1 /\
                (S:num->real^N->bool)(SUC x) IN L /\
                aff_dim((S:num->real^N->bool)(SUC x)) = &2 /\
                w IN (S:num->real^N->bool)(SUC x) /\
                (S:num->real^N->bool)(x + n - 1) IN L /\
                aff_dim((S:num->real^N->bool)(x + n - 1)) = &2 /\
                w IN (S:num->real^N->bool)(x + n - 1)`
  STRIP_ASSUME_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `~((S:num->real^N->bool)(SUC x) = S(x + n - 1))` ASSUME_TAC
  THENL
   [DISCH_THEN(MP_TAC o MATCH_MP (ASSUME
      `!i j. (S:num->real^N->bool) i = S j ==> i MOD n = j MOD n`)) THEN
    MP_TAC(SPECL [`x + n - 1`; `n:num`] MOI_FRN_MOD_SUC_NE) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(x + n - 1) + 2 = (SUC x) + 1 * n` SUBST1_TAC THENL
     [ASM_ARITH_TAC; REWRITE_TAC[MOD_MULT_ADD]] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `w:real^N`;
                 `(S:num->real^N->bool) x`] MOI_SCF_SURF_NEIGHBOURS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  FIRST_X_ASSUM(LABEL_TAC "NB" o check (fun th -> is_forall(concl th) &&
    can (find_term ((=) `t1:real^N->bool`)) (concl th))) THEN
  SUBGOAL_THEN `(S:num->real^N->bool) y = S(SUC x) \/ S y = S(x + n - 1)`
  MP_TAC THENL
   [SUBGOAL_THEN `(S:num->real^N->bool) y IN L /\ aff_dim(S y) = &2 /\
                  w IN S y` STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `tau' = (S:num->real^N->bool) y` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    REMOVE_THEN "NB" (fun th -> MP_TAC(SPEC `(S:num->real^N->bool) y` th) THEN
      MP_TAC(SPEC `(S:num->real^N->bool) (SUC x)` th) THEN
      MP_TAC(SPEC `(S:num->real^N->bool) (x + n - 1)` th)) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `~((S:num->real^N->bool)(SUC x) = S(x + n - 1))` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(E:real^N->bool) SUBSET S(x:num) /\ E SUBSET S(y:num)`
  STRIP_ASSUME_TAC THENL
   [MAP_EVERY UNDISCH_TAC [`tau = (S:num->real^N->bool) x`;
      `tau' = (S:num->real^N->bool) y`] THEN
    REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `x:num` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
    EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET_INTER] THEN
    UNDISCH_TAC `(E:real^N->bool) SUBSET S(y:num)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(SPECL [`x + n - 1`; `n:num`] DIVISION) THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `i0 = (x + n - 1) MOD n` THEN
  ABBREV_TAC `q0 = (x + n - 1) DIV n` THEN STRIP_TAC THEN
  FIRST_X_ASSUM(ASSUME_TAC o SYM o check (fun th -> is_eq(concl th) &&
    lhs(concl th) = `x + n - 1`)) THEN
  EXISTS_TAC `i0:num` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(S:num->real^N->bool) i0 = S(x + n - 1) /\
                (S:num->real^N->bool) (SUC i0) = S x`
  (fun th -> REWRITE_TAC[th]) THENL
   [MP_TAC(ISPECL [`S:num->real^N->bool`; `n:num`] MOI_FRN_PERIODIC_MULT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN CONJ_TAC THENL
     [FIRST_ASSUM(MP_TAC o SPECL [`q0:num`; `i0:num`]) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN AP_TERM_TAC THEN ASM_ARITH_TAC;
      FIRST_ASSUM(MP_TAC o SPECL [`q0:num`; `SUC i0`]) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      GEN_REWRITE_TAC RAND_CONV
        [SYM(ASSUME `(S:num->real^N->bool) (x + n) = S x`)] THEN
      AP_TERM_TAC THEN ASM_ARITH_TAC];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_SCF_SUBSET_DIM_EQ THEN
  EXISTS_TAC `L:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `(S:num->real^N->bool)(x + n - 1)`;
                   `(S:num->real^N->bool) x`] MOI_CON_SC_INTER) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN MATCH_MP_TAC MOI_CON_SC_FACE THEN
    EXISTS_TAC `(S:num->real^N->bool)(x + n - 1)` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET_INTER] THEN
    UNDISCH_TAC `(E:real^N->bool) SUBSET S(y:num)` THEN ASM_REWRITE_TAC[];
    ONCE_REWRITE_TAC[INTER_COMM] THEN ASM_REWRITE_TAC[]]);;

(* Rotation about an edge of k (the cycle of tetrahedra around it).          *)

let MOI_FRN_ARC_ARITH = prove
 (`!u v n. u < n /\ v < n /\ ~(u = v)
           ==> ?m. (u + 1 + m) MOD n = v /\
                   !k. k < m ==> ~((u + 1 + k) MOD n = u) /\
                                 ~((u + 1 + k) MOD n = v)`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `u < v:num` THENL
   [EXISTS_TAC `v - (u + 1)` THEN
    SUBGOAL_THEN `u + 1 + v - (u + 1) = v` SUBST1_TAC THENL
     [ASM_ARITH_TAC; ASM_SIMP_TAC[MOD_LT]] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(u + 1 + k) MOD n = u + 1 + k` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_LT THEN ASM_ARITH_TAC; ASM_ARITH_TAC];
    EXISTS_TAC `v + n - (u + 1)` THEN
    SUBGOAL_THEN `(u + 1 + v + n - (u + 1)) MOD n = v` SUBST1_TAC THENL
     [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC;
      REWRITE_TAC[]] THEN
    X_GEN_TAC `k:num` THEN DISCH_TAC THEN
    ASM_CASES_TAC `u + 1 + k < n` THENL
     [ASM_SIMP_TAC[MOD_LT] THEN ASM_ARITH_TAC;
      SUBGOAL_THEN `(u + 1 + k) MOD n = (u + 1 + k) - n` SUBST1_TAC THENL
       [MATCH_MP_TAC MOD_UNIQ THEN EXISTS_TAC `1` THEN ASM_ARITH_TAC;
        ASM_ARITH_TAC]]]);;

let MOI_FRN_EDGE_ROTATION = prove
 (`!(t:(real^N->bool)->bool) s X e D1 D2 r.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     (!D. D IN barycentric_subdivision s ==> aff_dim D <= &2) /\
     moi_frn_rclosed t s X /\
     e IN barycentric_subdivision s /\ aff_dim e = &1 /\
     D1 IN barycentric_subdivision s /\ aff_dim D1 = &2 /\ e SUBSET D1 /\
     D2 IN barycentric_subdivision s /\ aff_dim D2 = &2 /\ e SUBSET D2 /\
     ~(D1 = D2) /\
     (!D. D IN barycentric_subdivision s /\ aff_dim D = &2 /\ e SUBSET D
          ==> D = D1 \/ D = D2) /\
     r IN X /\ aff_dim r = &3 /\ D1 SUBSET r
     ==> ?r'. r' IN X /\ aff_dim r' = &3 /\ D2 SUBSET r'`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(e:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision s:(real^N->bool)->bool`;
                 `e:real^N->bool`] MOI_FM3_LF_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `a:real^N`] MOI_FRN_KVERTEX_SPHERE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `L = simplicial_link (barycentric_subdivision t) (a:real^N)` THEN
  SUBGOAL_THEN `(a:real^N) IN UNIONS s` ASSUME_TAC THENL
   [FIRST_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `UNIONS (barycentric_subdivision s):real^N->bool`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `{a:real^N}` THEN
    ASM_REWRITE_TAC[IN_SING];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q:real^N->bool. q IN L
      ==> convex hull (a INSERT q) IN barycentric_subdivision t /\
          aff_dim (convex hull (a INSERT q)) = aff_dim q + &1 /\
          a IN convex hull (a INSERT q) /\ q SUBSET convex hull (a INSERT q)`
  (LABEL_TAC "J") THENL
   [GEN_TAC THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`; `a:real^N`;
                   `q:real^N->bool`] MOI_FM3_LINK_JOIN) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q q':real^N->bool. q IN L /\ q' IN L
      ==> (convex hull (a INSERT q) SUBSET convex hull (a INSERT q') <=>
           q SUBSET q') /\
          (convex hull (a INSERT q) = convex hull (a INSERT q') ==> q = q')`
  (LABEL_TAC "JS") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LINK_JOIN_SUBSET THEN
      EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      DISCH_TAC THEN MATCH_MP_TAC MOI_FM3_LINK_JOIN_INJ THEN
      MAP_EVERY EXISTS_TAC [`barycentric_subdivision t:(real^N->bool)->bool`;
                            `a:real^N`] THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N->bool. x IN barycentric_subdivision s
                     ==> x IN barycentric_subdivision t`
  ASSUME_TAC THENL
   [MP_TAC(ASSUME `simplicial_subcomplex (barycentric_subdivision s)
                     (barycentric_subdivision t:(real^N->bool)->bool)`) THEN
    SIMP_TAC[simplicial_subcomplex; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!x:real^N->bool. x IN barycentric_subdivision t /\ a IN x
      ==> ?q. q IN L /\ x = convex hull (a INSERT q)`
  (LABEL_TAC "OPP") THENL
   [REPEAT STRIP_TAC THEN EXPAND_TAC "L" THEN
    MATCH_MP_TAC MOI_FM3_LINK_OPP THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  USE_THEN "OPP" (MP_TAC o SPEC `e:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p0:real^N->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(p0:real^N->bool) IN L`))) THEN STRIP_TAC THEN
  SUBGOAL_THEN `?w:real^N. p0 = {w}` (X_CHOOSE_THEN `w:real^N` SUBST_ALL_TAC)
  THENL
   [REWRITE_TAC[GSYM AFF_DIM_EQ_0] THEN
    UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN
    FIRST_X_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `e:real^N->bool`)) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `?E1 E2:real^N->bool.
      E1 IN L /\ aff_dim E1 = &1 /\ w IN E1 /\
      D1 = convex hull (a INSERT E1) /\
      E2 IN L /\ aff_dim E2 = &1 /\ w IN E2 /\
      D2 = convex hull (a INSERT E2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(a:real^N) IN D1 /\ a IN D2` STRIP_ASSUME_TAC
    THENL [ASM SET_TAC[]; ALL_TAC] THEN
    USE_THEN "OPP" (MP_TAC o SPEC `D1:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `E1:real^N->bool` STRIP_ASSUME_TAC) THEN
    USE_THEN "OPP" (MP_TAC o SPEC `D2:real^N->bool`) THEN
    ANTS_TAC THENL [ASM_SIMP_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `E2:real^N->bool` STRIP_ASSUME_TAC) THEN
    MAP_EVERY EXISTS_TAC [`E1:real^N->bool`; `E2:real^N->bool`] THEN
    ASM_REWRITE_TAC[] THEN
    USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(E1:real^N->bool) IN L`))) THEN
    USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th
      (ASSUME `(E2:real^N->bool) IN L`))) THEN
    REPEAT STRIP_TAC THENL
     [UNDISCH_TAC `aff_dim(D1:real^N->bool) = &2` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      USE_THEN "JS" (fun th -> MP_TAC(MATCH_MP th (CONJ
        (ASSUME `{w:real^N} IN L`) (ASSUME `(E1:real^N->bool) IN L`)))) THEN
      REWRITE_TAC[SING_SUBSET] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(e:real^N->bool) SUBSET D1` THEN ASM_REWRITE_TAC[];
      UNDISCH_TAC `aff_dim(D2:real^N->bool) = &2` THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      USE_THEN "JS" (fun th -> MP_TAC(MATCH_MP th (CONJ
        (ASSUME `{w:real^N} IN L`) (ASSUME `(E2:real^N->bool) IN L`)))) THEN
      REWRITE_TAC[SING_SUBSET] THEN DISCH_THEN(MP_TAC o CONJUNCT1) THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN
      UNDISCH_TAC `(e:real^N->bool) SUBSET D2` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(a:real^N) IN r /\ r IN barycentric_subdivision t`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `moi_frn_rclosed t s (X:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_frn_rclosed; moi_frn_vp] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "OPP" (MP_TAC o SPEC `r:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(q:real^N->bool) IN L`))) THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim(q:real^N->bool) = &2 /\ (E1:real^N->bool) SUBSET q`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [UNDISCH_TAC `aff_dim(r:real^N->bool) = &3` THEN ASM_REWRITE_TAC[] THEN
      INT_ARITH_TAC;
      USE_THEN "JS" (fun th -> MP_TAC(MATCH_MP th (CONJ
        (ASSUME `(E1:real^N->bool) IN L`) (ASSUME `(q:real^N->bool) IN L`))))
      THEN DISCH_THEN(SUBST1_TAC o SYM o CONJUNCT1) THEN
      UNDISCH_TAC `(D1:real^N->bool) SUBSET r` THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`L:(real^N->bool)->bool`; `w:real^N`] MOI_FRN_SPHERE_CYCLE)
  THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `n:num` (X_CHOOSE_THEN `S:num->real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 (LABEL_TAC "PER")
    (CONJUNCTS_THEN2 (LABEL_TAC "IM") (CONJUNCTS_THEN2 (LABEL_TAC "SI")
    (CONJUNCTS_THEN2 (LABEL_TAC "ALLT") (CONJUNCTS_THEN2 (LABEL_TAC "TWO")
    (CONJUNCTS_THEN2 (LABEL_TAC "EINJ") (LABEL_TAC "ALLE")))))))))) THEN
  USE_THEN "ALLE" (MP_TAC o SPEC `E1:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `i1:num` STRIP_ASSUME_TAC) THEN
  USE_THEN "ALLE" (MP_TAC o SPEC `E2:real^N->bool`) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:num` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `~(i1:num = p)` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~(D1:real^N->bool = D2)` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. convex hull ((a:real^N) INSERT ((S:num->real^N->bool) m INTER
          S(SUC m))) IN barycentric_subdivision s
        ==> m MOD n = i1 \/ m MOD n = p`
  (LABEL_TAC "WALL") THENL
   [X_GEN_TAC `m:num` THEN DISCH_TAC THEN
    USE_THEN "SI" (STRIP_ASSUME_TAC o SPEC `m:num`) THEN
    USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `(S:num->real^N->bool) m INTER S(SUC m) IN L`))) THEN STRIP_TAC THEN
    SUBGOAL_THEN `(e:real^N->bool) SUBSET
                  convex hull (a INSERT ((S:num->real^N->bool) m INTER
                  S(SUC m)))` ASSUME_TAC THENL
     [FIRST_ASSUM(SUBST1_TAC o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `e:real^N->bool`)) THEN
      USE_THEN "JS" (fun th -> MP_TAC(MATCH_MP th (CONJ
        (ASSUME `{w:real^N} IN L`) (ASSUME
        `(S:num->real^N->bool) m INTER S(SUC m) IN L`)))) THEN
      DISCH_THEN(SUBST1_TAC o CONJUNCT1) THEN ASM_REWRITE_TAC[SING_SUBSET];
      ALL_TAC] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `convex hull ((a:real^N) INSERT
      ((S:num->real^N->bool) m INTER S(SUC m)))` o check (fun th ->
      is_forall(concl th) && can (find_term ((=) `D1:real^N->bool`))
      (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [INT_ARITH_TAC; ALL_TAC] THEN
    STRIP_TAC THENL
     [SUBGOAL_THEN `(S:num->real^N->bool) m INTER S(SUC m) = E1` ASSUME_TAC
      THENL
       [USE_THEN "JS" (fun th -> MP_TAC(MATCH_MP th (CONJ
          (ASSUME `(S:num->real^N->bool) m INTER S(SUC m) IN L`)
          (ASSUME `(E1:real^N->bool) IN L`)))) THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[];
        DISJ1_TAC THEN
        SUBGOAL_THEN `m MOD n = i1 MOD n` SUBST1_TAC THENL
         [USE_THEN "EINJ" MATCH_MP_TAC THEN ASM_MESON_TAC[];
          ASM_SIMP_TAC[MOD_LT]]];
      SUBGOAL_THEN `(S:num->real^N->bool) m INTER S(SUC m) = E2` ASSUME_TAC
      THENL
       [USE_THEN "JS" (fun th -> MP_TAC(MATCH_MP th (CONJ
          (ASSUME `(S:num->real^N->bool) m INTER S(SUC m) IN L`)
          (ASSUME `(E2:real^N->bool) IN L`)))) THEN
        DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN ASM_MESON_TAC[];
        DISJ2_TAC THEN
        SUBGOAL_THEN `m MOD n = p MOD n` SUBST1_TAC THENL
         [USE_THEN "EINJ" MATCH_MP_TAC THEN ASM_MESON_TAC[];
          ASM_SIMP_TAC[MOD_LT]]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!m. moi_frn_vp t s (convex hull ((a:real^N) INSERT (S:num->real^N->bool) m))
        /\ aff_dim (convex hull (a INSERT S m)) = &3`
  (LABEL_TAC "TET") THENL
   [X_GEN_TAC `m:num` THEN
    USE_THEN "SI" (STRIP_ASSUME_TAC o SPEC `m:num`) THEN
    USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `(S:num->real^N->bool) m IN L`))) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[moi_frn_vp] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      DISCH_TAC THEN
      SUBGOAL_THEN `convex hull ((a:real^N) INSERT (S:num->real^N->bool) m) IN
                    barycentric_subdivision s` MP_TAC THENL
       [MATCH_MP_TAC MOI_FRN_FULL_SUBSET THEN
        EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        DISCH_THEN(fun th -> FIRST_ASSUM(MP_TAC o C MATCH_MP th o
          check (fun th -> is_forall(concl th) &&
            can (find_term ((=) `&2:int`)) (concl th) &&
            is_imp(snd(strip_forall(concl th))) &&
            not(can (find_term ((=) `D1:real^N->bool`)) (concl th))))) THEN
        ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
      INT_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!j m. (!k. k < m ==> ~(convex hull ((a:real^N) INSERT
             ((S:num->real^N->bool)(j + k) INTER S(SUC(j + k)))) IN
             barycentric_subdivision s))
          ==> (convex hull (a INSERT S j) IN X <=>
               convex hull (a INSERT S(j + m)) IN X)`
  (LABEL_TAC "ARC") THENL
   [GEN_TAC THEN INDUCT_TAC THENL
     [REWRITE_TAC[ADD_CLAUSES]; ALL_TAC] THEN
    DISCH_TAC THEN
    FIRST_X_ASSUM(MP_TAC o check (fun th -> is_imp(concl th))) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      ASM_ARITH_TAC;
      DISCH_THEN SUBST1_TAC] THEN
    REWRITE_TAC[ADD_CLAUSES] THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `m:num`) THEN REWRITE_TAC[LT] THEN
    DISCH_TAC THEN
    ABBREV_TAC `jm = j + m:num` THEN
    USE_THEN "SI" (STRIP_ASSUME_TAC o SPEC `jm:num`) THEN
    USE_THEN "J" (fun th -> MP_TAC(MATCH_MP th (ASSUME
      `(S:num->real^N->bool) jm INTER S(SUC jm) IN L`))) THEN STRIP_TAC THEN
    SUBGOAL_THEN `moi_frn_vp t s (convex hull ((a:real^N) INSERT
                    ((S:num->real^N->bool) jm INTER S(SUC jm))))` ASSUME_TAC
    THENL
     [ASM_REWRITE_TAC[moi_frn_vp] THEN CONJ_TAC THENL
       [ASM SET_TAC[];
        DISCH_TAC THEN UNDISCH_TAC `~(convex hull ((a:real^N) INSERT
          ((S:num->real^N->bool) jm INTER S(SUC jm))) IN
          barycentric_subdivision s)` THEN REWRITE_TAC[] THEN
        MATCH_MP_TAC MOI_FRN_FULL_SUBSET THEN
        EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `convex hull ((a:real^N) INSERT ((S:num->real^N->bool) jm INTER S(SUC jm)))
      SUBSET convex hull (a INSERT S jm) /\
      convex hull ((a:real^N) INSERT ((S:num->real^N->bool) jm INTER S(SUC jm)))
      SUBSET convex hull (a INSERT S(SUC jm))`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[]; ALL_TAC] THEN
    USE_THEN "TET" (STRIP_ASSUME_TAC o SPEC `jm:num`) THEN
    USE_THEN "TET" (STRIP_ASSUME_TAC o SPEC `SUC jm`) THEN
    MP_TAC(ASSUME `moi_frn_rclosed t s (X:(real^N->bool)->bool)`) THEN
    REWRITE_TAC[moi_frn_rclosed] THEN
    DISCH_THEN(ASSUME_TAC o CONJUNCT2) THEN EQ_TAC THEN
    DISCH_THEN(LABEL_TAC "SRC") THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    EXISTS_TAC `convex hull ((a:real^N) INSERT ((S:num->real^N->bool) jm INTER
                S(SUC jm)))` THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_ASSUM MATCH_MP_TAC THEN
    USE_THEN "SRC" (fun th -> EXISTS_TAC (lhand(concl th))) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. u < n /\ v < n /\ ~(u = v) /\
          (!k. ~(k MOD n = u) /\ ~(k MOD n = v) ==>
               ~(convex hull ((a:real^N) INSERT ((S:num->real^N->bool) k INTER
                  S(SUC k))) IN barycentric_subdivision s))
          ==> (convex hull (a INSERT S(SUC u)) IN X <=>
               convex hull (a INSERT S v) IN X)`
  (LABEL_TAC "ARC2") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    MP_TAC(SPECL [`u:num`; `v:num`; `n:num`] MOI_FRN_ARC_ARITH) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `m:num` STRIP_ASSUME_TAC) THEN
    USE_THEN "ARC" (MP_TAC o SPECL [`SUC u`; `m:num`]) THEN
    ANTS_TAC THENL
     [X_GEN_TAC `k:num` THEN DISCH_TAC THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `k:num`) THEN ASM_REWRITE_TAC[ADD1] THEN
      REWRITE_TAC[ARITH_RULE `(u + 1) + k = u + 1 + k`];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    SUBGOAL_THEN `(S:num->real^N->bool)(SUC u + m) = S v` SUBST1_TAC THENL
     [MP_TAC(ISPECL [`S:num->real^N->bool`; `n:num`] MOI_FRN_PERIODIC_MOD) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
      DISCH_THEN(fun th -> ONCE_REWRITE_TAC[th]) THEN AP_TERM_TAC THEN
      ASM_SIMP_TAC[MOD_LT; ARITH_RULE `SUC u + m = u + 1 + m`];
      REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u v. (u = i1 /\ v = p) \/ (u = p /\ v = i1)
          ==> !k. ~(k MOD n = u) /\ ~(k MOD n = v) ==>
               ~(convex hull ((a:real^N) INSERT ((S:num->real^N->bool) k INTER
                  S(SUC k))) IN barycentric_subdivision s)`
  (LABEL_TAC "NOW") THENL
   [REPEAT GEN_TAC THEN DISCH_TAC THEN X_GEN_TAC `k:num` THEN STRIP_TAC THEN
    DISCH_THEN(fun th -> USE_THEN "WALL" (MP_TAC o C MATCH_MP th)) THEN
    FIRST_X_ASSUM(DISJ_CASES_THEN STRIP_ASSUME_TAC o check (fun th ->
      is_disj(concl th) && can (find_term ((=) `i1:num`)) (concl th))) THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[];
    ALL_TAC] THEN
  USE_THEN "TWO" (MP_TAC o SPECL [`i1:num`; `q:real^N->bool`]) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
      lhs(concl th) = `E1:real^N->bool`)) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [USE_THEN "ARC2" (MP_TAC o SPECL [`p:num`; `i1:num`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "NOW" MATCH_MP_TAC THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex hull ((a:real^N) INSERT (S:num->real^N->bool) i1) IN X`
    (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `q:real^N->bool`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `r:real^N->bool`)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    EXISTS_TAC `convex hull ((a:real^N) INSERT (S:num->real^N->bool) (SUC p))`
    THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    USE_THEN "ARC2" (MP_TAC o SPECL [`i1:num`; `p:num`]) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN USE_THEN "NOW" MATCH_MP_TAC THEN SIMP_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex hull ((a:real^N) INSERT (S:num->real^N->bool) (SUC i1))
                  IN X` (fun th -> REWRITE_TAC[th]) THENL
     [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `q:real^N->bool`)) THEN
      FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> is_eq(concl th) &&
        lhs(concl th) = `r:real^N->bool`)) THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    DISCH_TAC THEN
    EXISTS_TAC `convex hull ((a:real^N) INSERT (S:num->real^N->bool) p)`
    THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[]]);;

(* ========================================================================= *)
(* Chains of a finite combinatorial 2-manifold c                            *)
(* and the simplices of its barycentric subdivision: hulls of barycentres   *)
(* determine chains, dimensions, flags (vertex, edge, triangle), and every  *)
(* edge of the subdivision lies in exactly two of its triangles.            *)
(* ========================================================================= *)

let MOI_FRN_CHAIN_EXTREME = prove
 (`!(c:(real^N->bool)->bool) f.
     moi_bar_complex c /\ moi_bar_chain c f
     ==> {x | x extreme_point_of convex hull (IMAGE simplex_barycentre f)} =
         IMAGE simplex_barycentre f`,
  REPEAT STRIP_TAC THEN
  MATCH_MP_TAC EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT THEN
  MATCH_MP_TAC MOI_BAR_CHAIN_AFFINE_INDEPENDENT THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_FRN_CHAIN_IMAGE_INJ = prove
 (`!(c:(real^N->bool)->bool) f g.
     moi_bar_complex c /\ moi_bar_chain c f /\ moi_bar_chain c g /\
     IMAGE simplex_barycentre f SUBSET IMAGE simplex_barycentre g
     ==> f SUBSET g`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N->bool` THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `simplex_barycentre (x:real^N->bool) IN
                IMAGE simplex_barycentre g` MP_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IN_IMAGE] THEN
  DISCH_THEN(X_CHOOSE_THEN `y:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N->bool) = y` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOI_FRN_BARYCENTRE_INJ THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]);;

let MOI_FRN_CHAIN_HULL_SUBSET = prove
 (`!(c:(real^N->bool)->bool) f g.
     moi_bar_complex c /\ moi_bar_chain c f /\ moi_bar_chain c g
     ==> (convex hull (IMAGE simplex_barycentre f) SUBSET
          convex hull (IMAGE simplex_barycentre g) <=> f SUBSET g)`,
  REPEAT STRIP_TAC THEN EQ_TAC THENL
   [DISCH_TAC; DISCH_TAC THEN MATCH_MP_TAC HULL_MONO THEN ASM SET_TAC[]] THEN
  MATCH_MP_TAC MOI_FRN_CHAIN_IMAGE_INJ THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))
                face_of convex hull (IMAGE simplex_barycentre g)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
    EXISTS_TAC `barycentric_subdivision c:(real^N->bool)->bool` THEN
    ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_COMPLEX; MOI_BAR_IN_SUBDIVISION] THEN
    ASM_MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_FRN_CHAIN_EXTREME) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
    MOI_FRN_CHAIN_EXTREME) THEN
  ASM_REWRITE_TAC[] THEN
  REPEAT(DISCH_THEN(SUBST1_TAC o SYM)) THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`convex hull (IMAGE simplex_barycentre (f:(real^N->bool)->bool))`;
                 `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))`;
                 `x:real^N`] EXTREME_POINT_OF_FACE) THEN
  ASM_REWRITE_TAC[] THEN SIMP_TAC[]);;

let MOI_FRN_CHAIN_HULL_INJ = prove
 (`!(c:(real^N->bool)->bool) f g.
     moi_bar_complex c /\ moi_bar_chain c f /\ moi_bar_chain c g /\
     convex hull (IMAGE simplex_barycentre f) =
     convex hull (IMAGE simplex_barycentre g)
     ==> f = g`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `g:(real^N->bool)->bool`] MOI_FRN_CHAIN_HULL_SUBSET);
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`;
                   `f:(real^N->bool)->bool`] MOI_FRN_CHAIN_HULL_SUBSET)] THEN
  ASM_REWRITE_TAC[SUBSET_REFL]);;

let MOI_FRN_CHAIN_DIM_LT = prove
 (`!(c:(real^N->bool)->bool) f r r'.
     moi_bar_complex c /\ moi_bar_chain c f /\ r IN f /\ r' IN f /\
     r SUBSET r' /\ ~(r = r')
     ==> aff_dim r < aff_dim r'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT; SIMPLEX_IMP_CONVEX];
    MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]]);;

let MOI_FRN_CHAIN_DIM_INJ = prove
 (`!(c:(real^N->bool)->bool) f r r'.
     moi_bar_complex c /\ moi_bar_chain c f /\ r IN f /\ r' IN f /\
     aff_dim r = aff_dim r'
     ==> r = r'`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) SUBSET r' \/ r' SUBSET r` MP_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  ASM_CASES_TAC `r:real^N->bool = r'` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(DISJ_CASES_THEN ASSUME_TAC) THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `r:real^N->bool`; `r':real^N->bool`] MOI_FRN_CHAIN_DIM_LT);
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                   `r':real^N->bool`; `r:real^N->bool`] MOI_FRN_CHAIN_DIM_LT)]
  THEN ASM_MESON_TAC[INT_LT_REFL]);;

let MOI_FRN_CHAIN_DIM_GE0 = prove
 (`!(c:(real^N->bool)->bool) f r.
     moi_bar_complex c /\ moi_bar_chain c f /\ r IN f ==> &0 <= aff_dim r`,
  REWRITE_TAC[AFF_DIM_POS_LE] THEN MESON_TAC[MOI_BAR_CHAIN_ELEMENT]);;

let MOI_FRN_CHAIN_CARD_LE3 = prove
 (`!(c:(real^N->bool)->bool) f.
     moi_bar_complex c /\ (!r. r IN c ==> aff_dim r <= &2) /\
     moi_bar_chain c f
     ==> CARD f <= 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (f:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  MP_TAC(ISPECL [`aff_dim:(real^N->bool)->int`; `f:(real^N->bool)->bool`]
    CARD_IMAGE_INJ) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    MATCH_MP_TAC MOI_FRN_CHAIN_DIM_INJ THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN
    EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    DISCH_THEN(SUBST1_TAC o SYM)] THEN
  MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC `CARD {&0:int,&1,&2}` THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN
    REWRITE_TAC[SUBSET; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY] THEN
    X_GEN_TAC `d:int` THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `&0 <= aff_dim(r:real^N->bool) /\ aff_dim r <= &2` MP_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FRN_CHAIN_DIM_GE0 THEN ASM_MESON_TAC[];
        ASM_MESON_TAC[moi_bar_chain; SUBSET]];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
             NOT_IN_EMPTY] THEN
    CONV_TAC INT_REDUCE_CONV THEN CONV_TAC NUM_REDUCE_CONV]);;

let MOI_FRN_BARY_AFF_DIM = prove
 (`!(c:(real^N->bool)->bool) f.
     moi_bar_complex c /\ moi_bar_chain c f
     ==> aff_dim (convex hull (IMAGE simplex_barycentre f)) = &(CARD f) - &1`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC AFF_DIM_SIMPLEX THEN
  MATCH_MP_TAC MOI_BAR_CHAIN_SIMPLEX THEN
  EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]);;

let MOI_FRN_BARY_DIM_LE2 = prove
 (`!(c:(real^N->bool)->bool) r.
     moi_bar_complex c /\ (!q. q IN c ==> aff_dim q <= &2) /\
     r IN barycentric_subdivision c
     ==> aff_dim r <= &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_FRN_BARY_AFF_DIM) THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_FRN_CHAIN_CARD_LE3) THEN
  ASM_REWRITE_TAC[GSYM INT_OF_NUM_LE] THEN INT_ARITH_TAC);;

let MOI_FRN_CHAIN3_FLAG = prove
 (`!(c:(real^N->bool)->bool) f.
     moi_bar_complex c /\ (!r. r IN c ==> aff_dim r <= &2) /\
     moi_bar_chain c f /\ CARD f = 3
     ==> ?v e D. {v} IN c /\ e IN c /\ aff_dim e = &1 /\ D IN c /\
                 aff_dim D = &2 /\ v IN e /\ e SUBSET D /\ f = {{v},e,D}`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `FINITE (f:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN f ==> r IN c /\ &0 <= aff_dim r /\
                                            aff_dim r <= &2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT];
      MATCH_MP_TAC MOI_FRN_CHAIN_DIM_GE0 THEN ASM_MESON_TAC[];
      ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]];
    ALL_TAC] THEN
  SUBGOAL_THEN `IMAGE (aff_dim:(real^N->bool)->int) f = {&0,&1,&2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC CARD_SUBSET_EQ THEN
    REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY] THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `d:int` THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      FIRST_X_ASSUM(MP_TAC o SPEC `r:real^N->bool` o check (fun th ->
        is_forall(concl th) && can (find_term ((=) `&2:int`)) (concl th) &&
        can (find_term ((=) `f:(real^N->bool)->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      MP_TAC(ISPECL [`aff_dim:(real^N->bool)->int`; `f:(real^N->bool)->bool`]
        CARD_IMAGE_INJ) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
        MATCH_MP_TAC MOI_FRN_CHAIN_DIM_INJ THEN
        MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`;
                              `f:(real^N->bool)->bool`] THEN
        ASM_REWRITE_TAC[];
        DISCH_THEN SUBST1_TAC] THEN
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
               NOT_IN_EMPTY] THEN
      CONV_TAC INT_REDUCE_CONV THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC NUM_REDUCE_CONV];
    ALL_TAC] THEN
  SUBGOAL_THEN `?v0 e D:real^N->bool. v0 IN f /\ aff_dim v0 = &0 /\
                  e IN f /\ aff_dim e = &1 /\ D IN f /\ aff_dim D = &2`
  STRIP_ASSUME_TAC THENL
   [MP_TAC(ASSUME `IMAGE (aff_dim:(real^N->bool)->int) f = {&0,&1,&2}`) THEN
    REWRITE_TAC[EXTENSION; IN_IMAGE; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(fun th -> MP_TAC(SPEC `&0:int` th) THEN
      MP_TAC(SPEC `&1:int` th) THEN MP_TAC(SPEC `&2:int` th)) THEN
    CONV_TAC INT_REDUCE_CONV THEN MESON_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `v0:real^N->bool` AFF_DIM_EQ_0) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` SUBST_ALL_TAC) THEN
  MAP_EVERY EXISTS_TAC [`v:real^N`; `e:real^N->bool`; `D:real^N->bool`] THEN
  ASM_SIMP_TAC[] THEN
  SUBGOAL_THEN `!r r':real^N->bool. r IN f /\ r' IN f /\ aff_dim r < aff_dim r'
                                    ==> r SUBSET r'` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SUBGOAL_THEN `(r:real^N->bool) SUBSET r' \/ r' SUBSET r` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`r':real^N->bool`; `r:real^N->bool`] AFF_DIM_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `{v:real^N} SUBSET e` MP_TAC THENL
     [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_SING] THEN
      INT_ARITH_TAC;
      SIMP_TAC[SING_SUBSET]];
    FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
    SUBGOAL_THEN `~({v:real^N} = e) /\ ~({v} = D) /\ ~(e:real^N->bool = D)`
    STRIP_ASSUME_TAC THENL
     [REPEAT CONJ_TAC THEN
      DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
      ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC NUM_REDUCE_CONV]);;

let MOI_FRN_CHAIN_INSERT2 = prove
 (`!(c:(real^N->bool)->bool) r1 r2 p.
     moi_bar_chain c {r1,r2}
     ==> (moi_bar_chain c (p INSERT {r1,r2}) <=>
          p IN c /\ ~(p = {}) /\ (p SUBSET r1 \/ r1 SUBSET p) /\
          (p SUBSET r2 \/ r2 SUBSET p))`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; FINITE_INSERT; FINITE_EMPTY;
              IN_INSERT; NOT_IN_EMPTY; EMPTY_SUBSET] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN EQ_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET_REFL]);;

let MOI_FRN_SEG_VERTS = prove
 (`!(c:(real^N->bool)->bool) r.
     moi_bar_complex c /\ r IN c /\ aff_dim r = &1
     ==> ?x y. ~(x = y) /\ r = convex hull {x,y} /\ {x} IN c /\ {y} IN c`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `r:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  ABBREV_TAC `V = {v:real^N | v extreme_point_of r}` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(V:real^N->bool) HAS_SIZE 2` MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN
    CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
    MP_TAC(ISPEC `V:real^N->bool` AFF_DIM_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `aff_dim(V:real^N->bool) = &1` SUBST1_TAC THENL
     [ASM_MESON_TAC[AFF_DIM_CONVEX_HULL]; ALL_TAC] THEN
    REWRITE_TAC[INT_ARITH `&1:int = x - &1 <=> x = &2`; INT_OF_NUM_EQ];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN
  CONJ_TAC THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  CONJ_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) extreme_point_of r /\ y extreme_point_of r`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{v:real^N | v extreme_point_of r} = V` THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THEN MATCH_MP_TAC(CONJUNCT1(CONJUNCT2
    (REWRITE_RULE[moi_bar_complex] (ASSUME
      `moi_bar_complex (c:(real^N->bool)->bool)`)))) THEN
  EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING]);;

let MOI_FRN_TRI_VERTS = prove
 (`!(c:(real^N->bool)->bool) r v.
     moi_bar_complex c /\ r IN c /\ aff_dim r = &2 /\ {v} IN c /\ v IN r
     ==> ?x y. ~affine_dependent {v,x,y} /\ ~(x = v) /\ ~(y = v) /\
               ~(x = y) /\ r = convex hull {v,x,y}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `r:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  ABBREV_TAC `V = {u:real^N | u extreme_point_of r}` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN V` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM; GSYM FACE_OF_SING] THEN
    SUBGOAL_THEN `{v:real^N} = {v} INTER r` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[moi_bar_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN `(V DELETE (v:real^N)) HAS_SIZE 2` MP_TAC THENL
   [SUBGOAL_THEN `FINITE (V:real^N->bool) /\ CARD V = 3` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
      MP_TAC(ISPEC `V:real^N->bool` AFF_DIM_AFFINE_INDEPENDENT) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `aff_dim(V:real^N->bool) = &2` SUBST1_TAC THENL
       [ASM_MESON_TAC[AFF_DIM_CONVEX_HULL]; ALL_TAC] THEN
      REWRITE_TAC[INT_ARITH `&2:int = x - &1 <=> x = &3`; INT_OF_NUM_EQ];
      ALL_TAC] THEN
    ASM_SIMP_TAC[HAS_SIZE; FINITE_DELETE; CARD_DELETE] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `V = {v:real^N,x,y}` ASSUME_TAC THENL
   [UNDISCH_TAC `V DELETE (v:real^N) = {x,y}` THEN
    UNDISCH_TAC `(v:real^N) IN V` THEN SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`x:real^N`; `y:real^N`] THEN
  SUBGOAL_THEN `~(x:real^N = v) /\ ~(y = v)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `V DELETE (v:real^N) = {x,y}` THEN SET_TAC[]; ALL_TAC] THEN
  ASM_MESON_TAC[]);;

let MOI_FRN_TRI_EDGE_IN = prove
 (`!(c:(real^N->bool)->bool) v x y.
     moi_bar_complex c /\ convex hull {v,x,y} IN c /\
     ~affine_dependent {v,x,y} /\ ~(x = v) /\ ~(y = v) /\ ~(x = y)
     ==> convex hull {v,x} IN c /\ aff_dim(convex hull {v,x}) = &1 /\
         convex hull {v,x} SUBSET convex hull {v,x,y} /\
         v IN convex hull {v,x}`,
  REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC(CONJUNCT1(CONJUNCT2
      (REWRITE_RULE[moi_bar_complex] (ASSUME
        `moi_bar_complex (c:(real^N->bool)->bool)`)))) THEN
    EXISTS_TAC `convex hull {v:real^N,x,y}` THEN ASM_REWRITE_TAC[] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{v:real^N,x}` THEN REWRITE_TAC[] THEN SET_TAC[];
    REWRITE_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_2] THEN ASM_MESON_TAC[];
    MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]]);;

let MOI_FRN_CHAIN2_EXT = prove
 (`!(c:(real^N->bool)->bool) r1 r2.
     FINITE c /\ combinatorial_manifold 2 c /\ moi_bar_complex c /\
     moi_bar_chain c {r1,r2} /\ r1 SUBSET r2 /\ ~(r1 = r2)
     ==> ?p1 p2. ~(p1 = p2) /\
                 !p. p IN c /\ ~(p IN {r1,r2}) /\
                     moi_bar_chain c (p INSERT {r1,r2}) <=> p = p1 \/ p = p2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r1:real^N->bool) IN c /\ r2 IN c /\ ~(r1 = {}) /\ ~(r2 = {})`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT; IN_INSERT]; ALL_TAC] THEN
  SUBGOAL_THEN `aff_dim(r1:real^N->bool) < aff_dim(r2:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_CHAIN_DIM_LT THEN
    MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`;
                          `{r1,r2}:(real^N->bool)->bool`] THEN
    ASM_REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN `&0 <= aff_dim(r1:real^N->bool) /\ aff_dim(r2:real^N->bool) <= &2`
  STRIP_ASSUME_TAC THENL
   [ASM_SIMP_TAC[AFF_DIM_POS_LE] THEN MATCH_MP_TAC MOI_FRN_SA_CM_DIM THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^N->bool.
      p IN c /\ ~(p IN {r1,r2}) /\ moi_bar_chain c (p INSERT {r1,r2}) <=>
      p IN c /\ ~(p = {}) /\ ~(aff_dim p = aff_dim r1) /\
      ~(aff_dim p = aff_dim r2) /\
      (p SUBSET r1 \/ r1 SUBSET p) /\ (p SUBSET r2 \/ r2 SUBSET p)`
  (fun th -> REWRITE_TAC[th]) THENL
   [X_GEN_TAC `p:real^N->bool` THEN
    SUBGOAL_THEN
     `moi_bar_chain c ((p:real^N->bool) INSERT {r1,r2})
      ==> ((p = r1 <=> aff_dim p = aff_dim(r1:real^N->bool)) /\
           (p = r2 <=> aff_dim p = aff_dim(r2:real^N->bool)))` MP_TAC THENL
     [DISCH_TAC THEN CONJ_TAC THEN EQ_TAC THEN SIMP_TAC[] THEN DISCH_TAC THEN
      MATCH_MP_TAC MOI_FRN_CHAIN_DIM_INJ THEN
      MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`;
                            `(p:real^N->bool) INSERT {r1,r2}`] THEN
      ASM_REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r1:real^N->bool`;
                   `r2:real^N->bool`; `p:real^N->bool`] MOI_FRN_CHAIN_INSERT2) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p:real^N->bool. p IN c /\ ~(p = {}) ==> &0 <= aff_dim p /\ aff_dim p <= &2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[AFF_DIM_POS_LE] THEN
    MATCH_MP_TAC MOI_FRN_SA_CM_DIM THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(aff_dim(r1:real^N->bool) = &0 /\ aff_dim(r2:real^N->bool) = &1)
                \/ (aff_dim r1 = &0 /\ aff_dim r2 = &2) \/
                (aff_dim r1 = &1 /\ aff_dim r2 = &2)` MP_TAC THENL
   [MAP_EVERY UNDISCH_TAC
     [`aff_dim(r1:real^N->bool) < aff_dim(r2:real^N->bool)`;
      `&0 <= aff_dim(r1:real^N->bool)`; `aff_dim(r2:real^N->bool) <= &2`] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r2:real^N->bool`]
      MOI_FRN_SA_CM_EDGE2) THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    SUBGOAL_THEN `{q:real^N->bool | q IN c /\ aff_dim q = &2 /\ r2 SUBSET q}
                  HAS_SIZE 2` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE] THEN MATCH_MP_TAC FINITE_RESTRICT THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p1:real^N->bool` THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `p2:real^N->bool` THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o
      GEN_REWRITE_RULE I [EXTENSION])) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    DISCH_THEN(fun th -> ASM_REWRITE_TAC[GSYM th]) THEN
    X_GEN_TAC `p:real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
      SUBGOAL_THEN `aff_dim(p:real^N->bool) = &2` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `p:real^N->bool` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `&2:int`)) (concl th)))
        THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
        ALL_TAC] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
        can (find_term ((=) `r2:real^N->bool`)) (concl th))) THEN
      ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`p:real^N->bool`; `r2:real^N->bool`] AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONV_TAC INT_REDUCE_CONV THEN REPEAT CONJ_TAC THENL
       [DISCH_TAC THEN UNDISCH_TAC `aff_dim(p:real^N->bool) = &2` THEN
        ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
        DISJ2_TAC THEN ASM SET_TAC[]]];
    MP_TAC(ISPEC `r1:real^N->bool` AFF_DIM_EQ_0) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r2:real^N->bool`; `v:real^N`]
      MOI_FRN_TRI_VERTS) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N`
      STRIP_ASSUME_TAC)) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `x:real^N`;
                   `y:real^N`] MOI_FRN_TRI_EDGE_IN) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`; `y:real^N`;
                   `x:real^N`] MOI_FRN_TRI_EDGE_IN) THEN
    SUBGOAL_THEN `{v:real^N,y,x} = {v,x,y}` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    UNDISCH_TAC `(r2:real^N->bool) = convex hull {v,x,y}` THEN
    DISCH_THEN(fun th -> SUBST_ALL_TAC th THEN ASSUME_TAC th) THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT(ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    STRIP_TAC THEN
    REPEAT(ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC]) THEN
    STRIP_TAC THEN
    MAP_EVERY EXISTS_TAC [`convex hull {v:real^N,x}`; `convex hull {v:real^N,y}`]
    THEN CONJ_TAC THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(y:real^N) extreme_point_of convex hull {v,x}` MP_TAC THENL
       [UNDISCH_TAC `convex hull {v:real^N,x} = convex hull {v,y}` THEN
        DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[EXTREME_POINT_OF_CONVEX_HULL_2];
        REWRITE_TAC[EXTREME_POINT_OF_CONVEX_HULL_2] THEN ASM_MESON_TAC[]];
      ALL_TAC] THEN
    X_GEN_TAC `p:real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC))))) THEN
      SUBGOAL_THEN `aff_dim(p:real^N->bool) = &1` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `p:real^N->bool` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `&2:int`)) (concl th)))
        THEN ASM_REWRITE_TAC[AFF_DIM_SING] THEN ASM_INT_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(v:real^N) IN p /\ p SUBSET convex hull {v,x,y}`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
            can (find_term ((=) `{v:real^N}`)) (concl th))) THENL
           [MP_TAC(ISPECL [`p:real^N->bool`; `{v:real^N}`] AFF_DIM_SUBSET) THEN
            ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
            ASM SET_TAC[]];
          FIRST_X_ASSUM(DISJ_CASES_TAC o check (fun th -> is_disj(concl th) &&
            can (find_term ((=) `convex hull {v:real^N,x,y}`)) (concl th)))
          THEN ASM_REWRITE_TAC[] THEN
          MP_TAC(ISPECL [`convex hull {v:real^N,x,y}`; `p:real^N->bool`]
            AFF_DIM_SUBSET) THEN
          ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
        ALL_TAC] THEN
      MATCH_MP_TAC MOI_SCF_EDGE_AT_VERTEX THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EQ_EMPTY; NOT_INSERT_EMPTY; AFF_DIM_SING] THEN
      CONV_TAC INT_REDUCE_CONV THEN
      ASM_REWRITE_TAC[SING_SUBSET]];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r1:real^N->bool`]
      MOI_FRN_SEG_VERTS) THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM SUBST_ALL_TAC THEN
    MAP_EVERY EXISTS_TAC [`{x:real^N}`; `{y:real^N}`] THEN
    CONJ_TAC THENL
     [REWRITE_TAC[SET_RULE `{a:A} = {b} <=> a = b`] THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    X_GEN_TAC `p:real^N->bool` THEN EQ_TAC THENL
     [DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
       (CONJUNCTS_THEN2 (LABEL_TAC "D1") ASSUME_TAC))))) THEN
      SUBGOAL_THEN `aff_dim(p:real^N->bool) = &0` ASSUME_TAC THENL
       [FIRST_X_ASSUM(MP_TAC o SPEC `p:real^N->bool` o check (fun th ->
          is_forall(concl th) && can (find_term ((=) `&2:int`)) (concl th)))
        THEN ASM_REWRITE_TAC[] THEN ASM_INT_ARITH_TAC;
        ALL_TAC] THEN
      MP_TAC(ISPEC `p:real^N->bool` AFF_DIM_EQ_0) THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `z:real^N` SUBST_ALL_TAC) THEN
      SUBGOAL_THEN `{z:real^N} SUBSET convex hull {x,y}` ASSUME_TAC THENL
       [REMOVE_THEN "D1" DISJ_CASES_TAC THEN ASM_REWRITE_TAC[] THEN
        MP_TAC(ISPECL [`convex hull {x:real^N,y}`; `{z:real^N}`]
          AFF_DIM_SUBSET) THEN
        ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
        ALL_TAC] THEN
      SUBGOAL_THEN `(z:real^N) extreme_point_of convex hull {x,y}` MP_TAC THENL
       [REWRITE_TAC[GSYM FACE_OF_SING] THEN
        MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
        EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[EXTREME_POINT_OF_CONVEX_HULL_2] THEN MESON_TAC[]];
      SUBGOAL_THEN `{x:real^N} SUBSET convex hull {x,y} /\
                    {y:real^N} SUBSET convex hull {x,y}`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[SING_SUBSET] THEN CONJ_TAC THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
        ALL_TAC] THEN
      DISCH_THEN(DISJ_CASES_THEN SUBST1_TAC) THEN
      ASM_REWRITE_TAC[NOT_INSERT_EMPTY; AFF_DIM_SING] THEN
      CONV_TAC INT_REDUCE_CONV THEN ASM SET_TAC[]]]);;

let MOI_FRN_BARY_EDGE2 = prove
 (`!(c:(real^N->bool)->bool) e.
     FINITE c /\ combinatorial_manifold 2 c /\ moi_bar_complex c /\
     e IN barycentric_subdivision c /\ aff_dim e = &1
     ==> ?D1 D2. ~(D1 = D2) /\
                 D1 IN barycentric_subdivision c /\ aff_dim D1 = &2 /\
                 e SUBSET D1 /\
                 D2 IN barycentric_subdivision c /\ aff_dim D2 = &2 /\
                 e SUBSET D2 /\
                 !D. D IN barycentric_subdivision c /\ aff_dim D = &2 /\
                     e SUBSET D ==> D = D1 \/ D = D2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `!q:real^N->bool. q IN c ==> aff_dim q <= &2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_SA_CM_DIM THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(e:real^N->bool) IN barycentric_subdivision c` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `CARD(f:(real^N->bool)->bool) = 2` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
      MOI_FRN_BARY_AFF_DIM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INT_ARITH `&1:int = x - &1 <=> x = &2`; INT_OF_NUM_EQ] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?r1 r2:real^N->bool. f = {r1,r2} /\ r1 SUBSET r2 /\ ~(r1 = r2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:(real^N->bool)->bool) HAS_SIZE 2` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE] THEN ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
    REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a:real^N->bool) SUBSET b \/ b SUBSET a` MP_TAC THENL
     [UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[moi_bar_chain] THEN
      DISCH_THEN(MP_TAC o SPECL [`a:real^N->bool`; `b:real^N->bool`] o
        last o CONJUNCTS) THEN REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`a:real^N->bool`; `b:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`b:real^N->bool`; `a:real^N->bool`]] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r1:real^N->bool`;
                 `r2:real^N->bool`] MOI_FRN_CHAIN2_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^N->bool` (X_CHOOSE_THEN `p2:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "EXT")))) THEN
  SUBGOAL_THEN
   `!p:real^N->bool. p = p1 \/ p = p2
       ==> moi_bar_chain c (p INSERT {r1,r2}) /\ CARD (p INSERT {r1,r2}) = 3`
  (LABEL_TAC "CH") THENL
   [X_GEN_TAC `p:real^N->bool` THEN
    USE_THEN "EXT" (fun th -> REWRITE_TAC[GSYM th]) THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY] THEN
    ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    UNDISCH_TAC `~((p:real^N->bool) IN {r1,r2})` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN STRIP_TAC THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull (IMAGE simplex_barycentre ((p1:real^N->bool) INSERT {r1,r2}))`;
    `convex hull (IMAGE simplex_barycentre ((p2:real^N->bool) INSERT {r1,r2}))`]
  THEN
  USE_THEN "CH" (MP_TAC o SPEC `p1:real^N->bool`) THEN
  USE_THEN "CH" (MP_TAC o SPEC `p2:real^N->bool`) THEN
  REWRITE_TAC[] THEN STRIP_TAC THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                   `(p1:real^N->bool) INSERT {r1,r2}`;
                   `(p2:real^N->bool) INSERT {r1,r2}`] MOI_FRN_CHAIN_HULL_INJ) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(MP_TAC o AP_TERM
      `\u:(real^N->bool)->bool. (p1:real^N->bool) IN u`) THEN
    USE_THEN "EXT" (MP_TAC o SPEC `p1:real^N->bool`) THEN
    UNDISCH_TAC `~((p1:real^N->bool) = p2)` THEN
    BETA_TAC THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
    CONV_TAC TAUT;
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `(p1:real^N->bool) INSERT {r1,r2}` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                   `(p1:real^N->bool) INSERT {r1,r2}`] MOI_FRN_BARY_AFF_DIM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `(p2:real^N->bool) INSERT {r1,r2}` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`;
                   `(p2:real^N->bool) INSERT {r1,r2}`] MOI_FRN_BARY_AFF_DIM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC;
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN SET_TAC[];
    ALL_TAC] THEN
  X_GEN_TAC `D:real^N->bool` THEN
  DISCH_THEN(CONJUNCTS_THEN2 MP_TAC STRIP_ASSUME_TAC) THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `CARD(g:(real^N->bool)->bool) = 3` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
      MOI_FRN_BARY_AFF_DIM) THEN ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `aff_dim(D:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
    DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INT_ARITH `&2:int = x - &1 <=> x = &3`; INT_OF_NUM_EQ] THEN
    SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{r1,r2} SUBSET (g:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{r1:real^N->bool,r2}`;
                   `g:(real^N->bool)->bool`] MOI_FRN_CHAIN_HULL_SUBSET) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(SUBST1_TAC o SYM) THEN
    UNDISCH_TAC
     `convex hull (IMAGE simplex_barycentre {r1:real^N->bool,r2}) SUBSET D` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?p:real^N->bool. p IN g /\ ~(p IN {r1,r2})`
  STRIP_ASSUME_TAC THENL
   [MATCH_MP_TAC(SET_RULE
     `~((g:(real^N->bool)->bool) SUBSET s) ==> ?p. p IN g /\ ~(p IN s)`) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `CARD(g:(real^N->bool)->bool) <= CARD {r1:real^N->bool,r2}`
    MP_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY] THEN
    ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~((p:real^N->bool) = r1) /\ ~(p = r2)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `~((p:real^N->bool) IN {r1,r2})` THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `g = (p:real^N->bool) INSERT {r1,r2}` SUBST_ALL_TAC THENL
   [CONV_TAC SYM_CONV THEN MATCH_MP_TAC CARD_SUBSET_EQ THEN
    CONJ_TAC THENL
     [UNDISCH_TAC `moi_bar_chain c (g:(real^N->bool)->bool)` THEN
      SIMP_TAC[moi_bar_chain];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC(SET_RULE
       `(p:real^N->bool) IN g /\ s SUBSET g ==> (p INSERT s) SUBSET g`) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
                 NOT_IN_EMPTY] THEN
    CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N->bool) = p1 \/ p = p2` MP_TAC THENL
   [USE_THEN "EXT" (fun th -> REWRITE_TAC[GSYM th]) THEN
    REPEAT CONJ_TAC THEN TRY(FIRST_ASSUM ACCEPT_TAC) THEN
    UNDISCH_TAC `moi_bar_chain c ((p:real^N->bool) INSERT {r1,r2})` THEN
    REWRITE_TAC[moi_bar_chain; INSERT_SUBSET] THEN MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;


(* ========================================================================= *)
(* Dual connectivity and purity of a connected                             *)
(* finite combinatorial 2-manifold s and of its first derived k (walks     *)
(* among flags), and the core of SURFACE_NBHD_SIDES: every nonempty        *)
(* R-closed set of simplices of the first derived of t meeting UNIONS s    *)
(* contains a tetrahedron over every triangle of k.                        *)
(* ========================================================================= *)

(* Two triangles of a complex sharing two distinct points are equal or    *)
(* meet in an edge.                                                        *)

let MOI_FRN_TRI_SHARE2 = prove
 (`!(c:(real^N->bool)->bool) t t' u w.
     moi_bar_complex c /\ t IN c /\ t' IN c /\ aff_dim t = &2 /\
     aff_dim t' = &2 /\ u IN t /\ u IN t' /\ w IN t /\ w IN t' /\ ~(u = w)
     ==> t = t' \/ aff_dim (t INTER t') = &1`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(t INTER t':real^N->bool) face_of t /\ (t INTER t') face_of t'`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  SUBGOAL_THEN `convex(t:real^N->bool) /\ convex(t':real^N->bool)`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 <= aff_dim(t INTER t':real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim{u:real^N,w}` THEN
    CONJ_TAC THENL [ASM_REWRITE_TAC[AFF_DIM_2; INT_LE_REFL]; ALL_TAC] THEN
    MATCH_MP_TAC AFF_DIM_SUBSET THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_CASES_TAC `aff_dim(t INTER t':real^N->bool) = &1` THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `t INTER t':real^N->bool = t /\ t INTER t' = t'` MP_TAC THENL
   [ALL_TAC; SET_TAC[]] THEN
  CONJ_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THENL
   [MP_TAC(ISPECL [`t INTER t':real^N->bool`; `t:real^N->bool`]
      FACE_OF_AFF_DIM_LT);
    MP_TAC(ISPECL [`t INTER t':real^N->bool`; `t':real^N->bool`]
      FACE_OF_AFF_DIM_LT)] THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `&1 <= aff_dim(t INTER t':real^N->bool)` THEN
  UNDISCH_TAC `~(aff_dim(t INTER t':real^N->bool) = &1)` THEN
  INT_ARITH_TAC);;

(* Purity of finite combinatorial 2-manifolds: every nonempty simplex lies *)
(* in a triangle.                                                          *)

let MOI_FRN_CM_PURE = prove
 (`!(c:(real^N->bool)->bool) q.
     FINITE c /\ combinatorial_manifold 2 c /\ q IN c /\ ~(q = {})
     ==> ?t. t IN c /\ aff_dim t = &2 /\ q SUBSET t`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `aff_dim(q:real^N->bool) = &0 \/ aff_dim q = &1 \/ aff_dim q = &2`
  MP_TAC THENL
   [MP_TAC(ISPEC `q:real^N->bool` AFF_DIM_GE) THEN
    MP_TAC(ISPEC `q:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:real^N->bool`]
      MOI_FRN_SA_CM_DIM) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [UNDISCH_TAC `aff_dim(q:real^N->bool) = &0` THEN
    REWRITE_TAC[AFF_DIM_EQ_0] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`]
      MOI_FRN_SA_CM_VTRI) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN
    SIMP_TAC[SING_SUBSET];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:real^N->bool`]
      MOI_FRN_SA_CM_EDGE2) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC
     `{t:real^N->bool | t IN c /\ aff_dim t = &2 /\ q SUBSET t} = {}` THENL
     [ASM_REWRITE_TAC[CARD_CLAUSES] THEN ARITH_TAC;
      POP_ASSUM MP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      MESON_TAC[]];
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

(* Dual connectivity of a connected finite combinatorial 2-manifold: a     *)
(* nonempty set of triangles closed under crossing edges is all of them.   *)

let MOI_FRN_CM_DCONN = prove
 (`!(c:(real^N->bool)->bool) Z.
     FINITE c /\ combinatorial_manifold 2 c /\ connected (UNIONS c) /\
     Z SUBSET {t | t IN c /\ aff_dim t = &2} /\ ~(Z = {}) /\
     (!t t'. t IN Z /\ t' IN c /\ aff_dim t' = &2 /\ aff_dim(t INTER t') = &1
             ==> t' IN Z)
     ==> Z = {t | t IN c /\ aff_dim t = &2}`,
  REPEAT STRIP_TAC THEN POP_ASSUM(LABEL_TAC "ZC") THEN
  SUBGOAL_THEN `simplicial_complex (c:(real^N->bool)->bool) /\ moi_bar_complex c`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[MOI_SIMPLICIAL_COMPLEX_LF] THEN
    ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_FRN_TOUCH_CLOSED THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC FINITE_RESTRICT THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THENL
     [ASM_MESON_TAC[MOI_SCF_SC_CLOSED];
      UNDISCH_TAC `aff_dim(t:real^N->bool) = &2` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC];
    SUBGOAL_THEN `UNIONS {t:real^N->bool | t IN c /\ aff_dim t = &2} =
                  UNIONS c` (fun th -> ASM_REWRITE_TAC[th]) THEN
    MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_UNIONS; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:real^N->bool`]
      MOI_FRN_CM_PURE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `t:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `t:real^N->bool` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `t':real^N->bool`] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(t:real^N->bool) IN c /\ aff_dim t = &2` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(t INTER t':real^N->bool) IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t INTER t':real^N->bool`]
    MOI_SCF_SC_VERTEX) THEN ASM_REWRITE_TAC[IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `w:real^N`;
                 `{u:real^N->bool | u IN Z /\ w IN u}`] MOI_FRN_SA_CM_LCONN) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN
      MAP_EVERY X_GEN_TAC [`a:real^N->bool`; `a':real^N->bool`; `u:real^N`] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(a:real^N->bool) IN c /\ aff_dim a = &2`
      STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `a:real^N->bool`;
                     `a':real^N->bool`; `u:real^N`; `w:real^N`]
        MOI_FRN_TRI_SHARE2) THEN
      ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
       [UNDISCH_TAC `(a:real^N->bool) IN Z` THEN ASM_REWRITE_TAC[];
        USE_THEN "ZC" MATCH_MP_TAC THEN EXISTS_TAC `a:real^N->bool` THEN
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPEC `t':real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  SIMP_TAC[]);;

(* Flags (vertex, edge, triangle) of a complex as chains.                  *)

let MOI_FRN_FLAG_CHAIN = prove
 (`!(s:(real^N->bool)->bool) v e D.
     moi_bar_complex s /\ {v} IN s /\ e IN s /\ aff_dim e = &1 /\
     D IN s /\ aff_dim D = &2 /\ v IN e /\ e SUBSET D
     ==> moi_bar_chain s {{v},e,D} /\ CARD {{v},e,D} = 3 /\
         moi_bar_chain s {{v},D} /\ CARD {{v},D} = 2 /\
         moi_bar_chain s {e,D} /\ CARD {e,D} = 2 /\
         moi_bar_chain s {{v},e} /\ CARD {{v},e} = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `~({v:real^N} = e) /\ ~(e = D) /\ ~({v:real^N} = D) /\
                ~(e:real^N->bool = {}) /\ ~(D:real^N->bool = {})`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
    ASM_REWRITE_TAC[AFF_DIM_SING; AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN D` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_chain s {{v:real^N},e,D}` ASSUME_TAC THENL
   [REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT;
                FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY; NOT_EMPTY_INSERT;
                NOT_INSERT_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
    ASM_REWRITE_TAC[SUBSET_REFL; SING_SUBSET];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THEN
  TRY(MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
      EXISTS_TAC `{{v:real^N},e,D}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]) THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
           NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

(* One step of the flag walk: crossing a common edge of the subdivision.   *)

let MOI_FRN_FLAG_STEP = prove
 (`!(s:(real^N->bool)->bool) Z f1 f2 g.
     moi_bar_complex s /\
     (!D1 D2 e. D1 IN Z /\ D2 IN barycentric_subdivision s /\
                aff_dim D2 = &2 /\ e IN barycentric_subdivision s /\
                aff_dim e = &1 /\ e SUBSET D1 /\ e SUBSET D2 ==> D2 IN Z) /\
     moi_bar_chain s f2 /\ CARD f2 = 3 /\ moi_bar_chain s g /\ CARD g = 2 /\
     g SUBSET f1 /\ g SUBSET f2 /\
     convex hull (IMAGE simplex_barycentre f1) IN Z
     ==> convex hull (IMAGE simplex_barycentre f2) IN Z`,
  REPEAT STRIP_TAC THEN
  FIRST_X_ASSUM(MATCH_MP_TAC o check (is_forall o concl)) THEN
  MAP_EVERY EXISTS_TAC
   [`convex hull (IMAGE simplex_barycentre (f1:(real^N->bool)->bool))`;
    `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))`] THEN
  REPEAT CONJ_TAC THENL
   [ASM_REWRITE_TAC[];
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `f2:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `f2:(real^N->bool)->bool`]
      MOI_FRN_BARY_AFF_DIM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC;
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
      MOI_FRN_BARY_AFF_DIM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC;
    MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
    ASM_REWRITE_TAC[]]);;

(* Two edges of a triangle of a finite complex share a vertex.            *)

let MOI_FRN_TRI_EDGES_MEET = prove
 (`!(s:(real^N->bool)->bool) D e e'.
     simplicial_complex s /\ moi_bar_complex s /\ D IN s /\ aff_dim D = &2 /\
     e IN s /\ aff_dim e = &1 /\ e SUBSET D /\
     e' IN s /\ aff_dim e' = &1 /\ e' SUBSET D
     ==> ?w. {w} IN s /\ w IN e /\ w IN e'`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `e:real^N->bool`]
    MOI_FRN_SA_EDGE_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `e':real^N->bool`]
    MOI_FRN_SA_EDGE_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p':real^N` (X_CHOOSE_THEN `q':real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(p:real^N) IN e /\ (q:real^N) IN e /\ (p':real^N) IN e' /\
                (q':real^N) IN e'` STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[ENDS_IN_SEGMENT]; ALL_TAC] THEN
  SUBGOAL_THEN `!u:real^N. {u} IN s /\ u IN D ==> u extreme_point_of D`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
    SUBGOAL_THEN `{u:real^N} = {u} INTER D` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_MESON_TAC[moi_bar_complex];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `D:real^N->bool`; `p:real^N`]
    MOI_FRN_TRI_VERTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `!u:real^N. {u} IN s /\ u IN D ==> u = p \/ u = x \/ u = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `u:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPEC `{p:real^N,x,y}`
      EXTREME_POINTS_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
    ASM_REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `u:real^N`) THEN
    SUBGOAL_THEN `(u:real^N) extreme_point_of convex hull {p,x,y}`
     (fun th -> REWRITE_TAC[th]) THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(p:real^N) = p' \/ p = q' \/ q = p' \/ q = q'` MP_TAC THENL
   [SUBGOAL_THEN `((q:real^N) = p \/ q = x \/ q = y) /\
                  ((p':real^N) = p \/ p' = x \/ p' = y) /\
                  ((q':real^N) = p \/ q' = x \/ q' = y)` MP_TAC THENL
     [REPEAT CONJ_TAC THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~(p:real^N = q)` THEN UNDISCH_TAC `~(p':real^N = q')` THEN
    MESON_TAC[];
    ALL_TAC] THEN
  STRIP_TAC THENL
   [EXISTS_TAC `p:real^N`; EXISTS_TAC `p:real^N`;
    EXISTS_TAC `q:real^N`; EXISTS_TAC `q:real^N`] THEN
  ASM_REWRITE_TAC[ENDS_IN_SEGMENT]);;

(* Walking among the six flags of one triangle.                            *)

let MOI_FRN_FLAG_ROT_E = prove
 (`!(s:(real^N->bool)->bool) Z D v e e'.
     moi_bar_complex s /\
     (!D1 D2 e. D1 IN Z /\ D2 IN barycentric_subdivision s /\
                aff_dim D2 = &2 /\ e IN barycentric_subdivision s /\
                aff_dim e = &1 /\ e SUBSET D1 /\ e SUBSET D2 ==> D2 IN Z) /\
     D IN s /\ aff_dim D = &2 /\ {v} IN s /\
     e IN s /\ aff_dim e = &1 /\ v IN e /\ e SUBSET D /\
     e' IN s /\ aff_dim e' = &1 /\ v IN e' /\ e' SUBSET D /\
     convex hull (IMAGE simplex_barycentre {{v},e,D}) IN Z
     ==> convex hull (IMAGE simplex_barycentre {{v},e',D}) IN Z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`;
                 `D:real^N->bool`] MOI_FRN_FLAG_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `v:real^N`; `e':real^N->bool`;
                 `D:real^N->bool`] MOI_FRN_FLAG_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FRN_FLAG_STEP THEN
  MAP_EVERY EXISTS_TAC [`s:(real^N->bool)->bool`; `{{v:real^N},e,D}`;
                        `{{v:real^N},D}`] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_FRN_FLAG_ROT_V = prove
 (`!(s:(real^N->bool)->bool) Z D v v' e.
     moi_bar_complex s /\
     (!D1 D2 e. D1 IN Z /\ D2 IN barycentric_subdivision s /\
                aff_dim D2 = &2 /\ e IN barycentric_subdivision s /\
                aff_dim e = &1 /\ e SUBSET D1 /\ e SUBSET D2 ==> D2 IN Z) /\
     D IN s /\ aff_dim D = &2 /\ {v} IN s /\ {v'} IN s /\
     e IN s /\ aff_dim e = &1 /\ v IN e /\ v' IN e /\ e SUBSET D /\
     convex hull (IMAGE simplex_barycentre {{v},e,D}) IN Z
     ==> convex hull (IMAGE simplex_barycentre {{v'},e,D}) IN Z`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `v:real^N`; `e:real^N->bool`;
                 `D:real^N->bool`] MOI_FRN_FLAG_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `v':real^N`; `e:real^N->bool`;
                 `D:real^N->bool`] MOI_FRN_FLAG_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC MOI_FRN_FLAG_STEP THEN
  MAP_EVERY EXISTS_TAC [`s:(real^N->bool)->bool`; `{{v:real^N},e,D}`;
                        `{e:real^N->bool,D}`] THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_FRN_FLAG_ALL = prove
 (`!(s:(real^N->bool)->bool) Z D v e v' e'.
     FINITE s /\ lf_simplicial_complex s /\
     (!D1 D2 e. D1 IN Z /\ D2 IN barycentric_subdivision s /\
                aff_dim D2 = &2 /\ e IN barycentric_subdivision s /\
                aff_dim e = &1 /\ e SUBSET D1 /\ e SUBSET D2 ==> D2 IN Z) /\
     D IN s /\ aff_dim D = &2 /\
     {v} IN s /\ e IN s /\ aff_dim e = &1 /\ v IN e /\ e SUBSET D /\
     {v'} IN s /\ e' IN s /\ aff_dim e' = &1 /\ v' IN e' /\ e' SUBSET D /\
     convex hull (IMAGE simplex_barycentre {{v},e,D}) IN Z
     ==> convex hull (IMAGE simplex_barycentre {{v'},e',D}) IN Z`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplicial_complex (s:(real^N->bool)->bool) /\
                moi_bar_complex s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF; MOI_FRN_LF_BAR_COMPLEX];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `D:real^N->bool`; `e:real^N->bool`;
                 `e':real^N->bool`] MOI_FRN_TRI_EDGES_MEET) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `w:real^N` STRIP_ASSUME_TAC) THEN
  MATCH_MP_TAC MOI_FRN_FLAG_ROT_V THEN
  MAP_EVERY EXISTS_TAC [`s:(real^N->bool)->bool`; `w:real^N`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FRN_FLAG_ROT_E THEN
  MAP_EVERY EXISTS_TAC [`s:(real^N->bool)->bool`; `e:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MOI_FRN_FLAG_ROT_V THEN
  MAP_EVERY EXISTS_TAC [`s:(real^N->bool)->bool`; `v:real^N`] THEN
  ASM_REWRITE_TAC[]);;

(* Every triangle of the first derived of a finite combinatorial          *)
(* 2-manifold is the hull of the barycentres of a flag.                   *)

let MOI_FRN_BARY_TRI_FLAG = prove
 (`!(s:(real^N->bool)->bool) K.
     FINITE s /\ combinatorial_manifold 2 s /\
     K IN barycentric_subdivision s /\ aff_dim K = &2
     ==> ?v e D. {v} IN s /\ e IN s /\ aff_dim e = &1 /\ D IN s /\
                 aff_dim D = &2 /\ v IN e /\ e SUBSET D /\
                 K = convex hull (IMAGE simplex_barycentre {{v},e,D})`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (s:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX];
    ALL_TAC] THEN
  UNDISCH_TAC `(K:real^N->bool) IN barycentric_subdivision s` THEN
  REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_FRN_CHAIN3_FLAG) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_SA_CM_DIM THEN
      EXISTS_TAC `s:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
        MOI_FRN_BARY_AFF_DIM) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `aff_dim(K:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
      DISCH_THEN SUBST1_TAC THEN
      REWRITE_TAC[INT_ARITH `&2:int = x - &1 <=> x = &3`; INT_OF_NUM_EQ] THEN
      SIMP_TAC[]];
    ALL_TAC] THEN
  REPEAT(MATCH_MP_TAC MONO_EXISTS THEN GEN_TAC) THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

(* Dual connectivity of the first derived k of a connected finite         *)
(* combinatorial 2-manifold: a nonempty set of triangles of k closed      *)
(* under crossing edges of k contains every triangle of k.                *)

let MOI_FRN_KDCONN = prove
 (`!(s:(real^N->bool)->bool) Z.
     FINITE s /\ combinatorial_manifold 2 s /\ connected (UNIONS s) /\
     Z SUBSET {D | D IN barycentric_subdivision s /\ aff_dim D = &2} /\
     ~(Z = {}) /\
     (!D1 D2 e. D1 IN Z /\ D2 IN barycentric_subdivision s /\
                aff_dim D2 = &2 /\ e IN barycentric_subdivision s /\
                aff_dim e = &1 /\ e SUBSET D1 /\ e SUBSET D2 ==> D2 IN Z)
     ==> Z = {D | D IN barycentric_subdivision s /\ aff_dim D = &2}`,
  REPEAT STRIP_TAC THEN POP_ASSUM(LABEL_TAC "ZC") THEN
  SUBGOAL_THEN `lf_simplicial_complex (s:(real^N->bool)->bool) /\
                moi_bar_complex s /\ simplicial_complex s`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX;
                  MOI_SIMPLICIAL_COMPLEX_LF];
    ALL_TAC] THEN
  ABBREV_TAC
   `Ys = {D:real^N->bool | D IN s /\ aff_dim D = &2 /\
          !v e. {v} IN s /\ e IN s /\ aff_dim e = &1 /\ v IN e /\
                e SUBSET D
                ==> convex hull (IMAGE simplex_barycentre {{v},e,D}) IN Z}` THEN
  SUBGOAL_THEN `Ys = {D:real^N->bool | D IN s /\ aff_dim D = &2}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_CM_DCONN THEN ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [EXPAND_TAC "Ys" THEN SET_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      UNDISCH_TAC `~(Z:(real^N->bool)->bool = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      DISCH_THEN(X_CHOOSE_TAC `K:real^N->bool`) THEN
      SUBGOAL_THEN `(K:real^N->bool) IN barycentric_subdivision s /\
                    aff_dim K = &2` STRIP_ASSUME_TAC THENL
       [ASM SET_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `K:real^N->bool`]
        MOI_FRN_BARY_TRI_FLAG) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `e:real^N->bool`
        (X_CHOOSE_THEN `D:real^N->bool` STRIP_ASSUME_TAC))) THEN
      SUBGOAL_THEN
       `convex hull (IMAGE simplex_barycentre {{v:real^N},e,D}) IN Z`
      ASSUME_TAC THENL
       [UNDISCH_TAC `(K:real^N->bool) IN Z` THEN ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `D:real^N->bool` THEN EXPAND_TAC "Ys" THEN
      REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MAP_EVERY X_GEN_TAC [`v':real^N`; `e':real^N->bool`] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_FRN_FLAG_ALL THEN
      MAP_EVERY EXISTS_TAC [`s:(real^N->bool)->bool`; `v:real^N`;
                            `e:real^N->bool`] THEN
      ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`D:real^N->bool`; `D':real^N->bool`] THEN
      EXPAND_TAC "Ys" THEN REWRITE_TAC[IN_ELIM_THM] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "DY"))) STRIP_ASSUME_TAC) THEN
      ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `e0 = D INTER D':real^N->bool` THEN
      SUBGOAL_THEN `aff_dim(e0:real^N->bool) = &1` ASSUME_TAC THENL
       [EXPAND_TAC "e0" THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN `(e0:real^N->bool) IN s` ASSUME_TAC THENL
       [EXPAND_TAC "e0" THEN ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
      MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `e0:real^N->bool`]
        MOI_FRN_SEG_VERTS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N`
        STRIP_ASSUME_TAC)) THEN
      SUBGOAL_THEN `(x:real^N) IN e0 /\ e0 SUBSET D /\ e0 SUBSET D'`
      STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN SET_TAC[];
          EXPAND_TAC "e0" THEN SET_TAC[]];
        ALL_TAC] THEN
      SUBGOAL_THEN
       `convex hull (IMAGE simplex_barycentre {{x:real^N},e0,D}) IN Z`
      ASSUME_TAC THENL
       [USE_THEN "DY" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      SUBGOAL_THEN
       `convex hull (IMAGE simplex_barycentre {{x:real^N},e0,D'}) IN Z`
      ASSUME_TAC THENL
       [MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `x:real^N`;
                       `e0:real^N->bool`; `D:real^N->bool`]
          MOI_FRN_FLAG_CHAIN) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `x:real^N`;
                       `e0:real^N->bool`; `D':real^N->bool`]
          MOI_FRN_FLAG_CHAIN) THEN
        ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
        MATCH_MP_TAC MOI_FRN_FLAG_STEP THEN
        MAP_EVERY EXISTS_TAC [`s:(real^N->bool)->bool`; `{{x:real^N},e0,D}`;
                              `{{x:real^N},e0}`] THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`v':real^N`; `e':real^N->bool`] THEN STRIP_TAC THEN
      MATCH_MP_TAC MOI_FRN_FLAG_ALL THEN
      MAP_EVERY EXISTS_TAC [`s:(real^N->bool)->bool`; `x:real^N`;
                            `e0:real^N->bool`] THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `K:real^N->bool` THEN
  STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `K:real^N->bool`]
    MOI_FRN_BARY_TRI_FLAG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N` (X_CHOOSE_THEN `e:real^N->bool`
    (X_CHOOSE_THEN `D:real^N->bool` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN `(D:real^N->bool) IN Ys` MP_TAC THENL
   [ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  EXPAND_TAC "Ys" THEN REWRITE_TAC[IN_ELIM_THM] THEN
  DISCH_THEN(MP_TAC o SPECL [`v:real^N`; `e:real^N->bool`] o
    CONJUNCT2 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[]);;

(* Purity of the first derived of a finite combinatorial 2-manifold.      *)

let MOI_FRN_CHAIN_PAIR = prove
 (`!(c:(real^N->bool)->bool) a b.
     moi_bar_chain c {a,b} <=>
     a IN c /\ b IN c /\ ~(a = {}) /\ ~(b = {}) /\ (a SUBSET b \/ b SUBSET a)`,
  REPEAT GEN_TAC THEN
  REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT;
              FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN
  EQ_TAC THENL
   [STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM(MP_TAC o SPECL [`a:real^N->bool`; `b:real^N->bool`]) THEN
    REWRITE_TAC[];
    STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL] THEN
    REPEAT GEN_TAC THEN STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

let MOI_FRN_CHAIN2_TO3 = prove
 (`!(c:(real^N->bool)->bool) f.
     FINITE c /\ combinatorial_manifold 2 c /\ moi_bar_complex c /\
     moi_bar_chain c f /\ CARD f = 2
     ==> ?g. moi_bar_chain c g /\ CARD g = 3 /\ f SUBSET g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `?r1 r2:real^N->bool. f = {r1,r2} /\ r1 SUBSET r2 /\ ~(r1 = r2)`
  STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(f:(real^N->bool)->bool) HAS_SIZE 2` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE] THEN ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
    REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N->bool` (X_CHOOSE_THEN `b:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `(a:real^N->bool) SUBSET b \/ b SUBSET a` MP_TAC THENL
     [UNDISCH_TAC `moi_bar_chain c (f:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[MOI_FRN_CHAIN_PAIR] THEN SIMP_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [MAP_EVERY EXISTS_TAC [`a:real^N->bool`; `b:real^N->bool`];
      MAP_EVERY EXISTS_TAC [`b:real^N->bool`; `a:real^N->bool`]] THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r1:real^N->bool`;
                 `r2:real^N->bool`] MOI_FRN_CHAIN2_EXT) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^N->bool` (X_CHOOSE_THEN `p2:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o SPEC `p1:real^N->bool`)))) THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM] THEN STRIP_TAC THEN
  EXISTS_TAC `(p1:real^N->bool) INSERT {r1,r2}` THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [ALL_TAC; SET_TAC[]] THEN
  SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
           NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV);;

let MOI_FRN_CHAIN1_TO2 = prove
 (`!(c:(real^N->bool)->bool) q.
     FINITE c /\ combinatorial_manifold 2 c /\ q IN c /\ ~(q = {})
     ==> ?r. moi_bar_chain c {q,r} /\ CARD {q,r} = 2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (c:(real^N->bool)->bool)` ASSUME_TAC
  THENL [ASM_MESON_TAC[combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `!r:real^N->bool. ~(r = q) ==> CARD {q,r} = 2`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
             NOT_IN_EMPTY] THEN
    ASM_REWRITE_TAC[] THEN CONV_TAC NUM_REDUCE_CONV;
    ALL_TAC] THEN
  ASM_CASES_TAC `aff_dim(q:real^N->bool) = &2` THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:real^N->bool`]
      MOI_FM3_LF_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `v:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `{v:real^N}` THEN
    SUBGOAL_THEN `~({v:real^N} = q)` ASSUME_TAC THENL
     [DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
      ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_FRN_CHAIN_PAIR; NOT_INSERT_EMPTY; SING_SUBSET];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:real^N->bool`]
      MOI_FRN_CM_PURE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `D:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `D:real^N->bool` THEN
    SUBGOAL_THEN `~(D:real^N->bool = q) /\ ~(D:real^N->bool = {})`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      DISCH_THEN(MP_TAC o AP_TERM `aff_dim:(real^N->bool)->int`) THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    ASM_SIMP_TAC[MOI_FRN_CHAIN_PAIR]]);;

let MOI_FRN_CHAIN_TO3 = prove
 (`!(c:(real^N->bool)->bool) f.
     FINITE c /\ combinatorial_manifold 2 c /\ moi_bar_chain c f /\
     ~(f = {})
     ==> ?g. moi_bar_chain c g /\ CARD g = 3 /\ f SUBSET g`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (f:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  SUBGOAL_THEN `CARD(f:(real^N->bool)->bool) <= 3` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_CHAIN_CARD_LE3 THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_SA_CM_DIM THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD(f:(real^N->bool)->bool) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0]; ALL_TAC] THEN
  SUBGOAL_THEN
   `CARD(f:(real^N->bool)->bool) = 1 \/ CARD f = 2 \/ CARD f = 3`
  MP_TAC THENL
   [UNDISCH_TAC `CARD(f:(real^N->bool)->bool) <= 3` THEN
    UNDISCH_TAC `~(CARD(f:(real^N->bool)->bool) = 0)` THEN ARITH_TAC;
    ALL_TAC] THEN
  STRIP_TAC THENL
   [MP_TAC(ISPEC `f:(real^N->bool)->bool` MOI_FRN_SA_CARD_EQ_1) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` SUBST_ALL_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `q:real^N->bool`]
      MOI_FRN_CHAIN1_TO2) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `moi_bar_chain c {q:real^N->bool}` THEN
      REWRITE_TAC[moi_bar_chain; SING_SUBSET; IN_SING] THEN MESON_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{q:real^N->bool,r}`]
      MOI_FRN_CHAIN2_TO3) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MONO_EXISTS THEN SET_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
      MOI_FRN_CHAIN2_TO3) THEN
    ASM_REWRITE_TAC[];
    EXISTS_TAC `f:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[SUBSET_REFL]]);;

let MOI_FRN_KPURE = prove
 (`!(s:(real^N->bool)->bool) x.
     FINITE s /\ combinatorial_manifold 2 s /\ x IN UNIONS s
     ==> ?D. D IN barycentric_subdivision s /\ aff_dim D = &2 /\ x IN D`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (s:(real^N->bool)->bool) /\
                moi_bar_complex s` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS s` THEN
  ASM_SIMP_TAC[GSYM UNIONS_BARYCENTRIC_SUBDIVISION] THEN
  REWRITE_TAC[IN_UNIONS; MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  SUBGOAL_THEN `~(f:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN q` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `f:(real^N->bool)->bool`]
    MOI_FRN_CHAIN_TO3) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))`
  THEN REPEAT CONJ_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
      MOI_FRN_BARY_AFF_DIM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC;
    SUBGOAL_THEN
     `(q:real^N->bool) SUBSET convex hull (IMAGE simplex_barycentre g)`
     (fun th -> ASM_MESON_TAC[th; SUBSET]) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_MONO THEN
    MATCH_MP_TAC IMAGE_SUBSET THEN ASM_REWRITE_TAC[]]);;

(* Core of SURFACE_NBHD_SIDES: every nonempty R-closed set of simplices   *)
(* of the first derived contains a tetrahedron over every triangle of the *)
(* first derived k of the surface.                                         *)

let MOI_FRN_SIDES_CORE = prove
 (`!(t:(real^N->bool)->bool) s X.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     combinatorial_manifold 2 s /\ connected (UNIONS s) /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     moi_frn_rclosed t s X /\ ~(X = {})
     ==> !D. D IN barycentric_subdivision s /\ aff_dim D = &2
             ==> ?r. r IN X /\ aff_dim r = &3 /\ D SUBSET r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (s:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!D:real^N->bool. D IN barycentric_subdivision s
                                 ==> aff_dim D <= &2` ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_BARY_DIM_LE2 THEN
    EXISTS_TAC `s:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_SA_CM_DIM THEN
    EXISTS_TAC `s:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC
   `Y = {D:real^N->bool | D IN barycentric_subdivision s /\ aff_dim D = &2 /\
                          ?r. r IN X /\ aff_dim r = &3 /\ D SUBSET r}` THEN
  SUBGOAL_THEN
   `Y = {D:real^N->bool | D IN barycentric_subdivision s /\ aff_dim D = &2}`
  MP_TAC THENL
   [ALL_TAC;
    EXPAND_TAC "Y" THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]]
  THEN
  MATCH_MP_TAC MOI_FRN_KDCONN THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THENL
   [EXPAND_TAC "Y" THEN SET_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    UNDISCH_TAC `~(X:(real^N->bool)->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
    DISCH_THEN(X_CHOOSE_TAC `r0:real^N->bool`) THEN
    SUBGOAL_THEN `moi_frn_vp t s (r0:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[moi_frn_rclosed]; ALL_TAC] THEN
    REWRITE_TAC[moi_frn_vp] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `r0:real^N->bool`] MOI_FRN_FULL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`barycentric_subdivision s:(real^N->bool)->bool`;
                   `r0 INTER UNIONS s:real^N->bool`] MOI_FM3_LF_VERTEX) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `a:real^N`; `r0:real^N->bool`] MOI_FRN_NEAR_PURE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r3:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(r3:real^N->bool) IN X` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_frn_rclosed t s (X:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_frn_rclosed] THEN
      DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
      EXISTS_TAC `r0:real^N->bool` THEN ASM_REWRITE_TAC[moi_frn_vp] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `X:(real^N->bool)->bool`; `a:real^N`; `r3:real^N->bool`]
      MOI_FRN_VERTEX_ROTATION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FRN_KPURE THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r':real^N->bool` (X_CHOOSE_THEN `D:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    EXISTS_TAC `D:real^N->bool` THEN EXPAND_TAC "Y" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
    EXISTS_TAC `r':real^N->bool` THEN ASM_REWRITE_TAC[];
    MAP_EVERY X_GEN_TAC
     [`D1:real^N->bool`; `D2:real^N->bool`; `e:real^N->bool`] THEN
    EXPAND_TAC "Y" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(CONJUNCTS_THEN2 (CONJUNCTS_THEN2 ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC)))
      STRIP_ASSUME_TAC) THEN
    ASM_REWRITE_TAC[] THEN
    ASM_CASES_TAC `D1:real^N->bool = D2` THENL
     [UNDISCH_TAC `(D1:real^N->bool) SUBSET r` THEN ASM_REWRITE_TAC[] THEN
      DISCH_TAC THEN EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `e:real^N->bool`]
      MOI_FRN_BARY_EDGE2) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `E1:real^N->bool` (X_CHOOSE_THEN `E2:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    FIRST_X_ASSUM(LABEL_TAC "ONLY" o check (is_forall o concl)) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `X:(real^N->bool)->bool`; `e:real^N->bool`;
                   `D1:real^N->bool`; `D2:real^N->bool`; `r:real^N->bool`]
      MOI_FRN_EDGE_ROTATION) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      X_GEN_TAC `D:real^N->bool` THEN STRIP_TAC THEN
      SUBGOAL_THEN
       `((D1:real^N->bool) = E1 \/ D1 = E2) /\ (D2 = E1 \/ D2 = E2) /\
        (D = E1 \/ D = E2)` MP_TAC THENL
       [REPEAT CONJ_TAC THEN USE_THEN "ONLY" MATCH_MP_TAC THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      UNDISCH_TAC `~(D1:real^N->bool = D2)` THEN
      UNDISCH_TAC `~(E1:real^N->bool = E2)` THEN MESON_TAC[];
      SIMP_TAC[]]]);;


(* ========================================================================= *)
(* The components of N DIFF UNIONS s.  The points                           *)
(* of N outside the surface lie in the relative interiors of simplices of  *)
(* the first derived meeting the surface but not inside it; each such      *)
(* piece is joined to the barycentre of its simplex, and barycentres of    *)
(* nested simplices are joined by segments, so the simplices whose         *)
(* barycentres lie in one component form a nonempty R-closed set; the core *)
(* lemma then gives at most two components, each accumulating on the      *)
(* whole surface.                                                          *)
(* ========================================================================= *)

(* Pieces of N DIFF UNIONS s inside the simplices of the first derived.    *)

let MOI_FRN_CARRIER = prove
 (`!(t:(real^N->bool)->bool) x.
     lf_simplicial_complex t /\ x IN UNIONS t
     ==> ?r. r IN barycentric_subdivision t /\ x IN relative_interior r`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS t` THEN
  ASM_SIMP_TAC[GSYM UNIONS_BARYCENTRIC_SUBDIVISION] THEN
  REWRITE_TAC[IN_UNIONS; MOI_BAR_IN_SUBDIVISION] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` (CONJUNCTS_THEN2
    (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                 `x:real^N`] MOI_BAR_CHAIN_HULL_RI) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC
   `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
  ASM_REWRITE_TAC[] THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
  ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET]);;

let MOI_FRN_RELINT_SUBSET = prove
 (`!(c:(real^N->bool)->bool) r q x.
     moi_bar_complex c /\ r IN c /\ q IN c /\ x IN relative_interior r /\
     x IN q
     ==> r SUBSET q`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) SUBSET r INTER q`
   (fun th -> MP_TAC th THEN SET_TAC[]) THEN
  MATCH_MP_TAC SUBSET_OF_FACE_OF THEN EXISTS_TAC `r:real^N->bool` THEN
  REWRITE_TAC[SUBSET_REFL] THEN CONJ_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  REWRITE_TAC[DISJOINT; GSYM MEMBER_NOT_EMPTY] THEN EXISTS_TAC `x:real^N` THEN
  ASM_REWRITE_TAC[IN_INTER] THEN
  ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]);;

let MOI_FRN_RELINT_NOT_S = prove
 (`!(t:(real^N->bool)->bool) s r.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     r IN barycentric_subdivision t /\ ~(r SUBSET UNIONS s)
     ==> relative_interior r INTER UNIONS s = {}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FRN_FULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r INTER UNIONS s:real^N->bool`; `r:real^N->bool`]
    FACE_OF_DISJOINT_RELATIVE_INTERIOR) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN SET_TAC[]);;

let MOI_FRN_SIMPLEX_REP = prove
 (`!r x:real^N.
     (?n. n simplex r) /\ x IN r
     ==> ?mu. (!v. v extreme_point_of r ==> &0 <= mu v) /\
              sum {v | v extreme_point_of r} mu = &1 /\
              vsum {v | v extreme_point_of r} (\v. mu v % v) = x`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPEC `r:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
  ABBREV_TAC `V = {v:real^N | v extreme_point_of r}` THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN r` THEN
  FIRST_ASSUM(fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV) [th]) THEN
  REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `mu:real^N->real` THEN
  EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN SIMP_TAC[]);;

let MOI_FRN_NBHD_MEETS = prove
 (`!(t:(real^N->bool)->bool) s r x.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     r IN barycentric_subdivision t /\ x IN r /\ x IN derived_nbhd t s
     ==> ~(r INTER UNIONS s = {})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`r:real^N->bool`; `x:real^N`] MOI_FRN_SIMPLEX_REP) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real^N->real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`; `mu:real^N->real`] MOI_FRN_NBHD_IMP_MAX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` STRIP_ASSUME_TAC) THEN
  UNDISCH_TAC `r INTER UNIONS s:real^N->bool = {}` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
  ASM_MESON_TAC[extreme_point_of]);;

(* The star property: the segment from a point of N in a simplex r of the *)
(* first derived to the barycentre of r stays in N.                        *)

let MOI_FRN_NBHD_STAR = prove
 (`!(t:(real^N->bool)->bool) s r x.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     r IN barycentric_subdivision t /\ x IN r /\ x IN derived_nbhd t s
     ==> segment[x,simplex_barycentre r] SUBSET derived_nbhd t s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `(x:real^N) IN derived_nbhd t s` THEN
  ASM_SIMP_TAC[MOI_FRN_IN_NBHD] THEN
  DISCH_THEN(X_CHOOSE_THEN `f:(real^N->bool)->bool` (CONJUNCTS_THEN2
    ASSUME_TAC (CONJUNCTS_THEN2
      (X_CHOOSE_THEN `p:real^N->bool` STRIP_ASSUME_TAC) ASSUME_TAC))) THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `f:(real^N->bool)->bool`; `x:real^N`] MOI_BAR_CHAIN_HULL_RI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t)
                  (g:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `(x:real^N) IN relative_interior
                   (convex hull IMAGE simplex_barycentre g)` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; RELATIVE_INTERIOR_EMPTY;
                    NOT_IN_EMPTY];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `g:(real^N->bool)->bool`] MOI_BAR_CHAIN_MAX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC `r0 = UNIONS (g:(real^N->bool)->bool)` THEN
  SUBGOAL_THEN `(x:real^N) IN relative_interior r0` ASSUME_TAC THENL
   [EXPAND_TAC "r0" THEN MATCH_MP_TAC MOI_BAR_CHAIN_RI_MAX THEN
    EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r0:real^N->bool) IN f /\ r0 IN barycentric_subdivision t`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; moi_bar_chain]; ALL_TAC] THEN
  SUBGOAL_THEN `(r0:real^N->bool) SUBSET r` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC
     [`barycentric_subdivision t:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ABBREV_TAC `f2 = (r:real^N->bool) INSERT {q | q IN f /\ q SUBSET r0}` THEN
  SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision t)
                  (f2:(real^N->bool)->bool)` ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision t)
                   (f:(real^N->bool)->bool)` THEN
    EXPAND_TAC "f2" THEN REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
    REPEAT CONJ_TAC THENL
     [ASM SET_TAC[];
      REWRITE_TAC[FINITE_INSERT] THEN MATCH_MP_TAC FINITE_RESTRICT THEN
      ASM_REWRITE_TAC[];
      REWRITE_TAC[IN_INSERT; IN_ELIM_THM; DE_MORGAN_THM] THEN
      CONJ_TAC THENL [ASM SET_TAC[]; ASM_MESON_TAC[]];
      REWRITE_TAC[IN_INSERT; IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN ASM_MESON_TAC[SUBSET_TRANS]];
    ALL_TAC] THEN
  SUBGOAL_THEN `?q:real^N->bool. q IN f2 /\ q IN barycentric_subdivision s`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `(p:real^N->bool) SUBSET r0 \/ r0 SUBSET p` MP_TAC THENL
     [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision t)
                     (f:(real^N->bool)->bool)` THEN
      REWRITE_TAC[moi_bar_chain] THEN
      DISCH_THEN(MP_TAC o SPECL [`p:real^N->bool`; `r0:real^N->bool`] o
        last o CONJUNCTS) THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [EXISTS_TAC `p:real^N->bool` THEN EXPAND_TAC "f2" THEN
      ASM_REWRITE_TAC[IN_INSERT; IN_ELIM_THM];
      EXISTS_TAC `r0:real^N->bool` THEN EXPAND_TAC "f2" THEN
      ASM_REWRITE_TAC[IN_INSERT; IN_ELIM_THM; SUBSET_REFL] THEN
      MATCH_MP_TAC MOI_FRN_RELINT_MEETS_SUBCOMPLEX THEN
      MAP_EVERY EXISTS_TAC
       [`barycentric_subdivision t:(real^N->bool)->bool`; `x:real^N`] THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(x:real^N) IN r0` ASSUME_TAC THENL
       [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^N) IN UNIONS (barycentric_subdivision s)` MP_TAC
      THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `p:real^N->bool` THEN
        ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
        ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[x:real^N,simplex_barycentre r] SUBSET
    convex hull (IMAGE simplex_barycentre f2)` ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN MATCH_MP_TAC HULL_MINIMAL THEN
    REWRITE_TAC[CONVEX_CONVEX_HULL; INSERT_SUBSET; EMPTY_SUBSET] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))
        SUBSET convex hull (IMAGE simplex_barycentre f2)` MP_TAC THENL
       [MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        EXPAND_TAC "f2" THEN REWRITE_TAC[SUBSET; IN_INSERT; IN_ELIM_THM] THEN
        ASM_MESON_TAC[SUBSET];
        ALL_TAC] THEN
      MP_TAC(ISPEC
        `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))`
        RELATIVE_INTERIOR_SUBSET) THEN
      ASM SET_TAC[];
      MATCH_MP_TAC HULL_INC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
      EXPAND_TAC "f2" THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  ASM_SIMP_TAC[MOI_FRN_IN_NBHD] THEN EXISTS_TAC `f2:(real^N->bool)->bool` THEN
  ASM_REWRITE_TAC[] THEN ASM SET_TAC[]);;

let MOI_FRN_N_FACTS = prove
 (`!(t:(real^N->bool)->bool) s.
     lf_simplicial_complex t /\ simplicial_subcomplex s t
     ==> derived_nbhd t s SUBSET UNIONS t /\
         UNIONS s SUBSET derived_nbhd t s /\
         UNIONS s SUBSET
           (subtopology euclidean (UNIONS t)) interior_of (derived_nbhd t s)`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP DERIVED_NBHD_BASIC) THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `(subtopology euclidean (UNIONS t)) interior_of
              (derived_nbhd t s:real^N->bool)` THEN
  ASM_REWRITE_TAC[INTERIOR_OF_SUBSET]);;

let MOI_FRN_VP_BARY = prove
 (`!(t:(real^N->bool)->bool) s r.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ moi_frn_vp t s r
     ==> simplex_barycentre r IN derived_nbhd t s /\
         simplex_barycentre r IN relative_interior r /\
         ~(simplex_barycentre r IN UNIONS s)`,
  REWRITE_TAC[moi_frn_vp] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_N_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplex_barycentre r IN relative_interior (r:real^N->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    EXISTS_TAC `n:int` THEN ASM SET_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [UNDISCH_TAC `~(r INTER UNIONS s:real^N->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `r:real^N->bool`; `y:real^N`] MOI_FRN_NBHD_STAR) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`y:real^N`; `simplex_barycentre r:real^N`]
      ENDS_IN_SEGMENT) THEN
    SET_TAC[];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `r:real^N->bool`] MOI_FRN_RELINT_NOT_S) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MOI_FRN_PIECE_CC = prove
 (`!(t:(real^N->bool)->bool) s r x.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_vp t s r /\ x IN derived_nbhd t s /\ x IN relative_interior r
     ==> connected_component (derived_nbhd t s DIFF UNIONS s) x
           (simplex_barycentre r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FRN_VP_BARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_frn_vp t s (r:real^N->bool)` THEN
  REWRITE_TAC[moi_frn_vp] THEN STRIP_TAC THEN
  REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `segment[x:real^N,simplex_barycentre r]` THEN
  REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN
  SUBGOAL_THEN `(x:real^N) IN r` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`; `x:real^N`] MOI_FRN_NBHD_STAR) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FRN_RELINT_NOT_S) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `segment[x:real^N,simplex_barycentre r] SUBSET relative_interior r`
  MP_TAC THENL
   [SUBGOAL_THEN `convex(relative_interior(r:real^N->bool))` MP_TAC THENL
     [MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR THEN
      ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let MOI_FRN_ADJ_CC = prove
 (`!(t:(real^N->bool)->bool) s r r'.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_vp t s r /\ moi_frn_vp t s r' /\ r SUBSET r'
     ==> connected_component (derived_nbhd t s DIFF UNIONS s)
           (simplex_barycentre r) (simplex_barycentre r')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FRN_VP_BARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r':real^N->bool`] MOI_FRN_VP_BARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_frn_vp t s (r:real^N->bool)` THEN
  UNDISCH_TAC `moi_frn_vp t s (r':real^N->bool)` THEN
  REWRITE_TAC[moi_frn_vp] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `simplex_barycentre r IN (r':real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  REWRITE_TAC[connected_component] THEN
  EXISTS_TAC
   `segment[simplex_barycentre r:real^N,simplex_barycentre r']` THEN
  REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN
  SUBGOAL_THEN
   `segment[simplex_barycentre r:real^N,simplex_barycentre r'] SUBSET
    derived_nbhd t s` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_NBHD_STAR THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `segment(simplex_barycentre r':real^N,simplex_barycentre r) SUBSET
    relative_interior r'` ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r':real^N->bool`] MOI_FRN_RELINT_NOT_S) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN
   `segment[simplex_barycentre r:real^N,simplex_barycentre r'] INTER
    UNIONS s = {}` MP_TAC THENL
   [REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    ONCE_REWRITE_TAC[CONJUNCT2 SEGMENT_SYM] THEN ASM SET_TAC[];
    ASM SET_TAC[]]);;

let MOI_FRN_COVER = prove
 (`!(t:(real^N->bool)->bool) s x.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     x IN derived_nbhd t s /\ ~(x IN UNIONS s)
     ==> ?r. moi_frn_vp t s r /\ x IN relative_interior r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `x:real^N`] MOI_FRN_CARRIER) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
      MOI_FRN_N_FACTS) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_frn_vp] THEN
  SUBGOAL_THEN `(x:real^N) IN r` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FRN_NBHD_MEETS THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

(* The simplices whose barycentres lie in one component form a nonempty  *)
(* R-closed set.                                                           *)

let MOI_FRN_COMP_CLASS = prove
 (`!(t:(real^N->bool)->bool) s K.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     K IN components (derived_nbhd t s DIFF UNIONS s)
     ==> moi_frn_rclosed t s
           {r | moi_frn_vp t s r /\ simplex_barycentre r IN K} /\
         ~({r | moi_frn_vp t s r /\ simplex_barycentre r IN K} = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o GEN_REWRITE_RULE I [IN_COMPONENTS]) THEN
  DISCH_THEN(X_CHOOSE_THEN `z:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
  REWRITE_TAC[moi_frn_rclosed; IN_ELIM_THM; GSYM MEMBER_NOT_EMPTY] THEN
  REPEAT CONJ_TAC THENL
   [SIMP_TAC[];
    MAP_EVERY X_GEN_TAC [`r:real^N->bool`; `r':real^N->bool`] THEN
    DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
      (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "OR"))) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN
     `connected_component (derived_nbhd t s DIFF UNIONS s)
        (simplex_barycentre r) (simplex_barycentre (r':real^N->bool))`
    MP_TAC THENL
     [REMOVE_THEN "OR" DISJ_CASES_TAC THENL
       [MATCH_MP_TAC MOI_FRN_ADJ_CC THEN ASM_REWRITE_TAC[];
        MATCH_MP_TAC CONNECTED_COMPONENT_SYM THEN
        MATCH_MP_TAC MOI_FRN_ADJ_CC THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    UNDISCH_TAC `simplex_barycentre r IN
                 connected_component (derived_nbhd t s DIFF UNIONS s)
                   (z:real^N)` THEN
    REWRITE_TAC[IN] THEN MESON_TAC[CONNECTED_COMPONENT_TRANS];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `z:real^N`] MOI_FRN_COVER) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->bool` THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
    MATCH_MP_TAC MOI_FRN_PIECE_CC THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[]]);;

let MOI_FRN_COMP_TETS = prove
 (`!(t:(real^N->bool)->bool) s K D.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     combinatorial_manifold 2 s /\ connected (UNIONS s) /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     K IN components (derived_nbhd t s DIFF UNIONS s) /\
     D IN barycentric_subdivision s /\ aff_dim D = &2
     ==> ?r. moi_frn_vp t s r /\ simplex_barycentre r IN K /\
             aff_dim r = &3 /\ D SUBSET r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `K:real^N->bool`] MOI_FRN_COMP_CLASS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `{r:real^N->bool | moi_frn_vp t s r /\
                                    simplex_barycentre r IN K}`]
    MOI_FRN_SIDES_CORE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(MP_TAC o SPEC `D:real^N->bool`) THEN
  ASM_REWRITE_TAC[IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FRN_COMP_EQ = prove
 (`!u k x:real^N.
     k IN components u /\ x IN k ==> k = connected_component u x`,
  REWRITE_TAC[IN_COMPONENTS] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[CONNECTED_COMPONENT_EQ]);;

let MOI_FRN_KTRI_TWO = prove
 (`!(t:(real^N->bool)->bool) s D.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     D IN barycentric_subdivision s /\ aff_dim D = &2
     ==> ?T1 T2. ~(T1 = T2) /\
                 {r | r IN barycentric_subdivision t /\ aff_dim r = &3 /\
                      D SUBSET r} = {T1,T2}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `D:real^N->bool`] MOI_FRN_KTRI_TETS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(D:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(D:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN
   `FINITE {r:real^N->bool | r IN barycentric_subdivision t /\
                             aff_dim r = &3 /\ D SUBSET r}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN
    EXISTS_TAC `{r:real^N->bool | r IN barycentric_subdivision t /\
                                  ~(r INTER D = {})}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FDN_LF_COMPACT_MEETS_FINITE THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
        EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[];
        ASM SET_TAC[]];
      REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MOI_SCF_HAS_SIZE_2] THEN ASM_REWRITE_TAC[HAS_SIZE]);;

let MOI_FRN_TET_VP = prove
 (`!(t:(real^N->bool)->bool) s r D.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     combinatorial_manifold 2 s /\
     r IN barycentric_subdivision t /\ aff_dim r = &3 /\
     D IN barycentric_subdivision s /\ aff_dim D = &2 /\ D SUBSET r
     ==> moi_frn_vp t s r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (s:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[combinatorial_manifold; MOI_FRN_LF_BAR_COMPLEX];
    ALL_TAC] THEN
  REWRITE_TAC[moi_frn_vp] THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `~(D:real^N->bool = {})` ASSUME_TAC THENL
     [DISCH_TAC THEN UNDISCH_TAC `aff_dim(D:real^N->bool) = &2` THEN
      ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    SUBGOAL_THEN `(D:real^N->bool) SUBSET UNIONS s` MP_TAC THENL
     [SUBGOAL_THEN
       `(D:real^N->bool) SUBSET UNIONS (barycentric_subdivision s)` MP_TAC
      THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
      ASM SET_TAC[]];
    DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `r:real^N->bool`] MOI_FRN_FULL) THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `r INTER UNIONS s:real^N->bool = r` SUBST1_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `aff_dim(r:real^N->bool) <= &2` MP_TAC THENL
     [MATCH_MP_TAC MOI_FRN_BARY_DIM_LE2 THEN
      EXISTS_TAC `s:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_SA_CM_DIM THEN
      EXISTS_TAC `s:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[] THEN INT_ARITH_TAC]]);;

(* Every component contains the barycentre of one of the two tetrahedra   *)
(* over a fixed triangle of k.                                             *)

let MOI_FRN_SIDES_TWO = prove
 (`!(t:(real^N->bool)->bool) s.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     combinatorial_manifold 2 s /\ connected (UNIONS s) /\
     ~(UNIONS s = {}) /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v)))
     ==> ?T1 T2. moi_frn_vp t s T1 /\ moi_frn_vp t s T2 /\
                 components (derived_nbhd t s DIFF UNIONS s) SUBSET
                 {connected_component (derived_nbhd t s DIFF UNIONS s)
                    (simplex_barycentre T1),
                  connected_component (derived_nbhd t s DIFF UNIONS s)
                    (simplex_barycentre T2)}`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `~(UNIONS s:real^N->bool = {})` THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `y:real^N`) THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `y:real^N`] MOI_FRN_KPURE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `D:real^N->bool`] MOI_FRN_KTRI_TWO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real^N->bool` (X_CHOOSE_THEN `T2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `!r:real^N->bool. r IN barycentric_subdivision t /\ aff_dim r = &3 /\
                     D SUBSET r <=> r = T1 \/ r = T2` (LABEL_TAC "TT") THENL
   [GEN_TAC THEN FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION]) THEN
    DISCH_THEN(MP_TAC o SPEC `r:real^N->bool`) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_frn_vp t s (T1:real^N->bool) /\ moi_frn_vp t s T2`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC MOI_FRN_TET_VP THEN
    EXISTS_TAC `D:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    USE_THEN "TT" (fun th -> REWRITE_TAC[th]);
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`T1:real^N->bool`; `T2:real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[SUBSET; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `K:real^N->bool` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `K:real^N->bool`; `D:real^N->bool`] MOI_FRN_COMP_TETS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(r:real^N->bool) = T1 \/ r = T2` MP_TAC THENL
   [USE_THEN "TT" (fun th -> REWRITE_TAC[GSYM th]) THEN
    ASM_MESON_TAC[moi_frn_vp];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`derived_nbhd t s DIFF UNIONS s:real^N->bool`;
                 `K:real^N->bool`; `simplex_barycentre r:real^N`]
    MOI_FRN_COMP_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[]);;

let MOI_FRN_SIDES_FINITE = prove
 (`!(t:(real^N->bool)->bool) s.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     combinatorial_manifold 2 s /\ connected (UNIONS s) /\
     ~(UNIONS s = {}) /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v)))
     ==> FINITE (components (derived_nbhd t s DIFF UNIONS s)) /\
         1 <= CARD (components (derived_nbhd t s DIFF UNIONS s)) /\
         CARD (components (derived_nbhd t s DIFF UNIONS s)) <= 2`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FRN_SIDES_TWO) THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real^N->bool` (X_CHOOSE_THEN `T2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  POP_ASSUM MP_TAC THEN FIRST_X_ASSUM STRIP_ASSUME_TAC THEN DISCH_TAC THEN
  ABBREV_TAC `C = components (derived_nbhd t s DIFF UNIONS s:real^N->bool)` THEN
  SUBGOAL_THEN `FINITE (C:(real^N->bool)->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC
     `{connected_component (derived_nbhd t s DIFF UNIONS s)
         (simplex_barycentre T1),
       connected_component (derived_nbhd t s DIFF UNIONS s)
         (simplex_barycentre (T2:real^N->bool))}` THEN
    ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `~(C:(real^N->bool)->bool = {})` MP_TAC THENL
     [EXPAND_TAC "C" THEN REWRITE_TAC[COMPONENTS_EQ_EMPTY] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                     `T1:real^N->bool`] MOI_FRN_VP_BARY) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[CARD_EQ_0; ARITH_RULE `1 <= n <=> ~(n = 0)`];
    MATCH_MP_TAC LE_TRANS THEN EXISTS_TAC
     `CARD {connected_component (derived_nbhd t s DIFF UNIONS s)
              (simplex_barycentre T1),
            connected_component (derived_nbhd t s DIFF UNIONS s)
              (simplex_barycentre (T2:real^N->bool))}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_SUBSET THEN
      ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY];
      SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT;
               NOT_IN_EMPTY] THEN
      COND_CASES_TAC THEN ARITH_TAC]]);;

(* Every component accumulates on every point of the surface.             *)

let MOI_FRN_SIDES_ACCUM = prove
 (`!(t:(real^N->bool)->bool) s k.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     combinatorial_manifold 2 s /\ connected (UNIONS s) /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     k IN components (derived_nbhd t s DIFF UNIONS s)
     ==> UNIONS s SUBSET closure k`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_N_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `y:real^N`] MOI_FRN_KPURE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `k:real^N->bool`; `D:real^N->bool`] MOI_FRN_COMP_TETS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FRN_VP_BARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(y:real^N) IN r` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision t` ASSUME_TAC
  THENL [ASM_MESON_TAC[moi_frn_vp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`derived_nbhd t s DIFF UNIONS s:real^N->bool`;
                 `k:real^N->bool`; `simplex_barycentre r:real^N`]
    MOI_FRN_COMP_EQ) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `segment(y:real^N,simplex_barycentre r) SUBSET k` ASSUME_TAC
  THENL
   [SUBGOAL_THEN
     `segment[y:real^N,simplex_barycentre r] SUBSET derived_nbhd t s`
    ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FRN_NBHD_STAR THEN ASM_REWRITE_TAC[] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN
     `segment(simplex_barycentre r:real^N,y) SUBSET relative_interior r`
    ASSUME_TAC THENL
     [MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX];
        ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    ASM_REWRITE_TAC[] THEN REWRITE_TAC[IN] THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_SYM THEN
    MATCH_MP_TAC MOI_FRN_PIECE_CC THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MP_TAC(ISPECL [`y:real^N`; `simplex_barycentre r:real^N`]
        SEGMENT_OPEN_SUBSET_CLOSED) THEN ASM SET_TAC[];
      ASM_MESON_TAC[SEGMENT_SYM; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^N = simplex_barycentre r)` ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN closure(segment(y,simplex_barycentre r))`
  MP_TAC THENL
   [ASM_REWRITE_TAC[CLOSURE_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`segment(y:real^N,simplex_barycentre r)`; `k:real^N->bool`]
    SUBSET_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;


(* ========================================================================= *)
(* Two-sidedness.  With one component the union of                         *)
(* the pieces over an R-closed set is open in N DIFF UNIONS s, so there is *)
(* a single R-class; the weight function of the surface (simplexwise       *)
(* affine on the first derived, 1 on the vertices in the surface, 0 on the *)
(* others) gives small neighbourhoods W whose complements W DIFF UNIONS s  *)
(* are connected.                                                          *)
(* ========================================================================= *)

(* When N DIFF UNIONS s is connected there is only one R-class.          *)

let MOI_FRN_RELINT_UNIQUE = prove
 (`!(c:(real^N->bool)->bool) r r' x.
     moi_bar_complex c /\ r IN c /\ r' IN c /\
     x IN relative_interior r /\ x IN relative_interior r'
     ==> r = r'`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC SUBSET_ANTISYM THEN CONJ_TAC THEN
  MATCH_MP_TAC MOI_FRN_RELINT_SUBSET THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
  ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]);;

let MOI_FRN_UX_OPEN = prove
 (`!(t:(real^N->bool)->bool) s X.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_rclosed t s X
     ==> open_in (subtopology euclidean (derived_nbhd t s DIFF UNIONS s))
           {x | x IN derived_nbhd t s DIFF UNIONS s /\
                ?r. r IN X /\ x IN relative_interior r}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_N_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  GEN_REWRITE_TAC I [OPEN_IN_SUBOPEN] THEN
  REWRITE_TAC[IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC
    (X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision t` ASSUME_TAC
  THENL [ASM_MESON_TAC[moi_frn_rclosed; moi_frn_vp]; ALL_TAC] THEN
  EXISTS_TAC `(derived_nbhd t s DIFF UNIONS s) INTER
              moi_sta_open_star (barycentric_subdivision t) (x:real^N)` THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC OPEN_IN_SUBTOPOLOGY_INTER_SUBSET THEN
    EXISTS_TAC `UNIONS (barycentric_subdivision t):real^N->bool` THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN
       `UNIONS (barycentric_subdivision t) INTER
        moi_sta_open_star (barycentric_subdivision t) (x:real^N) =
        moi_sta_open_star (barycentric_subdivision t) x`
      SUBST1_TAC THENL
       [REWRITE_TAC[moi_sta_open_star] THEN SET_TAC[];
        MATCH_MP_TAC MOI_STA_OPEN_STAR_OPEN THEN ASM_REWRITE_TAC[]];
      ASM SET_TAC[]];
    ASM_REWRITE_TAC[IN_INTER] THEN REWRITE_TAC[moi_sta_open_star; IN_ELIM_THM] THEN
    SIMP_TAC[] THEN ASM SET_TAC[];
    REWRITE_TAC[SUBSET; IN_INTER; IN_ELIM_THM; moi_sta_open_star] THEN
    X_GEN_TAC `y:real^N` THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `y:real^N`] MOI_FRN_COVER) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r':real^N->bool` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `r':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(r':real^N->bool) IN barycentric_subdivision t` ASSUME_TAC
    THENL [ASM_MESON_TAC[moi_frn_vp]; ALL_TAC] THEN
    UNDISCH_TAC `moi_frn_rclosed t s (X:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_frn_rclosed] THEN DISCH_THEN(MATCH_MP_TAC o CONJUNCT2) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN DISJ1_TAC THEN
    MATCH_MP_TAC MOI_FRN_RELINT_SUBSET THEN
    MAP_EVERY EXISTS_TAC
     [`barycentric_subdivision t:(real^N->bool)->bool`; `x:real^N`] THEN
    ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
    ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]]);;

let MOI_FRN_ONE_CLASS = prove
 (`!(t:(real^N->bool)->bool) s X.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     connected (derived_nbhd t s DIFF UNIONS s) /\
     moi_frn_rclosed t s X /\ ~(X = {})
     ==> !r. moi_frn_vp t s r ==> r IN X`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(r:real^N->bool) IN X` THEN ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `Y = {r':real^N->bool | moi_frn_vp t s r' /\ ~(r' IN X)}` THEN
  SUBGOAL_THEN `moi_frn_rclosed t s (Y:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN
    UNDISCH_TAC `moi_frn_rclosed t s (X:(real^N->bool)->bool)` THEN
    REWRITE_TAC[moi_frn_rclosed; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(r:real^N->bool) IN Y` ASSUME_TAC THENL
   [EXPAND_TAC "Y" THEN ASM_REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  UNDISCH_TAC `connected (derived_nbhd t s DIFF UNIONS s:real^N->bool)` THEN
  REWRITE_TAC[CONNECTED_OPEN_IN] THEN
  MAP_EVERY EXISTS_TAC
   [`{x | x IN derived_nbhd t s DIFF UNIONS s /\
          ?r:real^N->bool. r IN X /\ x IN relative_interior r}`;
    `{x | x IN derived_nbhd t s DIFF UNIONS s /\
          ?r:real^N->bool. r IN Y /\ x IN relative_interior r}`] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FRN_UX_OPEN THEN ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_FRN_UX_OPEN THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_UNION; IN_ELIM_THM] THEN
    X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `x:real^N`] MOI_FRN_COVER) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r':real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `(r':real^N->bool) IN X` THENL
     [DISJ1_TAC THEN EXISTS_TAC `r':real^N->bool` THEN ASM_REWRITE_TAC[];
      DISJ2_TAC THEN EXISTS_TAC `r':real^N->bool` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "Y" THEN ASM_REWRITE_TAC[IN_ELIM_THM]];
    REWRITE_TAC[EXTENSION; IN_INTER; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `x:real^N` THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r1:real^N->bool`
        STRIP_ASSUME_TAC))
      (CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `r2:real^N->bool`
        STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(r1:real^N->bool) = r2` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FRN_RELINT_UNIQUE THEN
      MAP_EVERY EXISTS_TAC
       [`barycentric_subdivision t:(real^N->bool)->bool`; `x:real^N`] THEN
      ASM_REWRITE_TAC[] THEN
      ASM_MESON_TAC[moi_frn_rclosed; moi_frn_vp];
      ALL_TAC] THEN
    UNDISCH_TAC `(r2:real^N->bool) IN Y` THEN EXPAND_TAC "Y" THEN
    REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
    UNDISCH_TAC `~(X:(real^N->bool)->bool = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_TAC `r0:real^N->bool`) THEN
    EXISTS_TAC `simplex_barycentre r0:real^N` THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `r0:real^N->bool`] MOI_FRN_VP_BARY) THEN
    ANTS_TAC THENL [ASM_MESON_TAC[moi_frn_rclosed]; ALL_TAC] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    EXISTS_TAC `r0:real^N->bool` THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
    EXISTS_TAC `simplex_barycentre r:real^N` THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `r:real^N->bool`] MOI_FRN_VP_BARY) THEN
    ASM_REWRITE_TAC[] THEN
    STRIP_TAC THEN ASM_REWRITE_TAC[IN_DIFF] THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[]]);;

(* The weight of the surface: the simplexwise affine function on the      *)
(* first derived equal to 1 at the vertices in UNIONS s and 0 at the      *)
(* other vertices.                                                         *)

let moi_frn_sig = new_definition
 `moi_frn_sig (t:(real^N->bool)->bool) (s:(real^N->bool)->bool)
              (h:real^N->real^1) <=>
    h continuous_on UNIONS t /\
    (!r. r IN barycentric_subdivision t
         ==> ?l y. linear l /\ !x. x IN r ==> h x = l x + y) /\
    (!r mu. r IN barycentric_subdivision t /\
            (!v. v extreme_point_of r ==> &0 <= mu v) /\
            sum {v | v extreme_point_of r} mu = &1
            ==> drop(h (vsum {v | v extreme_point_of r} (\v. mu v % v))) =
                sum {v | v extreme_point_of r /\ v IN UNIONS s} mu)`;;

let MOI_FRN_SIG_EXISTS = prove
 (`!(t:(real^N->bool)->bool) s.
     lf_simplicial_complex t /\ simplicial_subcomplex s t
     ==> ?h. moi_frn_sig t s h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                 `\v:real^N. if v IN UNIONS s then vec 1 else vec 0:real^1`]
    MOI_FRN_SIMPLEXWISE_EXTENSION) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `h:real^N->real^1`
    (CONJUNCTS_THEN2 (LABEL_TAC "AFF") (LABEL_TAC "VAL"))) THEN
  EXISTS_TAC `h:real^N->real^1` THEN REWRITE_TAC[moi_frn_sig] THEN
  CONJ_TAC THENL
   [MP_TAC(ISPECL [`barycentric_subdivision t:(real^N->bool)->bool`;
                   `h:real^N->real^1`] MOI_FRN_SIMPLEXWISE_PL) THEN
    ASM_REWRITE_TAC[] THEN SIMP_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL [USE_THEN "AFF" ACCEPT_TAC; ALL_TAC] THEN
  MAP_EVERY X_GEN_TAC [`r:real^N->bool`; `mu:real^N->real`] THEN
  STRIP_TAC THEN
  MP_TAC(ISPEC `r:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  ABBREV_TAC `V = {v:real^N | v extreme_point_of r}` THEN
  DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)) THEN
  SUBGOAL_THEN `FINITE (V:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!v:real^N. v IN V ==> v IN r /\ {v} IN barycentric_subdivision t`
  ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    CONJ_TAC THENL [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
    MATCH_MP_TAC(CONJUNCT1(CONJUNCT2(REWRITE_RULE[moi_bar_complex]
      (ASSUME `moi_bar_complex
                 (barycentric_subdivision t:(real^N->bool)->bool)`)))) THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING];
    ALL_TAC] THEN
  USE_THEN "AFF" (fun th -> MP_TAC(MATCH_MP th
    (ASSUME `(r:real^N->bool) IN barycentric_subdivision t`))) THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real^1` (X_CHOOSE_THEN `y:real^1`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `vsum V (\v:real^N. mu v % v) IN r` ASSUME_TAC THENL
   [SUBGOAL_THEN `vsum V (\v:real^N. mu v % v) IN convex hull V` MP_TAC THENL
     [REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
      EXISTS_TAC `mu:real^N->real` THEN ASM_REWRITE_TAC[] THEN
      EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v:real^N | v extreme_point_of r /\ v IN UNIONS s} =
                {v | v IN V /\ v IN UNIONS s}` SUBST1_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM]; ALL_TAC] THEN
  REWRITE_TAC[SUM_RESTRICT_SET] THEN
  SUBGOAL_THEN
   `(h:real^N->real^1) (vsum V (\v. mu v % v)) =
    vsum V (\v. mu v % (if v IN UNIONS s then vec 1 else vec 0))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `(l:real^N->real^1) (vsum V (\v. mu v % v)) + y` THEN
    CONJ_TAC THENL [FIRST_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
                    ALL_TAC] THEN
    MP_TAC(ISPECL [`l:real^N->real^1`; `y:real^1`; `V:real^N->bool`;
                   `mu:real^N->real`; `\v:real^N. v`] MOI_FRN_AFFINE_VSUM) THEN
    REWRITE_TAC[] THEN ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC VSUM_EQ THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
    REWRITE_TAC[] THEN AP_TERM_TAC THEN
    MATCH_MP_TAC EQ_TRANS THEN EXISTS_TAC `(h:real^N->real^1) v` THEN
    CONJ_TAC THENL
     [CONV_TAC SYM_CONV THEN FIRST_ASSUM MATCH_MP_TAC THEN ASM_MESON_TAC[];
      USE_THEN "VAL" (MP_TAC o SPEC `v:real^N`) THEN ASM_SIMP_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[DROP_VSUM; o_DEF; DROP_CMUL] THEN
  MATCH_MP_TAC SUM_EQ THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  REWRITE_TAC[] THEN COND_CASES_TAC THEN REWRITE_TAC[DROP_VEC] THEN
  REAL_ARITH_TAC);;

let MOI_FRN_SIG_SIMPLEX = prove
 (`!(t:(real^N->bool)->bool) s h r x.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ r IN barycentric_subdivision t /\ x IN r
     ==> ?mu. (!v. v extreme_point_of r ==> &0 <= mu v) /\
              sum {v | v extreme_point_of r} mu = &1 /\
              vsum {v | v extreme_point_of r} (\v. mu v % v) = x /\
              drop(h x) = sum {v | v extreme_point_of r /\ v IN UNIONS s} mu /\
              FINITE {v | v extreme_point_of r}`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
  MP_TAC(ISPECL [`r:real^N->bool`; `x:real^N`] MOI_FRN_SIMPLEX_REP) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `mu:real^N->real` THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq(concl th) && rand(concl th) = `x:real^N`)) THEN
    UNDISCH_TAC `moi_frn_sig t s (h:real^N->real^1)` THEN
    REWRITE_TAC[moi_frn_sig] THEN
    DISCH_THEN(MATCH_MP_TAC o CONJUNCT2 o CONJUNCT2) THEN
    ASM_REWRITE_TAC[];
    MP_TAC(ISPEC `r:real^N->bool` MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
    ASM_REWRITE_TAC[] THEN MESON_TAC[AFFINE_INDEPENDENT_IMP_FINITE]]);;

let MOI_FRN_SIG_RANGE = prove
 (`!(t:(real^N->bool)->bool) s h x.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ x IN UNIONS t
     ==> &0 <= drop(h x) /\ drop(h x) <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `x:real^N`] MOI_FRN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `r:real^N->bool`; `x:real^N`]
    MOI_FRN_SIG_SIMPLEX) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real^N->real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC SUM_POS_LE THEN ASM_SIMP_TAC[IN_ELIM_THM];
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
      check (fun th -> is_eq(concl th) && rand(concl th) = `&1`)) THEN
    MATCH_MP_TAC SUM_SUBSET_SIMPLE THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; IN_ELIM_THM] THEN ASM_MESON_TAC[]]);;

let MOI_FRN_SIG_ONE = prove
 (`!(t:(real^N->bool)->bool) s h x.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ x IN UNIONS s
     ==> drop(h x) = &1`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `?q:real^N->bool. q IN barycentric_subdivision s /\ x IN q`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `(x:real^N) IN UNIONS s` THEN
    FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC (LAND_CONV o RAND_CONV)
      [SYM th]) o check (fun th -> is_eq(concl th) &&
        rand(concl th) = `UNIONS (s:(real^N->bool)->bool)`)) THEN
    REWRITE_TAC[IN_UNIONS] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^N->bool) IN barycentric_subdivision t /\
                q SUBSET UNIONS s` STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL
     [ASM_MESON_TAC[simplicial_subcomplex; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(q:real^N->bool) SUBSET UNIONS (barycentric_subdivision s)`
    MP_TAC THENL [ASM SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `q:real^N->bool`; `x:real^N`]
    MOI_FRN_SIG_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real^N->real` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `{v:real^N | v extreme_point_of q /\ v IN UNIONS s} =
                {v | v extreme_point_of q}` (fun th -> ASM_REWRITE_TAC[th]) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN
  ASM_MESON_TAC[extreme_point_of; SUBSET]);;

let MOI_FRN_SIG_EQ_ONE = prove
 (`!(t:(real^N->bool)->bool) s h x.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ x IN UNIONS t /\ drop(h x) = &1
     ==> x IN UNIONS s`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `x:real^N`] MOI_FRN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x:real^N) IN r` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `r:real^N->bool`; `x:real^N`]
    MOI_FRN_SIG_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real^N->real` STRIP_ASSUME_TAC) THEN
  ABBREV_TAC `V = {v:real^N | v extreme_point_of r}` THEN
  ABBREV_TAC `VS = {v:real^N | v extreme_point_of r /\ v IN UNIONS s}` THEN
  SUBGOAL_THEN `(VS:real^N->bool) SUBSET V` ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["V"; "VS"] THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. v IN V ==> v IN r` ASSUME_TAC THENL
   [EXPAND_TAC "V" THEN REWRITE_TAC[IN_ELIM_THM] THEN
    MESON_TAC[extreme_point_of];
    ALL_TAC] THEN
  SUBGOAL_THEN `!v:real^N. v IN V DIFF VS ==> mu v = &0` ASSUME_TAC THENL
   [MATCH_MP_TAC SUM_POS_EQ_0 THEN
    ASM_SIMP_TAC[SUM_DIFF; FINITE_DIFF] THEN
    CONJ_TAC THENL
     [EXPAND_TAC "V" THEN REWRITE_TAC[IN_DIFF; IN_ELIM_THM] THEN
      ASM_MESON_TAC[];
      UNDISCH_TAC `drop((h:real^N->real^1) x) = &1` THEN
      ASM_REWRITE_TAC[] THEN REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN convex hull VS` MP_TAC THENL
   [REWRITE_TAC[CONVEX_HULL_FINITE; IN_ELIM_THM] THEN
    EXISTS_TAC `mu:real^N->real` THEN REPEAT CONJ_TAC THENL
     [EXPAND_TAC "VS" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_MESON_TAC[];
      UNDISCH_TAC `drop((h:real^N->real^1) x) = &1` THEN
      ASM_REWRITE_TAC[];
      FIRST_X_ASSUM((fun th -> GEN_REWRITE_TAC RAND_CONV [SYM th]) o
        check (fun th -> is_eq(concl th) && rand(concl th) = `x:real^N`)) THEN
      CONV_TAC SYM_CONV THEN MATCH_MP_TAC VSUM_SUPERSET THEN
      ASM_REWRITE_TAC[] THEN REPEAT STRIP_TAC THEN
      SUBGOAL_THEN `(mu:real^N->real) x' = &0` SUBST1_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM SET_TAC[];
        REWRITE_TAC[VECTOR_MUL_LZERO]]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FRN_FULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex hull VS SUBSET r INTER UNIONS (s:(real^N->bool)->bool)`
  MP_TAC THENL
   [MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [EXPAND_TAC "VS" THEN REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN
      MESON_TAC[extreme_point_of];
      ASM_MESON_TAC[FACE_OF_IMP_CONVEX]];
    SET_TAC[]]);;

let MOI_FRN_SIG_POS = prove
 (`!(t:(real^N->bool)->bool) s h r x.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ r IN barycentric_subdivision t /\ x IN r /\
     &0 < drop(h x)
     ==> ~(r INTER UNIONS s = {})`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `r:real^N->bool`; `x:real^N`]
    MOI_FRN_SIG_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `mu:real^N->real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `{v:real^N | v extreme_point_of r /\ v IN UNIONS s} = {}`
  ASSUME_TAC THENL
   [REWRITE_TAC[EXTENSION; IN_ELIM_THM; NOT_IN_EMPTY] THEN
    X_GEN_TAC `v:real^N` THEN STRIP_TAC THEN
    UNDISCH_TAC `r INTER UNIONS s:real^N->bool = {}` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `v:real^N` THEN ASM_MESON_TAC[extreme_point_of];
    ALL_TAC] THEN
  UNDISCH_TAC `&0 < drop((h:real^N->real^1) x)` THEN
  ASM_REWRITE_TAC[SUM_CLAUSES] THEN REAL_ARITH_TAC);;

let MOI_FRN_SIG_SEG = prove
 (`!(t:(real^N->bool)->bool) s h r a b e z.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ r IN barycentric_subdivision t /\
     a IN r /\ b IN r /\ e <= drop(h a) /\ e <= drop(h b) /\
     z IN segment[a,b]
     ==> e <= drop(h z)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_frn_sig t s (h:real^N->real^1)` THEN
  REWRITE_TAC[moi_frn_sig] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real^1` (X_CHOOSE_THEN `y:real^1`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(z:real^N) IN r` ASSUME_TAC THENL
   [SUBGOAL_THEN `convex(r:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  UNDISCH_TAC `(z:real^N) IN segment[a,b]` THEN REWRITE_TAC[IN_SEGMENT] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN
   `drop((h:real^N->real^1) z) = (&1 - u) * drop(h a) + u * drop(h b)`
  SUBST1_TAC THENL
   [SUBGOAL_THEN `(h:real^N->real^1) z = l z + y /\ h a = l a + y /\
                  h b = l b + y` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    FIRST_X_ASSUM((fun th -> REWRITE_TAC[th]) o check (fun th ->
      is_eq(concl th) && lhs(concl th) = `z:real^N`)) THEN
    ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
    REWRITE_TAC[DROP_ADD; DROP_CMUL] THEN REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_TRANS THEN
  EXISTS_TAC `(&1 - u) * e + u * e` THEN CONJ_TAC THENL
   [REAL_ARITH_TAC; ALL_TAC] THEN
  MATCH_MP_TAC REAL_LE_ADD2 THEN CONJ_TAC THEN
  MATCH_MP_TAC REAL_LE_LMUL THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC);;

let MOI_FRN_SIG_AFF = prove
 (`!(t:(real^N->bool)->bool) s h r a b u.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ r IN barycentric_subdivision t /\
     a IN r /\ b IN r /\ &0 <= u /\ u <= &1
     ==> drop(h((&1 - u) % a + u % b)) = (&1 - u) * drop(h a) + u * drop(h b)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_frn_sig t s (h:real^N->real^1)` THEN
  REWRITE_TAC[moi_frn_sig] THEN
  DISCH_THEN(MP_TAC o SPEC `r:real^N->bool` o CONJUNCT1 o CONJUNCT2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `l:real^N->real^1` (X_CHOOSE_THEN `y:real^1`
    STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(&1 - u) % a + u % b IN (r:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `convex(r:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`a:real^N`; `b:real^N`]) THEN
    ASM_REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SEGMENT] THEN EXISTS_TAC `u:real` THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(h:real^N->real^1) ((&1 - u) % a + u % b) =
                l((&1 - u) % a + u % b) + y /\ h a = l a + y /\
                h b = l b + y` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[]; ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN ASM_SIMP_TAC[LINEAR_ADD; LINEAR_CMUL] THEN
  REWRITE_TAC[DROP_ADD; DROP_CMUL] THEN REAL_ARITH_TAC);;

let moi_frn_wset = new_definition
 `moi_frn_wset (t:(real^N->bool)->bool) (h:real^N->real^1) e =
    {x | x IN UNIONS t /\ &1 - e <= drop(h x)}`;;

let moi_frn_wpt = new_definition
 `moi_frn_wpt (s:(real^N->bool)->bool) e (r:real^N->bool) =
    (&1 - e) % simplex_barycentre (r INTER UNIONS s) +
    e % simplex_barycentre r`;;

let MOI_FRN_WPT = prove
 (`!(t:(real^N->bool)->bool) s h e r.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ &0 < e /\ e < &1 /\ moi_frn_vp t s r
     ==> moi_frn_wpt s e r IN relative_interior r /\
         moi_frn_wpt s e r IN moi_frn_wset t h e /\
         ~(moi_frn_wpt s e r IN UNIONS s)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FRN_VP_BARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_frn_vp t s (r:real^N->bool)` THEN
  REWRITE_TAC[moi_frn_vp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FRN_FULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `simplex_barycentre (r INTER UNIONS s) IN
                (r INTER UNIONS s:real^N->bool)` ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (r INTER UNIONS s:real^N->bool)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_BAR_SIMPLEX_BARYCENTRE_IN THEN
    EXISTS_TAC `n:int` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `moi_frn_wpt s e r IN relative_interior (r:real^N->bool)`
  ASSUME_TAC THENL
   [SUBGOAL_THEN
     `segment(simplex_barycentre r,
              simplex_barycentre (r INTER UNIONS s)) SUBSET
      relative_interior (r:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX];
        MATCH_MP_TAC(REWRITE_RULE[SUBSET] CLOSURE_SUBSET) THEN ASM SET_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SEGMENT; moi_frn_wpt] THEN CONJ_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `&1 - e` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[moi_frn_wset; IN_ELIM_THM] THEN CONJ_TAC THENL
     [SUBGOAL_THEN
       `moi_frn_wpt s e r IN UNIONS (barycentric_subdivision t:
                                      (real^N->bool)->bool)` MP_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^N->bool` THEN
        ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[moi_frn_wpt] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `r:real^N->bool`;
                   `simplex_barycentre (r INTER UNIONS s):real^N`;
                   `simplex_barycentre r:real^N`; `e:real`] MOI_FRN_SIG_AFF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM SET_TAC[]; ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `h:real^N->real^1`;
                   `simplex_barycentre (r INTER UNIONS s):real^N`]
      MOI_FRN_SIG_ONE) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `simplex_barycentre r:real^N`]
      MOI_FRN_SIG_RANGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
        MOI_FRN_N_FACTS) THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN `&0 <= e * drop((h:real^N->real^1) (simplex_barycentre r))`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
                  REAL_ARITH_TAC];
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `r:real^N->bool`] MOI_FRN_RELINT_NOT_S) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[]]);;

let MOI_FRN_WSET_FACTS = prove
 (`!(t:(real^N->bool)->bool) h e x.
     x IN moi_frn_wset t h e <=> x IN UNIONS t /\ &1 - e <= drop(h x)`,
  REWRITE_TAC[moi_frn_wset; IN_ELIM_THM]);;

let MOI_FRN_WPIECE_CC = prove
 (`!(t:(real^N->bool)->bool) s h e r x.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ &0 < e /\ e < &1 /\ moi_frn_vp t s r /\
     x IN moi_frn_wset t h e /\ x IN relative_interior r
     ==> connected_component (moi_frn_wset t h e DIFF UNIONS s) x
           (moi_frn_wpt s e r)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `e:real`; `r:real^N->bool`]
    MOI_FRN_WPT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_frn_vp t s (r:real^N->bool)` THEN
  REWRITE_TAC[moi_frn_vp] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FRN_RELINT_NOT_S) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOI_FRN_WSET_FACTS]) THEN
  REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `segment[x:real^N,moi_frn_wpt s e r]` THEN
  REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN
  SUBGOAL_THEN
   `segment[x:real^N,moi_frn_wpt s e r] SUBSET relative_interior r`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `convex(relative_interior(r:real^N->bool))` MP_TAC THENL
     [MATCH_MP_TAC CONVEX_RELATIVE_INTERIOR THEN
      ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX];
      ALL_TAC] THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; MOI_FRN_WSET_FACTS] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN r` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(z:real^N) IN UNIONS (barycentric_subdivision t)` MP_TAC
    THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_FRN_SIG_SEG THEN
    MAP_EVERY EXISTS_TAC
     [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`; `r:real^N->bool`;
      `x:real^N`; `moi_frn_wpt s e r:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
    ASM SET_TAC[]]);;

let MOI_FRN_WADJ_CC = prove
 (`!(t:(real^N->bool)->bool) s h e r r'.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ &0 < e /\ e < &1 /\
     moi_frn_vp t s r /\ moi_frn_vp t s r' /\ r SUBSET r'
     ==> connected_component (moi_frn_wset t h e DIFF UNIONS s)
           (moi_frn_wpt s e r) (moi_frn_wpt s e r')`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `e:real`; `r:real^N->bool`]
    MOI_FRN_WPT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `e:real`; `r':real^N->bool`]
    MOI_FRN_WPT) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  UNDISCH_TAC `moi_frn_vp t s (r:real^N->bool)` THEN
  UNDISCH_TAC `moi_frn_vp t s (r':real^N->bool)` THEN
  REWRITE_TAC[moi_frn_vp] THEN REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r':real^N->bool`] MOI_FRN_RELINT_NOT_S) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOI_FRN_WSET_FACTS]) THEN
  SUBGOAL_THEN `moi_frn_wpt s e r IN (r':real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_frn_wpt s e r' IN (r':real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN
   `segment(moi_frn_wpt s e r',moi_frn_wpt s e r) SUBSET
    relative_interior (r':real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX];
      ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET]];
    ALL_TAC] THEN
  SUBGOAL_THEN `convex(r':real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  REWRITE_TAC[connected_component] THEN
  EXISTS_TAC `segment[moi_frn_wpt s e r:real^N,moi_frn_wpt s e r']` THEN
  REWRITE_TAC[CONNECTED_SEGMENT; ENDS_IN_SEGMENT] THEN
  REWRITE_TAC[SUBSET; IN_DIFF; MOI_FRN_WSET_FACTS] THEN
  X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(z:real^N) IN r'` ASSUME_TAC THENL
   [UNDISCH_TAC `convex(r':real^N->bool)` THEN
    REWRITE_TAC[CONVEX_CONTAINS_SEGMENT] THEN
    DISCH_THEN(MP_TAC o SPECL [`moi_frn_wpt s e r:real^N`;
                               `moi_frn_wpt s e r':real^N`]) THEN
    ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [SUBGOAL_THEN `(z:real^N) IN UNIONS (barycentric_subdivision t)` MP_TAC
    THENL
     [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r':real^N->bool` THEN
      ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[]];
    MATCH_MP_TAC MOI_FRN_SIG_SEG THEN
    MAP_EVERY EXISTS_TAC
     [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`; `r':real^N->bool`;
      `moi_frn_wpt s e r:real^N`; `moi_frn_wpt s e r':real^N`] THEN
    ASM_REWRITE_TAC[];
    UNDISCH_TAC `(z:real^N) IN segment[moi_frn_wpt s e r,moi_frn_wpt s e r']`
    THEN REWRITE_TAC[SEGMENT_CLOSED_OPEN] THEN
    ONCE_REWRITE_TAC[CONJUNCT2 SEGMENT_SYM] THEN ASM SET_TAC[]]);;

let MOI_FRN_WCOVER = prove
 (`!(t:(real^N->bool)->bool) s h e x.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ e < &1 /\
     x IN moi_frn_wset t h e /\ ~(x IN UNIONS s)
     ==> ?r. moi_frn_vp t s r /\ x IN relative_interior r`,
  REPEAT STRIP_TAC THEN
  RULE_ASSUM_TAC(REWRITE_RULE[MOI_FRN_WSET_FACTS]) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `x:real^N`] MOI_FRN_CARRIER) THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[moi_frn_vp] THEN
  SUBGOAL_THEN `(x:real^N) IN r` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FRN_SIG_POS THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `h:real^N->real^1`;
                          `x:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ASM SET_TAC[]]);;

let MOI_FRN_W_CONN_DIFF = prove
 (`!(t:(real^N->bool)->bool) s h e T0.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ &0 < e /\ e < &1 /\
     connected (derived_nbhd t s DIFF UNIONS s) /\ moi_frn_vp t s T0
     ==> connected (moi_frn_wset t h e DIFF UNIONS s)`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC
   `W = moi_frn_wset t h e DIFF UNIONS (s:(real^N->bool)->bool)` THEN
  ABBREV_TAC
   `X = {r:real^N->bool | moi_frn_vp t s r /\
                          connected_component W (moi_frn_wpt s e T0)
                            (moi_frn_wpt s e r)}` THEN
  SUBGOAL_THEN `!r:real^N->bool. moi_frn_vp t s r ==> r IN X` ASSUME_TAC
  THENL
   [MATCH_MP_TAC MOI_FRN_ONE_CLASS THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [EXPAND_TAC "X" THEN REWRITE_TAC[moi_frn_rclosed; IN_ELIM_THM] THEN
      CONJ_TAC THENL [SIMP_TAC[]; ALL_TAC] THEN
      MAP_EVERY X_GEN_TAC [`r:real^N->bool`; `r':real^N->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 STRIP_ASSUME_TAC
        (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "OR"))) THEN
      ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN
       `connected_component W (moi_frn_wpt s e (r:real^N->bool))
          (moi_frn_wpt s e (r':real^N->bool))`
      MP_TAC THENL
       [EXPAND_TAC "W" THEN REMOVE_THEN "OR" DISJ_CASES_TAC THENL
         [MATCH_MP_TAC MOI_FRN_WADJ_CC THEN ASM_REWRITE_TAC[];
          MATCH_MP_TAC CONNECTED_COMPONENT_SYM THEN
          MATCH_MP_TAC MOI_FRN_WADJ_CC THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      UNDISCH_TAC `connected_component W (moi_frn_wpt s e T0)
                     (moi_frn_wpt s e (r:real^N->bool))` THEN
      MESON_TAC[CONNECTED_COMPONENT_TRANS];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
      EXISTS_TAC `T0:real^N->bool` THEN
      EXPAND_TAC "X" THEN REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN EXPAND_TAC "W" THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                     `h:real^N->real^1`; `e:real`; `T0:real^N->bool`]
        MOI_FRN_WPT) THEN
      ANTS_TAC THENL [ASM_REWRITE_TAC[]; SET_TAC[]]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `W = connected_component W (moi_frn_wpt s e (T0:real^N->bool))`
  SUBST1_TAC THENL
   [MATCH_MP_TAC SUBSET_ANTISYM THEN
    REWRITE_TAC[CONNECTED_COMPONENT_SUBSET] THEN
    REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `e:real`; `x:real^N`]
      MOI_FRN_WCOVER) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN
     `connected_component W x (moi_frn_wpt s e (r:real^N->bool))`
    ASSUME_TAC THENL
     [EXPAND_TAC "W" THEN MATCH_MP_TAC MOI_FRN_WPIECE_CC THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(r:real^N->bool) IN X` MP_TAC THENL
     [ASM_MESON_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "X" THEN REWRITE_TAC[IN_ELIM_THM; IN] THEN
    ASM_MESON_TAC[CONNECTED_COMPONENT_TRANS; CONNECTED_COMPONENT_SYM];
    REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT]]);;

let MOI_FRN_TET_THROUGH = prove
 (`!(t:(real^N->bool)->bool) s y.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     combinatorial_manifold 2 s /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     y IN UNIONS s
     ==> ?r. moi_frn_vp t s r /\ y IN r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`s:(real^N->bool)->bool`; `y:real^N`] MOI_FRN_KPURE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `D:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `D:real^N->bool`] MOI_FRN_KTRI_TWO) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real^N->bool` (X_CHOOSE_THEN `T2:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (MP_TAC o GEN_REWRITE_RULE I [EXTENSION])))) THEN
  DISCH_THEN(MP_TAC o SPEC `T1:real^N->bool`) THEN
  REWRITE_TAC[IN_ELIM_THM; IN_INSERT] THEN STRIP_TAC THEN
  EXISTS_TAC `T1:real^N->bool` THEN CONJ_TAC THENL
   [MATCH_MP_TAC MOI_FRN_TET_VP THEN EXISTS_TAC `D:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ASM SET_TAC[]]);;

let MOI_FRN_W_CLOSURE = prove
 (`!(t:(real^N->bool)->bool) s h e.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     combinatorial_manifold 2 s /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     moi_frn_sig t s h /\ &0 < e /\ e < &1
     ==> UNIONS s SUBSET closure (moi_frn_wset t h e DIFF UNIONS s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `y:real^N`] MOI_FRN_TET_THROUGH) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FRN_VP_BARY) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(r:real^N->bool) IN barycentric_subdivision t /\
                ~(r SUBSET UNIONS s)` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_frn_vp]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `r:real^N->bool`] MOI_FRN_RELINT_NOT_S) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `convex(r:real^N->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]; ALL_TAC] THEN
  ABBREV_TAC `q:real^N = (&1 - e) % y + e % simplex_barycentre r` THEN
  SUBGOAL_THEN `(q:real^N) IN relative_interior r` ASSUME_TAC THENL
   [SUBGOAL_THEN `segment(simplex_barycentre r,y) SUBSET
                  relative_interior (r:real^N->bool)` MP_TAC THENL
     [MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
    REWRITE_TAC[IN_SEGMENT] THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    EXISTS_TAC `&1 - e` THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ALL_TAC] THEN
    EXPAND_TAC "q" THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(q:real^N) IN r` ASSUME_TAC THENL
   [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
  SUBGOAL_THEN `&1 - e <= drop((h:real^N->real^1) q)` ASSUME_TAC THENL
   [EXPAND_TAC "q" THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `r:real^N->bool`; `y:real^N`;
                   `simplex_barycentre r:real^N`; `e:real`]
      MOI_FRN_SIG_AFF) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THENL
       [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
        ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC];
      ALL_TAC] THEN
    DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `y:real^N`] MOI_FRN_SIG_ONE) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `simplex_barycentre r:real^N`]
      MOI_FRN_SIG_RANGE) THEN
    ANTS_TAC THENL
     [ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `simplex_barycentre r IN
                    UNIONS (barycentric_subdivision t:(real^N->bool)->bool)`
      MP_TAC THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^N->bool` THEN
        ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET];
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    STRIP_TAC THEN
    SUBGOAL_THEN
     `&0 <= e * drop((h:real^N->real^1) (simplex_barycentre r))`
    MP_TAC THENL [MATCH_MP_TAC REAL_LE_MUL THEN ASM_REAL_ARITH_TAC;
                  REAL_ARITH_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(y:real^N = q)` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `segment(y:real^N,q) SUBSET moi_frn_wset t h e DIFF UNIONS s`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `segment(q:real^N,y) SUBSET relative_interior r`
    ASSUME_TAC THENL
     [MATCH_MP_TAC IN_RELATIVE_INTERIOR_CLOSURE_CONVEX_SEGMENT THEN
      ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[CLOSURE_SUBSET; SUBSET];
      ALL_TAC] THEN
    REWRITE_TAC[SUBSET; IN_DIFF; MOI_FRN_WSET_FACTS] THEN
    X_GEN_TAC `z:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(z:real^N) IN relative_interior r` ASSUME_TAC THENL
     [ASM_MESON_TAC[SEGMENT_SYM; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN `(z:real^N) IN r` ASSUME_TAC THENL
     [ASM_MESON_TAC[SUBSET; RELATIVE_INTERIOR_SUBSET]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [SUBGOAL_THEN `(z:real^N) IN UNIONS (barycentric_subdivision t)` MP_TAC
      THENL
       [REWRITE_TAC[IN_UNIONS] THEN EXISTS_TAC `r:real^N->bool` THEN
        ASM_REWRITE_TAC[];
        ASM_REWRITE_TAC[]];
      MATCH_MP_TAC MOI_FRN_SIG_SEG THEN
      MAP_EVERY EXISTS_TAC
       [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
        `r:real^N->bool`; `y:real^N`; `q:real^N`] THEN
      ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
       [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                       `h:real^N->real^1`; `y:real^N`] MOI_FRN_SIG_ONE) THEN
        ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
        MP_TAC(ISPECL [`y:real^N`; `q:real^N`] SEGMENT_OPEN_SUBSET_CLOSED) THEN
        ASM SET_TAC[]];
      ASM SET_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(y:real^N) IN closure(segment(y,q))` MP_TAC THENL
   [ASM_REWRITE_TAC[CLOSURE_SEGMENT; ENDS_IN_SEGMENT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`segment(y:real^N,q)`;
                 `moi_frn_wset t h e DIFF UNIONS s:real^N->bool`]
    SUBSET_CLOSURE) THEN
  ASM_REWRITE_TAC[] THEN SET_TAC[]);;

let MOI_FRN_W_INT = prove
 (`!(t:(real^N->bool)->bool) s h e.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\
     moi_frn_sig t s h /\ &0 < e
     ==> UNIONS s SUBSET
         (subtopology euclidean (UNIONS t)) interior_of (moi_frn_wset t h e)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_N_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MATCH_MP_TAC SUBSET_TRANS THEN
  EXISTS_TAC `{x | x IN UNIONS t /\
                   (h:real^N->real^1) x IN {z:real^1 | z$1 > &1 - e}}` THEN
  CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN X_GEN_TAC `x:real^N` THEN
    DISCH_TAC THEN CONJ_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `x:real^N`] MOI_FRN_SIG_ONE) THEN
    ASM_REWRITE_TAC[drop] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  MATCH_MP_TAC INTERIOR_OF_MAXIMAL THEN CONJ_TAC THENL
   [REWRITE_TAC[SUBSET; IN_ELIM_THM; MOI_FRN_WSET_FACTS; drop] THEN
    REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    MATCH_MP_TAC CONTINUOUS_OPEN_IN_PREIMAGE THEN
    REWRITE_TAC[OPEN_HALFSPACE_COMPONENT_GT] THEN
    ASM_MESON_TAC[moi_frn_sig]]);;

let MOI_FRN_W_SMALL = prove
 (`!(t:(real^N->bool)->bool) s h v.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     moi_frn_sig t s h /\
     open_in (subtopology euclidean (UNIONS t)) v /\ UNIONS s SUBSET v
     ==> ?e. &0 < e /\ e < &1 /\ moi_frn_wset t h e SUBSET v`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SETUP) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_N_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ABBREV_TAC
   `St = UNIONS {r:real^N->bool | r IN barycentric_subdivision t /\
                                  ~(r INTER UNIONS s = {})}` THEN
  SUBGOAL_THEN `compact (UNIONS s:real^N->bool)` ASSUME_TAC THENL
   [MATCH_MP_TAC COMPACT_UNIONS THEN ASM_REWRITE_TAC[] THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN
    ASM_MESON_TAC[simplicial_subcomplex; SUBSET];
    ALL_TAC] THEN
  SUBGOAL_THEN `compact (St:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "St" THEN MATCH_MP_TAC COMPACT_UNIONS THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FDN_LF_COMPACT_MEETS_FINITE THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      REWRITE_TAC[IN_ELIM_THM] THEN REPEAT STRIP_TAC THEN
      MATCH_MP_TAC MOI_FM3_LF_COMPACT THEN
      EXISTS_TAC `barycentric_subdivision t:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `(St:real^N->bool) SUBSET UNIONS t` ASSUME_TAC THENL
   [SUBGOAL_THEN `(St:real^N->bool) SUBSET UNIONS (barycentric_subdivision t)`
    MP_TAC THENL [EXPAND_TAC "St" THEN SET_TAC[]; ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e. e < &1 ==> moi_frn_wset t h e SUBSET (St:real^N->bool)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN REWRITE_TAC[SUBSET; MOI_FRN_WSET_FACTS] THEN
    X_GEN_TAC `x:real^N` THEN STRIP_TAC THEN
    SUBGOAL_THEN `(x:real^N) IN UNIONS (barycentric_subdivision t)` MP_TAC
    THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REWRITE_TAC[IN_UNIONS] THEN
    DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
    EXPAND_TAC "St" THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EXISTS_TAC `r:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FRN_SIG_POS THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `h:real^N->real^1`;
                          `x:real^N`] THEN
    ASM_REWRITE_TAC[] THEN ASM_REAL_ARITH_TAC;
    ALL_TAC] THEN
  UNDISCH_TAC `open_in (subtopology euclidean (UNIONS t)) (v:real^N->bool)` THEN
  REWRITE_TAC[OPEN_IN_OPEN] THEN
  DISCH_THEN(X_CHOOSE_THEN `G:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_CASES_TAC `(St:real^N->bool) DIFF G = {}` THENL
   [EXISTS_TAC `&1 / &2` THEN CONV_TAC REAL_RAT_REDUCE_CONV THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `&1 / &2`) THEN
    CONV_TAC REAL_RAT_REDUCE_CONV THEN
    REWRITE_TAC[MOI_FRN_WSET_FACTS; SUBSET] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`\x:real^N. drop((h:real^N->real^1) x)`;
                 `(St:real^N->bool) DIFF G`] CONTINUOUS_ATTAINS_SUP) THEN
  ANTS_TAC THENL
   [ASM_SIMP_TAC[COMPACT_DIFF] THEN
    REWRITE_TAC[o_DEF; LIFT_DROP; ETA_AX] THEN
    MATCH_MP_TAC CONTINUOUS_ON_SUBSET THEN
    EXISTS_TAC `UNIONS t:real^N->bool` THEN
    CONJ_TAC THENL [ASM_MESON_TAC[moi_frn_sig]; ASM SET_TAC[]];
    ALL_TAC] THEN
  REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(x0:real^N) IN UNIONS t /\ ~(x0 IN UNIONS s)`
  STRIP_ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `x0:real^N`] MOI_FRN_SIG_RANGE) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(drop((h:real^N->real^1) x0) = &1)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `x0:real^N`] MOI_FRN_SIG_EQ_ONE) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `(&1 - drop((h:real^N->real^1) x0)) / &2` THEN
  REPEAT CONJ_TAC THENL [ASM_REAL_ARITH_TAC; ASM_REAL_ARITH_TAC; ALL_TAC] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  SUBGOAL_THEN `(x:real^N) IN St` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `(&1 - drop((h:real^N->real^1) x0)) / &2`) THEN
    ANTS_TAC THENL [ASM_REAL_ARITH_TAC; ASM SET_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN
               moi_frn_wset t h ((&1 - drop((h:real^N->real^1) x0)) / &2)` THEN
  REWRITE_TAC[MOI_FRN_WSET_FACTS] THEN STRIP_TAC THEN
  ASM_CASES_TAC `(x:real^N) IN G` THENL [ASM SET_TAC[]; ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN
  ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  ASM_REAL_ARITH_TAC);;

let MOI_FRN_TWO_SIDED_CONN = prove
 (`!x s:real^N->bool.
     connected s /\ ~(s = {})
     ==> (two_sided_in x s <=>
          ?v. open_in (subtopology euclidean x) v /\ s SUBSET v /\
              !w. w SUBSET v /\ connected w /\
                  s SUBSET (subtopology euclidean x) interior_of w
                  ==> ~connected (w DIFF s))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[two_sided_in] THEN
  SUBGOAL_THEN `components (s:real^N->bool) = {s}` SUBST1_TAC THENL
   [ASM_REWRITE_TAC[COMPONENTS_EQ_SING]; ALL_TAC] THEN
  REWRITE_TAC[FORALL_IN_INSERT; NOT_IN_EMPTY]);;

let MOI_FRN_ONE_NOT_TWO_SIDED = prove
 (`!(t:(real^N->bool)->bool) s.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     combinatorial_manifold 2 s /\ connected (UNIONS s) /\
     ~(UNIONS s = {}) /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     connected (derived_nbhd t s DIFF UNIONS s)
     ==> ~two_sided_in (UNIONS t) (UNIONS s)`,
  REPEAT STRIP_TAC THEN
  UNDISCH_TAC `two_sided_in (UNIONS t) (UNIONS s:real^N->bool)` THEN
  ASM_SIMP_TAC[MOI_FRN_TWO_SIDED_CONN] THEN
  DISCH_THEN(X_CHOOSE_THEN `v:real^N->bool` (CONJUNCTS_THEN2 ASSUME_TAC
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "W")))) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SIG_EXISTS) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_TAC `h:real^N->real^1`) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `v:real^N->bool`] MOI_FRN_W_SMALL) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_SIDES_TWO) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `T1:real^N->bool` (X_CHOOSE_THEN `T2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                 `h:real^N->real^1`; `e:real`; `T1:real^N->bool`]
    MOI_FRN_W_CONN_DIFF) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  REMOVE_THEN "W" (MP_TAC o SPEC `moi_frn_wset t h e:real^N->bool`) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [MATCH_MP_TAC CONNECTED_INTERMEDIATE_CLOSURE THEN
    EXISTS_TAC `moi_frn_wset t h e DIFF UNIONS s:real^N->bool` THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL [SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `h:real^N->real^1`; `e:real`] MOI_FRN_W_CLOSURE) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `moi_frn_wset t h e DIFF UNIONS s:real^N->bool`
      CLOSURE_SUBSET) THEN
    SET_TAC[];
    MATCH_MP_TAC MOI_FRN_W_INT THEN ASM_REWRITE_TAC[]]);;

let MOI_FRN_TWO_TWO_SIDED = prove
 (`!(t:(real^N->bool)->bool) s.
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     combinatorial_manifold 2 s /\ connected (UNIONS s) /\
     ~(UNIONS s = {}) /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v))) /\
     FINITE (components (derived_nbhd t s DIFF UNIONS s)) /\
     CARD (components (derived_nbhd t s DIFF UNIONS s)) = 2
     ==> two_sided_in (UNIONS t) (UNIONS s)`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`]
    MOI_FRN_N_FACTS) THEN ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `?K1 K2. ~(K1 = K2) /\
            components (derived_nbhd t s DIFF UNIONS s) = {K1, K2:real^N->bool}`
  STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_SCF_HAS_SIZE_2] THEN ASM_REWRITE_TAC[HAS_SIZE];
    ALL_TAC] THEN
  ASM_SIMP_TAC[MOI_FRN_TWO_SIDED_CONN] THEN
  EXISTS_TAC `(subtopology euclidean (UNIONS t)) interior_of
              (derived_nbhd t s:real^N->bool)` THEN
  ASM_REWRITE_TAC[OPEN_IN_INTERIOR_OF] THEN
  X_GEN_TAC `w:real^N->bool` THEN STRIP_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `(w:real^N->bool) SUBSET derived_nbhd t s` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`subtopology euclidean (UNIONS t:real^N->bool)`;
                   `derived_nbhd t s:real^N->bool`] INTERIOR_OF_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `?y:real^N. y IN UNIONS s` STRIP_ASSUME_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN
   `!K:real^N->bool. K IN components (derived_nbhd t s DIFF UNIONS s)
                     ==> ~((w DIFF UNIONS s) INTER K = {})`
  ASSUME_TAC THENL
   [X_GEN_TAC `K:real^N->bool` THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `s:(real^N->bool)->bool`;
                   `K:real^N->bool`] MOI_FRN_SIDES_ACCUM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS t:real^N->bool)`;
                   `w:real^N->bool`] OPEN_IN_INTERIOR_OF) THEN
    REWRITE_TAC[OPEN_IN_OPEN] THEN
    DISCH_THEN(X_CHOOSE_THEN `G:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `(y:real^N) IN G` ASSUME_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `~(G INTER closure K:real^N->bool = {})` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    ASM_SIMP_TAC[OPEN_INTER_CLOSURE_EQ_EMPTY] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    EXISTS_TAC `z:real^N` THEN
    SUBGOAL_THEN `(z:real^N) IN derived_nbhd t s DIFF UNIONS s`
    ASSUME_TAC THENL
     [ASM_MESON_TAC[IN_COMPONENTS_SUBSET; SUBSET]; ALL_TAC] THEN
    SUBGOAL_THEN
     `(z:real^N) IN (subtopology euclidean (UNIONS t)) interior_of w`
    MP_TAC THENL
     [ASM_REWRITE_TAC[IN_INTER] THEN ASM SET_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`subtopology euclidean (UNIONS t:real^N->bool)`;
                   `w:real^N->bool`] INTERIOR_OF_SUBSET) THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(w DIFF UNIONS s:real^N->bool) SUBSET K1` ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o SPEC `K1:real^N->bool`) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`derived_nbhd t s DIFF UNIONS s:real^N->bool`;
                   `K1:real^N->bool`; `z:real^N`] MOI_FRN_COMP_EQ) THEN
    ASM_REWRITE_TAC[IN_INSERT] THEN DISCH_THEN SUBST1_TAC THEN
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `K2:real^N->bool`) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN
  MP_TAC(ISPECL [`derived_nbhd t s DIFF UNIONS s:real^N->bool`;
                 `K1:real^N->bool`; `K2:real^N->bool`] COMPONENTS_NONOVERLAP) THEN
  ASM_REWRITE_TAC[IN_INSERT] THEN ASM SET_TAC[]);;

let SURFACE_NBHD_SIDES = prove
 (`!(t:(real^N->bool)->bool) (s:(real^N->bool)->bool).
     lf_simplicial_complex t /\ simplicial_subcomplex s t /\ FINITE s /\
     combinatorial_manifold 2 s /\ connected (UNIONS s) /\ ~(UNIONS s = {}) /\
     (!v. {v} IN s ==> pl_sphere 2 (UNIONS (simplicial_link t v)))
     ==> FINITE (components (derived_nbhd t s DIFF UNIONS s)) /\
         1 <= CARD (components (derived_nbhd t s DIFF UNIONS s)) /\
         CARD (components (derived_nbhd t s DIFF UNIONS s)) <= 2 /\
         (!k. k IN components (derived_nbhd t s DIFF UNIONS s)
              ==> UNIONS s SUBSET closure k) /\
         (CARD (components (derived_nbhd t s DIFF UNIONS s)) = 2 <=>
          two_sided_in (UNIONS t) (UNIONS s))`,
  REPEAT GEN_TAC THEN DISCH_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_FRN_SIDES_FINITE) THEN STRIP_TAC THEN
  FIRST_X_ASSUM(STRIP_ASSUME_TAC o check (is_conj o concl)) THEN
  ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FRN_SIDES_ACCUM THEN
    EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  EQ_TAC THENL
   [DISCH_TAC THEN MATCH_MP_TAC MOI_FRN_TWO_TWO_SIDED THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ONCE_REWRITE_TAC[GSYM CONTRAPOS_THM] THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_FRN_ONE_NOT_TWO_SIDED THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN
   `CARD (components (derived_nbhd t s DIFF UNIONS s:real^N->bool)) = 1`
  ASSUME_TAC THENL [ASM_ARITH_TAC; ALL_TAC] THEN
  MP_TAC(ISPEC `components (derived_nbhd t s DIFF UNIONS s:real^N->bool)`
    MOI_FRN_SA_CARD_EQ_1) THEN
  ASM_REWRITE_TAC[COMPONENTS_EQ_SING_EXISTS] THEN SIMP_TAC[]);;


