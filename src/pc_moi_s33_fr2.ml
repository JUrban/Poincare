(* ========================================================================= *)
(* pc_moi_s33_fr2: the 2D derived frontier, used in pc_moi_s33_gp (Moise     *)
(* GTM 47, Sec 33, Lemma 9).  Main theorems:                                 *)
(*   MOI_S3F2_DFR_CHAIN: the derived frontier is the union of the hulls of   *)
(*     the barycentres of nonempty vp chains of the first derived (any       *)
(*     dimension);                                                           *)
(*   MOI_S3F2_DFR_CIRCLES: in dimension at most 2, with plane points on the  *)
(*     vp edges, it has finitely many components, each a PL circle;          *)
(*   MOI_S3F2_DFR_EDGE_STAR: near the barycentre of a vp edge it is the      *)
(*     union of the two segments to the barycentres of the two triangles;    *)
(*   MOI_S3F2_LOCAL_EDGE: the local edge lemma (two triangles at an edge     *)
(*     with a plane point).                                                  *)
(* Route: fullness of the subdivided subcomplex, vp simplices of dimension 1 *)
(* or 2, two vp edges per vp triangle, the vp-chain complex of dimension at  *)
(* most 1 and MOI_S4L_CM1_CIRCLES.                                           *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_nb2.ml";;
needs "src/pc_moi_pl1m.ml";;
needs "src/pc_moi_s28_trib.ml";;
needs "src/pc_moi_smo_cf.ml";;
needs "src/pc_moi_assembly.ml";;

prioritize_real();;
type_invention_error := true;;

(* ------------------------------------------------------------------------- *)
(* Part 1: the derived frontier of an arbitrary subcomplex.  In the        *)
(* first derived t' the subcomplex l' is full, so a point lies in the       *)
(* frontier of the second-derived neighbourhood of l exactly when it lies   *)
(* in the hull of the barycentres of a nonempty chain of t' all of whose    *)
(* members meet |l| without lying in it (any dimension).                     *)
(* ------------------------------------------------------------------------- *)

let MOI_S3F2_CHAIN_MIN = prove
 (`!c (f:(real^N->bool)->bool).
     moi_bar_chain c f /\ ~(f = {})
     ==> INTERS f IN f /\ !s. s IN f ==> INTERS f SUBSET s`,
  REWRITE_TAC[moi_bar_chain] THEN REPEAT STRIP_TAC THENL
   [MATCH_MP_TAC INTERS_IN_CHAIN THEN ASM_REWRITE_TAC[];
    REWRITE_TAC[SUBSET; IN_INTERS] THEN ASM_MESON_TAC[]]);;

let MOI_S3F2_CARRIER_SUB = prove
 (`!c (f:(real^N->bool)->bool) h x.
     moi_bar_complex c /\ moi_bar_chain c f /\ moi_bar_chain c h /\
     x IN relative_interior (convex hull (IMAGE simplex_barycentre f)) /\
     x IN convex hull (IMAGE simplex_barycentre h)
     ==> f SUBSET h`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `h:(real^N->bool)->bool`; `x:real^N`]
                MOI_BAR_CHAIN_HULL_RI) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(f:(real^N->bool)->bool) = g` (fun th -> ASM_REWRITE_TAC[th]) THEN
  MATCH_MP_TAC MOI_BAR_CHAIN_RI_UNIQUE THEN
  MAP_EVERY EXISTS_TAC [`c:(real^N->bool)->bool`; `x:real^N`] THEN
  ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET]);;

(* A chain of the first derived meets |l| exactly when it has a member in   *)
(* the first derived of l.                                                   *)

let MOI_S3F2_CHAIN_MEETS = prove
 (`!(t:(real^N->bool)->bool) l h.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     moi_bar_chain (barycentric_subdivision t) h /\
     ~(convex hull (IMAGE simplex_barycentre h) INTER UNIONS l = {})
     ==> ?q. q IN h /\ q IN barycentric_subdivision l /\ ~(q = {}) /\
             q SUBSET UNIONS l`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                 `barycentric_subdivision (l:(real^N->bool)->bool)`;
                 `h:(real^N->bool)->bool`] MOI_FRN_FULL_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
  SUBGOAL_THEN `~((h:(real^N->bool)->bool) INTER barycentric_subdivision l = {})`
  MP_TAC THENL
   [DISCH_TAC THEN
    UNDISCH_TAC `~(convex hull (IMAGE simplex_barycentre (h:(real^N->bool)->bool)) INTER
                   UNIONS l = {})` THEN
    UNDISCH_TAC `convex hull (IMAGE simplex_barycentre (h:(real^N->bool)->bool)) INTER
                 UNIONS l =
                 convex hull (IMAGE simplex_barycentre (h INTER barycentric_subdivision l))` THEN
    ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [REWRITE_TAC[MEMBER_NOT_EMPTY] THEN DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool)) h` THEN
    REWRITE_TAC[moi_bar_chain] THEN ASM_REWRITE_TAC[];
    UNDISCH_TAC `UNIONS (barycentric_subdivision (l:(real^N->bool)->bool)) = UNIONS l` THEN
    DISCH_THEN(SUBST1_TAC o SYM) THEN
    MATCH_MP_TAC(SET_RULE `(x:real^N->bool) IN s ==> x SUBSET UNIONS s`) THEN
    FIRST_ASSUM ACCEPT_TAC]);;

let MOI_S3F2_DFR_CHAIN = prove
 (`!(t:(real^N->bool)->bool) l x.
     lf_simplicial_complex t /\ simplicial_subcomplex l t
     ==> (x IN derived_frontier t l <=>
          ?c. moi_bar_chain (barycentric_subdivision t) c /\ ~(c = {}) /\
              (!f. f IN c ==> moi_frn_vp t l f) /\
              x IN convex hull (IMAGE simplex_barycentre c))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `x:real^N`]
                MOI_FN2_FRONTIER_NC) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN EQ_TAC THENL
   [(* a frontier point lies in a chain of vp simplices *)
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC (X_CHOOSE_THEN `s:real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `(s:real^N->bool) IN barycentric_subdivision (barycentric_subdivision t)` THEN
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `g:(real^N->bool)->bool`; `x:real^N`] MOI_BAR_CHAIN_HULL_RI) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool)) c`
    ASSUME_TAC THENL [ASM_MESON_TAC[MOI_BAR_CHAIN_SUBSET]; ALL_TAC] THEN
    EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(x:real^N) IN relative_interior (convex hull (IMAGE simplex_barycentre
                     ({}:(real^N->bool)->bool)))` THEN
      REWRITE_TAC[MOI_BAR_CHAIN_EMPTY_RI];
      ALL_TAC;
      MP_TAC(ISPEC `convex hull (IMAGE simplex_barycentre (c:(real^N->bool)->bool))`
                   RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(x:real^N) IN relative_interior (convex hull (IMAGE simplex_barycentre
                     (c:(real^N->bool)->bool)))` THEN SET_TAC[]] THEN
    X_GEN_TAC `f:real^N->bool` THEN DISCH_TAC THEN REWRITE_TAC[moi_frn_vp] THEN
    SUBGOAL_THEN `(f:real^N->bool) IN barycentric_subdivision t /\ ~(f = {})`
    STRIP_ASSUME_TAC THENL
     [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool)) c` THEN
      REWRITE_TAC[moi_bar_chain] THEN ASM_MESON_TAC[SUBSET];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [(* f meets |l|, through a neighbourhood simplex at x *)
      UNDISCH_TAC `(x:real^N) IN derived_nbhd t l` THEN
      REWRITE_TAC[derived_nbhd; IN_UNIONS; IN_ELIM_THM] THEN
      DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
      UNDISCH_TAC `(r:real^N->bool) IN barycentric_subdivision (barycentric_subdivision t)` THEN
      REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool`
        (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
      SUBGOAL_THEN `(c:(real^N->bool)->bool) SUBSET h` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_S3F2_CARRIER_SUB THEN
        MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                              `x:real^N`] THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                     `h:(real^N->bool)->bool`] MOI_S3F2_CHAIN_MEETS) THEN
      ASM_REWRITE_TAC[] THEN
      DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
      SUBGOAL_THEN `(q:real^N->bool) SUBSET f \/ f SUBSET q` MP_TAC THENL
       [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool)) h` THEN
        REWRITE_TAC[moi_bar_chain] THEN ASM_MESON_TAC[SUBSET];
        ALL_TAC] THEN
      UNDISCH_TAC `~(q:real^N->bool = {})` THEN UNDISCH_TAC `~(f:real^N->bool = {})` THEN
      UNDISCH_TAC `(q:real^N->bool) SUBSET UNIONS l` THEN SET_TAC[];
      (* f does not lie in |l|: otherwise the simplex at x would be a neighbourhood one *)
      DISCH_TAC THEN
      SUBGOAL_THEN `(f:real^N->bool) IN barycentric_subdivision l` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_FRN_FULL_SUBSET THEN EXISTS_TAC `t:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      UNDISCH_TAC `~(convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool)) IN
                     derived_nbhd_complex t l)` THEN
      REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM] THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre (g:(real^N->bool)->bool))` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `g:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `simplex_barycentre (f:real^N->bool)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC HULL_INC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN
          UNDISCH_TAC `(c:(real^N->bool)->bool) SUBSET g` THEN
          UNDISCH_TAC `(f:real^N->bool) IN c` THEN SET_TAC[];
          UNDISCH_TAC `(f:real^N->bool) SUBSET UNIONS l` THEN
          MATCH_MP_TAC(SET_RULE `(x:real^N) IN s ==> s SUBSET t ==> x IN t`) THEN
          MATCH_MP_TAC MOI_BAR_CHAIN_BARYCENTRE_IN THEN
          MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                                `c:(real^N->bool)->bool`] THEN
          ASM_REWRITE_TAC[]];
        MATCH_MP_TAC FACE_OF_REFL THEN REWRITE_TAC[CONVEX_CONVEX_HULL]]];
    (* a chain of vp simplices lies in the frontier *)
    DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                   `c:(real^N->bool)->bool`] MOI_S3F2_CHAIN_MIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    SUBGOAL_THEN `?f0:real^N->bool. f0 IN c /\ !s. s IN c ==> f0 SUBSET s`
    STRIP_ASSUME_TAC THENL
     [EXISTS_TAC `INTERS (c:(real^N->bool)->bool)` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `(f0:real^N->bool) IN barycentric_subdivision t /\
                  ~(f0 INTER UNIONS l = {}) /\ ~(f0 SUBSET UNIONS l)`
    STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[moi_frn_vp]; ALL_TAC] THEN
    SUBGOAL_THEN `?n. n simplex (f0:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `f0:real^N->bool`] MOI_FRN_FULL) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
    CONJ_TAC THENL
     [(* x is in the neighbourhood: add the trace f0 INTER |l| below f0 *)
      REWRITE_TAC[derived_nbhd; IN_UNIONS; IN_ELIM_THM] THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre
                     (((f0:real^N->bool) INTER UNIONS l) INSERT c))` THEN
      SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool))
                      (((f0:real^N->bool) INTER UNIONS l) INSERT c)` ASSUME_TAC THENL
       [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool)) c` THEN
        REWRITE_TAC[moi_bar_chain] THEN STRIP_TAC THEN
        REWRITE_TAC[moi_bar_chain] THEN REPEAT CONJ_TAC THENL
         [REWRITE_TAC[INSERT_SUBSET] THEN CONJ_TAC THENL
           [UNDISCH_TAC `simplicial_subcomplex (barycentric_subdivision (l:(real^N->bool)->bool))
                          (barycentric_subdivision t)` THEN
            REWRITE_TAC[simplicial_subcomplex] THEN
            UNDISCH_TAC `(f0:real^N->bool) INTER UNIONS l IN barycentric_subdivision l` THEN
            SET_TAC[];
            FIRST_ASSUM ACCEPT_TAC];
          ASM_REWRITE_TAC[FINITE_INSERT];
          ASM_REWRITE_TAC[IN_INSERT];
          REWRITE_TAC[IN_INSERT] THEN
          MAP_EVERY X_GEN_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
          DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN ASSUME_TAC)
            (DISJ_CASES_THEN ASSUME_TAC)) THEN
          ASM_REWRITE_TAC[SUBSET_REFL] THEN
          TRY(DISJ1_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
              EXISTS_TAC `f0:real^N->bool` THEN ASM_SIMP_TAC[INTER_SUBSET] THEN NO_TAC) THEN
          TRY(DISJ2_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
              EXISTS_TAC `f0:real^N->bool` THEN ASM_SIMP_TAC[INTER_SUBSET] THEN NO_TAC) THEN
          ASM_SIMP_TAC[]];
        ALL_TAC] THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
        EXISTS_TAC `((f0:real^N->bool) INTER UNIONS l) INSERT c` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
        EXISTS_TAC `simplex_barycentre ((f0:real^N->bool) INTER UNIONS l)` THEN CONJ_TAC THENL
         [MATCH_MP_TAC HULL_INC THEN MATCH_MP_TAC FUN_IN_IMAGE THEN REWRITE_TAC[IN_INSERT];
          SUBGOAL_THEN `simplex_barycentre ((f0:real^N->bool) INTER UNIONS l) IN
                        f0 INTER UNIONS l` MP_TAC THENL
           [MATCH_MP_TAC MOI_BAR_CHAIN_BARYCENTRE_IN THEN
            MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                                  `((f0:real^N->bool) INTER UNIONS l) INSERT c`] THEN
            ASM_REWRITE_TAC[IN_INSERT];
            SET_TAC[]]];
        UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre c)` THEN
        MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^N) IN s ==> x IN t`) THEN
        MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
        REWRITE_TAC[SUBSET; IN_INSERT] THEN MESON_TAC[]];
      ALL_TAC] THEN
    (* a vertex w of f0 outside |l| gives a simplex at x missing the neighbourhood *)
    SUBGOAL_THEN `?w:real^N. w extreme_point_of f0 /\ ~(w IN UNIONS l)` STRIP_ASSUME_TAC THENL
     [MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN
      DISCH_THEN(MP_TAC o REWRITE_RULE[NOT_EXISTS_THM; TAUT `~(a /\ ~b) <=> a ==> b`]) THEN
      DISCH_TAC THEN
      UNDISCH_TAC `~((f0:real^N->bool) SUBSET UNIONS l)` THEN REWRITE_TAC[] THEN
      SUBGOAL_THEN `(f0:real^N->bool) = convex hull {v | v extreme_point_of f0}`
      SUBST1_TAC THENL
       [MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN
        ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT];
        ALL_TAC] THEN
      MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(f0:real^N->bool) INTER UNIONS l` THEN
      REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
       [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `v:real^N` THEN
        DISCH_TAC THEN CONJ_TAC THENL
         [ASM_MESON_TAC[extreme_point_of]; ASM_MESON_TAC[]];
        ASM_MESON_TAC[FACE_OF_IMP_CONVEX]];
      ALL_TAC] THEN
    SUBGOAL_THEN `{w:real^N} IN barycentric_subdivision t /\ (w:real^N) IN f0`
    STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC MOI_BAR_COMPLEX_FACE THEN EXISTS_TAC `f0:real^N->bool` THEN
        ASM_REWRITE_TAC[FACE_OF_SING];
        ASM_MESON_TAC[extreme_point_of]];
      ALL_TAC] THEN
    SUBGOAL_THEN `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool))
                    ({w:real^N} INSERT c)` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool)) c` THEN
      REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; FINITE_INSERT; IN_INSERT] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY; NOT_EMPTY_INSERT] THEN
      MAP_EVERY X_GEN_TAC [`s1:real^N->bool`; `s2:real^N->bool`] THEN
      DISCH_THEN(CONJUNCTS_THEN2 (DISJ_CASES_THEN ASSUME_TAC)
        (DISJ_CASES_THEN ASSUME_TAC)) THEN
      ASM_REWRITE_TAC[SUBSET_REFL] THEN
      TRY(DISJ1_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `f0:real^N->bool` THEN ASM_SIMP_TAC[SING_SUBSET] THEN NO_TAC) THEN
      TRY(DISJ2_TAC THEN MATCH_MP_TAC SUBSET_TRANS THEN
          EXISTS_TAC `f0:real^N->bool` THEN ASM_SIMP_TAC[SING_SUBSET] THEN NO_TAC) THEN
      ASM_SIMP_TAC[];
      ALL_TAC] THEN
    EXISTS_TAC `convex hull (IMAGE simplex_barycentre ({w:real^N} INSERT c))` THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN EXISTS_TAC `{w:real^N} INSERT c` THEN
      ASM_REWRITE_TAC[];
      UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre c)` THEN
      MATCH_MP_TAC(SET_RULE `s SUBSET t ==> (x:real^N) IN s ==> x IN t`) THEN
      MATCH_MP_TAC HULL_MONO THEN MATCH_MP_TAC IMAGE_SUBSET THEN
      REWRITE_TAC[SUBSET; IN_INSERT] THEN MESON_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[derived_nbhd_complex; IN_ELIM_THM; NOT_EXISTS_THM] THEN
    X_GEN_TAC `r:real^N->bool` THEN STRIP_TAC THEN
    UNDISCH_TAC `(r:real^N->bool) IN barycentric_subdivision (barycentric_subdivision t)` THEN
    REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(X_CHOOSE_THEN `h:(real^N->bool)->bool`
      (CONJUNCTS_THEN2 ASSUME_TAC SUBST_ALL_TAC)) THEN
    SUBGOAL_THEN `~(relative_interior (convex hull (IMAGE simplex_barycentre
                     ({w:real^N} INSERT c))) = {})` MP_TAC THENL
     [SIMP_TAC[RELATIVE_INTERIOR_EQ_EMPTY; CONVEX_CONVEX_HULL; CONVEX_HULL_EQ_EMPTY;
               IMAGE_EQ_EMPTY; NOT_INSERT_EMPTY];
      ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `y:real^N` o REWRITE_RULE[GSYM MEMBER_NOT_EMPTY]) THEN
    SUBGOAL_THEN `({w:real^N} INSERT c) SUBSET h` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_S3F2_CARRIER_SUB THEN
      MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`; `y:real^N`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_ASSUM(MATCH_MP_TAC o MATCH_MP (SET_RULE `s SUBSET t ==> (x:real^N) IN s ==> x IN t`) o
        MATCH_MP FACE_OF_IMP_SUBSET o
        check (fun th -> is_binary "face_of" (concl th))) THEN
      MP_TAC(ISPEC `convex hull (IMAGE simplex_barycentre ({w:real^N} INSERT c))`
                   RELATIVE_INTERIOR_SUBSET) THEN
      UNDISCH_TAC `(y:real^N) IN relative_interior (convex hull (IMAGE simplex_barycentre
                     ({w:real^N} INSERT c)))` THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `h:(real^N->bool)->bool`] MOI_S3F2_CHAIN_MEETS) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `{w:real^N} SUBSET q \/ q SUBSET {w}` MP_TAC THENL
     [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool)) h` THEN
      REWRITE_TAC[moi_bar_chain] THEN
      DISCH_THEN(MATCH_MP_TAC o last o CONJUNCTS) THEN ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `({w:real^N} INSERT c) SUBSET h` THEN SET_TAC[];
      ALL_TAC] THEN
    UNDISCH_TAC `~(q:real^N->bool = {})` THEN UNDISCH_TAC `(q:real^N->bool) SUBSET UNIONS l` THEN
    UNDISCH_TAC `~((w:real^N) IN UNIONS l)` THEN SET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 2: in dimension at most 2 the chains of vp simplices are            *)
(* single simplices or an edge in a triangle, so their hulls form a 1-dim   *)
(* complex on the derived frontier.  A vp triangle has exactly two vp       *)
(* edges (fullness); if every vp edge lies in exactly two triangles, every  *)
(* vertex of this complex has degree 2 and the derived frontier is a       *)
(* finite union of PL circles (MOI_S4L_CM1_CIRCLES).                        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3F2_RELINT_EQ = prove
 (`!c (s:real^N->bool) r z.
     moi_bar_complex c /\ s IN c /\ r IN c /\
     z IN relative_interior s /\ z IN relative_interior r ==> s = r`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `r:real^N->bool`]
                MOI_BAR_COMPLEX_INTER) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) INTER r = s /\ s INTER r = r` MP_TAC THENL
   [CONJ_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THENL
     [MP_TAC(ISPECL [`(s:real^N->bool) INTER r`; `s:real^N->bool`]
                    FACE_OF_DISJOINT_RELATIVE_INTERIOR);
      MP_TAC(ISPECL [`(s:real^N->bool) INTER r`; `r:real^N->bool`]
                    FACE_OF_DISJOINT_RELATIVE_INTERIOR)] THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    MP_TAC(ISPEC `r:real^N->bool` RELATIVE_INTERIOR_SUBSET) THEN
    UNDISCH_TAC `(z:real^N) IN relative_interior s` THEN
    UNDISCH_TAC `(z:real^N) IN relative_interior r` THEN SET_TAC[];
    SET_TAC[]]);;

(* Fullness in terms of vertices.                                            *)

let MOI_S3F2_FULL_VERTS = prove
 (`!(t:(real^N->bool)->bool) l s.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     s IN barycentric_subdivision t
     ==> (~(s INTER UNIONS l = {}) <=> ?v. v extreme_point_of s /\ v IN UNIONS l) /\
         (s SUBSET UNIONS l <=> !v. v extreme_point_of s ==> v IN UNIONS l)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `s:real^N->bool`]
                MOI_FRN_FULL) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `convex (s:real^N->bool) /\ compact s` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
    ASM_MESON_TAC[SIMPLEX_IMP_CONVEX; SIMPLEX_IMP_COMPACT];
    ALL_TAC] THEN
  CONJ_TAC THEN EQ_TAC THENL
   [DISCH_TAC THEN
    MP_TAC(ISPEC `(s:real^N->bool) INTER UNIONS l` EXTREME_POINT_EXISTS_CONVEX) THEN
    ANTS_TAC THENL
     [ASM_MESON_TAC[FACE_OF_IMP_COMPACT; FACE_OF_IMP_CONVEX]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_TAC `v:real^N`) THEN EXISTS_TAC `v:real^N` THEN
    MP_TAC(ISPECL [`(s:real^N->bool) INTER UNIONS l`; `s:real^N->bool`; `v:real^N`]
                  EXTREME_POINT_OF_FACE) THEN
    ASM_REWRITE_TAC[IN_INTER] THEN MESON_TAC[];
    STRIP_TAC THEN REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_INTER] THEN
    EXISTS_TAC `v:real^N` THEN ASM_MESON_TAC[extreme_point_of];
    REPEAT STRIP_TAC THEN ASM_MESON_TAC[extreme_point_of; SUBSET];
    DISCH_TAC THEN
    SUBGOAL_THEN `(s:real^N->bool) = convex hull {v | v extreme_point_of s}` SUBST1_TAC THENL
     [MATCH_MP_TAC KREIN_MILMAN_MINKOWSKI THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC SUBSET_TRANS THEN EXISTS_TAC `(s:real^N->bool) INTER UNIONS l` THEN
    REWRITE_TAC[INTER_SUBSET] THEN MATCH_MP_TAC HULL_MINIMAL THEN CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM; IN_INTER] THEN X_GEN_TAC `v:real^N` THEN
      DISCH_TAC THEN CONJ_TAC THENL [ASM_MESON_TAC[extreme_point_of]; ASM_MESON_TAC[]];
      ASM_MESON_TAC[FACE_OF_IMP_CONVEX]]]);;

(* vp simplices have dimension 1 or 2, and vp chains are short.             *)

let MOI_S3F2_VP_DIM = prove
 (`!(t:(real^N->bool)->bool) l f.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!s. s IN t ==> aff_dim s <= &2) /\ moi_frn_vp t l f
     ==> aff_dim f = &1 \/ aff_dim f = &2`,
  REPEAT GEN_TAC THEN REWRITE_TAC[moi_frn_vp] THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim (f:real^N->bool) <= &2` ASSUME_TAC THENL
   [MP_TAC(ISPEC `t:(real^N->bool)->bool` BARYCENTRIC_SUBDIVISION_REFINES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `f:real^N->bool` o CONJUNCT1) THEN
    ANTS_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(s:real^N->bool)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC AFF_DIM_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
                    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(aff_dim (f:real^N->bool) = &0) /\ ~(aff_dim f = -- &1)` MP_TAC THENL
   [REWRITE_TAC[AFF_DIM_EQ_0; AFF_DIM_EQ_MINUS1] THEN CONJ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN ASM SET_TAC[];
      DISCH_THEN SUBST_ALL_TAC THEN ASM SET_TAC[]];
    MP_TAC(ISPEC `f:real^N->bool` AFF_DIM_GE) THEN
    UNDISCH_TAC `aff_dim(f:real^N->bool) <= &2` THEN INT_ARITH_TAC]);;

let MOI_S3F2_VP_CHAIN = prove
 (`!(t:(real^N->bool)->bool) l c.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     (!s. s IN t ==> aff_dim s <= &2) /\
     moi_bar_chain (barycentric_subdivision t) c /\ ~(c = {}) /\
     (!f. f IN c ==> moi_frn_vp t l f)
     ==> (?f. c = {f}) \/
         (?e r. c = {e,r} /\ aff_dim e = &1 /\ aff_dim r = &2 /\ e SUBSET r /\
                ~(e = r))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!f. f IN c ==> aff_dim (f:real^N->bool) = &1 \/ aff_dim f = &2`
  (LABEL_TAC "dims") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_S3F2_VP_DIM THEN
    MAP_EVERY EXISTS_TAC [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] THEN
    ASM_SIMP_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f g:real^N->bool. f IN c /\ g IN c ==> f SUBSET g \/ g SUBSET f`
  (LABEL_TAC "cmp") THENL
   [UNDISCH_TAC `moi_bar_chain (barycentric_subdivision (t:(real^N->bool)->bool)) c` THEN
    REWRITE_TAC[moi_bar_chain] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f g:real^N->bool. f IN c /\ g IN c /\ f SUBSET g /\ ~(f = g)
                                   ==> aff_dim f < aff_dim g` (LABEL_TAC "lt") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC FACE_OF_AFF_DIM_LT THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `(f:real^N->bool) IN barycentric_subdivision t /\
                  (g:real^N->bool) IN barycentric_subdivision t /\
                  (?n. n simplex (g:real^N->bool))` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT]; ALL_TAC] THEN
    CONJ_TAC THENL
     [ASM_MESON_TAC[SIMPLEX_IMP_CONVEX];
      MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN
      EXISTS_TAC `barycentric_subdivision (t:(real^N->bool)->bool)` THEN
      ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!f g:real^N->bool. f IN c /\ g IN c /\ aff_dim f = aff_dim g ==> f = g`
  (LABEL_TAC "eq") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC(TAUT `(~p ==> F) ==> p`) THEN DISCH_TAC THEN
    USE_THEN "cmp" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(f:real^N->bool) IN c`)
      (ASSUME `(g:real^N->bool) IN c`))) THEN
    STRIP_TAC THENL
     [USE_THEN "lt" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(f:real^N->bool) IN c`)
        (CONJ (ASSUME `(g:real^N->bool) IN c`) (CONJ (ASSUME `(f:real^N->bool) SUBSET g`)
          (ASSUME `~(f:real^N->bool = g)`))))) THEN
      ASM_REWRITE_TAC[INT_LT_REFL];
      USE_THEN "lt" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(g:real^N->bool) IN c`)
        (CONJ (ASSUME `(f:real^N->bool) IN c`) (CONJ (ASSUME `(g:real^N->bool) SUBSET f`)
          (ONCE_REWRITE_RULE[EQ_SYM_EQ] (ASSUME `~(f:real^N->bool = g)`)))))) THEN
      ASM_REWRITE_TAC[INT_LT_REFL]];
    ALL_TAC] THEN
  SUBGOAL_THEN `!e r:real^N->bool. e IN c /\ r IN c /\ aff_dim e = &1 /\ aff_dim r = &2
                  ==> c = {e,r} /\ e SUBSET r /\ ~(e = r)` (LABEL_TAC "two") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THENL
     [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      X_GEN_TAC `h:real^N->bool` THEN EQ_TAC THENL
       [DISCH_TAC THEN
        USE_THEN "dims" (MP_TAC o C MATCH_MP (ASSUME `(h:real^N->bool) IN c`)) THEN
        STRIP_TAC THENL
         [DISJ1_TAC THEN USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
          DISJ2_TAC THEN USE_THEN "eq" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
        STRIP_TAC THEN ASM_REWRITE_TAC[]];
      USE_THEN "cmp" (MP_TAC o C MATCH_MP (CONJ (ASSUME `(e:real^N->bool) IN c`)
        (ASSUME `(r:real^N->bool) IN c`))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MP_TAC(ISPECL [`r:real^N->bool`; `e:real^N->bool`] AFF_DIM_SUBSET) THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC(TAUT `~p ==> p ==> q`) THEN INT_ARITH_TAC;
      DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `aff_dim(r:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC];
    ALL_TAC] THEN
  FIRST_ASSUM(X_CHOOSE_TAC `f:real^N->bool` o GEN_REWRITE_RULE I [GSYM MEMBER_NOT_EMPTY] o
    check (fun th -> concl th = `~(c:(real^N->bool)->bool = {})`)) THEN
  ASM_CASES_TAC `!g:real^N->bool. g IN c ==> aff_dim g = aff_dim (f:real^N->bool)` THENL
   [DISJ1_TAC THEN EXISTS_TAC `f:real^N->bool` THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_SING] THEN
    X_GEN_TAC `g:real^N->bool` THEN EQ_TAC THENL
     [DISCH_TAC THEN USE_THEN "eq" MATCH_MP_TAC THEN
      REWRITE_TAC[ASSUME `(g:real^N->bool) IN c`; ASSUME `(f:real^N->bool) IN c`] THEN
      UNDISCH_TAC `!g:real^N->bool. g IN c ==> aff_dim g = aff_dim (f:real^N->bool)` THEN
      DISCH_THEN(MP_TAC o SPEC `g:real^N->bool`) THEN
      REWRITE_TAC[ASSUME `(g:real^N->bool) IN c`];
      DISCH_THEN SUBST1_TAC THEN ASM_REWRITE_TAC[]];
    DISJ2_TAC THEN
    FIRST_X_ASSUM(X_CHOOSE_THEN `g:real^N->bool` STRIP_ASSUME_TAC o
      REWRITE_RULE[NOT_FORALL_THM; NOT_IMP]) THEN
    USE_THEN "dims" (MP_TAC o C MATCH_MP (ASSUME `(f:real^N->bool) IN c`)) THEN
    USE_THEN "dims" (MP_TAC o C MATCH_MP (ASSUME `(g:real^N->bool) IN c`)) THEN
    STRIP_TAC THEN STRIP_TAC THEN ASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Part 3: a vp triangle of the first derived has exactly two vp            *)
(* edges.  The edges of a triangle r = hull {a,b,c} of a complex are the    *)
(* three segments; an edge is vp exactly when one of its two ends lies in  *)
(* |l|, and r being vp means that one or two of a, b, c lie in |l|.        *)
(* ------------------------------------------------------------------------- *)

let MOI_S3F2_TRI_EDGES = prove
 (`!c (a:real^N) b d.
     moi_bar_complex c /\ convex hull {a,b,d} IN c /\ ~affine_dependent {a,b,d} /\
     ~(a = b) /\ ~(a = d) /\ ~(b = d)
     ==> !e. e IN c /\ aff_dim e = &1 /\ e SUBSET convex hull {a,b,d} <=>
             e = segment[a,b] \/ e = segment[a,d] \/ e = segment[b,d]`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN X_GEN_TAC `e:real^N->bool` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    SUBGOAL_THEN `(e:real^N->bool) face_of convex hull {a,b,d}` MP_TAC THENL
     [MATCH_MP_TAC MOI_BAR_COMPLEX_SUBSET_FACE THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    DISCH_THEN(X_CHOOSE_THEN `S:real^N->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `~affine_dependent (S:real^N->bool) /\ FINITE S` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THENL
       [MATCH_MP_TAC AFFINE_INDEPENDENT_SUBSET THEN EXISTS_TAC `{a:real^N,b,d}` THEN
        ASM_REWRITE_TAC[];
        MATCH_MP_TAC FINITE_SUBSET THEN EXISTS_TAC `{a:real^N,b,d}` THEN
        ASM_REWRITE_TAC[FINITE_INSERT; FINITE_EMPTY]];
      ALL_TAC] THEN
    SUBGOAL_THEN `(S:real^N->bool) HAS_SIZE 2` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE] THEN
      UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL] THEN
      ASM_SIMP_TAC[AFF_DIM_AFFINE_INDEPENDENT] THEN
      REWRITE_TAC[INT_ARITH `x - &1:int = &1 <=> x = &2`; INT_OF_NUM_EQ];
      ALL_TAC] THEN
    REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
    DISCH_THEN(X_CHOOSE_THEN `p:real^N` (X_CHOOSE_THEN `q:real^N` STRIP_ASSUME_TAC)) THEN
    UNDISCH_TAC `e:real^N->bool = convex hull S` THEN
    ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN DISCH_THEN SUBST1_TAC THEN
    UNDISCH_TAC `(S:real^N->bool) SUBSET {a,b,d}` THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[INSERT_SUBSET; IN_INSERT; NOT_IN_EMPTY; EMPTY_SUBSET] THEN
    ASM_MESON_TAC[SEGMENT_SYM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!p q:real^N. p IN {a,b,d} /\ q IN {a,b,d} /\ ~(p = q)
                 ==> segment[p,q] IN c /\ aff_dim (segment[p,q]) = &1 /\
                     segment[p,q] SUBSET convex hull {a,b,d}`
  ASSUME_TAC THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN
    SUBGOAL_THEN `segment[p:real^N,q] face_of convex hull {a,b,d}` ASSUME_TAC THENL
     [ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
      EXISTS_TAC `{p:real^N,q}` THEN REWRITE_TAC[SEGMENT_CONVEX_HULL] THEN
      ASM SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_COMPLEX_FACE THEN
      EXISTS_TAC `convex hull {a:real^N,b,d}` THEN ASM_REWRITE_TAC[];
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT];
      ASM_MESON_TAC[FACE_OF_IMP_SUBSET]];
    ALL_TAC] THEN
  STRIP_TAC THEN ASM_REWRITE_TAC[] THEN FIRST_X_ASSUM MATCH_MP_TAC THEN
  ASM_REWRITE_TAC[IN_INSERT]);;

let MOI_S3F2_SEG_VP = prove
 (`!(t:(real^N->bool)->bool) l p q.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     segment[p,q] IN barycentric_subdivision t /\ ~(p = q)
     ==> (moi_frn_vp t l (segment[p,q]) <=> ~(p IN UNIONS l <=> q IN UNIONS l))`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                 `segment[p:real^N,q]`] MOI_S3F2_FULL_VERTS) THEN
  ASM_REWRITE_TAC[moi_frn_vp; EXTREME_POINT_OF_SEGMENT] THEN
  DISCH_THEN(CONJUNCTS_THEN SUBST1_TAC) THEN MESON_TAC[]);;

let MOI_S3F2_TRIANGLE_VERTS = prove
 (`!r:real^N->bool.
     &2 simplex r
     ==> ?a b d. ~(a = b) /\ ~(a = d) /\ ~(b = d) /\ ~affine_dependent {a,b,d} /\
                 r = convex hull {a,b,d}`,
  GEN_TAC THEN REWRITE_TAC[MOI_PL2_SIMPLEX_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` (X_CHOOSE_THEN `d:real^N`
    STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`a:real^N`; `b:real^N`; `d:real^N`] THEN
  ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~collinear {b:real^N,b,d}` THEN
    REWRITE_TAC[SET_RULE `{x:real^N,x,y} = {x,y}`; COLLINEAR_2];
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~collinear {d:real^N,b,d}` THEN
    REWRITE_TAC[SET_RULE `{x:real^N,y,x} = {x,y}`; COLLINEAR_2];
    DISCH_THEN SUBST_ALL_TAC THEN UNDISCH_TAC `~collinear {a:real^N,d,d}` THEN
    REWRITE_TAC[SET_RULE `{x:real^N,y,y} = {x,y}`; COLLINEAR_2];
    ASM_MESON_TAC[AFFINE_DEPENDENT_IMP_COLLINEAR_3]]);;

let MOI_S3F2_CARD_TWO_OF_THREE = prove
 (`!(P:A->bool) x y z.
     ~(x = y) /\ ~(x = z) /\ ~(y = z) /\
     ((P x /\ P y /\ ~P z) \/ (P x /\ ~P y /\ P z) \/ (~P x /\ P y /\ P z))
     ==> CARD {e | (e = x \/ e = y \/ e = z) /\ P e} = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THENL
   [SUBGOAL_THEN `{e:A | (e = x \/ e = y \/ e = z) /\ P e} = {x,y}` SUBST1_TAC;
    SUBGOAL_THEN `{e:A | (e = x \/ e = y \/ e = z) /\ P e} = {x,z}` SUBST1_TAC;
    SUBGOAL_THEN `{e:A | (e = x \/ e = y \/ e = z) /\ P e} = {y,z}` SUBST1_TAC] THEN
  TRY(ASM_SIMP_TAC[CARD_CLAUSES; FINITE_INSERT; FINITE_EMPTY; IN_INSERT; NOT_IN_EMPTY] THEN
      CONV_TAC NUM_REDUCE_CONV THEN NO_TAC) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `e:A` THEN
  ASM_CASES_TAC `e:A = x` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `e:A = y` THEN ASM_REWRITE_TAC[] THEN
  ASM_CASES_TAC `e:A = z` THEN ASM_REWRITE_TAC[]);;

let MOI_S3F2_TRI_VP_EDGES = prove
 (`!(t:(real^N->bool)->bool) l r.
     lf_simplicial_complex t /\ simplicial_subcomplex l t /\
     r IN barycentric_subdivision t /\ aff_dim r = &2 /\ moi_frn_vp t l r
     ==> CARD {e | e IN barycentric_subdivision t /\ aff_dim e = &1 /\ e SUBSET r /\
                   moi_frn_vp t l e} = 2`,
  REPEAT STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  (* r is a triangle hull {a,b,d} *)
  SUBGOAL_THEN `&2 simplex (r:real^N->bool)` MP_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (r:real^N->bool)` STRIP_ASSUME_TAC THENL
     [ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX]; ALL_TAC] THEN
    SUBGOAL_THEN `n:int = &2` (fun th -> ASM_MESON_TAC[th]) THEN
    ASM_MESON_TAC[AFF_DIM_SIMPLEX];
    ALL_TAC] THEN
  DISCH_THEN(MP_TAC o MATCH_MP MOI_S3F2_TRIANGLE_VERTS) THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` (X_CHOOSE_THEN `d:real^N`
    (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC (CONJUNCTS_THEN2 ASSUME_TAC
     (CONJUNCTS_THEN2 ASSUME_TAC (ASSUME_TAC o SYM)))))))) THEN
  SUBGOAL_THEN `!v:real^N. v extreme_point_of r <=> v = a \/ v = b \/ v = d` ASSUME_TAC THENL
   [GEN_TAC THEN SUBST1_TAC(SYM(ASSUME `convex hull {a:real^N,b,d} = r`)) THEN
    ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  (* r vp: one or two of a, b, d lie in |l| *)
  SUBGOAL_THEN `((a:real^N) IN UNIONS l \/ b IN UNIONS l \/ d IN UNIONS l) /\
                ~((a:real^N) IN UNIONS l /\ b IN UNIONS l /\ d IN UNIONS l)`
  (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `r:real^N->bool`]
                  MOI_S3F2_FULL_VERTS) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `moi_frn_vp t l (r:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN
    MESON_TAC[];
    ALL_TAC] THEN
  (* the edges of r *)
  MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`; `a:real^N`;
                 `b:real^N`; `d:real^N`] MOI_S3F2_TRI_EDGES) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN(LABEL_TAC "edges") THEN
  SUBGOAL_THEN
   `segment[a:real^N,b] IN barycentric_subdivision t /\
    segment[a:real^N,d] IN barycentric_subdivision t /\
    segment[b:real^N,d] IN barycentric_subdivision t`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN
    USE_THEN "edges" (fun th -> MESON_TAC[th]);
    ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`; `b:real^N`]
                MOI_S3F2_SEG_VP) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `a:real^N`; `d:real^N`]
                MOI_S3F2_SEG_VP) THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `b:real^N`; `d:real^N`]
                MOI_S3F2_SEG_VP) THEN
  ASM_REWRITE_TAC[] THEN REPEAT DISCH_TAC THEN
  SUBGOAL_THEN
   `{e | e IN barycentric_subdivision t /\ aff_dim e = &1 /\ e SUBSET r /\
         moi_frn_vp t l e} =
    {e | (e = segment[a:real^N,b] \/ e = segment[a,d] \/ e = segment[b,d]) /\
         moi_frn_vp t l e}`
  SUBST1_TAC THENL
   [GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    X_GEN_TAC `e:real^N->bool` THEN
    USE_THEN "edges" (MP_TAC o SPEC `e:real^N->bool`) THEN CONV_TAC TAUT;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(segment[a:real^N,b] = segment[a,d]) /\ ~(segment[a,b] = segment[b,d]) /\
                ~(segment[a:real^N,d] = segment[b,d])` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[SEGMENT_EQ] THEN
    MAP_EVERY UNDISCH_TAC [`~(a:real^N = b)`; `~(a:real^N = d)`; `~(b:real^N = d)`] THEN
    SET_TAC[];
    ALL_TAC] THEN
  MATCH_MP_TAC MOI_S3F2_CARD_TWO_OF_THREE THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `(a:real^N) IN UNIONS l \/ b IN UNIONS l \/ d IN UNIONS l` THEN
  UNDISCH_TAC `~((a:real^N) IN UNIONS l /\ b IN UNIONS l /\ d IN UNIONS l)` THEN
  CONV_TAC TAUT);;

(* ------------------------------------------------------------------------- *)
(* Part 4: the hulls of the vp chains form a 1-dimensional simplicial       *)
(* complex whose polyhedron is the derived frontier; when every vp edge of  *)
(* the first derived lies in exactly two of its triangles, every vertex has *)
(* degree two and the derived frontier is a finite union of PL circles.    *)
(* ------------------------------------------------------------------------- *)

let MOI_S3F2_SUBCOMPLEX_SC = prove
 (`!(k:(real^N->bool)->bool) c.
     simplicial_complex c /\ k SUBSET c /\ (!s f. s IN k /\ f face_of s ==> f IN k)
     ==> simplicial_complex k`,
  REWRITE_TAC[simplicial_complex] THEN REPEAT STRIP_TAC THEN
  ASM_MESON_TAC[SUBSET; FINITE_SUBSET]);;

(* The hulls of the vp chains (the frontier complex).                       *)

let moi_s3f2_fcx = new_definition
 `moi_s3f2_fcx (t:(real^N->bool)->bool) (l:(real^N->bool)->bool) =
    {convex hull (IMAGE simplex_barycentre c) | c |
     moi_bar_chain (barycentric_subdivision t) c /\ (!f. f IN c ==> moi_frn_vp t l f)}`;;

let MOI_S3F2_DFR_COMPLEX = prove
 (`!(t:(real^N->bool)->bool) l.
     simplicial_complex t /\ simplicial_subcomplex l t /\
     (!s. s IN t ==> aff_dim s <= &2)
     ==> simplicial_complex (moi_s3f2_fcx t l) /\
         UNIONS (moi_s3f2_fcx t l) = derived_frontier t l /\
         (!s. s IN moi_s3f2_fcx t l ==> aff_dim s <= &1)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REWRITE_TAC[moi_s3f2_fcx] THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_S3F2_SUBCOMPLEX_SC THEN
    EXISTS_TAC `barycentric_subdivision (barycentric_subdivision (t:(real^N->bool)->bool))` THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX];
      REWRITE_TAC[SUBSET; FORALL_IN_GSPEC; MOI_BAR_IN_SUBDIVISION] THEN
      REPEAT STRIP_TAC THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMP_CONJ; RIGHT_FORALL_IMP_THM; FORALL_IN_GSPEC] THEN
      X_GEN_TAC `c:(real^N->bool)->bool` THEN REPEAT DISCH_TAC THEN
      X_GEN_TAC `s:real^N->bool` THEN
      MP_TAC(ISPECL [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                     `c:(real^N->bool)->bool`] MOI_BAR_CHAIN_AFFINE_INDEPENDENT) THEN
      ASM_REWRITE_TAC[] THEN
      SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN DISCH_TAC THEN
      DISCH_THEN(X_CHOOSE_THEN `S:real^N->bool` STRIP_ASSUME_TAC) THEN
      REWRITE_TAC[IN_ELIM_THM] THEN
      EXISTS_TAC `{f:real^N->bool | f IN c /\ simplex_barycentre f IN S}` THEN
      REPEAT CONJ_TAC THENL
       [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN SET_TAC[];
        ASM SET_TAC[];
        ASM_REWRITE_TAC[] THEN AP_TERM_TAC THEN
        UNDISCH_TAC `(S:real^N->bool) SUBSET IMAGE simplex_barycentre c` THEN SET_TAC[]]];
    (* the polyhedron *)
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
    ASM_SIMP_TAC[MOI_S3F2_DFR_CHAIN] THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` (CONJUNCTS_THEN2
        (X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) ASSUME_TAC)) THEN
      EXISTS_TAC `c:(real^N->bool)->bool` THEN
      UNDISCH_TAC `(x:real^N) IN s` THEN ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST_ALL_TAC THEN
      UNDISCH_TAC `(x:real^N) IN convex hull (IMAGE simplex_barycentre {})` THEN
      REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_IN_EMPTY];
      DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre (c:(real^N->bool)->bool))` THEN
      ASM_REWRITE_TAC[] THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
    (* dimension at most one *)
    REWRITE_TAC[FORALL_IN_GSPEC] THEN X_GEN_TAC `c:(real^N->bool)->bool` THEN STRIP_TAC THEN
    ASM_CASES_TAC `c:(real^N->bool)->bool = {}` THENL
     [ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `c:(real^N->bool)->bool`] MOI_S3F2_VP_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[IMAGE_CLAUSES] THENL
     [REWRITE_TAC[CONVEX_HULL_SING; AFF_DIM_SING] THEN INT_ARITH_TAC;
      REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; AFF_DIM_SEGMENT] THEN
      COND_CASES_TAC THEN INT_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Part 5: the local edge lemma (an edge with a locally planar point in its *)
(* relative interior lies in exactly two triangles), the vertex degrees of  *)
(* the frontier complex, the PL circles of the derived frontier             *)
(* (MOI_S3F2_DFR_CIRCLES) and the frontier near the barycentre of a vp edge *)
(* (MOI_S3F2_DFR_EDGE_STAR).                                                *)
(* ------------------------------------------------------------------------- *)

let MOI_S3F2_LOCAL_EDGE = prove
 (`!(c:(real^N->bool)->bool) e z.
     simplicial_complex c /\ (!s. s IN c ==> aff_dim s <= &2) /\
     e IN c /\ aff_dim e = &1 /\ z IN relative_interior e /\
     moi_s28_locally_r2 (UNIONS c) z
     ==> CARD {r | r IN c /\ aff_dim r = &2 /\ e SUBSET r} = 2`,
  REPEAT STRIP_TAC THEN
  ABBREV_TAC `tt = {r | r IN c /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r}` THEN
  SUBGOAL_THEN `FINITE (tt:(real^N->bool)->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "tt" THEN MATCH_MP_TAC FINITE_RESTRICT THEN
    ASM_MESON_TAC[simplicial_complex];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD (tt:(real^N->bool)->bool) = 0)` ASSUME_TAC THENL
   [ASM_SIMP_TAC[CARD_EQ_0] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `z:real^N`]
                  MOI_S8TA_EDGE0_NO) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{r | r IN c /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = tt` THEN
    ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `~(CARD (tt:(real^N->bool)->bool) = 1)` ASSUME_TAC THENL
   [DISCH_TAC THEN
    SUBGOAL_THEN `(tt:(real^N->bool)->bool) HAS_SIZE 1` MP_TAC THENL
     [ASM_REWRITE_TAC[HAS_SIZE]; ALL_TAC] THEN
    CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN
    DISCH_THEN(X_CHOOSE_TAC `r0:real^N->bool`) THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `r0:real^N->bool`; `z:real^N`]
                  MOI_S8TA_EDGE1_NO_R2) THEN
    ASM_REWRITE_TAC[] THEN
    UNDISCH_TAC `{r | r IN c /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r} = tt` THEN
    ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[EXTENSION; IN_SING; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (tt:(real^N->bool)->bool) <= 2` MP_TAC THENL
   [REWRITE_TAC[GSYM NOT_LT] THEN DISCH_TAC THEN
    MP_TAC(ISPECL [`3`; `tt:(real^N->bool)->bool`] CHOOSE_SUBSET_STRONG) THEN
    ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN ASM_ARITH_TAC; ALL_TAC] THEN
    DISCH_THEN(X_CHOOSE_THEN `s3:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [MOI_SCF_HAS_SIZE_3]) THEN
    DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` (X_CHOOSE_THEN `t2:real^N->bool`
      (X_CHOOSE_THEN `t3:real^N->bool` STRIP_ASSUME_TAC))) THEN
    SUBGOAL_THEN `(t1:real^N->bool) IN tt /\ t2 IN tt /\ t3 IN tt` MP_TAC THENL
     [ASM SET_TAC[]; ALL_TAC] THEN
    EXPAND_TAC "tt" THEN REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `e:real^N->bool`; `t1:real^N->bool`;
                   `t2:real^N->bool`; `t3:real^N->bool`; `z:real^N`] MOI_S8TA_EDGE3_NO) THEN
    ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_S8TA_EMB2_OF THEN ASM_REWRITE_TAC[];
    ASM_ARITH_TAC]);;

(* Vertex degrees of the frontier complex.                                   *)

let MOI_S3F2_FCX_EDGES_AT = prove
 (`!(t:(real^N->bool)->bool) l f.
     simplicial_complex t /\ simplicial_subcomplex l t /\
     (!s. s IN t ==> aff_dim s <= &2) /\ moi_frn_vp t l f
     ==> {E | E IN moi_s3f2_fcx t l /\ aff_dim E = &1 /\ simplex_barycentre f IN E} =
         {segment[simplex_barycentre e,simplex_barycentre r] | e r |
          e IN barycentric_subdivision t /\ r IN barycentric_subdivision t /\
          aff_dim e = &1 /\ aff_dim r = &2 /\ e SUBSET r /\ moi_frn_vp t l e /\
          (e = f \/ r = f)}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN barycentric_subdivision t /\ ~(r = {})
                                 ==> simplex_barycentre r IN relative_interior r`
  (LABEL_TAC "bri") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX];
    ALL_TAC] THEN
  SUBGOAL_THEN `!g:real^N->bool. moi_frn_vp t l g ==> g IN barycentric_subdivision t /\ ~(g = {})`
  (LABEL_TAC "vpne") THENL
   [GEN_TAC THEN REWRITE_TAC[moi_frn_vp] THEN SET_TAC[]; ALL_TAC] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `E:real^N->bool` THEN
  REWRITE_TAC[moi_s3f2_fcx; IN_ELIM_THM] THEN EQ_TAC THENL
   [DISCH_THEN(CONJUNCTS_THEN2 (X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC)
      STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `c:(real^N->bool)->bool = {}` THENL
     [UNDISCH_TAC `aff_dim(E:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `c:(real^N->bool)->bool`] MOI_S3F2_VP_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [UNDISCH_TAC `aff_dim(E:real^N->bool) = &1` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; AFF_DIM_SING] THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `r:real^N->bool`] THEN
    SUBGOAL_THEN `(e:real^N->bool) IN c /\ (r:real^N->bool) IN c` STRIP_ASSUME_TAC THENL
     [ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
    SUBGOAL_THEN `moi_frn_vp t l (e:real^N->bool) /\ moi_frn_vp t l (r:real^N->bool)`
    STRIP_ASSUME_TAC THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    REPEAT CONJ_TAC THENL
     [ASM_MESON_TAC[];
      ASM_MESON_TAC[];
      ALL_TAC;
      ASM_REWRITE_TAC[IMAGE_CLAUSES; SEGMENT_CONVEX_HULL]] THEN
    (* the barycentre of f is an end of the segment *)
    SUBGOAL_THEN `simplex_barycentre (f:real^N->bool) = simplex_barycentre e \/
                  simplex_barycentre f = simplex_barycentre r` MP_TAC THENL
     [SUBGOAL_THEN `{simplex_barycentre (f:real^N->bool)} IN
                    barycentric_subdivision (barycentric_subdivision t) /\
                    E IN barycentric_subdivision (barycentric_subdivision t)`
      STRIP_ASSUME_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN CONJ_TAC THENL
         [EXISTS_TAC `{f:real^N->bool}` THEN
          REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING] THEN
          REWRITE_TAC[moi_bar_chain; SING_SUBSET; FINITE_SING; IN_SING] THEN
          ASM_MESON_TAC[SUBSET_REFL];
          EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]];
        ALL_TAC] THEN
      MP_TAC(ISPECL [`barycentric_subdivision (barycentric_subdivision (t:(real^N->bool)->bool))`;
                     `{simplex_barycentre (f:real^N->bool)}`; `E:real^N->bool`]
                    MOI_BAR_COMPLEX_INTER) THEN
      ANTS_TAC THENL
       [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_SUBDIVISION_COMPLEX THEN
        ASM_REWRITE_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `{simplex_barycentre (f:real^N->bool)} INTER E = {simplex_barycentre f}`
      SUBST1_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; GSYM SEGMENT_CONVEX_HULL; FACE_OF_SING;
                      EXTREME_POINT_OF_SEGMENT];
      ALL_TAC] THEN
    STRIP_TAC THENL
     [DISJ1_TAC; DISJ2_TAC] THEN CONV_TAC SYM_CONV THEN
    MATCH_MP_TAC MOI_S3F2_RELINT_EQ THEN
    MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                          `simplex_barycentre (f:real^N->bool)`] THEN
    ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
    DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (X_CHOOSE_THEN `r:real^N->bool` MP_TAC)) THEN
    REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
    SUBGOAL_THEN `moi_frn_vp t l (r:real^N->bool)` ASSUME_TAC THENL
     [UNDISCH_TAC `moi_frn_vp t l (e:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN
      UNDISCH_TAC `(e:real^N->bool) SUBSET r` THEN ASM SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `~(simplex_barycentre (e:real^N->bool) = simplex_barycentre r)` ASSUME_TAC
    THENL
     [DISCH_TAC THEN
      SUBGOAL_THEN `(e:real^N->bool) = r` MP_TAC THENL
       [MATCH_MP_TAC MOI_S3F2_RELINT_EQ THEN
        MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                              `simplex_barycentre (e:real^N->bool)`] THEN
        ASM_SIMP_TAC[] THEN ASM_MESON_TAC[];
        DISCH_THEN SUBST_ALL_TAC THEN
        UNDISCH_TAC `aff_dim(r:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
        INT_ARITH_TAC];
      ALL_TAC] THEN
    CONJ_TAC THENL
     [SUBGOAL_THEN `~(e:real^N->bool = {}) /\ ~(r:real^N->bool = {})` STRIP_ASSUME_TAC THENL
       [CONJ_TAC THENL
         [USE_THEN "vpne" (MP_TAC o SPEC `e:real^N->bool`);
          USE_THEN "vpne" (MP_TAC o SPEC `r:real^N->bool`)] THEN
        ASM_SIMP_TAC[];
        ALL_TAC] THEN
      EXISTS_TAC `{e:real^N->bool,r}` THEN
      REWRITE_TAC[IMAGE_CLAUSES; SEGMENT_CONVEX_HULL] THEN
      REWRITE_TAC[moi_bar_chain; INSERT_SUBSET; EMPTY_SUBSET; FINITE_INSERT; FINITE_EMPTY;
                  IN_INSERT; NOT_IN_EMPTY] THEN
      ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL] THEN
      REPEAT CONJ_TAC THEN REPEAT STRIP_TAC THEN ASM_REWRITE_TAC[SUBSET_REFL];
      ASM_REWRITE_TAC[AFF_DIM_SEGMENT] THEN
      FIRST_X_ASSUM(DISJ_CASES_THEN SUBST_ALL_TAC o check (is_disj o concl)) THEN
      REWRITE_TAC[ENDS_IN_SEGMENT]]]);;

let MOI_S3F2_FCX_DEGREE = prove
 (`!(t:(real^N->bool)->bool) l v.
     simplicial_complex t /\ simplicial_subcomplex l t /\
     (!s. s IN t ==> aff_dim s <= &2) /\
     (!e. e IN barycentric_subdivision t /\ aff_dim e = &1 /\ moi_frn_vp t l e
          ==> CARD {r | r IN barycentric_subdivision t /\ aff_dim r = &2 /\ e SUBSET r} = 2) /\
     {v} IN moi_s3f2_fcx t l
     ==> CARD {E | E IN moi_s3f2_fcx t l /\ aff_dim E = &1 /\ v IN E} = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `!r:real^N->bool. r IN barycentric_subdivision t /\ ~(r = {})
                                 ==> simplex_barycentre r IN relative_interior r`
  (LABEL_TAC "bri") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC SIMPLEX_BARYCENTRE_IN_RELATIVE_INTERIOR THEN
    ASM_MESON_TAC[MOI_BAR_COMPLEX_SIMPLEX];
    ALL_TAC] THEN
  (* the vertex is the barycentre of a vp simplex f *)
  SUBGOAL_THEN `?f:real^N->bool. moi_frn_vp t l f /\ v = simplex_barycentre f`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `{v:real^N} IN moi_s3f2_fcx t l` THEN REWRITE_TAC[moi_s3f2_fcx; IN_ELIM_THM] THEN
    DISCH_THEN(X_CHOOSE_THEN `c:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `c:(real^N->bool)->bool = {}` THENL
     [UNDISCH_TAC `{v:real^N} = convex hull (IMAGE simplex_barycentre c)` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY; NOT_INSERT_EMPTY];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`;
                   `c:(real^N->bool)->bool`] MOI_S3F2_VP_CHAIN) THEN
    ASM_REWRITE_TAC[] THEN STRIP_TAC THENL
     [EXISTS_TAC `f:real^N->bool` THEN CONJ_TAC THENL
       [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[IN_SING];
        UNDISCH_TAC `{v:real^N} = convex hull (IMAGE simplex_barycentre c)` THEN
        ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING] THEN SET_TAC[]];
      UNDISCH_TAC `{v:real^N} = convex hull (IMAGE simplex_barycentre c)` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; GSYM SEGMENT_CONVEX_HULL] THEN
      DISCH_THEN(MP_TAC o SYM) THEN REWRITE_TAC[SEGMENT_EQ_SING] THEN
      DISCH_THEN(CONJUNCTS_THEN ASSUME_TAC) THEN
      SUBGOAL_THEN `(e:real^N->bool) = r` (fun th -> ASM_MESON_TAC[th]) THEN
      MATCH_MP_TAC MOI_S3F2_RELINT_EQ THEN
      MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`; `v:real^N`] THEN
      SUBGOAL_THEN `moi_frn_vp t l (e:real^N->bool) /\ moi_frn_vp t l (r:real^N->bool)`
      MP_TAC THENL [ASM_MESON_TAC[IN_INSERT]; ALL_TAC] THEN
      REWRITE_TAC[moi_frn_vp] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [SUBST1_TAC(SYM(ASSUME `simplex_barycentre (e:real^N->bool) = v`));
        SUBST1_TAC(SYM(ASSUME `simplex_barycentre (r:real^N->bool) = v`))] THEN
      USE_THEN "bri" MATCH_MP_TAC THEN ASM SET_TAC[]];
    ALL_TAC] THEN
  FIRST_X_ASSUM SUBST_ALL_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
                MOI_S3F2_FCX_EDGES_AT) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `f:real^N->bool`]
                MOI_S3F2_VP_DIM) THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:real^N->bool) IN barycentric_subdivision t /\ ~(f = {})` STRIP_ASSUME_TAC
  THENL [UNDISCH_TAC `moi_frn_vp t l (f:real^N->bool)` THEN REWRITE_TAC[moi_frn_vp] THEN
         SET_TAC[];
         ALL_TAC] THEN
  STRIP_TAC THENL
   [(* f an edge: one segment per triangle on f *)
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `CARD (IMAGE (\r. segment[simplex_barycentre f,simplex_barycentre r])
                       {r:real^N->bool | r IN barycentric_subdivision t /\ aff_dim r = &2 /\
                                         f SUBSET r})` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `E:real^N->bool` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (X_CHOOSE_THEN `r:real^N->bool` MP_TAC)) THEN
        REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
        EXISTS_TAC `r:real^N->bool` THEN
        SUBGOAL_THEN `(e:real^N->bool) = f` SUBST_ALL_TAC THENL
         [FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `aff_dim(r:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
          ASM_REWRITE_TAC[]];
        DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
        MAP_EVERY EXISTS_TAC [`f:real^N->bool`; `r:real^N->bool`] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `CARD {r:real^N->bool | r IN barycentric_subdivision t /\ aff_dim r = &2 /\
                                       f SUBSET r}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`r1:real^N->bool`; `r2:real^N->bool`] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        MATCH_MP_TAC MOI_S3F2_RELINT_EQ THEN
        MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                              `simplex_barycentre (r1:real^N->bool)`] THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(r1:real^N->bool = {}) /\ ~(r2:real^N->bool = {})` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
          RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
          ASM_MESON_TAC[INT_ARITH `~(-- &1:int = &2)`];
          ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN
        SUBGOAL_THEN `simplex_barycentre (r1:real^N->bool) = simplex_barycentre r2`
        (fun th -> REWRITE_TAC[th]) THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
        UNDISCH_TAC `segment[simplex_barycentre f,simplex_barycentre (r1:real^N->bool)] =
                     segment[simplex_barycentre f,simplex_barycentre r2]` THEN
        REWRITE_TAC[SEGMENT_EQ] THEN
        SUBGOAL_THEN `~(simplex_barycentre (f:real^N->bool) = simplex_barycentre r1) /\
                      ~(simplex_barycentre (f:real^N->bool) = simplex_barycentre r2)`
        STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN DISCH_TAC THENL
           [SUBGOAL_THEN `(f:real^N->bool) = r1` MP_TAC;
            SUBGOAL_THEN `(f:real^N->bool) = r2` MP_TAC] THEN
          TRY(MATCH_MP_TAC MOI_S3F2_RELINT_EQ THEN
              MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                                    `simplex_barycentre (f:real^N->bool)`] THEN
              ASM_SIMP_TAC[] THEN NO_TAC) THEN
          DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[INT_ARITH `~(&1:int = &2)`];
          ALL_TAC] THEN
        REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC FINITE_RESTRICT THEN
        ASM_MESON_TAC[MOI_BAR_SUBDIVISION_FINITE; simplicial_complex]];
      FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]];
    (* f a triangle: one segment per vp edge of f *)
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `CARD (IMAGE (\e. segment[simplex_barycentre e,simplex_barycentre f])
                       {e:real^N->bool | e IN barycentric_subdivision t /\ aff_dim e = &1 /\
                                         e SUBSET f /\ moi_frn_vp t l e})` THEN
    CONJ_TAC THENL
     [AP_TERM_TAC THEN GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_IMAGE] THEN
      X_GEN_TAC `E:real^N->bool` THEN EQ_TAC THENL
       [DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` (X_CHOOSE_THEN `r:real^N->bool` MP_TAC)) THEN
        REWRITE_TAC[IMP_CONJ] THEN REPEAT DISCH_TAC THEN
        EXISTS_TAC `e:real^N->bool` THEN
        SUBGOAL_THEN `(r:real^N->bool) = f` SUBST_ALL_TAC THENL
         [FIRST_X_ASSUM(DISJ_CASES_THEN ASSUME_TAC o check (is_disj o concl)) THEN
          ASM_REWRITE_TAC[] THEN
          UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
          ASM_REWRITE_TAC[]];
        DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
        MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `f:real^N->bool`] THEN ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `CARD {e:real^N->bool | e IN barycentric_subdivision t /\ aff_dim e = &1 /\
                                       e SUBSET f /\ moi_frn_vp t l e}` THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC CARD_IMAGE_INJ THEN CONJ_TAC THENL
       [MAP_EVERY X_GEN_TAC [`e1:real^N->bool`; `e2:real^N->bool`] THEN
        REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN
        MATCH_MP_TAC MOI_S3F2_RELINT_EQ THEN
        MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                              `simplex_barycentre (e1:real^N->bool)`] THEN
        ASM_REWRITE_TAC[] THEN
        SUBGOAL_THEN `~(e1:real^N->bool = {}) /\ ~(e2:real^N->bool = {})` STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN DISCH_THEN SUBST_ALL_TAC THEN
          RULE_ASSUM_TAC(REWRITE_RULE[AFF_DIM_EMPTY]) THEN
          ASM_MESON_TAC[INT_ARITH `~(-- &1:int = &1)`];
          ALL_TAC] THEN
        ASM_SIMP_TAC[] THEN
        SUBGOAL_THEN `simplex_barycentre (e1:real^N->bool) = simplex_barycentre e2`
        (fun th -> REWRITE_TAC[th]) THENL [ALL_TAC; ASM_SIMP_TAC[]] THEN
        UNDISCH_TAC `segment[simplex_barycentre (e1:real^N->bool),simplex_barycentre f] =
                     segment[simplex_barycentre e2,simplex_barycentre f]` THEN
        REWRITE_TAC[SEGMENT_EQ] THEN
        SUBGOAL_THEN `~(simplex_barycentre (f:real^N->bool) = simplex_barycentre e1) /\
                      ~(simplex_barycentre (f:real^N->bool) = simplex_barycentre e2)`
        STRIP_ASSUME_TAC THENL
         [CONJ_TAC THEN DISCH_TAC THENL
           [SUBGOAL_THEN `(f:real^N->bool) = e1` MP_TAC;
            SUBGOAL_THEN `(f:real^N->bool) = e2` MP_TAC] THEN
          TRY(MATCH_MP_TAC MOI_S3F2_RELINT_EQ THEN
              MAP_EVERY EXISTS_TAC [`barycentric_subdivision (t:(real^N->bool)->bool)`;
                                    `simplex_barycentre (f:real^N->bool)`] THEN
              ASM_SIMP_TAC[] THEN NO_TAC) THEN
          DISCH_THEN SUBST_ALL_TAC THEN ASM_MESON_TAC[INT_ARITH `~(&2:int = &1)`];
          ALL_TAC] THEN
        REWRITE_TAC[EXTENSION; IN_INSERT; NOT_IN_EMPTY] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC FINITE_RESTRICT THEN
        ASM_MESON_TAC[MOI_BAR_SUBDIVISION_FINITE; simplicial_complex]];
      MATCH_MP_TAC MOI_S3F2_TRI_VP_EDGES THEN ASM_REWRITE_TAC[]]]);;

let MOI_S3F2_BSD_DIM = prove
 (`!(t:(real^N->bool)->bool).
     lf_simplicial_complex t /\ (!s. s IN t ==> aff_dim s <= &2)
     ==> !s. s IN barycentric_subdivision t ==> aff_dim s <= &2`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `s:real^N->bool = {}` THENL
   [ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    MP_TAC(ISPEC `t:(real^N->bool)->bool` BARYCENTRIC_SUBDIVISION_REFINES) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(MP_TAC o SPEC `s:real^N->bool` o CONJUNCT1) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `s0:real^N->bool` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC INT_LE_TRANS THEN EXISTS_TAC `aff_dim(s0:real^N->bool)` THEN
    CONJ_TAC THENL [MATCH_MP_TAC AFF_DIM_SUBSET THEN FIRST_ASSUM ACCEPT_TAC;
                    FIRST_X_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC]]);;

let MOI_S3F2_DFR_CIRCLES = prove
 (`!(t:(real^N->bool)->bool) l.
     2 <= dimindex(:N) /\ simplicial_complex t /\ simplicial_subcomplex l t /\
     (!s. s IN t ==> aff_dim s <= &2) /\
     (!e. e IN barycentric_subdivision t /\ aff_dim e = &1 /\ moi_frn_vp t l e
          ==> ?z. z IN relative_interior e /\ moi_s28_locally_r2 (UNIONS t) z)
     ==> FINITE (components (derived_frontier t l)) /\
         (!k. k IN components (derived_frontier t l) ==> pl_sphere 1 k)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_S3F2_DFR_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!e. e IN barycentric_subdivision t /\ aff_dim e = &1 /\ moi_frn_vp t l e
        ==> CARD {r | r IN barycentric_subdivision t /\ aff_dim r = &2 /\
                      (e:real^N->bool) SUBSET r} = 2`
  ASSUME_TAC THENL
   [X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
    FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
      can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s28_locally_r2"))
          (concl th))) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
    MATCH_MP_TAC MOI_S3F2_LOCAL_EDGE THEN EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[] THEN
    CONJ_TAC THENL
     [MATCH_MP_TAC BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX THEN FIRST_ASSUM ACCEPT_TAC;
      MATCH_MP_TAC MOI_S3F2_BSD_DIM THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  UNDISCH_TAC `UNIONS (moi_s3f2_fcx (t:(real^N->bool)->bool) l) = derived_frontier t l` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN MATCH_MP_TAC MOI_S4L_CM1_CIRCLES THEN
  ASM_REWRITE_TAC[] THEN X_GEN_TAC `v:real^N` THEN DISCH_TAC THEN
  MATCH_MP_TAC MOI_S3F2_FCX_DEGREE THEN ASM_REWRITE_TAC[]);;

(* FR2_EDGE_STAR: near the barycentre of a vp edge e the derived frontier   *)
(* is the union of the two segments to the barycentres of the triangles on *)
(* e.                                                                        *)

let MOI_S3F2_DFR_EDGE_STAR = prove
 (`!(t:(real^N->bool)->bool) l e.
     2 <= dimindex(:N) /\ simplicial_complex t /\ simplicial_subcomplex l t /\
     (!s. s IN t ==> aff_dim s <= &2) /\
     (!e. e IN barycentric_subdivision t /\ aff_dim e = &1 /\ moi_frn_vp t l e
          ==> ?z. z IN relative_interior e /\ moi_s28_locally_r2 (UNIONS t) z) /\
     e IN barycentric_subdivision t /\ aff_dim e = &1 /\ moi_frn_vp t l e
     ==> ?r1 r2 d.
           ~(r1 = r2) /\
           {r | r IN barycentric_subdivision t /\ aff_dim r = &2 /\ e SUBSET r} = {r1,r2} /\
           &0 < d /\
           derived_frontier t l INTER ball(simplex_barycentre e,d) =
           (segment[simplex_barycentre e,simplex_barycentre r1] UNION
            segment[simplex_barycentre e,simplex_barycentre r2]) INTER
           ball(simplex_barycentre e,d)`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `lf_simplicial_complex (t:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_SIMPLICIAL_COMPLEX_LF]; ALL_TAC] THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_FRN_SETUP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`] MOI_S3F2_DFR_COMPLEX) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `{r | r IN barycentric_subdivision t /\ aff_dim r = &2 /\ (e:real^N->bool) SUBSET r}
    HAS_SIZE 2`
  MP_TAC THENL
   [REWRITE_TAC[HAS_SIZE] THEN CONJ_TAC THENL
     [MATCH_MP_TAC FINITE_RESTRICT THEN
      ASM_MESON_TAC[MOI_BAR_SUBDIVISION_FINITE; simplicial_complex];
      FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool` o check (fun th ->
        can (find_term (fun t -> is_const t && fst(dest_const t) = "moi_s28_locally_r2"))
          (concl th))) THEN
      ASM_REWRITE_TAC[] THEN DISCH_THEN(X_CHOOSE_THEN `z:real^N` STRIP_ASSUME_TAC) THEN
      MATCH_MP_TAC MOI_S3F2_LOCAL_EDGE THEN EXISTS_TAC `z:real^N` THEN ASM_REWRITE_TAC[] THEN
      CONJ_TAC THENL
       [MATCH_MP_TAC BARYCENTRIC_SUBDIVISION_SIMPLICIAL_COMPLEX THEN FIRST_ASSUM ACCEPT_TAC;
        MATCH_MP_TAC MOI_S3F2_BSD_DIM THEN ASM_REWRITE_TAC[]]];
    ALL_TAC] THEN
  REWRITE_TAC[MOI_SCF_HAS_SIZE_2] THEN
  DISCH_THEN(X_CHOOSE_THEN `r1:real^N->bool` (X_CHOOSE_THEN `r2:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MAP_EVERY EXISTS_TAC [`r1:real^N->bool`; `r2:real^N->bool`] THEN ASM_REWRITE_TAC[] THEN
  (* the edges of the frontier complex at b(e) *)
  SUBGOAL_THEN
   `{E | E IN moi_s3f2_fcx t l /\ aff_dim E = &1 /\ simplex_barycentre e IN E} =
    {segment[simplex_barycentre e,simplex_barycentre r1],
     segment[simplex_barycentre (e:real^N->bool),simplex_barycentre r2]}`
  ASSUME_TAC THENL
   [MP_TAC(ISPECL [`t:(real^N->bool)->bool`; `l:(real^N->bool)->bool`; `e:real^N->bool`]
                  MOI_S3F2_FCX_EDGES_AT) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `E:real^N->bool` THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
    FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [EXTENSION] o check (fun th ->
      is_eq (concl th) && rhs (concl th) = `{r1:real^N->bool,r2}`)) THEN
    REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN DISCH_TAC THEN
    EQ_TAC THENL
     [DISCH_THEN(X_CHOOSE_THEN `e':real^N->bool` (X_CHOOSE_THEN `r:real^N->bool`
        STRIP_ASSUME_TAC)) THENL
       [ASM_MESON_TAC[];
        ASM_MESON_TAC[INT_ARITH `~(&1:int = &2)`]];
      STRIP_TAC THENL
       [MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `r1:real^N->bool`];
        MAP_EVERY EXISTS_TAC [`e:real^N->bool`; `r2:real^N->bool`]] THEN
      ASM_MESON_TAC[]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `segment[simplex_barycentre e,simplex_barycentre r1] IN moi_s3f2_fcx t l /\
    segment[simplex_barycentre (e:real^N->bool),simplex_barycentre r2] IN moi_s3f2_fcx t l`
  STRIP_ASSUME_TAC THENL
   [FIRST_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      rhs (concl th) = `{segment[simplex_barycentre e,simplex_barycentre r1],
                         segment[simplex_barycentre (e:real^N->bool),simplex_barycentre r2]}`))
    THEN REWRITE_TAC[EXTENSION; IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[];
    ALL_TAC] THEN
  (* the simplices missing b(e) stay away from it *)
  SUBGOAL_THEN `FINITE (moi_s3f2_fcx (t:(real^N->bool)->bool) l) /\
                (!s. s IN moi_s3f2_fcx t l ==> closed s)` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `simplicial_complex (moi_s3f2_fcx (t:(real^N->bool)->bool) l)` THEN
    REWRITE_TAC[simplicial_complex] THEN MESON_TAC[SIMPLEX_IMP_CLOSED];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`UNIONS {s | s IN moi_s3f2_fcx t l /\
                              ~(simplex_barycentre (e:real^N->bool) IN s)}`;
                 `simplex_barycentre (e:real^N->bool)`] SEPARATE_POINT_CLOSED) THEN
  ANTS_TAC THENL
   [CONJ_TAC THENL
     [MATCH_MP_TAC CLOSED_UNIONS THEN ASM_SIMP_TAC[FINITE_RESTRICT; IN_ELIM_THM];
      REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN MESON_TAC[]];
    ALL_TAC] THEN
  MATCH_MP_TAC MONO_EXISTS THEN X_GEN_TAC `d:real` THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `UNIONS (moi_s3f2_fcx (t:(real^N->bool)->bool) l) = derived_frontier t l` THEN
  DISCH_THEN(SUBST1_TAC o SYM) THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN X_GEN_TAC `x:real^N` THEN
  REWRITE_TAC[IN_INTER; IN_UNION] THEN
  ASM_CASES_TAC `(x:real^N) IN ball(simplex_barycentre e,d)` THEN ASM_REWRITE_TAC[] THEN
  REWRITE_TAC[IN_UNIONS] THEN EQ_TAC THENL
   [DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
    ASM_CASES_TAC `simplex_barycentre (e:real^N->bool) IN s` THENL
     [ALL_TAC;
      SUBGOAL_THEN `(d:real) <= dist(simplex_barycentre (e:real^N->bool),x)` MP_TAC THENL
       [FIRST_ASSUM MATCH_MP_TAC THEN REWRITE_TAC[IN_UNIONS; IN_ELIM_THM] THEN
        EXISTS_TAC `s:real^N->bool` THEN ASM_REWRITE_TAC[];
        UNDISCH_TAC `(x:real^N) IN ball(simplex_barycentre e,d)` THEN
        REWRITE_TAC[IN_BALL] THEN REAL_ARITH_TAC]] THEN
    SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) <= &1` ASSUME_TAC THENL
     [FIRST_ASSUM MATCH_MP_TAC THEN FIRST_ASSUM ACCEPT_TAC; ALL_TAC] THEN
    ASM_CASES_TAC `aff_dim(s:real^N->bool) = &1` THENL
     [SUBGOAL_THEN `(s:real^N->bool) IN
                    {E | E IN moi_s3f2_fcx t l /\ aff_dim E = &1 /\ simplex_barycentre e IN E}`
      MP_TAC THENL
       [REWRITE_TAC[IN_ELIM_THM] THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN
      STRIP_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `aff_dim(s:real^N->bool) = &0` MP_TAC THENL
     [MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN
      MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
      ASM_REWRITE_TAC[] THEN
      UNDISCH_TAC `aff_dim(s:real^N->bool) <= &1` THEN
      UNDISCH_TAC `~(aff_dim(s:real^N->bool) = &1)` THEN INT_ARITH_TAC;
      ALL_TAC] THEN
    REWRITE_TAC[AFF_DIM_EQ_0] THEN DISCH_THEN(X_CHOOSE_THEN `a:real^N` SUBST_ALL_TAC) THEN
    DISJ1_TAC THEN
    SUBGOAL_THEN `x:real^N = simplex_barycentre e` SUBST1_TAC THENL
     [ASM SET_TAC[]; REWRITE_TAC[ENDS_IN_SEGMENT]];
    STRIP_TAC THENL
     [EXISTS_TAC `segment[simplex_barycentre e,simplex_barycentre (r1:real^N->bool)]`;
      EXISTS_TAC `segment[simplex_barycentre e,simplex_barycentre (r2:real^N->bool)]`] THEN
    ASM_REWRITE_TAC[]]);;

