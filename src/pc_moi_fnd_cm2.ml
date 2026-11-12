(* ========================================================================= *)
(* pc_moi_fnd_cm2: generic facts on finite combinatorial 2-manifolds for the *)
(* Moise foundations (the 2D derived neighbourhoods of pc_moi_fnd_nb2, the   *)
(* split pc_moi_fnd_split, and DERIVED_NBHD_BALL_2 of pc_moi_fnd_rnb2):      *)
(*   the barycentric subdivision of a finite combinatorial 2-manifold is     *)
(*       one (links of b(s) via chains of c: every 2-chain extends to        *)
(*       exactly two full flags, MOI_FRN_CHAIN2_EXT; connected links; 1D     *)
(*       recognition MOI_S4L_CM1_CIRCLES);                                   *)
(*   closed stars of vertices are PL 2-cells bounded by their links          *)
(*       (cone extension).                                                   *)
(* ========================================================================= *)

needs "src/pc_moi_fnd_rn.ml";;
needs "src/pc_moi_pl1m.ml";;

prioritize_real();;
type_invention_error := true;;

(* ========================================================================= *)
(* Links of vertices in the barycentric subdivision of a finite              *)
(* combinatorial 2-manifold.                                                 *)
(* ========================================================================= *)

let MOI_FC2_BSD_VERTEX = prove
 (`!(c:(real^N->bool)->bool) w.
     moi_bar_complex c
     ==> ({w} IN barycentric_subdivision c <=>
          ?s. s IN c /\ ~(s = {}) /\ w = simplex_barycentre s)`,
  REPEAT STRIP_TAC THEN
  FIRST_ASSUM(MP_TAC o MATCH_MP MOI_BAR_SUBDIVISION_VERTICES) THEN
  REWRITE_TAC[EXTENSION; IN_ELIM_THM] THEN MESON_TAC[]);;

let MOI_FC2_BARY_IN_HULL = prove
 (`!(c:(real^N->bool)->bool) f s.
     moi_bar_complex c /\ moi_bar_chain c f /\ s IN c /\ ~(s = {}) /\
     simplex_barycentre s IN convex hull (IMAGE simplex_barycentre f)
     ==> s IN f`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_chain (c:(real^N->bool)->bool) {s}` ASSUME_TAC THENL
   [REWRITE_TAC[moi_bar_chain; SING_SUBSET; FINITE_SING; IN_SING] THEN
    ASM_MESON_TAC[SUBSET_REFL];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `f:(real^N->bool)->bool`;
                 `{s:real^N->bool}`] MOI_BAR_CHAIN_HULL_INTER) THEN
  ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING] THEN
  ASM_CASES_TAC `(s:real^N->bool) IN f` THEN ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `(f:(real^N->bool)->bool) INTER {s} = {}` SUBST1_TAC THENL
   [ASM SET_TAC[]; ALL_TAC] THEN
  REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY] THEN ASM SET_TAC[]);;

let MOI_FC2_LINK_CHAIN = prove
 (`!(c:(real^N->bool)->bool) s x.
     moi_bar_complex c /\ s IN c /\ ~(s = {})
     ==> (x IN simplicial_link (barycentric_subdivision c) (simplex_barycentre s) <=>
          ?g. moi_bar_chain c (s INSERT g) /\ ~(s IN g) /\
              x = convex hull (IMAGE simplex_barycentre g))`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN EQ_TAC THENL
   [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
    DISCH_THEN(CONJUNCTS_THEN2
      (X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC)
      (CONJUNCTS_THEN2 ASSUME_TAC
        (X_CHOOSE_THEN `t:real^N->bool` (CONJUNCTS_THEN2
          (X_CHOOSE_THEN `f:(real^N->bool)->bool` STRIP_ASSUME_TAC)
          STRIP_ASSUME_TAC)))) THEN
    SUBGOAL_THEN `(s:real^N->bool) IN f` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_FC2_BARY_IN_HULL THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(g:(real^N->bool)->bool) SUBSET f` ASSUME_TAC THENL
     [MP_TAC(ISPECL [`IMAGE simplex_barycentre (f:(real^N->bool)->bool)`;
                     `x:real^N->bool`] FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT) THEN
      ANTS_TAC THENL [ASM_MESON_TAC[MOI_BAR_CHAIN_AFFINE_INDEPENDENT]; ALL_TAC] THEN
      SUBGOAL_THEN `(x:real^N->bool) face_of convex hull (IMAGE simplex_barycentre f)`
      (fun th -> REWRITE_TAC[th]) THENL [ASM_MESON_TAC[]; ALL_TAC] THEN
      DISCH_THEN(X_CHOOSE_THEN `S:real^N->bool` STRIP_ASSUME_TAC) THEN
      ABBREV_TAC `g' = {r:real^N->bool | r IN f /\ simplex_barycentre r IN S}` THEN
      SUBGOAL_THEN `S = IMAGE simplex_barycentre (g':(real^N->bool)->bool)` ASSUME_TAC THENL
       [EXPAND_TAC "g'" THEN UNDISCH_TAC `S SUBSET IMAGE simplex_barycentre (f:(real^N->bool)->bool)` THEN
        SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `moi_bar_chain (c:(real^N->bool)->bool) g'` ASSUME_TAC THENL
       [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
        ASM_REWRITE_TAC[] THEN EXPAND_TAC "g'" THEN SET_TAC[];
        ALL_TAC] THEN
      SUBGOAL_THEN `(g:(real^N->bool)->bool) = g'` SUBST1_TAC THENL
       [MATCH_MP_TAC MOI_FRN_CHAIN_HULL_INJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
        ASM_MESON_TAC[];
        EXPAND_TAC "g'" THEN SET_TAC[]];
      ALL_TAC] THEN
    EXISTS_TAC `g:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN EXISTS_TAC `f:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[] THEN ASM SET_TAC[];
      DISCH_TAC THEN UNDISCH_TAC `~(simplex_barycentre (s:real^N->bool) IN x)` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN ASM SET_TAC[]];
    DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
    SUBGOAL_THEN `moi_bar_chain (c:(real^N->bool)->bool) g` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
      EXISTS_TAC `(s:real^N->bool) INSERT g` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN ASM_MESON_TAC[];
      ASM_REWRITE_TAC[] THEN DISCH_TAC THEN
      UNDISCH_TAC `~((s:real^N->bool) IN g)` THEN REWRITE_TAC[] THEN
      MATCH_MP_TAC MOI_FC2_BARY_IN_HULL THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[];
      EXISTS_TAC `convex hull (IMAGE simplex_barycentre ((s:real^N->bool) INSERT g))` THEN
      REPEAT CONJ_TAC THENL
       [REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN ASM_MESON_TAC[];
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_IMAGE; IN_INSERT] THEN MESON_TAC[];
        ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBCHAIN_FACE THEN
        EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[] THEN SET_TAC[]]]]);;

let MOI_FC2_CARD_EQ_2 = prove
 (`!s:A->bool. FINITE s /\ CARD s = 2 <=> ?a b. ~(a = b) /\ s = {a,b}`,
  GEN_TAC THEN REWRITE_TAC[GSYM HAS_SIZE] THEN
  CONV_TAC(LAND_CONV HAS_SIZE_CONV) THEN MESON_TAC[]);;

let MOI_FC2_LINK_VERTEX = prove
 (`!(c:(real^N->bool)->bool) s y.
     moi_bar_complex c /\ s IN c /\ ~(s = {}) /\
     {y} IN simplicial_link (barycentric_subdivision c) (simplex_barycentre s)
     ==> ?r. r IN c /\ ~(r = {}) /\ ~(r = s) /\ moi_bar_chain c {s,r} /\
             y = simplex_barycentre r`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `{y:real^N} IN simplicial_link (barycentric_subdivision c)
                 (simplex_barycentre s)` THEN
  ASM_SIMP_TAC[MOI_FC2_LINK_CHAIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain (c:(real^N->bool)->bool) g` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `(s:real^N->bool) INSERT g` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
                MOI_FRN_BARY_AFF_DIM) THEN
  ASM_REWRITE_TAC[] THEN FIRST_ASSUM(SUBST1_TAC o SYM) THEN
  REWRITE_TAC[AFF_DIM_SING; INT_ARITH `&0:int = x - &1 <=> x = &1`; INT_OF_NUM_EQ] THEN
  DISCH_TAC THEN
  SUBGOAL_THEN `?r:real^N->bool. g = {r}` (X_CHOOSE_THEN `r:real^N->bool` SUBST_ALL_TAC) THENL
   [REWRITE_TAC[GSYM MOI_FRN_SA_CARD_EQ_1] THEN ASM_MESON_TAC[moi_bar_chain];
    ALL_TAC] THEN
  EXISTS_TAC `r:real^N->bool` THEN
  UNDISCH_TAC `{y:real^N} = convex hull IMAGE simplex_barycentre {r:real^N->bool}` THEN
  REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING; SET_RULE `{a:real^N} = {b} <=> a = b`] THEN
  DISCH_TAC THEN ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `~((s:real^N->bool) IN {r})` THEN REWRITE_TAC[IN_SING] THEN
  DISCH_TAC THEN CONJ_TAC THENL
   [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT; IN_INSERT];
    CONJ_TAC THENL [ASM_MESON_TAC[MOI_BAR_CHAIN_ELEMENT; IN_INSERT]; ASM_MESON_TAC[]]]);;

let MOI_FC2_LINK_EDGE = prove
 (`!(c:(real^N->bool)->bool) s e.
     moi_bar_complex c /\ s IN c /\ ~(s = {}) /\
     e IN simplicial_link (barycentric_subdivision c) (simplex_barycentre s) /\
     aff_dim e = &1
     ==> ?r p. moi_bar_chain c {s,r,p} /\ ~(r = s) /\ ~(p = s) /\ ~(r = p) /\
               e = convex hull {simplex_barycentre r, simplex_barycentre p}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `(e:real^N->bool) IN simplicial_link (barycentric_subdivision c)
                 (simplex_barycentre s)` THEN
  ASM_SIMP_TAC[MOI_FC2_LINK_CHAIN] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain (c:(real^N->bool)->bool) g` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `(s:real^N->bool) INSERT g` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
                MOI_FRN_BARY_AFF_DIM) THEN
  ASM_REWRITE_TAC[] THEN
  UNDISCH_TAC `aff_dim(e:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN SUBST1_TAC THEN
  REWRITE_TAC[INT_ARITH `&1:int = x - &1 <=> x = &2`; INT_OF_NUM_EQ] THEN DISCH_TAC THEN
  SUBGOAL_THEN `?r p:real^N->bool. ~(r = p) /\ g = {r,p}` STRIP_ASSUME_TAC THENL
   [REWRITE_TAC[GSYM MOI_FC2_CARD_EQ_2] THEN ASM_MESON_TAC[moi_bar_chain];
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC [`r:real^N->bool`; `p:real^N->bool`] THEN
  UNDISCH_TAC `~((s:real^N->bool) IN g)` THEN
  UNDISCH_TAC `moi_bar_chain (c:(real^N->bool)->bool) (s INSERT g)` THEN
  ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY; DE_MORGAN_THM; IMAGE_CLAUSES] THEN
  REPEAT STRIP_TAC THEN ASM_MESON_TAC[]);;

let MOI_FC2_CHAIN2_EXT_SYM = prove
 (`!(c:(real^N->bool)->bool) s r.
     FINITE c /\ combinatorial_manifold 2 c /\ moi_bar_complex c /\
     moi_bar_chain c {s,r} /\ ~(s = r)
     ==> ?p1 p2. ~(p1 = p2) /\
                 !p. p IN c /\ ~(p IN {s,r}) /\ moi_bar_chain c (p INSERT {s,r}) <=>
                     p = p1 \/ p = p2`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(s:real^N->bool) SUBSET r \/ r SUBSET s` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `moi_bar_chain (c:(real^N->bool)->bool) {s,r}` THEN
    REWRITE_TAC[moi_bar_chain] THEN MESON_TAC[IN_INSERT];
    MATCH_MP_TAC MOI_FRN_CHAIN2_EXT THEN ASM_REWRITE_TAC[];
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `r:real^N->bool`; `s:real^N->bool`]
                  MOI_FRN_CHAIN2_EXT) THEN
    SUBGOAL_THEN `{r:real^N->bool,s} = {s,r}` SUBST1_TAC THENL
     [SET_TAC[]; ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN MATCH_MP_TAC THEN ASM_MESON_TAC[]]);;

let MOI_FC2_PAIR_CANCEL = prove
 (`!a b c:A. {a,b} = {a,c} /\ ~(b = a) /\ ~(c = a) ==> b = c`,
  SET_TAC[]);;

let MOI_FC2_NOT_IN_PAIR = prove
 (`!p s r:A. ~(p IN {s,r}) <=> ~(p = s) /\ ~(p = r)`,
  SET_TAC[]);;

let MOI_FC2_LINK_DEG2 = prove
 (`!(c:(real^N->bool)->bool) s y.
     FINITE c /\ combinatorial_manifold 2 c /\ s IN c /\ ~(s = {}) /\
     {y} IN simplicial_link (barycentric_subdivision c) (simplex_barycentre s)
     ==> CARD {e | e IN simplicial_link (barycentric_subdivision c)
                                        (simplex_barycentre s) /\
                   aff_dim e = &1 /\ y IN e} = 2`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `y:real^N`]
                MOI_FC2_LINK_VERTEX) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `r:real^N->bool`]
                MOI_FC2_CHAIN2_EXT_SYM) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `p1:real^N->bool` (X_CHOOSE_THEN `p2:real^N->bool`
    (CONJUNCTS_THEN2 ASSUME_TAC (LABEL_TAC "ext")))) THEN
  SUBGOAL_THEN
   `!p. p IN c /\ ~(p IN {s,r}) /\ moi_bar_chain c (p INSERT {s,r}) ==>
        moi_bar_chain (c:(real^N->bool)->bool) {r,p}`
  (LABEL_TAC "rp") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `p INSERT {s:real^N->bool,r}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `(p1:real^N->bool) IN c /\ ~(p1 IN {s,r}) /\ moi_bar_chain c (p1 INSERT {s,r}) /\
    (p2:real^N->bool) IN c /\ ~(p2 IN {s,r}) /\ moi_bar_chain c (p2 INSERT {s,r})`
  STRIP_ASSUME_TAC THENL
   [USE_THEN "ext" (fun th -> MP_TAC(SPEC `p1:real^N->bool` th) THEN
                              MP_TAC(SPEC `p2:real^N->bool` th)) THEN
    REWRITE_TAC[] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{e | e IN simplicial_link (barycentric_subdivision c) (simplex_barycentre s) /\
         aff_dim e = &1 /\ simplex_barycentre (r:real^N->bool) IN e} =
    {convex hull {simplex_barycentre r, simplex_barycentre p1},
     convex hull {simplex_barycentre r, simplex_barycentre p2}}`
  SUBST1_TAC THENL
   [ALL_TAC;
    MATCH_MP_TAC(MESON[MOI_FC2_CARD_EQ_2] `~(a:real^N->bool = b) ==> CARD {a,b} = 2`) THEN
    DISCH_TAC THEN
    SUBGOAL_THEN `{r,p1} = {r:real^N->bool,p2}` MP_TAC THENL
     [MATCH_MP_TAC MOI_FRN_CHAIN_HULL_INJ THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_SIMP_TAC[IMAGE_CLAUSES];
      UNDISCH_TAC `~((p1:real^N->bool) IN {s,r})` THEN
      UNDISCH_TAC `~((p2:real^N->bool) IN {s,r})` THEN
      UNDISCH_TAC `~(p1:real^N->bool = p2)` THEN
      REWRITE_TAC[MOI_FC2_NOT_IN_PAIR] THEN MESON_TAC[MOI_FC2_PAIR_CANCEL]]] THEN
  GEN_REWRITE_TAC I [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM; IN_INSERT; NOT_IN_EMPTY] THEN
  X_GEN_TAC `e:real^N->bool` THEN EQ_TAC THENL
   [STRIP_TAC THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `e:real^N->bool`]
                  MOI_FC2_LINK_EDGE) THEN
    ASM_REWRITE_TAC[] THEN
    DISCH_THEN(X_CHOOSE_THEN `r':real^N->bool` (X_CHOOSE_THEN `p':real^N->bool`
      STRIP_ASSUME_TAC)) THEN
    SUBGOAL_THEN `moi_bar_chain (c:(real^N->bool)->bool) {r',p'}` ASSUME_TAC THENL
     [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
      EXISTS_TAC `{s:real^N->bool,r',p'}` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `(r:real^N->bool) IN {r',p'}` MP_TAC THENL
     [MATCH_MP_TAC MOI_FC2_BARY_IN_HULL THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
      UNDISCH_TAC `simplex_barycentre (r:real^N->bool) IN e` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THEN
    FIRST_X_ASSUM(SUBST_ALL_TAC o SYM) THENL
     [SUBGOAL_THEN `(p':real^N->bool) = p1 \/ p' = p2` MP_TAC THENL
       [REMOVE_THEN "ext" (fun th -> REWRITE_TAC[GSYM th]) THEN
        REPEAT CONJ_TAC THENL
         [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{s:real^N->bool,r,p'}`;
                         `p':real^N->bool`] MOI_BAR_CHAIN_ELEMENT) THEN
          ASM_REWRITE_TAC[IN_INSERT] THEN SIMP_TAC[];
          ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
          UNDISCH_TAC `moi_bar_chain (c:(real^N->bool)->bool) {s,r,p'}` THEN
          MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]];
        STRIP_TAC THEN ASM_REWRITE_TAC[]];
      SUBGOAL_THEN `(r':real^N->bool) = p1 \/ r' = p2` MP_TAC THENL
       [REMOVE_THEN "ext" (fun th -> REWRITE_TAC[GSYM th]) THEN
        REPEAT CONJ_TAC THENL
         [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{s:real^N->bool,r',r}`;
                         `r':real^N->bool`] MOI_BAR_CHAIN_ELEMENT) THEN
          ASM_REWRITE_TAC[IN_INSERT] THEN SIMP_TAC[];
          ASM_REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY];
          UNDISCH_TAC `moi_bar_chain (c:(real^N->bool)->bool) {s,r',r}` THEN
          MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[]];
        STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
        REWRITE_TAC[SET_RULE `{a:real^N,b} = {b,a}`]]];
    REMOVE_THEN "ext" (K ALL_TAC) THEN
    SUBGOAL_THEN
     `!p. (p:real^N->bool) IN c /\ ~(p IN {s,r}) /\ moi_bar_chain c (p INSERT {s,r})
          ==> convex hull {simplex_barycentre r, simplex_barycentre p} IN
              simplicial_link (barycentric_subdivision c) (simplex_barycentre s) /\
              aff_dim (convex hull {simplex_barycentre r, simplex_barycentre p}) = &1 /\
              simplex_barycentre r IN
              convex hull {simplex_barycentre r, simplex_barycentre p}`
    (fun th -> STRIP_TAC THEN ASM_REWRITE_TAC[] THEN MATCH_MP_TAC th THEN
               ASM_REWRITE_TAC[]) THEN
    X_GEN_TAC `p:real^N->bool` THEN STRIP_TAC THEN
    SUBGOAL_THEN `moi_bar_chain (c:(real^N->bool)->bool) {r,p}` ASSUME_TAC THENL
     [USE_THEN "rp" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    REPEAT CONJ_TAC THENL
     [ASM_SIMP_TAC[MOI_FC2_LINK_CHAIN] THEN
      EXISTS_TAC `{r:real^N->bool,p}` THEN REWRITE_TAC[IMAGE_CLAUSES] THEN
      CONJ_TAC THENL
       [UNDISCH_TAC `moi_bar_chain (c:(real^N->bool)->bool) (p INSERT {s,r})` THEN
        MATCH_MP_TAC EQ_IMP THEN AP_TERM_TAC THEN SET_TAC[];
        UNDISCH_TAC `~((p:real^N->bool) IN {s,r})` THEN
        UNDISCH_TAC `~(r:real^N->bool = s)` THEN
        REWRITE_TAC[MOI_FC2_NOT_IN_PAIR; IN_INSERT; NOT_IN_EMPTY] THEN MESON_TAC[]];
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{r:real^N->bool,p}`]
                    MOI_FRN_BARY_AFF_DIM) THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN DISCH_THEN SUBST1_TAC THEN
      SUBGOAL_THEN `CARD {r:real^N->bool,p} = 2` SUBST1_TAC THENL
       [SUBGOAL_THEN `~(r:real^N->bool = p)` ASSUME_TAC THENL
         [UNDISCH_TAC `~((p:real^N->bool) IN {s,r})` THEN
          REWRITE_TAC[MOI_FC2_NOT_IN_PAIR] THEN MESON_TAC[];
          ALL_TAC] THEN
        ASM_SIMP_TAC[FINITE_INSERT; FINITE_EMPTY; CARD_CLAUSES; IN_INSERT;
                     NOT_IN_EMPTY] THEN
        CONV_TAC NUM_REDUCE_CONV;
        INT_ARITH_TAC];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]]]);;

(* Link edges of b(s) are the flags (vertex, edge, triangle) of c through s *)
(* with s removed.                                                          *)

let MOI_FC2_TRIPLE_DELETE = prove
 (`!s r p a b c:A.
     {s,r,p} = {a,b,c} /\ ~(r = s) /\ ~(p = s) /\ ~(b = a) /\ ~(c = a) /\
     ~(c = b) /\ s = a
     ==> {r,p} = {b,c}`,
  SET_TAC[]);;

let MOI_FC2_CARD_3 = prove
 (`!a b c:A. ~(a = b) /\ ~(a = c) /\ ~(b = c) ==> CARD {a,b,c} = 3`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `{a:A,b,c} HAS_SIZE 3` (fun th -> MESON_TAC[th; HAS_SIZE]) THEN
  CONV_TAC HAS_SIZE_CONV THEN MAP_EVERY EXISTS_TAC [`a:A`; `b:A`; `c:A`] THEN
  ASM_REWRITE_TAC[]);;

let MOI_FC2_LINK_EDGE_FLAG = prove
 (`!(c:(real^N->bool)->bool) s e.
     FINITE c /\ combinatorial_manifold 2 c /\ s IN c /\ ~(s = {}) /\
     e IN simplicial_link (barycentric_subdivision c) (simplex_barycentre s) /\
     aff_dim e = &1
     ==> ?u e' t'. {u} IN c /\ e' IN c /\ aff_dim e' = &1 /\ t' IN c /\
                   aff_dim t' = &2 /\ u IN e' /\ e' SUBSET t' /\
                   ((s = {u} /\
                     e = convex hull {simplex_barycentre e', simplex_barycentre t'}) \/
                    (s = e' /\ e = convex hull {u, simplex_barycentre t'}) \/
                    (s = t' /\ e = convex hull {u, simplex_barycentre e'}))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `e:real^N->bool`]
                MOI_FC2_LINK_EDGE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `r:real^N->bool` (X_CHOOSE_THEN `p:real^N->bool`
    STRIP_ASSUME_TAC)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{s:real^N->bool,r,p}`]
                MOI_FRN_CHAIN3_FLAG) THEN
  ASM_REWRITE_TAC[] THEN ANTS_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[MOI_FRN_SA_CM_DIM]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FC2_CARD_3 THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `e':real^N->bool`
    (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC))) THEN
  MAP_EVERY EXISTS_TAC [`u:real^N`; `e':real^N->bool`; `t':real^N->bool`] THEN
  ASM_REWRITE_TAC[] THEN
  SUBGOAL_THEN `~(e':real^N->bool = {u}) /\ ~(t':real^N->bool = {u}) /\ ~(t' = e')`
  STRIP_ASSUME_TAC THENL
   [REPEAT CONJ_TAC THEN DISCH_TAC THEN
    RULE_ASSUM_TAC(REWRITE_RULE[]) THEN
    REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
      (try fst(dest_const(rator(lhs(concl th)))) = "aff_dim" with Failure _ -> false)))) THEN
    ASM_REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(s:real^N->bool) IN {{u},e',t'}` MP_TAC THENL
   [FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th ->
      is_eq (concl th) && lhs(concl th) = `{s:real^N->bool,r,p}`)) THEN
    REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `convex hull {simplex_barycentre r, simplex_barycentre p} =
    convex hull (IMAGE simplex_barycentre {r:real^N->bool,p})`
  SUBST1_TAC THENL [REWRITE_TAC[IMAGE_CLAUSES]; ALL_TAC] THEN
  REWRITE_TAC[IN_INSERT; NOT_IN_EMPTY] THEN STRIP_TAC THENL
   [DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{r:real^N->bool,p} = {e',t'}` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_FC2_TRIPLE_DELETE THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `{u:real^N}`] THEN ASM_REWRITE_TAC[];
      REWRITE_TAC[IMAGE_CLAUSES]];
    DISJ2_TAC THEN DISJ1_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{r:real^N->bool,p} = {{u},t'}` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_FC2_TRIPLE_DELETE THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `e':real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq (concl th) && lhs(concl th) = `{s:real^N->bool,r,p}`)) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IMAGE_CLAUSES; MOI_FRN_BARYCENTRE_SING]];
    DISJ2_TAC THEN DISJ2_TAC THEN ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `{r:real^N->bool,p} = {{u},e'}` SUBST1_TAC THENL
     [MATCH_MP_TAC MOI_FC2_TRIPLE_DELETE THEN
      MAP_EVERY EXISTS_TAC [`s:real^N->bool`; `t':real^N->bool`] THEN
      ASM_REWRITE_TAC[] THEN
      FIRST_X_ASSUM(SUBST1_TAC o check (fun th ->
        is_eq (concl th) && lhs(concl th) = `{s:real^N->bool,r,p}`)) THEN
      ASM_REWRITE_TAC[] THEN SET_TAC[];
      REWRITE_TAC[IMAGE_CLAUSES; MOI_FRN_BARYCENTRE_SING]]]);;

(* Connectedness of the links: helpers. *)

let MOI_FC2_VERTEX_EXTREME = prove
 (`!(c:(real^N->bool)->bool) u q.
     moi_bar_complex c /\ {u} IN c /\ q IN c /\ u IN q ==> u extreme_point_of q`,
  REPEAT STRIP_TAC THEN REWRITE_TAC[GSYM FACE_OF_SING] THEN
  SUBGOAL_THEN `{u:real^N} = {u} INTER q` SUBST1_TAC THENL
   [ASM SET_TAC[]; ASM_MESON_TAC[moi_bar_complex]]);;

let MOI_FC2_FLAG_LINK_EDGE = prove
 (`!(c:(real^N->bool)->bool) s r p.
     moi_bar_complex c /\ s IN c /\ ~(s = {}) /\ moi_bar_chain c {s,r,p} /\
     ~(r = s) /\ ~(p = s)
     ==> convex hull {simplex_barycentre r, simplex_barycentre p} IN
         simplicial_link (barycentric_subdivision c) (simplex_barycentre s)`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[MOI_FC2_LINK_CHAIN] THEN
  EXISTS_TAC `{r:real^N->bool,p}` THEN ASM_REWRITE_TAC[IMAGE_CLAUSES] THEN
  REWRITE_TAC[MOI_FC2_NOT_IN_PAIR] THEN ASM_MESON_TAC[]);;

let MOI_FC2_LINK_POINT = prove
 (`!(c:(real^N->bool)->bool) s x.
     FINITE c /\ combinatorial_manifold 2 c /\ s IN c /\ ~(s = {}) /\
     x IN UNIONS (simplicial_link (barycentric_subdivision c) (simplex_barycentre s))
     ==> ?e. e IN simplicial_link (barycentric_subdivision c) (simplex_barycentre s) /\
             aff_dim e = &1 /\ x IN e`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; combinatorial_manifold]; ALL_TAC] THEN
  UNDISCH_TAC `(x:real^N) IN UNIONS (simplicial_link (barycentric_subdivision c)
                 (simplex_barycentre s))` THEN
  REWRITE_TAC[IN_UNIONS] THEN
  DISCH_THEN(X_CHOOSE_THEN `q:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `q:real^N->bool`]
                MOI_FC2_LINK_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain (c:(real^N->bool)->bool) g` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `(s:real^N->bool) INSERT g` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (g:(real^N->bool)->bool) /\ CARD ((s:real^N->bool) INSERT g) <= 3`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THENL [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
    MATCH_MP_TAC MOI_FRN_CHAIN_CARD_LE3 THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
    ASM_REWRITE_TAC[] THEN ASM_MESON_TAC[MOI_FRN_SA_CM_DIM];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (g:(real^N->bool)->bool) <= 2` ASSUME_TAC THENL
   [UNDISCH_TAC `CARD ((s:real^N->bool) INSERT g) <= 3` THEN
    ASM_SIMP_TAC[CARD_CLAUSES] THEN ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `~(g:(real^N->bool)->bool = {})` ASSUME_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `(x:real^N) IN q` THEN ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_EMPTY;
                                                      NOT_IN_EMPTY];
    ALL_TAC] THEN
  SUBGOAL_THEN `CARD (g:(real^N->bool)->bool) = 1 \/ CARD g = 2` STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC `CARD (g:(real^N->bool)->bool) <= 2` THEN
    UNDISCH_TAC `~(g:(real^N->bool)->bool = {})` THEN
    ASM_SIMP_TAC[GSYM CARD_EQ_0] THEN ARITH_TAC;
    SUBGOAL_THEN `?r:real^N->bool. g = {r}` (X_CHOOSE_THEN `r:real^N->bool` SUBST_ALL_TAC)
    THENL [ASM_MESON_TAC[MOI_FRN_SA_CARD_EQ_1]; ALL_TAC] THEN
    SUBGOAL_THEN `q = {x:real^N}` SUBST_ALL_TAC THENL
     [UNDISCH_TAC `(x:real^N) IN q` THEN
      ASM_REWRITE_TAC[IMAGE_CLAUSES; CONVEX_HULL_SING] THEN SET_TAC[];
      ALL_TAC] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `x:real^N`]
                  MOI_FC2_LINK_DEG2) THEN
    ASM_REWRITE_TAC[] THEN
    ABBREV_TAC `S = {e | e IN simplicial_link (barycentric_subdivision c)
                                              (simplex_barycentre s) /\
                         aff_dim e = &1 /\ (x:real^N) IN e}` THEN
    ASM_CASES_TAC `S:(real^N->bool)->bool = {}` THEN
    ASM_REWRITE_TAC[CARD_CLAUSES; ARITH_EQ] THEN
    UNDISCH_TAC `~(S:(real^N->bool)->bool = {})` THEN EXPAND_TAC "S" THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN MESON_TAC[];
    EXISTS_TAC `q:real^N->bool` THEN ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
                  MOI_FRN_BARY_AFF_DIM) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN INT_ARITH_TAC]);;

let MOI_FC2_IN_OWN_COMPONENT = prove
 (`!s (x:real^N). x IN s ==> x IN connected_component s x`,
  REPEAT STRIP_TAC THEN ONCE_REWRITE_TAC[IN] THEN
  MATCH_MP_TAC CONNECTED_COMPONENT_REFL THEN ASM_REWRITE_TAC[]);;

let MOI_FC2_COMP_EDGE = prove
 (`!(S:real^N->bool) e x y.
     connected e /\ e SUBSET S /\ y IN e /\ y IN connected_component S x
     ==> e SUBSET connected_component S x`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `connected_component S (y:real^N) = connected_component S x`
  (SUBST1_TAC o SYM) THENL
   [ASM_MESON_TAC[CONNECTED_COMPONENT_EQ];
    MATCH_MP_TAC CONNECTED_COMPONENT_MAXIMAL THEN ASM_REWRITE_TAC[]]);;

let MOI_FC2_CONN_FROM_EDGES = prove
 (`!(L:(real^N->bool)->bool) x0.
     (!x. x IN UNIONS L ==> ?e. e IN L /\ aff_dim e = &1 /\ x IN e) /\
     (!e. e IN L /\ aff_dim e = &1 ==> e SUBSET connected_component (UNIONS L) x0)
     ==> connected (UNIONS L)`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `UNIONS L = connected_component (UNIONS L) (x0:real^N)`
  (fun th -> ONCE_REWRITE_TAC[th] THEN REWRITE_TAC[CONNECTED_CONNECTED_COMPONENT]) THEN
  MATCH_MP_TAC SUBSET_ANTISYM THEN REWRITE_TAC[CONNECTED_COMPONENT_SUBSET] THEN
  REWRITE_TAC[SUBSET] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `x:real^N`) THEN ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `e:real^N->bool` STRIP_ASSUME_TAC) THEN
  FIRST_X_ASSUM(MP_TAC o SPEC `e:real^N->bool`) THEN ASM_REWRITE_TAC[] THEN
  ASM SET_TAC[]);;

let MOI_FC2_CHAIN3 = prove
 (`!(c:(real^N->bool)->bool) x y z.
     x IN c /\ y IN c /\ z IN c /\ ~(x = {}) /\ ~(y = {}) /\ ~(z = {}) /\
     (x SUBSET y \/ y SUBSET x) /\ (x SUBSET z \/ z SUBSET x) /\
     (y SUBSET z \/ z SUBSET y)
     ==> moi_bar_chain c {x,y,z}`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  REWRITE_TAC[moi_bar_chain; FINITE_INSERT; FINITE_EMPTY; INSERT_SUBSET; EMPTY_SUBSET;
              IN_INSERT; NOT_IN_EMPTY] THEN
  ASM_REWRITE_TAC[] THEN REPEAT GEN_TAC THEN STRIP_TAC THEN
  ASM_REWRITE_TAC[SUBSET_REFL] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (is_disj o concl)) THEN
  ASM_MESON_TAC[]);;

let MOI_FC2_EXTREME_VERTEX = prove
 (`!(c:(real^N->bool)->bool) t u.
     moi_bar_complex c /\ t IN c /\ u extreme_point_of t ==> {u} IN c`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_BAR_COMPLEX_FACE THEN
  EXISTS_TAC `t:real^N->bool` THEN ASM_REWRITE_TAC[FACE_OF_SING]);;

let MOI_FC2_EDGE_OF_SIMPLEX = prove
 (`!(c:(real^N->bool)->bool) t u v.
     moi_bar_complex c /\ t IN c /\ u extreme_point_of t /\ v extreme_point_of t /\
     ~(u = v)
     ==> convex hull {u,v} IN c /\ aff_dim (convex hull {u,v}) = &1 /\
         convex hull {u,v} SUBSET t`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `(convex hull {u:real^N,v}) face_of t` ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (t:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
    DISCH_THEN(CONJUNCTS_THEN2 ASSUME_TAC SUBST1_TAC) THEN
    ASM_SIMP_TAC[FACE_OF_CONVEX_HULL_AFFINE_INDEPENDENT] THEN
    EXISTS_TAC `{u:real^N,v}` THEN REWRITE_TAC[] THEN
    REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET; IN_ELIM_THM] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  REPEAT CONJ_TAC THENL
   [MATCH_MP_TAC MOI_BAR_COMPLEX_FACE THEN EXISTS_TAC `t:real^N->bool` THEN
    ASM_REWRITE_TAC[];
    ASM_REWRITE_TAC[AFF_DIM_CONVEX_HULL; AFF_DIM_2];
    ASM_MESON_TAC[FACE_OF_IMP_SUBSET]]);;

(* The three cases of connectedness: s an edge, a triangle, a vertex. *)

let MOI_FC2_HULL_TAC = TRY(MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT] THEN NO_TAC);;

let MOI_FC2_LINK_EDGE_SUBSET = prove
 (`!(c:(real^N->bool)->bool) s e x0 y.
     e IN simplicial_link (barycentric_subdivision c) (simplex_barycentre s) /\
     y IN e /\
     y IN connected_component
            (UNIONS (simplicial_link (barycentric_subdivision c) (simplex_barycentre s)))
            x0 /\
     lf_simplicial_complex c
     ==> e SUBSET connected_component
            (UNIONS (simplicial_link (barycentric_subdivision c) (simplex_barycentre s)))
            x0`,
  REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FC2_COMP_EDGE THEN
  EXISTS_TAC `y:real^N` THEN ASM_REWRITE_TAC[] THEN CONJ_TAC THENL
   [SUBGOAL_THEN `(e:real^N->bool) IN barycentric_subdivision c` MP_TAC THENL
     [UNDISCH_TAC `(e:real^N->bool) IN simplicial_link (barycentric_subdivision c)
                     (simplex_barycentre s)` THEN
      REWRITE_TAC[simplicial_link; IN_ELIM_THM] THEN SIMP_TAC[];
      REWRITE_TAC[MOI_BAR_IN_SUBDIVISION] THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      MATCH_MP_TAC CONVEX_CONNECTED THEN REWRITE_TAC[CONVEX_CONVEX_HULL]];
    ASM SET_TAC[]]);;

let MOI_FC2_DISTINCT_DIMS = prove
 (`!x y z:real^N->bool.
     aff_dim x = &0 /\ aff_dim y = &1 /\ aff_dim z = &2
     ==> ~(x = y) /\ ~(x = z) /\ ~(y = z) /\ ~(y = x) /\ ~(z = x) /\ ~(z = y) /\
         ~(x = {}) /\ ~(y = {}) /\ ~(z = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN REPEAT CONJ_TAC THEN DISCH_TAC THEN
  REPEAT(FIRST_X_ASSUM(MP_TAC o check (fun th -> is_eq (concl th) &&
    (try fst(dest_const(rator(lhs(concl th)))) = "aff_dim" with Failure _ -> false)))) THEN
  FIRST_X_ASSUM SUBST1_TAC THEN REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC);;

let MOI_FC2_CONN_EDGE_CASE = prove
 (`!(c:(real^N->bool)->bool) s.
     FINITE c /\ combinatorial_manifold 2 c /\ s IN c /\ aff_dim s = &1
     ==> ?x0. x0 IN UNIONS (simplicial_link (barycentric_subdivision c)
                                            (simplex_barycentre s)) /\
              !e. e IN simplicial_link (barycentric_subdivision c) (simplex_barycentre s) /\
                  aff_dim e = &1
                  ==> e SUBSET connected_component
                        (UNIONS (simplicial_link (barycentric_subdivision c)
                                                 (simplex_barycentre s))) x0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool) /\ lf_simplicial_complex c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &1` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FRN_CM_PURE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `t1:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FRN_SEG_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `a:real^N` (X_CHOOSE_THEN `b:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(a:real^N) IN s /\ (b:real^N) IN s /\
                (!u:real^N. u extreme_point_of s ==> u = a \/ u = b)`
  STRIP_ASSUME_TAC THENL
   [ASM_REWRITE_TAC[GSYM SEGMENT_CONVEX_HULL; EXTREME_POINT_OF_SEGMENT;
                    ENDS_IN_SEGMENT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `s = convex hull {a:real^N,b}`)) THEN
  MP_TAC(ISPECL [`{a:real^N}`; `s:real^N->bool`; `t1:real^N->bool`]
                MOI_FC2_DISTINCT_DIMS) THEN
  MP_TAC(ISPECL [`{b:real^N}`; `s:real^N->bool`; `t1:real^N->bool`]
                MOI_FC2_DISTINCT_DIMS) THEN
  REWRITE_TAC[AFF_DIM_SING] THEN
  SUBGOAL_THEN `aff_dim(s:real^N->bool) = &1 /\ aff_dim(t1:real^N->bool) = &2`
  (fun th -> REWRITE_TAC[th]) THENL [ASM_REWRITE_TAC[]; ALL_TAC] THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `convex hull {a, simplex_barycentre t1} IN
      simplicial_link (barycentric_subdivision c) (simplex_barycentre s) /\
    convex hull {b, simplex_barycentre t1} IN
      simplicial_link (barycentric_subdivision c) (simplex_barycentre (s:real^N->bool))`
  STRIP_ASSUME_TAC THENL
   [CONJ_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [GSYM MOI_FRN_BARYCENTRE_SING] THEN
    MATCH_MP_TAC MOI_FC2_FLAG_LINK_EDGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FC2_CHAIN3 THEN ASM_REWRITE_TAC[] THEN
    REWRITE_TAC[SET_RULE `~({a:real^N} = {})`] THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN
    ASM_MESON_TAC[HULL_INC; IN_INSERT; SUBSET_TRANS; SING_SUBSET];
    ALL_TAC] THEN
  EXISTS_TAC `a:real^N` THEN
  ABBREV_TAC `P = connected_component
                    (UNIONS (simplicial_link (barycentric_subdivision c)
                                             (simplex_barycentre s))) (a:real^N)` THEN
  SUBGOAL_THEN `(a:real^N) IN P /\ b IN P` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `(a:real^N) IN P` ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN MATCH_MP_TAC MOI_FC2_IN_OWN_COMPONENT THEN
      REWRITE_TAC[IN_UNIONS] THEN
      EXISTS_TAC `convex hull {a:real^N, simplex_barycentre t1}` THEN
      ASM_REWRITE_TAC[] THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
      ALL_TAC] THEN
    ASM_REWRITE_TAC[] THEN
    SUBGOAL_THEN `convex hull {a:real^N, simplex_barycentre t1} SUBSET P` ASSUME_TAC THENL
     [EXPAND_TAC "P" THEN MATCH_MP_TAC MOI_FC2_LINK_EDGE_SUBSET THEN
      EXISTS_TAC `a:real^N` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN MOI_FC2_HULL_TAC THEN ASM_MESON_TAC[];
      ALL_TAC] THEN
    SUBGOAL_THEN `convex hull {b:real^N, simplex_barycentre t1} SUBSET P` MP_TAC THENL
     [EXPAND_TAC "P" THEN MATCH_MP_TAC MOI_FC2_LINK_EDGE_SUBSET THEN
      EXISTS_TAC `simplex_barycentre (t1:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
      REPEAT CONJ_TAC THEN MOI_FC2_HULL_TAC THEN
      SUBGOAL_THEN `simplex_barycentre (t1:real^N->bool) IN P` MP_TAC THENL
       [FIRST_X_ASSUM(MATCH_MP_TAC o REWRITE_RULE[SUBSET]) THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
        EXPAND_TAC "P" THEN REWRITE_TAC[]];
      REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(a:real^N) IN P` THEN EXPAND_TAC "P" THEN
    MESON_TAC[CONNECTED_COMPONENT_SUBSET; SUBSET];
    ALL_TAC] THEN
  X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `e:real^N->bool`]
                MOI_FC2_LINK_EDGE_FLAG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `e':real^N->bool`
    (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC))) THENL
   [UNDISCH_TAC `aff_dim(s:real^N->bool) = &1` THEN ASM_REWRITE_TAC[AFF_DIM_SING] THEN
    INT_ARITH_TAC;
    ALL_TAC;
    UNDISCH_TAC `aff_dim(s:real^N->bool) = &1` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC] THEN
  SUBGOAL_THEN `(u:real^N) IN P` ASSUME_TAC THENL
   [SUBGOAL_THEN `(u:real^N) extreme_point_of s` MP_TAC THENL
     [MATCH_MP_TAC MOI_FC2_VERTEX_EXTREME THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[];
      DISCH_THEN(fun th -> FIRST_X_ASSUM(MP_TAC o C MATCH_MP th o check (is_forall o concl))) THEN
      STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXPAND_TAC "P" THEN MATCH_MP_TAC MOI_FC2_LINK_EDGE_SUBSET THEN
  EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN MOI_FC2_HULL_TAC THEN ASM_MESON_TAC[]);;

let MOI_FC2_CONN_TRI_CASE = prove
 (`!(c:(real^N->bool)->bool) s.
     FINITE c /\ combinatorial_manifold 2 c /\ s IN c /\ aff_dim s = &2
     ==> ?x0. x0 IN UNIONS (simplicial_link (barycentric_subdivision c)
                                            (simplex_barycentre s)) /\
              !e. e IN simplicial_link (barycentric_subdivision c) (simplex_barycentre s) /\
                  aff_dim e = &1
                  ==> e SUBSET connected_component
                        (UNIONS (simplicial_link (barycentric_subdivision c)
                                                 (simplex_barycentre s))) x0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool) /\ lf_simplicial_complex c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `~(s:real^N->bool = {})` ASSUME_TAC THENL
   [DISCH_TAC THEN UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN
    ASM_REWRITE_TAC[AFF_DIM_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `?v0:real^N. v0 extreme_point_of s` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` MP_TAC THENL
     [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
    DISCH_THEN(MP_TAC o MATCH_MP MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
    DISCH_THEN(MP_TAC o CONJUNCT2) THEN
    ASM_CASES_TAC `{v:real^N | v extreme_point_of s} = {}` THEN
    ASM_REWRITE_TAC[CONVEX_HULL_EMPTY] THEN
    UNDISCH_TAC `~({v:real^N | v extreme_point_of s} = {})` THEN
    REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN MESON_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `{v0:real^N} IN c` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FC2_EXTREME_VERTEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `v0:real^N`]
                MOI_FRN_TRI_VERTS) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[extreme_point_of]; ALL_TAC] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN
   `(!u:real^N. u extreme_point_of s <=> u = v0 \/ u = x \/ u = y)`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; IN_INSERT; NOT_IN_EMPTY];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `s = convex hull {v0:real^N,x,y}`)) THEN
  SUBGOAL_THEN `{x:real^N} IN c /\ {y:real^N} IN c` STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FC2_EXTREME_VERTEX]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `v0:real^N`; `x:real^N`]
                MOI_FC2_EDGE_OF_SIMPLEX) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `v0:real^N`; `y:real^N`]
                MOI_FC2_EDGE_OF_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `q1 = convex hull {v0:real^N,x}` THEN
  ABBREV_TAC `q2 = convex hull {v0:real^N,y}` THEN
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `(v0:real^N) IN q1 /\ x IN q1 /\ v0 IN q2 /\ y IN q2` STRIP_ASSUME_TAC THENL
   [MAP_EVERY EXPAND_TAC ["q1"; "q2"] THEN REPEAT CONJ_TAC THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`{v0:real^N}`; `q1:real^N->bool`; `s:real^N->bool`]
                MOI_FC2_DISTINCT_DIMS) THEN
  MP_TAC(ISPECL [`{x:real^N}`; `q1:real^N->bool`; `s:real^N->bool`]
                MOI_FC2_DISTINCT_DIMS) THEN
  MP_TAC(ISPECL [`{v0:real^N}`; `q2:real^N->bool`; `s:real^N->bool`]
                MOI_FC2_DISTINCT_DIMS) THEN
  MP_TAC(ISPECL [`{y:real^N}`; `q2:real^N->bool`; `s:real^N->bool`]
                MOI_FC2_DISTINCT_DIMS) THEN
  ASM_REWRITE_TAC[AFF_DIM_SING] THEN REPEAT STRIP_TAC THEN
  SUBGOAL_THEN
   `!u q. {u} IN c /\ q IN c /\ ~(q = {}) /\ u IN q /\ q SUBSET s /\
          ~({u:real^N} = s) /\ ~(q = s)
          ==> convex hull {u, simplex_barycentre q} IN
              simplicial_link (barycentric_subdivision c) (simplex_barycentre s)`
  ASSUME_TAC THENL
   [REPEAT STRIP_TAC THEN
    GEN_REWRITE_TAC (LAND_CONV o RAND_CONV o LAND_CONV) [GSYM MOI_FRN_BARYCENTRE_SING] THEN
    MATCH_MP_TAC MOI_FC2_FLAG_LINK_EDGE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC MOI_FC2_CHAIN3 THEN ASM_REWRITE_TAC[SET_RULE `~({a:real^N} = {})`] THEN
    ASM_REWRITE_TAC[SING_SUBSET] THEN ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `v0:real^N` THEN
  ABBREV_TAC `P = connected_component
                    (UNIONS (simplicial_link (barycentric_subdivision c)
                                             (simplex_barycentre s))) (v0:real^N)` THEN
  SUBGOAL_THEN `(v0:real^N) IN P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC MOI_FC2_IN_OWN_COMPONENT THEN
    REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `convex hull {v0:real^N, simplex_barycentre q1}` THEN
    CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!u q w. {u} IN c /\ q IN c /\ ~(q = {}) /\ u IN q /\ q SUBSET s /\
            ~({u:real^N} = s) /\ ~(q = s) /\
            (w = u \/ w = simplex_barycentre q) /\ w IN P
            ==> convex hull {u, simplex_barycentre q} SUBSET P`
  (LABEL_TAC "edgeP") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "P" THEN
    MATCH_MP_TAC MOI_FC2_LINK_EDGE_SUBSET THEN EXISTS_TAC `w:real^N` THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [FIRST_X_ASSUM MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (CONJ_TAC THENL [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC]) THEN
    UNDISCH_TAC `(w:real^N) IN P` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `(x:real^N) IN P /\ y IN P` STRIP_ASSUME_TAC THENL
   [SUBGOAL_THEN `simplex_barycentre (q1:real^N->bool) IN P /\
                  simplex_barycentre (q2:real^N->bool) IN P` STRIP_ASSUME_TAC THENL
     [CONJ_TAC THEN
      MATCH_MP_TAC(SET_RULE `!s t (x:real^N). x IN s /\ s SUBSET t ==> x IN t`) THENL
       [EXISTS_TAC `convex hull {v0:real^N, simplex_barycentre q1}`;
        EXISTS_TAC `convex hull {v0:real^N, simplex_barycentre q2}`] THEN
      (CONJ_TAC THENL [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC]) THEN
      USE_THEN "edgeP" MATCH_MP_TAC THEN EXISTS_TAC `v0:real^N` THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    CONJ_TAC THEN
    MATCH_MP_TAC(SET_RULE `!s t (x:real^N). x IN s /\ s SUBSET t ==> x IN t`) THENL
     [EXISTS_TAC `convex hull {x:real^N, simplex_barycentre q1}`;
      EXISTS_TAC `convex hull {y:real^N, simplex_barycentre q2}`] THEN
    (CONJ_TAC THENL [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC]) THEN
    USE_THEN "edgeP" MATCH_MP_TAC THENL
     [EXISTS_TAC `simplex_barycentre (q1:real^N->bool)`;
      EXISTS_TAC `simplex_barycentre (q2:real^N->bool)`] THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `(v0:real^N) IN P` THEN EXPAND_TAC "P" THEN
    MESON_TAC[CONNECTED_COMPONENT_SUBSET; SUBSET];
    ALL_TAC] THEN
  X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `e:real^N->bool`]
                MOI_FC2_LINK_EDGE_FLAG) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `e':real^N->bool`
    (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC))) THENL
   [UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN ASM_REWRITE_TAC[AFF_DIM_SING] THEN
    INT_ARITH_TAC;
    UNDISCH_TAC `aff_dim(s:real^N->bool) = &2` THEN ASM_REWRITE_TAC[] THEN
    INT_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `(u:real^N) IN P` ASSUME_TAC THENL
   [SUBGOAL_THEN `(u:real^N) extreme_point_of s` MP_TAC THENL
     [MATCH_MP_TAC MOI_FC2_VERTEX_EXTREME THEN EXISTS_TAC `c:(real^N->bool)->bool` THEN
      ASM_MESON_TAC[SUBSET];
      ASM_REWRITE_TAC[] THEN STRIP_TAC THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  EXPAND_TAC "P" THEN MATCH_MP_TAC MOI_FC2_LINK_EDGE_SUBSET THEN
  EXISTS_TAC `u:real^N` THEN ASM_REWRITE_TAC[] THEN
  REPEAT CONJ_TAC THEN MOI_FC2_HULL_TAC THEN ASM_MESON_TAC[]);;

let MOI_FC2_CONN_VERT_CASE = prove
 (`!(c:(real^N->bool)->bool) s.
     FINITE c /\ combinatorial_manifold 2 c /\ s IN c /\ aff_dim s = &0
     ==> ?x0. x0 IN UNIONS (simplicial_link (barycentric_subdivision c)
                                            (simplex_barycentre s)) /\
              !e. e IN simplicial_link (barycentric_subdivision c) (simplex_barycentre s) /\
                  aff_dim e = &1
                  ==> e SUBSET connected_component
                        (UNIONS (simplicial_link (barycentric_subdivision c)
                                                 (simplex_barycentre s))) x0`,
  REPEAT STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool) /\ lf_simplicial_complex c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `?v:real^N. s = {v}` (X_CHOOSE_THEN `v:real^N` SUBST_ALL_TAC) THENL
   [ASM_MESON_TAC[AFF_DIM_EQ_0]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{v:real^N}`] MOI_FRN_CM_PURE) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `t0:real^N->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `(v:real^N) IN t0` ASSUME_TAC THENL [ASM SET_TAC[]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t0:real^N->bool`; `v:real^N`]
                MOI_FRN_TRI_VERTS) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x:real^N` (X_CHOOSE_THEN `y:real^N` STRIP_ASSUME_TAC)) THEN
  SUBGOAL_THEN `(v:real^N) extreme_point_of t0 /\ x extreme_point_of t0` STRIP_ASSUME_TAC
  THENL
   [ASM_SIMP_TAC[EXTREME_POINT_OF_CONVEX_HULL_AFFINE_INDEPENDENT; IN_INSERT];
    ALL_TAC] THEN
  FIRST_X_ASSUM(K ALL_TAC o check (fun th -> concl th = `t0 = convex hull {v:real^N,x,y}`)) THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t0:real^N->bool`; `v:real^N`; `x:real^N`]
                MOI_FC2_EDGE_OF_SIMPLEX) THEN
  ASM_REWRITE_TAC[] THEN
  ABBREV_TAC `e0 = convex hull {v:real^N,x}` THEN STRIP_TAC THEN
  SUBGOAL_THEN `(v:real^N) IN e0` ASSUME_TAC THENL
   [EXPAND_TAC "e0" THEN MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
  MP_TAC(ISPECL [`{v:real^N}`; `e0:real^N->bool`; `t0:real^N->bool`]
                MOI_FC2_DISTINCT_DIMS) THEN
  ASM_REWRITE_TAC[AFF_DIM_SING] THEN STRIP_TAC THEN
  SUBGOAL_THEN
   `!q t. q IN c /\ t IN c /\ aff_dim q = &1 /\ aff_dim t = &2 /\
          (v:real^N) IN q /\ q SUBSET t
          ==> convex hull {simplex_barycentre q, simplex_barycentre t} IN
              simplicial_link (barycentric_subdivision c) (simplex_barycentre {v})`
  (LABEL_TAC "vedge") THENL
   [REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FC2_FLAG_LINK_EDGE THEN
    MP_TAC(ISPECL [`{v:real^N}`; `q:real^N->bool`; `t:real^N->bool`]
                  MOI_FC2_DISTINCT_DIMS) THEN
    ASM_REWRITE_TAC[AFF_DIM_SING] THEN STRIP_TAC THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
    MATCH_MP_TAC MOI_FC2_CHAIN3 THEN ASM_REWRITE_TAC[NOT_INSERT_EMPTY; SING_SUBSET] THEN
    ASM SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `simplex_barycentre (t0:real^N->bool)` THEN
  ABBREV_TAC `P = connected_component
                    (UNIONS (simplicial_link (barycentric_subdivision c)
                                             (simplex_barycentre {v:real^N})))
                    (simplex_barycentre (t0:real^N->bool))` THEN
  SUBGOAL_THEN `simplex_barycentre (t0:real^N->bool) IN P` ASSUME_TAC THENL
   [EXPAND_TAC "P" THEN MATCH_MP_TAC MOI_FC2_IN_OWN_COMPONENT THEN
    REWRITE_TAC[IN_UNIONS] THEN
    EXISTS_TAC `convex hull {simplex_barycentre e0, simplex_barycentre (t0:real^N->bool)}` THEN
    CONJ_TAC THENL
     [USE_THEN "vedge" MATCH_MP_TAC THEN ASM_REWRITE_TAC[];
      MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!q t w. q IN c /\ t IN c /\ aff_dim q = &1 /\ aff_dim t = &2 /\
            (v:real^N) IN q /\ q SUBSET t /\
            (w = simplex_barycentre q \/ w = simplex_barycentre t) /\ w IN P
            ==> convex hull {simplex_barycentre q, simplex_barycentre t} SUBSET P`
  (LABEL_TAC "vsub") THENL
   [REPEAT GEN_TAC THEN STRIP_TAC THEN EXPAND_TAC "P" THEN
    MATCH_MP_TAC MOI_FC2_LINK_EDGE_SUBSET THEN EXISTS_TAC `w:real^N` THEN
    ASM_REWRITE_TAC[] THEN
    (CONJ_TAC THENL [USE_THEN "vedge" MATCH_MP_TAC THEN ASM_REWRITE_TAC[]; ALL_TAC]) THEN
    (CONJ_TAC THENL [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[IN_INSERT]; ALL_TAC]) THEN
    UNDISCH_TAC `(w:real^N) IN P` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `{t | t IN c /\ aff_dim t = &2 /\ (v:real^N) IN t /\ simplex_barycentre t IN P} =
    {t | t IN c /\ aff_dim t = &2 /\ v IN t}`
  ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_FRN_SA_CM_LCONN THEN ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [REWRITE_TAC[SUBSET; IN_ELIM_THM] THEN MESON_TAC[];
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN
      EXISTS_TAC `t0:real^N->bool` THEN ASM_REWRITE_TAC[];
      MAP_EVERY X_GEN_TAC [`t:real^N->bool`; `t':real^N->bool`; `u:real^N`] THEN
      REWRITE_TAC[IN_ELIM_THM] THEN STRIP_TAC THEN ASM_REWRITE_TAC[] THEN
      SUBGOAL_THEN `(v:real^N) extreme_point_of t /\ u extreme_point_of t` STRIP_ASSUME_TAC
      THENL [CONJ_TAC THEN MATCH_MP_TAC MOI_FC2_VERTEX_EXTREME THEN
             EXISTS_TAC `c:(real^N->bool)->bool` THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
      MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `t:real^N->bool`; `v:real^N`; `u:real^N`]
                    MOI_FC2_EDGE_OF_SIMPLEX) THEN
      ASM_REWRITE_TAC[] THEN
      ABBREV_TAC `q = convex hull {v:real^N,u}` THEN STRIP_TAC THEN
      SUBGOAL_THEN `(v:real^N) IN q /\ (q:real^N->bool) SUBSET t'` STRIP_ASSUME_TAC THENL
       [EXPAND_TAC "q" THEN CONJ_TAC THENL
         [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT];
          MATCH_MP_TAC HULL_MINIMAL THEN ASM_REWRITE_TAC[INSERT_SUBSET; EMPTY_SUBSET] THEN
          ASM_MESON_TAC[moi_bar_complex; SIMPLEX_IMP_CONVEX]];
        ALL_TAC] THEN
      SUBGOAL_THEN `convex hull {simplex_barycentre (q:real^N->bool),
                                 simplex_barycentre (t':real^N->bool)} SUBSET P`
      MP_TAC THENL
       [USE_THEN "vsub" MATCH_MP_TAC THEN
        EXISTS_TAC `simplex_barycentre (q:real^N->bool)` THEN ASM_REWRITE_TAC[] THEN
        MATCH_MP_TAC(SET_RULE `!s t (x:real^N). x IN s /\ s SUBSET t ==> x IN t`) THEN
        EXISTS_TAC `convex hull {simplex_barycentre q, simplex_barycentre (t:real^N->bool)}` THEN
        CONJ_TAC THENL [MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]; ALL_TAC] THEN
        USE_THEN "vsub" MATCH_MP_TAC THEN
        EXISTS_TAC `simplex_barycentre (t:real^N->bool)` THEN ASM_REWRITE_TAC[];
        REWRITE_TAC[SUBSET] THEN DISCH_THEN MATCH_MP_TAC THEN
        MATCH_MP_TAC HULL_INC THEN REWRITE_TAC[IN_INSERT]]];
    ALL_TAC] THEN
  CONJ_TAC THENL
   [UNDISCH_TAC `simplex_barycentre (t0:real^N->bool) IN P` THEN EXPAND_TAC "P" THEN
    MESON_TAC[CONNECTED_COMPONENT_SUBSET; SUBSET];
    ALL_TAC] THEN
  X_GEN_TAC `e:real^N->bool` THEN STRIP_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `{v:real^N}`; `e:real^N->bool`]
                MOI_FC2_LINK_EDGE_FLAG) THEN
  ASM_REWRITE_TAC[NOT_INSERT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_THEN `u:real^N` (X_CHOOSE_THEN `e':real^N->bool`
    (X_CHOOSE_THEN `t':real^N->bool` STRIP_ASSUME_TAC))) THENL
   [ALL_TAC;
    UNDISCH_TAC `aff_dim(e':real^N->bool) = &1` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `{v:real^N} = e'`)) THEN
    REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC;
    UNDISCH_TAC `aff_dim(t':real^N->bool) = &2` THEN
    FIRST_X_ASSUM(SUBST1_TAC o SYM o check (fun th -> concl th = `{v:real^N} = t'`)) THEN
    REWRITE_TAC[AFF_DIM_SING] THEN INT_ARITH_TAC] THEN
  SUBGOAL_THEN `u:real^N = v` SUBST_ALL_TAC THENL
   [UNDISCH_TAC `{v:real^N} = {u}` THEN SET_TAC[]; ALL_TAC] THEN
  SUBGOAL_THEN `(v:real^N) IN t'` ASSUME_TAC THENL
   [UNDISCH_TAC `(e':real^N->bool) SUBSET t'` THEN UNDISCH_TAC `(v:real^N) IN e'` THEN
    SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `simplex_barycentre (t':real^N->bool) IN P` ASSUME_TAC THENL
   [UNDISCH_TAC
     `{t | t IN c /\ aff_dim t = &2 /\ (v:real^N) IN t /\ simplex_barycentre t IN P} =
      {t | t IN c /\ aff_dim t = &2 /\ v IN t}` THEN
    GEN_REWRITE_TAC LAND_CONV [EXTENSION] THEN REWRITE_TAC[IN_ELIM_THM] THEN
    DISCH_THEN(MP_TAC o SPEC `t':real^N->bool`) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  ASM_REWRITE_TAC[] THEN USE_THEN "vsub" MATCH_MP_TAC THEN
  EXISTS_TAC `simplex_barycentre (t':real^N->bool)` THEN ASM_REWRITE_TAC[]);;

(* Assembly: links of vertices of the barycentric subdivision are PL        *)
(* 1-spheres.                                                               *)

let MOI_FC2_LINK_CONNECTED = prove
 (`!(c:(real^N->bool)->bool) s.
     FINITE c /\ combinatorial_manifold 2 c /\ s IN c /\ ~(s = {})
     ==> connected (UNIONS (simplicial_link (barycentric_subdivision c)
                                            (simplex_barycentre s))) /\
         ~(UNIONS (simplicial_link (barycentric_subdivision c)
                                   (simplex_barycentre s)) = {})`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `aff_dim s = &0 \/ aff_dim s = &1 \/ aff_dim (s:real^N->bool) = &2`
  MP_TAC THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FRN_SA_CM_DIM) THEN
    ASM_REWRITE_TAC[] THEN
    MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_GE) THEN
    MP_TAC(ISPEC `s:real^N->bool` AFF_DIM_EQ_MINUS1) THEN
    ASM_REWRITE_TAC[] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  DISCH_THEN(REPEAT_TCL DISJ_CASES_THEN ASSUME_TAC) THENL
   [MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FC2_CONN_VERT_CASE);
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FC2_CONN_EDGE_CASE);
    MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FC2_CONN_TRI_CASE)] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `x0:real^N` STRIP_ASSUME_TAC) THEN
  (CONJ_TAC THENL
    [MATCH_MP_TAC MOI_FC2_CONN_FROM_EDGES THEN EXISTS_TAC `x0:real^N` THEN
     ASM_REWRITE_TAC[] THEN X_GEN_TAC `x:real^N` THEN DISCH_TAC THEN
     MATCH_MP_TAC MOI_FC2_LINK_POINT THEN ASM_REWRITE_TAC[];
     ASM SET_TAC[]]));;

let MOI_FC2_PL_SPHERE1_DIM = prove
 (`!s:real^N->bool. pl_sphere 1 s ==> 2 <= dimindex(:N)`,
  GEN_TAC THEN REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` STRIP_ASSUME_TAC) THEN
  MP_TAC(ISPEC `k:real^N->bool` AFF_DIM_LE_UNIV) THEN
  FIRST_X_ASSUM(MP_TAC o MATCH_MP AFF_DIM_SIMPLEX) THEN
  DISCH_THEN SUBST1_TAC THEN REWRITE_TAC[INT_OF_NUM_LE]);;

let MOI_FC2_LINK_DIM_LE1 = prove
 (`!(c:(real^N->bool)->bool) s q.
     FINITE c /\ combinatorial_manifold 2 c /\ s IN c /\ ~(s = {}) /\
     q IN simplicial_link (barycentric_subdivision c) (simplex_barycentre s)
     ==> aff_dim q <= &1`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; combinatorial_manifold]; ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`; `q:real^N->bool`]
                MOI_FC2_LINK_CHAIN) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `g:(real^N->bool)->bool` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `moi_bar_chain (c:(real^N->bool)->bool) g` ASSUME_TAC THENL
   [MATCH_MP_TAC MOI_BAR_CHAIN_SUBSET THEN
    EXISTS_TAC `(s:real^N->bool) INSERT g` THEN ASM_REWRITE_TAC[] THEN SET_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `(s:real^N->bool) INSERT g`]
                MOI_FRN_CHAIN_CARD_LE3) THEN
  ANTS_TAC THENL [ASM_MESON_TAC[MOI_FRN_SA_CM_DIM]; ALL_TAC] THEN
  SUBGOAL_THEN `FINITE (g:(real^N->bool)->bool)` ASSUME_TAC THENL
   [ASM_MESON_TAC[moi_bar_chain]; ALL_TAC] THEN
  ASM_SIMP_TAC[CARD_CLAUSES] THEN DISCH_TAC THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `g:(real^N->bool)->bool`]
                MOI_FRN_BARY_AFF_DIM) THEN
  ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
  UNDISCH_TAC `SUC (CARD (g:(real^N->bool)->bool)) <= 3` THEN
  REWRITE_TAC[GSYM INT_OF_NUM_LE; GSYM INT_OF_NUM_SUC] THEN INT_ARITH_TAC);;

let MOI_FC2_LINK_SPHERE = prove
 (`!(c:(real^N->bool)->bool) s.
     FINITE c /\ combinatorial_manifold 2 c /\ s IN c /\ ~(s = {})
     ==> pl_sphere 1 (UNIONS (simplicial_link (barycentric_subdivision c)
                                              (simplex_barycentre s)))`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool) /\ lf_simplicial_complex c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; combinatorial_manifold]; ALL_TAC] THEN
  SUBGOAL_THEN `2 <= dimindex(:N)` ASSUME_TAC THENL
   [SUBGOAL_THEN `?v:real^N. v extreme_point_of s` STRIP_ASSUME_TAC THENL
     [SUBGOAL_THEN `?n. n simplex (s:real^N->bool)` MP_TAC THENL
       [ASM_MESON_TAC[moi_bar_complex]; ALL_TAC] THEN
      DISCH_THEN(MP_TAC o CONJUNCT2 o MATCH_MP MOI_FRN_SIMPLEX_EXTREME_HULL) THEN
      ASM_CASES_TAC `{v:real^N | v extreme_point_of s} = {}` THEN
      ASM_REWRITE_TAC[CONVEX_HULL_EMPTY] THEN
      UNDISCH_TAC `~({v:real^N | v extreme_point_of s} = {})` THEN
      REWRITE_TAC[GSYM MEMBER_NOT_EMPTY; IN_ELIM_THM] THEN MESON_TAC[];
      ALL_TAC] THEN
    MATCH_MP_TAC MOI_FC2_PL_SPHERE1_DIM THEN
    EXISTS_TAC `UNIONS (simplicial_link c (v:real^N))` THEN
    FIRST_ASSUM(MP_TAC o CONJUNCT2 o GEN_REWRITE_RULE I [combinatorial_manifold]) THEN
    CONV_TAC NUM_REDUCE_CONV THEN DISCH_THEN MATCH_MP_TAC THEN
    ASM_MESON_TAC[MOI_FC2_EXTREME_VERTEX];
    ALL_TAC] THEN
  MP_TAC(ISPEC `simplicial_link (barycentric_subdivision c) (simplex_barycentre s:real^N)`
               MOI_S4L_CM1_CIRCLES) THEN
  ANTS_TAC THENL
   [ASM_REWRITE_TAC[] THEN REPEAT CONJ_TAC THENL
     [MATCH_MP_TAC MOI_FM3_LINK_SC THEN
      ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF; MOI_FC2_BSD_VERTEX] THEN ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FC2_LINK_DIM_LE1 THEN ASM_MESON_TAC[];
      REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_FC2_LINK_DEG2 THEN ASM_REWRITE_TAC[]];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `s:real^N->bool`] MOI_FC2_LINK_CONNECTED) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  ASM_SIMP_TAC[COMPONENTS_EQ_SING_EXISTS; IN_SING] THEN
  SUBGOAL_THEN
   `components (UNIONS (simplicial_link (barycentric_subdivision c)
                                       (simplex_barycentre s))) =
    {UNIONS (simplicial_link (barycentric_subdivision c) (simplex_barycentre (s:real^N->bool)))}`
  SUBST1_TAC THENL [ASM_REWRITE_TAC[COMPONENTS_EQ_SING]; ALL_TAC] THEN
  REWRITE_TAC[IN_SING] THEN MESON_TAC[]);;

let MOI_FC2_BARYCENTRIC_CM2 = prove
 (`!c:(real^N->bool)->bool.
     FINITE c /\ combinatorial_manifold 2 c
     ==> FINITE (barycentric_subdivision c) /\
         combinatorial_manifold 2 (barycentric_subdivision c)`,
  GEN_TAC THEN STRIP_TAC THEN CONJ_TAC THENL
   [ASM_SIMP_TAC[MOI_BAR_SUBDIVISION_FINITE]; ALL_TAC] THEN
  SUBGOAL_THEN `moi_bar_complex (c:(real^N->bool)->bool) /\ lf_simplicial_complex c`
  STRIP_ASSUME_TAC THENL
   [ASM_MESON_TAC[MOI_FRN_LF_BAR_COMPLEX; combinatorial_manifold]; ALL_TAC] THEN
  REWRITE_TAC[combinatorial_manifold] THEN CONV_TAC NUM_REDUCE_CONV THEN
  ASM_SIMP_TAC[BARYCENTRIC_SUBDIVISION_LF] THEN
  X_GEN_TAC `w:real^N` THEN ASM_SIMP_TAC[MOI_FC2_BSD_VERTEX] THEN
  DISCH_THEN(X_CHOOSE_THEN `s:real^N->bool` STRIP_ASSUME_TAC) THEN
  ASM_REWRITE_TAC[] THEN MATCH_MP_TAC MOI_FC2_LINK_SPHERE THEN ASM_REWRITE_TAC[]);;

(* ========================================================================= *)
(* The closed star of a vertex whose link is a PL 1-sphere is PL             *)
(* homeomorphic to a 2-simplex of real^2, the link going onto its relative   *)
(* frontier and the vertex to its barycentre (the 2D versions of             *)
(* MOI_STA_SIMPLEX_RF_R3 and MOI_STA_STAR_PLH of pc_moi_star, by the cone    *)
(* map of pc_moi_cone).  The arc-link case is MOI_S8TA_STAR_ARC in           *)
(* pc_moi_s28_tria.                                                          *)
(* ========================================================================= *)

let MOI_FC2_SIMPLEX_RF_R2 = prove
 (`!k:real^N->bool.
        &2 simplex k
        ==> ?S:real^2->bool f g.
                &2 simplex S /\
                pl_homeomorphism (relative_frontier S,relative_frontier k) (f,g)`,
  GEN_TAC THEN DISCH_TAC THEN
  SUBGOAL_THEN `~(k:real^N->bool = {})` MP_TAC THENL
   [DISCH_THEN SUBST_ALL_TAC THEN
    UNDISCH_TAC `&2 simplex ({}:real^N->bool)` THEN
    REWRITE_TAC[SIMPLEX_EMPTY] THEN INT_ARITH_TAC;
    ALL_TAC] THEN
  REWRITE_TAC[GSYM MEMBER_NOT_EMPTY] THEN
  DISCH_THEN(X_CHOOSE_TAC `a:real^N`) THEN
  ABBREV_TAC `k0 = IMAGE (\x:real^N. --a + x) k` THEN
  SUBGOAL_THEN `(vec 0:real^N) IN k0` ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN REWRITE_TAC[IN_IMAGE] THEN EXISTS_TAC `a:real^N` THEN
    ASM_REWRITE_TAC[] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 simplex (k0:real^N->bool)` ASSUME_TAC THENL
   [EXPAND_TAC "k0" THEN ASM_REWRITE_TAC[SIMPLEX_TRANSLATION_EQ]; ALL_TAC] THEN
  SUBGOAL_THEN `dim(span(k0:real^N->bool)) = 2` ASSUME_TAC THENL
   [REWRITE_TAC[DIM_SPAN] THEN
    MP_TAC(ISPEC `k0:real^N->bool` AFF_DIM_DIM_0) THEN
    ANTS_TAC THENL [MATCH_MP_TAC HULL_INC THEN ASM_REWRITE_TAC[]; ALL_TAC] THEN
    MP_TAC(ISPECL [`k0:real^N->bool`; `&2:int`] AFF_DIM_SIMPLEX) THEN
    ASM_REWRITE_TAC[] THEN DISCH_THEN SUBST1_TAC THEN
    REWRITE_TAC[INT_OF_NUM_EQ] THEN ARITH_TAC;
    ALL_TAC] THEN
  MP_TAC(ISPECL [`(:real^2)`; `span(k0:real^N->bool)`] ISOMETRY_SUBSPACES) THEN
  REWRITE_TAC[SUBSPACE_UNIV; SUBSPACE_SPAN; DIM_UNIV; DIMINDEX_2; IN_UNIV] THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m:real^2->real^N` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x y:real^2. (m:real^2->real^N) x = m y ==> x = y`
  ASSUME_TAC THENL
   [ASM_SIMP_TAC[LINEAR_INJECTIVE_0] THEN
    ONCE_REWRITE_TAC[GSYM NORM_EQ_0] THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  MP_TAC(ISPEC `m:real^2->real^N` LINEAR_INJECTIVE_LEFT_INVERSE) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `m':real^N->real^2` STRIP_ASSUME_TAC) THEN
  SUBGOAL_THEN `!x:real^2. (m':real^N->real^2) ((m:real^2->real^N) x) = x`
  ASSUME_TAC THENL
   [FIRST_X_ASSUM(MP_TAC o GEN_REWRITE_RULE I [FUN_EQ_THM]) THEN
    REWRITE_TAC[o_THM; I_THM];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `!y:real^N. y IN k0 ==> (m:real^2->real^N) ((m':real^N->real^2) y) = y`
  ASSUME_TAC THENL
   [X_GEN_TAC `y:real^N` THEN DISCH_TAC THEN
    SUBGOAL_THEN `(y:real^N) IN IMAGE (m:real^2->real^N) (:real^2)` MP_TAC
    THENL
     [ASM_REWRITE_TAC[] THEN MATCH_MP_TAC SPAN_SUPERSET THEN ASM_REWRITE_TAC[];
      ALL_TAC] THEN
    REWRITE_TAC[IN_IMAGE; IN_UNIV] THEN
    DISCH_THEN(X_CHOOSE_THEN `z:real^2` SUBST1_TAC) THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE (m:real^2->real^N) (IMAGE (m':real^N->real^2) k0) = k0`
  ASSUME_TAC THENL
   [UNDISCH_TAC
     `!y:real^N. y IN k0 ==> (m:real^2->real^N) ((m':real^N->real^2) y) = y`
    THEN SET_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN `&2 simplex (IMAGE (m':real^N->real^2) k0)` ASSUME_TAC THENL
   [MP_TAC(ISPECL [`m:real^2->real^N`; `IMAGE (m':real^N->real^2) k0`;
                   `&2:int`] SIMPLEX_LINEAR_IMAGE_EQ) THEN
    ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `relative_frontier k =
    IMAGE (\z:real^2. (m:real^2->real^N) z + a)
          (relative_frontier (IMAGE (m':real^N->real^2) k0))`
  ASSUME_TAC THENL
   [SUBGOAL_THEN `k = IMAGE (\x:real^N. a + x) k0` SUBST1_TAC THENL
     [UNDISCH_TAC `IMAGE (\x:real^N. --a + x) k = k0` THEN
      DISCH_THEN(SUBST1_TAC o SYM) THEN REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN
      REWRITE_TAC[VECTOR_ARITH `a + --a + x:real^N = x`; IMAGE_ID];
      ALL_TAC] THEN
    REWRITE_TAC[RELATIVE_FRONTIER_TRANSLATION] THEN
    SUBGOAL_THEN
     `relative_frontier k0 =
      IMAGE (m:real^2->real^N)
            (relative_frontier (IMAGE (m':real^N->real^2) k0))`
    SUBST1_TAC THENL
     [MATCH_MP_TAC EQ_TRANS THEN
      EXISTS_TAC `relative_frontier (IMAGE (m:real^2->real^N)
                    (IMAGE (m':real^N->real^2) k0))` THEN
      CONJ_TAC THENL
       [ASM_REWRITE_TAC[];
        MATCH_MP_TAC RELATIVE_FRONTIER_INJECTIVE_LINEAR_IMAGE THEN
        ASM_REWRITE_TAC[]];
      ALL_TAC] THEN
    REWRITE_TAC[GSYM IMAGE_o; o_DEF] THEN AP_THM_TAC THEN AP_TERM_TAC THEN
    REWRITE_TAC[FUN_EQ_THM] THEN VECTOR_ARITH_TAC;
    ALL_TAC] THEN
  MAP_EVERY EXISTS_TAC
   [`IMAGE (m':real^N->real^2) k0`;
    `\z:real^2. (m:real^2->real^N) z + a`;
    `\x:real^N. (m':real^N->real^2) x - m' a`] THEN
  ASM_REWRITE_TAC[] THEN
  MATCH_MP_TAC HOMEOMORPHISM_IMP_PL_HOMEOMORPHISM THEN CONJ_TAC THENL
   [SUBGOAL_THEN
     `!z:real^2. (m':real^N->real^2) ((m:real^2->real^N) z + a) - m' a = z`
    ASSUME_TAC THENL
     [ASM_SIMP_TAC[LINEAR_ADD] THEN VECTOR_ARITH_TAC; ALL_TAC] THEN
    REWRITE_TAC[homeomorphism; FORALL_IN_IMAGE] THEN
    ASM_REWRITE_TAC[GSYM IMAGE_o; o_DEF; IMAGE_ID] THEN
    ASM_SIMP_TAC[CONTINUOUS_ON_ADD; CONTINUOUS_ON_SUB; LINEAR_CONTINUOUS_ON;
                 CONTINUOUS_ON_CONST; ETA_AX];
    MATCH_MP_TAC PL_MAP_ON_AFFINE THEN ASM_REWRITE_TAC[] THEN
    MATCH_MP_TAC LOCALLY_POLYHEDRAL_PL_POLYHEDRON THEN
    MATCH_MP_TAC MOI_CMB_PL_POLYHEDRON_RELATIVE_FRONTIER THEN
    ASM_MESON_TAC[SIMPLEX_IMP_POLYTOPE]]);;

let MOI_FC2_STAR_CIRCLE = prove
 (`!(c:(real^N->bool)->bool) v.
     lf_simplicial_complex c /\ {v} IN c /\
     pl_sphere 1 (UNIONS (simplicial_link c v))
     ==> ?S:real^2->bool p q.
           &2 simplex S /\
           pl_homeomorphism
             (UNIONS {segment[v,y] | y | y IN UNIONS(simplicial_link c v)},S) (p,q) /\
           IMAGE p (UNIONS (simplicial_link c v)) = relative_frontier S /\
           p v = simplex_barycentre S`,
  REPEAT GEN_TAC THEN STRIP_TAC THEN
  UNDISCH_TAC `pl_sphere 1 (UNIONS (simplicial_link c (v:real^N)))` THEN
  REWRITE_TAC[pl_sphere] THEN CONV_TAC NUM_REDUCE_CONV THEN
  DISCH_THEN(X_CHOOSE_THEN `k:real^N->bool` (X_CHOOSE_THEN `f0:real^N->real^N`
    (X_CHOOSE_THEN `g0:real^N->real^N` STRIP_ASSUME_TAC))) THEN
  MP_TAC(ISPEC `k:real^N->bool` MOI_FC2_SIMPLEX_RF_R2) THEN
  ASM_REWRITE_TAC[] THEN
  DISCH_THEN(X_CHOOSE_THEN `S:real^2->bool` (X_CHOOSE_THEN `f1:real^2->real^N`
    (X_CHOOSE_THEN `g1:real^N->real^2` STRIP_ASSUME_TAC))) THEN
  SUBGOAL_THEN
   `pl_homeomorphism (relative_frontier S,UNIONS (simplicial_link c (v:real^N)))
      ((f0:real^N->real^N) o (f1:real^2->real^N),
       (g1:real^N->real^2) o (g0:real^N->real^N))`
  ASSUME_TAC THENL
   [MATCH_MP_TAC PL_HOMEOMORPHISM_COMPOSE THEN
    EXISTS_TAC `relative_frontier k:real^N->bool` THEN ASM_REWRITE_TAC[];
    ALL_TAC] THEN
  SUBGOAL_THEN
   `IMAGE ((g1:real^N->real^2) o (g0:real^N->real^N))
          (UNIONS (simplicial_link c (v:real^N))) = relative_frontier S /\
    IMAGE ((f0:real^N->real^N) o (f1:real^2->real^N)) (relative_frontier S) =
          UNIONS (simplicial_link c v)`
  STRIP_ASSUME_TAC THENL
   [UNDISCH_TAC
     `pl_homeomorphism (relative_frontier S,UNIONS (simplicial_link c (v:real^N)))
        ((f0:real^N->real^N) o (f1:real^2->real^N),
         (g1:real^N->real^2) o (g0:real^N->real^N))` THEN
    SIMP_TAC[pl_homeomorphism; homeomorphism];
    ALL_TAC] THEN
  MP_TAC(ISPECL [`S:real^2->bool`; `&2:int`] MOI_CON_SIMPLEX_RF_FACTS) THEN
  ANTS_TAC THENL [ASM_REWRITE_TAC[] THEN INT_ARITH_TAC; STRIP_TAC] THEN
  MP_TAC(ISPECL [`c:(real^N->bool)->bool`; `v:real^N`] MOI_STA_LINK_FACTS) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  MP_TAC(ISPECL
   [`relative_frontier S:real^2->bool`; `UNIONS (simplicial_link c (v:real^N))`;
    `simplex_barycentre (S:real^2->bool)`; `v:real^N`;
    `(f0:real^N->real^N) o (f1:real^2->real^N)`;
    `(g1:real^N->real^2) o (g0:real^N->real^N)`] MOI_CON_CONE_MAP) THEN
  ASM_REWRITE_TAC[] THEN STRIP_TAC THEN
  SUBGOAL_THEN `~(UNIONS (simplicial_link c (v:real^N)) = {})` ASSUME_TAC THENL
   [UNDISCH_TAC `~(relative_frontier S:real^2->bool = {})` THEN
    UNDISCH_TAC
     `IMAGE ((f0:real^N->real^N) o (f1:real^2->real^N)) (relative_frontier S) =
      UNIONS (simplicial_link c (v:real^N))` THEN
    SET_TAC[];
    ALL_TAC] THEN
  EXISTS_TAC `S:real^2->bool` THEN
  EXISTS_TAC `moi_con_conemap (UNIONS (simplicial_link c v)) (v:real^N)
               (simplex_barycentre (S:real^2->bool))
               ((g1:real^N->real^2) o (g0:real^N->real^N))` THEN
  EXISTS_TAC `moi_con_conemap (relative_frontier S)
               (simplex_barycentre (S:real^2->bool)) (v:real^N)
               ((f0:real^N->real^N) o (f1:real^2->real^N))` THEN
  ONCE_REWRITE_TAC[PL_HOMEOMORPHISM_SYM] THEN ASM_REWRITE_TAC[] THEN
  CONJ_TAC THENL
   [MATCH_MP_TAC EQ_TRANS THEN
    EXISTS_TAC `IMAGE ((g1:real^N->real^2) o (g0:real^N->real^N))
                      (UNIONS (simplicial_link c (v:real^N)))` THEN
    CONJ_TAC THENL [ALL_TAC; ASM_REWRITE_TAC[]] THEN
    MATCH_MP_TAC(SET_RULE
     `(!x:real^N. x IN s ==> (f:real^N->real^2) x = g x)
      ==> IMAGE f s = IMAGE g s`) THEN
    REPEAT STRIP_TAC THEN MATCH_MP_TAC MOI_CON_CONEMAP_ON_BASE THEN
    ASM_REWRITE_TAC[];
    MATCH_MP_TAC MOI_CON_CONEMAP_APEX THEN ASM_REWRITE_TAC[]]);;

